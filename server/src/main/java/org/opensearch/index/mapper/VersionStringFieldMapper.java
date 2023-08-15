/*
 * Copyright Elasticsearch B.V. and/or licensed to Elasticsearch B.V. under one
 * or more contributor license agreements. Licensed under the Elastic License
 * 2.0; you may not use this file except in compliance with the Elastic License
 * 2.0.
 */

package org.opensearch.index.mapper;

import org.apache.lucene.document.Field;
import org.apache.lucene.document.FieldType;
import org.apache.lucene.document.SortedSetDocValuesField;
import org.apache.lucene.index.FilteredTermsEnum;
import org.apache.lucene.index.IndexOptions;
import org.apache.lucene.index.SortedSetDocValues;
import org.apache.lucene.index.Term;
import org.apache.lucene.index.Terms;
import org.apache.lucene.index.TermsEnum;
import org.apache.lucene.search.AutomatonQuery;
import org.apache.lucene.search.DocValuesFieldExistsQuery;
import org.apache.lucene.search.FuzzyQuery;
import org.apache.lucene.search.MultiTermQuery;
import org.apache.lucene.search.Query;
import org.apache.lucene.search.RegexpQuery;
import org.apache.lucene.search.TermRangeQuery;
import org.apache.lucene.util.ArrayUtil;
import org.apache.lucene.util.AttributeSource;
import org.apache.lucene.util.BytesRef;
import org.apache.lucene.util.automaton.Automaton;
import org.apache.lucene.util.automaton.ByteRunAutomaton;
import org.opensearch.OpenSearchException;
import org.opensearch.common.Nullable;
import org.opensearch.common.collect.Iterators;
import org.opensearch.common.io.stream.StreamOutput;
import org.opensearch.common.lucene.BytesRefs;
import org.opensearch.common.lucene.Lucene;
import org.opensearch.common.lucene.search.AutomatonQueries;
import org.opensearch.common.unit.Fuzziness;
import org.opensearch.common.xcontent.XContentParser;
import org.opensearch.index.fielddata.IndexFieldData;
import org.opensearch.index.fielddata.ScriptDocValues;
import org.opensearch.index.fielddata.plain.SortedSetOrdinalsIndexFieldData;
import org.opensearch.index.mapper.VersionStringEncoder.EncodedVersion;
import org.opensearch.index.mapper.Mapper;
import org.opensearch.index.mapper.ParseContext;
import org.opensearch.index.mapper.SourceValueFetcher;
import org.opensearch.index.mapper.TermBasedFieldType;
import org.opensearch.index.mapper.TextSearchInfo;
import org.opensearch.index.mapper.ValueFetcher;
import org.opensearch.index.mapper.VersionStringEncoder;
import org.opensearch.index.query.QueryRewriteContext;
import org.opensearch.index.query.QueryShardContext;
import org.opensearch.index.query.support.QueryParsers;
import org.opensearch.search.DocValueFormat;
import org.opensearch.search.aggregations.support.CoreValuesSourceType;
import org.opensearch.search.lookup.SearchLookup;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.time.ZoneId;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.function.Supplier;

import static org.opensearch.search.SearchService.ALLOW_EXPENSIVE_QUERIES;

/**
 * A {@link FieldMapper} for indexing fields with version strings.
 */
public class VersionStringFieldMapper extends ParametrizedFieldMapper {

    private static final byte[] MIN_VALUE = new byte[16];
    private static final byte[] MAX_VALUE = new byte[16];
    static {
        Arrays.fill(MIN_VALUE, (byte) 0);
        Arrays.fill(MAX_VALUE, (byte) -1);
    }

    public static final String CONTENT_TYPE = "version_string_prototype";

    public static class Defaults {
        public static final FieldType FIELD_TYPE = new FieldType();

        static {
            FIELD_TYPE.setTokenized(false);
            FIELD_TYPE.setOmitNorms(true);
            FIELD_TYPE.setIndexOptions(IndexOptions.DOCS);
            FIELD_TYPE.freeze();
        }
    }

    static class Builder extends ParametrizedFieldMapper.Builder  {

        private final Parameter<Map<String, String>> meta = Parameter.metaParam();

        Builder(String name) {
            super(name);
        }

        private VersionStringFieldType buildFieldType(BuilderContext context, FieldType fieldtype) {
            return new VersionStringFieldType(context.path().pathAsText(name), fieldtype, meta.getValue());
        }

        @Override
        public VersionStringFieldMapper build(BuilderContext context) {
            FieldType fieldtype = new FieldType(Defaults.FIELD_TYPE);
            return new VersionStringFieldMapper(
                name,
                fieldtype,
                buildFieldType(context, fieldtype),
                multiFieldsBuilder.build(this, context),
                copyTo.build()
            );
        }

        @Override
        protected List<Parameter<?>> getParameters() {
            return org.opensearch.common.collect.List.of(meta);
        }
    }

    public static final TypeParser PARSER = new TypeParser((n, c) -> new Builder(n));

    public static final class VersionStringFieldType extends TermBasedFieldType {

        private VersionStringFieldType(String name, FieldType fieldType, Map<String, String> meta) {
            super(name, true, false, true, new TextSearchInfo(fieldType, null, Lucene.KEYWORD_ANALYZER, Lucene.KEYWORD_ANALYZER), meta);
        }

        @Override
        public String typeName() {
            return CONTENT_TYPE;
        }

       @Override
        public ValueFetcher valueFetcher(QueryShardContext context, SearchLookup searchLookup, @Nullable String format) {
            return SourceValueFetcher.toString(name(), context, format);
        }

        /*
        @Override
        public Query existsQuery(SearchExecutionContext context) {
            return new DocValuesFieldExistsQuery(name());
        }
        */

        /*
        @Override
        public Query prefixQuery(
            String value,
            MultiTermQuery.RewriteMethod method,
            boolean caseInsensitive,
            SearchExecutionContext context
        ) {
            return wildcardQuery(value + "*", method, caseInsensitive, context);
        }
        */

        /**
         * We cannot simply use RegexpQuery directly since we use the encoded terms from the dictionary, but the
         * automaton in the query will assume unencoded terms. We are running through all terms, decode them and
         * then run them through the automaton manually instead. This is not as efficient as intersecting the original
         * Terms with the compiled automaton, but we expect the number of distinct version terms indexed into this field
         * to be low enough and the use of "regexp" queries on this field rare enough to brute-force this
         */
        @Override
        public Query regexpQuery(
            String value,
            int syntaxFlags,
            int matchFlags,
            int maxDeterminizedStates,
            @Nullable MultiTermQuery.RewriteMethod method,
            QueryShardContext context
        ) {
            if (context.allowExpensiveQueries() == false) {
                throw new OpenSearchException(
                    "[regexp] queries cannot be executed when '" + ALLOW_EXPENSIVE_QUERIES.getKey() + "' is set to false."
                );
            }
            RegexpQuery query = new RegexpQuery(new Term(name(), new BytesRef(value)), syntaxFlags, matchFlags, maxDeterminizedStates) {

                @Override
                protected TermsEnum getTermsEnum(Terms terms, AttributeSource atts) throws IOException {
                    return new FilteredTermsEnum(terms.iterator(), false) {

                        @Override
                        protected AcceptStatus accept(BytesRef term) throws IOException {
                            byte[] decoded = VersionStringEncoder.decodeVersion(term).getBytes(StandardCharsets.UTF_8);
                            boolean accepted = compiled.runAutomaton.run(decoded, 0, decoded.length);
                            if (accepted) {
                                return AcceptStatus.YES;
                            }
                            return AcceptStatus.NO;
                        }
                    };
                }
            };

            if (method != null) {
                query.setRewriteMethod(method);
            }
            return query;
        }

        /**
         * We cannot simply use FuzzyQuery directly since we use the encoded terms from the dictionary, but the
         * automaton in the query will assume unencoded terms. We are running through all terms, decode them and
         * then run them through the automaton manually instead. This is not as efficient as intersecting the original
         * Terms with the compiled automaton, but we expect the number of distinct version terms indexed into this field
         * to be low enough and the use of "fuzzy" queries on this field rare enough to brute-force this
         */
        @Override
        public Query fuzzyQuery(
            Object value,
            Fuzziness fuzziness,
            int prefixLength,
            int maxExpansions,
            boolean transpositions,
            QueryShardContext context
        ) {
            if (context.allowExpensiveQueries() == false) {
                throw new OpenSearchException(
                    "[fuzzy] queries cannot be executed when '" + ALLOW_EXPENSIVE_QUERIES.getKey() + "' is set to false."
                );
            }
            return new FuzzyQuery(
                new Term(name(), (BytesRef) value),
                fuzziness.asDistance(BytesRefs.toString(value)),
                prefixLength,
                maxExpansions,
                transpositions
            ) {
                @Override
                protected TermsEnum getTermsEnum(Terms terms, AttributeSource atts) throws IOException {
                    ByteRunAutomaton runAutomaton = getAutomata().runAutomaton;

                    return new FilteredTermsEnum(terms.iterator(), false) {

                        @Override
                        protected AcceptStatus accept(BytesRef term) throws IOException {
                            byte[] decoded = VersionStringEncoder.decodeVersion(term).getBytes(StandardCharsets.UTF_8);
                            boolean accepted = runAutomaton.run(decoded, 0, decoded.length);
                            if (accepted) {
                                return AcceptStatus.YES;
                            }
                            return AcceptStatus.NO;
                        }
                    };
                }
            };
        }

        @Override
        public Query wildcardQuery(
            String value,
            MultiTermQuery.RewriteMethod method,
            boolean caseInsensitive,
            QueryShardContext context
        ) {
            if (context.allowExpensiveQueries() == false) {
                throw new OpenSearchException(
                    "[wildcard] queries cannot be executed when '" + ALLOW_EXPENSIVE_QUERIES.getKey() + "' is set to false."
                );
            }

            // FIXME(marcoaz): Replace AutomatonQuery with a VersionStringField specific variant.
            //VersionFieldWildcardQuery query = new VersionFieldWildcardQuery(new Term(name(), value), caseInsensitive);
            Term term = new Term(name(), value);
            if (caseInsensitive) {
                return AutomatonQueries.caseInsensitiveWildcardQuery(term, method);
            }
            AutomatonQuery query = new AutomatonQuery(term, new Automaton());
            QueryParsers.setRewriteMethod(query, method);
            return query;
        }

        @Override
        protected BytesRef indexedValueForSearch(Object value) {
            String valueAsString;
            if (value instanceof String) {
                valueAsString = (String) value;
            } else if (value instanceof BytesRef) {
                // encoded string, need to re-encode
                valueAsString = ((BytesRef) value).utf8ToString();
            } else {
                throw new IllegalArgumentException("Illegal value type: " + value.getClass() + ", value: " + value);
            }
            return VersionStringEncoder.encodeVersion(valueAsString).bytesRef;
        }

        @Override
        public IndexFieldData.Builder fielddataBuilder(String fullyQualifiedIndexName, Supplier<SearchLookup> searchLookup) {
            return new SortedSetOrdinalsIndexFieldData.Builder(name(), VersionStringScriptDocValues::new, CoreValuesSourceType.VERSION_STRING);
        }

        @Override
        public Object valueForDisplay(Object value) {
            if (value == null) {
                return null;
            }
            return VERSION_DOCVALUE.format((BytesRef) value);
        }

        @Override
        public DocValueFormat docValueFormat(@Nullable String format, ZoneId timeZone) {
            if (format != null) {
                throw new IllegalArgumentException("Field [" + name() + "] of type [" + typeName() + "] does not support custom formats");
            }
            if (timeZone != null) {
                throw new IllegalArgumentException(
                    "Field [" + name() + "] of type [" + typeName() + "] does not support custom time zones"
                );
            }
            return VERSION_DOCVALUE;
        }

        @Override
        public Query rangeQuery(
            Object lowerTerm,
            Object upperTerm,
            boolean includeLower,
            boolean includeUpper,
            QueryShardContext context
        ) {
            BytesRef lower = lowerTerm == null ? null : indexedValueForSearch(lowerTerm);
            BytesRef upper = upperTerm == null ? null : indexedValueForSearch(upperTerm);
            return new TermRangeQuery(name(), lower, upper, includeLower, includeUpper);
        }
    }

    private final FieldType fieldType;

    private VersionStringFieldMapper(
        String simpleName,
        FieldType fieldType,
        MappedFieldType mappedFieldType,
        MultiFields multiFields,
        CopyTo copyTo
    ) {
        super(simpleName, mappedFieldType, multiFields, copyTo);
        this.fieldType = fieldType;
    }

    @Override
    public VersionStringFieldType fieldType() {
        return (VersionStringFieldType) super.fieldType();
    }

    @Override
    protected String contentType() {
        return CONTENT_TYPE;
    }

    @Override
    protected void parseCreateField(ParseContext context) throws IOException {
        String versionString;
        if (context.externalValueSet()) {
            versionString = context.externalValue().toString();
        } else {
            XContentParser parser = context.parser();
            if (parser.currentToken() == XContentParser.Token.VALUE_NULL) {
                return;
            } else {
                versionString = parser.textOrNull();
            }
        }

        if (versionString == null) {
            return;
        }

        EncodedVersion encoding = VersionStringEncoder.encodeVersion(versionString);
        BytesRef encodedVersion = encoding.bytesRef;
        context.doc().add(new Field(fieldType().name(), encodedVersion, fieldType));
        context.doc().add(new SortedSetDocValuesField(fieldType().name(), encodedVersion));
    }

    @Override
    public Iterator<Mapper> iterator() {
        List<Mapper> subIterators = new ArrayList<>();
        @SuppressWarnings("unchecked")
        Iterator<Mapper> concat = Iterators.concat(super.iterator(), subIterators.iterator());
        return concat;
    }

    public static DocValueFormat VERSION_DOCVALUE = new DocValueFormat() {

        @Override
        public String getWriteableName() {
            return "version";
        }

        @Override
        public void writeTo(StreamOutput out) {}

        @Override
        public String format(BytesRef value) {
            return VersionStringEncoder.decodeVersion(value);
        }

        @Override
        public BytesRef parseBytesRef(String value) {
            return VersionStringEncoder.encodeVersion(value).bytesRef;
        }

        @Override
        public String toString() {
            return getWriteableName();
        }
    };

    @Override
    public ParametrizedFieldMapper.Builder getMergeBuilder() {
        return new Builder(simpleName()).init(this);
    }

    /**
     * Field type for VersionString Scripted doc values
     *
     * @opensearch.internal
     */
    public static final class VersionStringScriptDocValues extends ScriptDocValues<String> {

        private final SortedSetDocValues in;
        private long[] ords = new long[0];
        private int count;

        public VersionStringScriptDocValues(SortedSetDocValues in) {
            this.in = in;
        }

        @Override
        public void setNextDocId(int docId) throws IOException {
            count = 0;
            if (in.advanceExact(docId)) {
                for (long ord = in.nextOrd(); ord != SortedSetDocValues.NO_MORE_ORDS; ord = in.nextOrd()) {
                    ords = ArrayUtil.grow(ords, count + 1);
                    ords[count++] = ord;
                }
            }
        }

        public String getValue() {
            return get(0);
        }

        @Override
        public String get(int index) {
            if (count == 0) {
                throw new IllegalStateException(
                    "A document doesn't have a value for a field! " + "Use doc[<field>].size()==0 to check if a document is missing a field!"
                );
            }
            try {
                return VersionStringEncoder.decodeVersion(in.lookupOrd(ords[index]));
            } catch (IOException e) {
                throw new RuntimeException(e);
            }
        }

        @Override
        public int size() {
            return count;
        }
    }
}

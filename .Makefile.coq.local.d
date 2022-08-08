src/Basics.vo src/Basics.glob src/Basics.v.beautified src/Basics.required_vo: src/Basics.v 
src/Basics.vio: src/Basics.v 
src/Basics.vos src/Basics.vok src/Basics.required_vos: src/Basics.v 
src/Cypher.vo src/Cypher.glob src/Cypher.v.beautified src/Cypher.required_vo: src/Cypher.v src/PropertyGraph.vo
src/Cypher.vio: src/Cypher.v src/PropertyGraph.vio
src/Cypher.vos src/Cypher.vok src/Cypher.required_vos: src/Cypher.v src/PropertyGraph.vos
src/EvalExamples.vo src/EvalExamples.glob src/EvalExamples.v.beautified src/EvalExamples.required_vo: src/EvalExamples.v src/Cypher.vo src/KleeneTranslation.vo src/PGMatrixExtraction.vo src/Utils.vo
src/EvalExamples.vio: src/EvalExamples.v src/Cypher.vio src/KleeneTranslation.vio src/PGMatrixExtraction.vio src/Utils.vio
src/EvalExamples.vos src/EvalExamples.vok src/EvalExamples.required_vos: src/EvalExamples.v src/Cypher.vos src/KleeneTranslation.vos src/PGMatrixExtraction.vos src/Utils.vos
src/KleeneTranslation.vo src/KleeneTranslation.glob src/KleeneTranslation.v.beautified src/KleeneTranslation.required_vo: src/KleeneTranslation.v src/Cypher.vo src/PropertyGraph.vo src/PGMatrixExtraction.vo src/Utils.vo
src/KleeneTranslation.vio: src/KleeneTranslation.v src/Cypher.vio src/PropertyGraph.vio src/PGMatrixExtraction.vio src/Utils.vio
src/KleeneTranslation.vos src/KleeneTranslation.vok src/KleeneTranslation.required_vos: src/KleeneTranslation.v src/Cypher.vos src/PropertyGraph.vos src/PGMatrixExtraction.vos src/Utils.vos
src/Maps.vo src/Maps.glob src/Maps.v.beautified src/Maps.required_vo: src/Maps.v 
src/Maps.vio: src/Maps.v 
src/Maps.vos src/Maps.vok src/Maps.required_vos: src/Maps.v 
src/PGMatrixExtraction.vo src/PGMatrixExtraction.glob src/PGMatrixExtraction.v.beautified src/PGMatrixExtraction.required_vo: src/PGMatrixExtraction.v src/PropertyGraph.vo src/Utils.vo src/Basics.vo
src/PGMatrixExtraction.vio: src/PGMatrixExtraction.v src/PropertyGraph.vio src/Utils.vio src/Basics.vio
src/PGMatrixExtraction.vos src/PGMatrixExtraction.vok src/PGMatrixExtraction.required_vos: src/PGMatrixExtraction.v src/PropertyGraph.vos src/Utils.vos src/Basics.vos
src/PropertyGraph.vo src/PropertyGraph.glob src/PropertyGraph.v.beautified src/PropertyGraph.required_vo: src/PropertyGraph.v 
src/PropertyGraph.vio: src/PropertyGraph.v 
src/PropertyGraph.vos src/PropertyGraph.vok src/PropertyGraph.required_vos: src/PropertyGraph.v 
src/Queries.vo src/Queries.glob src/Queries.v.beautified src/Queries.required_vo: src/Queries.v src/Cypher.vo src/PropertyGraph.vo src/Maps.vo src/Utils.vo
src/Queries.vio: src/Queries.v src/Cypher.vio src/PropertyGraph.vio src/Maps.vio src/Utils.vio
src/Queries.vos src/Queries.vok src/Queries.required_vos: src/Queries.v src/Cypher.vos src/PropertyGraph.vos src/Maps.vos src/Utils.vos
src/Utils.vo src/Utils.glob src/Utils.v.beautified src/Utils.required_vo: src/Utils.v src/PropertyGraph.vo
src/Utils.vio: src/Utils.v src/PropertyGraph.vio
src/Utils.vos src/Utils.vok src/Utils.required_vos: src/Utils.v src/PropertyGraph.vos

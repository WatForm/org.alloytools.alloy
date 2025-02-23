package ca.uwaterloo.watform.portus;

/**
 * A Preprocessor modifies the Alloy AST before the main translation.
 */
interface Preprocessor {

    /**
     * Run the preprocessor on the problem, transforming it into a new problem which should be translated.
     */
    AlloyProblem preprocess(AlloyProblem problem);

}

# Dash: Declarative Abstract State hierarchy


Dash is an extension of Alloy for modelling transition systems. It combines the control-oriented constructs of Statecharts with the 
declarative modelling of Alloy.
From Statecharts, Dash inherits a means to specify hierarchy, concurrency, and 
communication, three useful aspects to describe the behaviour of reactive systems.
From Alloy, Dash uses the expressiveness of relational logic and set theory to 
abstractly and declaratively describe structures, data, and operations.

Examples of Dash models can be found at: https://github.com/WatForm/watform-models/tree/master/dash

This repo contains an extension to the Alloy Analyzer to edit and analyze Dash models.  All regular functionality of the Alloy Analyzer is present plus the support for Dash (see below).

The README.md for the original Alloy Analyzer can be found in README-alloy.md in this directory.

# Building the project


The project is built using the same directions as for building the (non-extended) Alloy Analyzer (repeated below for completeness).

Navigate to the

```org.alloytools.alloy```

directory in the command-line and then run the

```gradle build```

command. In the scenario that this command fails to build the project, please try

```./gradle build``` or ```./gradlew build``` or ```gradle build -x test```

Please note that ```gradle build -x test``` will not run the unit tests.

# Running the Alloy Analyzer GUI Extended with Dash

There is no change in the directions for how to run the Alloy Analyzer GUI extended with Dash.  These instructions are:

```java -jar org.alloytools.alloy.dist/target/org.alloytools.alloy.dist.jar```


# Running the Dash to Alloy Translator at the Command Line


To run the Dash to Alloy Translator at the command line, use the following command:

```java -jar org.alloytools.alloy.dashbuild/target/org.alloytools.alloy.dashbuild.jar```

This will give provide a prompt to specify a path for a Dash (.dsh) file input and
an output path where the Alloy model will be stored. 

# Overview: Modifications to the Alloy Analyzer GUI


The Alloy Analyzer GUI has been extended to support editing, translating, and analyzing Dash models.

**New Buttons and Menu Items**

- The ```New Dash``` button is situated in the Toolbar beside the existing `New` button and in the Menubar under the `File` option. Clicking this button will open a new tab with the .dsh extension and set the Alloy Analyzer to the Dash Mode. The Dash Mode is automatically activated whenever a tab with .dsh extension is the front tab. 

- If a file is opened with a .dsh extension, it automatically goes into Dash Mode and puts the file in a Dash editing window.

- The set of keywords that are used by Dash and those used by Alloy are highlighted in the Dash editing window.

- When in Dash Mode, a new button called ```Translate``` appears which translates the Dash model to an Alloy model in an Alloy editing tab.  Translate is also a menu item in the Execute menu.  During translation, both Dash and Alloy validation checks are completed.

- When in Dash Mode, the ```Execute``` button translates the Dash model to an Alloy model (displaying it in an Alloy tab), then executes the Alloy model and displays any instance.  The instances are displayed in a particular theme that makes Snapshots the nodes and the edges the transitions.

- Notes about the translation: 
1) The predicates and check/run commands may not appear in the Alloy file in the same order that they appear in the Dash file.
2) Any user-created comments in Dash will not appear in the Alloy file.  The translation adds some comments but the user-created comments are lost at parsing.

**Dash Options**

If the user opens a file with a Dash model or opens an empty tab using the ```New Dash``` button, there will be new options under the ```Option``` button in the Menubar that affect the Dash to Alloy translation. These are:

- `Variables Unchanged`: If this option is set to ``true``,  then any variables in that are not explicitly referenced in a taken transition will remain unchanged once a small step has been taken (addressing the frame problem). This is set to ``On`` by default.

- `Assume Single Input`: This option constrains the number of events that be present in a snapshot such that at most one environmental event can be present in every snapshot. This set to ``Off`` by default.

- `Generate Significance Axioms`: This option automatically creates predicates in the Alloy model for various significance axioms.  These predicates can be run to find a scope `big` enough that an instance of every Dash transition is in the Alloy instance or every basic state is reachable in the model, etc. This is set to ``On`` by default.  For more information on significance axioms see:
	+ Farheen et al., Transitive-closure-based model checking in Alloy. Journal of Software and Systems Modelling, 19:721--740, 2020 
	+ Jose Serna. Dash: Declarative Behavioural Modelling in Alloy. MMath thesis, University of Waterloo, David R. Cheriton School of Computer Science, 2019) 

- `CTL TCMC`: This option enables the automatic import of the ctl module for transitive-closure-based model checking (TCMC) and generates a fact that allows the user to perform model checking. This is set to ``On`` by default.  ctl.als is included in the util files.




# Code Modifications


In creating this extension to the Alloy Analyzer, we have added files to support Dash and made very minor modifications to existing code.  

The new Java files added to the Alloy Analyzer are described below:

**org.alloytools.alloy.dash/src/main/java/ca/uwaterloo/watform/parser/Dash.cup:** This is the grammar file
for Dash. It is an extention to Alloy.cup (the grammar file for Alloy). The Dash.cup retains the grammar
for Alloy as it will need to parse Alloy expressions, signatures, functions, predicates, etc. Once the 
project is built using gradle, this file will be used by CUP to create the DashParser.java file and 
it will be responsible for parsing Dash models.

**org.alloytools.alloy.dash/src/main/java/ca/uwaterloo/watform/parser/Dash.lex:** This is the lexer file
for Dash. It is an extention to Alloy.lex (the lexer file for Alloy). The Dash.lex retains the Alloy tokens
as they will appear in a Dash model. Once the  project is built using gradle, this file will be used by JFlex
to create the DashLexer.java file to store the Dash/Alloy tokens.

**org.alloytools.alloy.dash/src/main/java/ca/uwaterloo/watform/parser/DashModule.java :** This is an extension of
of the AlloyModule file located within the same directory. This file performs the same tasks as the 
AlloyModule file, but it additionally builds the internal data structure for Dash models after they
have been parsed. This internal data structure is stored within containers inside the file, and is 
later accessed by other files that are responsible for converting a Dash model to an Alloy model

**org.alloytools.alloy.dash/src/main/java/ca/uwaterloo/watform/parser/DashModuleToString.java :** This is used to print out
an Alloy AST after a Dash model has been converted to an Alloy AST. It iterates through all the openers, signatures,
functions, predicates, commands in a DashModule containing an Alloy AST and print them to the console.
Any labels with paths will have paths removed (`this/name` becomes `name`) and the Alloy string will be pretty printed.

**org.alloytools.alloy.dash/src/main/java/ca/uwaterloo/watform/parser/DashValidation.java :** This is used to check
for well-formedness conditions of a Dash model. It is called immediately after the internal data structure
has been build and it makes sure that the parsed Dash model is correct i.e. two states in the same hierarchical level
do not have the same name, correct variable references, default states exist, etc.

**org.alloytools.alloy.dash/src/main/java/ca/uwaterloo/watform/transform/DashToCoreDash.java :** This is used to convert the
internal Dash data structure in the DashModule and convert it to CoreDash. CoreDash expands transitions and modifies
commands within transitions such that it is easier to convert a Dash model to an Alloy model. It will largely modify
transitions stored inside the DashModule and create new transitions if necessary.

**org.alloytools.alloy.dash/src/main/java/ca/uwaterloo/watform/transform/CoreDashToAlloy.java :** This is used to create
an Alloy AST using a DashModule that is holding a CoreDash data structure. It will create the necessary Alloy 
ASTs such as signature, predicate, fact ASTs in order to tranform a CoreDash model to its respective Alloy model.
It will additionally create a command AST that will be used to build Alloy instances using Kodkod.

**org.alloytools.alloy.dash/src/main/java/ca/uwaterloo/watform/ast/ :** This folder contains several new Dash AST files.
These are important for storing the required information regarding any parsed Dash model. These AST files will be
used by the DashParser when parsing a Dash model.

**org.alloytools.alloy.application/src/main/java/ca/uwaterloo/watform/dash4whole/Dash.java :** This is called by the
jar file in the command line. It takes in a .dsh file as an input, converts the Dash model to CoreDash and then
to an Alloy AST. The Alloy AST is stored in a DashModule object that contains that necessary signatures, predicates,
facts and commands needed to create an Alloy instance from the Alloy AST by passing the AST to Kodkod. 
Alloy makes use of a CompModule object to store the Alloy AST, but Dash uses a DashModule instead as functions 
within a CompModule are inaccessible. 

**org.alloytools.alloy.dash/src/test/java/org/alloytools/dash/core/DashModelsTest.java :** This contains the unit tests for the 
Dash to Core Dash, Core Dash to Alloy and the DashModuleToString (converting an Alloy AST to a human-readable Alloy model) functionalities.
The unit tests are run every time the project is built using Gradle. Any failure of the unit tests will result in a failed build and the error message(s)
from the a failed unit test will can be found in: 'org.alloytools.alloy.dash\target\reports\tests\test\index.html'

The modifications to existing Alloy GUI files are described below:

**org.alloytools.alloy.application/src/main/java/edu/mit/csail/sdg/alloy4whole/SimpleGUI:**
- Added `doTranslate` to translate .dsh file and open a new tab with translated alloy. The corresponding translate button only appears when editing dash.
- Added `doNewDash()` for opening new tab in "dash mode" (currently unused)
- Modified `doRefreshRun()` to only display dash options in the run menu, and appropriately parse dash and log errors.
- Misc changes to add .dsh option when opening and saving files.

**org.alloytools.alloy.application/src/main/java/edu/mit/csail/sdg/alloy4whole/SimpleReporter:**
- Modified `SimpleTask1`'s run function to handle dash code.

**org.alloytools.alloy.core/src/main/java/edu/mit/csail/sdg/alloy4/OurSyntaxWidget:**
- Added `editingDash` field to indicate if the textbox is editing dash
- Misc changes to name add .dsh extension to untitled dash files

**org.alloytools.alloy.core/src/main/java/edu/mit/csail/sdg/alloy4/OurTabbedSyntaxWidget:**
- Modified `newTab()` function to create new `OurSyntaxWidgets` in "Dash Mode"

# Credits

The Dash language was created by Jose Serna and Nancy Day. The integration of Dash within the Alloy Analyzer was completed by Tamjid Hossain.  Kai Hsiang Yang contributed to the integration with the GUI.  Nancy Day provided guidance on the implementation.  Information on Dash can be found in:

* Jose Serna. Dash: Declarative Behavioural Modelling in Alloy. MMath thesis, University of Waterloo, David R. Cheriton School of Computer Science, 2019. [https://cs.uwaterloo.ca/~nday/pdf/theses/2019-01-jserna-mmath-thesis.pdf]
* Jose Serna, Nancy A. Day, and Sabria Farheen. Dash: A new language for declarative behavioural requirements with control state hierarchy. In International Workshop on Model-Driven Requirements Engineering (MoDRE) @ IEEE International Requirements Engineering Conference (RE), pages 64--68. IEEE Computer Society, September 2017. [https://cs.uwaterloo.ca/~nday/pdf/refereed/2017-SeDaFa-modre.pdf]
* Amin Bandali. A Comprehensive Study of Declarative Modelling Languages. MMath thesis, University of Waterloo, David R. Cheriton School of Computer Science, 2020. [https://cs.uwaterloo.ca/~nday/pdf/theses/2020-07-15-bandali-mmath-thesis.pdf]
* Ali Abbassi, Amin Bandali, Nancy A. Day, and Jose Serna. A comparison of the declarative modelling languages B, Dash, and TLA+. In International Workshop on Model-Driven Requirements Engineering (MoDRE) @ IEEE International Requirements Engineering Conference (RE), pages 11--20. IEEE Computer Society, August 2018. [https://cs.uwaterloo.ca/~nday/pdf/refereed/2018-AbBa-modre.pdf]

Dash continues to be developed.  Extensions to Dash are discussed in:
* Tamjid Hossain and Nancy A. Day. Dash+: Extending alloy with hierarchical states and replicated processes for modelling transition systems. In International Workshop on Model-Driven Requirements Engineering (MoDRE) @ IEEE International Requirements Engineering Conference (RE). IEEE, September 2021. [https://cs.uwaterloo.ca/~nday/pdf/refereed/2021-HoDa-modre.pdf]

# Issues/Bugs	

If you find problems with this implemenation or have feature suggestions, please make an issue in this repository. General comments can be sent to Nancy Day (nday@uwaterloo.ca) or Tamjid Hossaid (t7hossain@uwaterloo.ca). 






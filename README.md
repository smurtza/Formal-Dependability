# Formal-Dependability
Contains all the thesis HOL scripts
This work is part of a PhD Dissertation entitled "Formal Dependability Analysis using Higher-order-logic Theorem Proving".

This formaliation is carried out in HOL-kananaskis-10 and builds successfully.

List of files included in the project:

RBDScript.sml				Contains the formalization of RBD configurations
FT_deepScript.sml			Contains the formalization of FT gates and PIE principle
VDCScript.sml				Formalization about the reliability analysis of virutal data center
transform_FT_RBDscipt.sml	Lemmas about either way transformation of RBD and FT models
smart_gridScript.sml		Formalization describing the dependability analysis of smart grid substation
auto_smart_grid.ml			SML functions for automatic simplification and computation of dependability properties

To use the proof script, follow the steps below:
 
1) Run HOLmake in the folder HOL-script
2) Open the auto_smart_grid.ml
3) Load directory path to HOL shell
4) Run the script in HOL shell


Note: For any queries about this project contact:
Waqar Ahmed on email address waqar.ahmad@seecs.nust.edu.pk 

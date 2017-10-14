# Formal-Dependability
Contains all the thesis HOL scripts

This work is part of a PhD Dissertation entitled "Formal Dependability Analysis using Higher-order-logic Theorem Proving".

This formaliation is carried out in HOL-kananaskis-10 in Linux platform and builds successfully.

List of files included in the project:

RBDScript.sml				               Contains the formalization of RBD configurations

FT_deepScript.sml			            Contains the formalization of FT gates and PIE principle

VDCScript.sml				               Formalization about the reliability analysis of virutal data center

transform_FT_RBDscipt.sml	      Lemmas about either way transformation of RBD and FT models

smart_gridScript.sml		          Formalization describing the dependability analysis of smart grid substation

auto_smart_grid.ml			           SML functions for automatic simplification and computation of dependability properties

WSNScript.sml			Contains the formalization related to reliability analysis of WSN data transport protocol 

frogpScript.sml			Contains the formalization related to reliability analysis of oil and gas pipelines

To use the proof script, follow the steps below:

1) Install latest version of HOL by downloading it from  https://hol-theorem-prover.org/ or
	(Follow the steps mentioned in http://save.seecs.nust.edu.pk/Downloads/Installation%20of%20HOL%20&%20HOL-LIGHT%20in%20Linux.pdf) 
 
2) Open Emacs and load the file "hol-mode.el" 
	(ALT-x load-file <PATH to HOL folder>/tools/hol-mode.el)

3) Enter ALT+H 3, windows split into two and the hol starts

1) Run HOLmake in the folder HOL-script. At the top of Emacs window, click HOL tab. In the Process option, click Run Holmake

2) Open the auto_smart_grid.ml. 

3) Load directory path to HOL shell. loadPath := "<PATH to HOL script files>/Formal-Dependability" :: !loadPath; 

4) Run the script in HOL shell


Note: For any queries about this project contact:

Waqar Ahmed on email address waqar.ahmad@seecs.nust.edu.pk 

%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:52:11 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   12 (  24 expanded)
%              Number of clauses        :    7 (   8 expanded)
%              Number of leaves         :    2 (   6 expanded)
%              Depth                    :    5
%              Number of atoms          :   24 (  66 expanded)
%              Number of equality atoms :   12 (  33 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t201_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( k7_relat_1(X2,X1) = k7_relat_1(X3,X1)
           => k9_relat_1(X2,X1) = k9_relat_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t201_relat_1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(c_0_2,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ! [X3] :
            ( v1_relat_1(X3)
           => ( k7_relat_1(X2,X1) = k7_relat_1(X3,X1)
             => k9_relat_1(X2,X1) = k9_relat_1(X3,X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t201_relat_1])).

fof(c_0_3,plain,(
    ! [X4,X5] :
      ( ~ v1_relat_1(X5)
      | k2_relat_1(k7_relat_1(X5,X4)) = k9_relat_1(X5,X4) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

fof(c_0_4,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v1_relat_1(esk3_0)
    & k7_relat_1(esk2_0,esk1_0) = k7_relat_1(esk3_0,esk1_0)
    & k9_relat_1(esk2_0,esk1_0) != k9_relat_1(esk3_0,esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_2])])])).

cnf(c_0_5,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_6,negated_conjecture,
    ( k7_relat_1(esk2_0,esk1_0) = k7_relat_1(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk2_0,esk1_0)) = k9_relat_1(esk3_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_5,c_0_6]),c_0_7])])).

cnf(c_0_9,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_10,negated_conjecture,
    ( k9_relat_1(esk2_0,esk1_0) != k9_relat_1(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_11,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_5,c_0_8]),c_0_9])]),c_0_10]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n019.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 17:18:07 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.36  # AutoSched0-Mode selected heuristic G_E___107_C00_02_nc_F1_PI_AE_Q4_CS_SP_PS_S00EN
% 0.13/0.36  # and selection function PSelectSmallestOrientable.
% 0.13/0.36  #
% 0.13/0.36  # Preprocessing time       : 0.026 s
% 0.13/0.36  # Presaturation interreduction done
% 0.13/0.36  
% 0.13/0.36  # Proof found!
% 0.13/0.36  # SZS status Theorem
% 0.13/0.36  # SZS output start CNFRefutation
% 0.13/0.36  fof(t201_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(k7_relat_1(X2,X1)=k7_relat_1(X3,X1)=>k9_relat_1(X2,X1)=k9_relat_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t201_relat_1)).
% 0.13/0.36  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 0.13/0.36  fof(c_0_2, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(k7_relat_1(X2,X1)=k7_relat_1(X3,X1)=>k9_relat_1(X2,X1)=k9_relat_1(X3,X1))))), inference(assume_negation,[status(cth)],[t201_relat_1])).
% 0.13/0.36  fof(c_0_3, plain, ![X4, X5]:(~v1_relat_1(X5)|k2_relat_1(k7_relat_1(X5,X4))=k9_relat_1(X5,X4)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.13/0.36  fof(c_0_4, negated_conjecture, (v1_relat_1(esk2_0)&(v1_relat_1(esk3_0)&(k7_relat_1(esk2_0,esk1_0)=k7_relat_1(esk3_0,esk1_0)&k9_relat_1(esk2_0,esk1_0)!=k9_relat_1(esk3_0,esk1_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_2])])])).
% 0.13/0.36  cnf(c_0_5, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.13/0.36  cnf(c_0_6, negated_conjecture, (k7_relat_1(esk2_0,esk1_0)=k7_relat_1(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.36  cnf(c_0_7, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.36  cnf(c_0_8, negated_conjecture, (k2_relat_1(k7_relat_1(esk2_0,esk1_0))=k9_relat_1(esk3_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_5, c_0_6]), c_0_7])])).
% 0.13/0.36  cnf(c_0_9, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.36  cnf(c_0_10, negated_conjecture, (k9_relat_1(esk2_0,esk1_0)!=k9_relat_1(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.36  cnf(c_0_11, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_5, c_0_8]), c_0_9])]), c_0_10]), ['proof']).
% 0.13/0.36  # SZS output end CNFRefutation
% 0.13/0.36  # Proof object total steps             : 12
% 0.13/0.36  # Proof object clause steps            : 7
% 0.13/0.36  # Proof object formula steps           : 5
% 0.13/0.36  # Proof object conjectures             : 9
% 0.13/0.36  # Proof object clause conjectures      : 6
% 0.13/0.36  # Proof object formula conjectures     : 3
% 0.13/0.36  # Proof object initial clauses used    : 5
% 0.13/0.36  # Proof object initial formulas used   : 2
% 0.13/0.36  # Proof object generating inferences   : 2
% 0.13/0.36  # Proof object simplifying inferences  : 5
% 0.13/0.36  # Training examples: 0 positive, 0 negative
% 0.13/0.36  # Parsed axioms                        : 2
% 0.13/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.36  # Initial clauses                      : 5
% 0.13/0.36  # Removed in clause preprocessing      : 0
% 0.13/0.36  # Initial clauses in saturation        : 5
% 0.13/0.36  # Processed clauses                    : 11
% 0.13/0.36  # ...of these trivial                  : 0
% 0.13/0.36  # ...subsumed                          : 0
% 0.13/0.36  # ...remaining for further processing  : 11
% 0.13/0.36  # Other redundant clauses eliminated   : 0
% 0.13/0.36  # Clauses deleted for lack of memory   : 0
% 0.13/0.36  # Backward-subsumed                    : 0
% 0.13/0.36  # Backward-rewritten                   : 0
% 0.13/0.36  # Generated clauses                    : 4
% 0.13/0.36  # ...of the previous two non-trivial   : 3
% 0.13/0.36  # Contextual simplify-reflections      : 0
% 0.13/0.36  # Paramodulations                      : 4
% 0.13/0.36  # Factorizations                       : 0
% 0.13/0.36  # Equation resolutions                 : 0
% 0.13/0.36  # Propositional unsat checks           : 0
% 0.13/0.36  #    Propositional check models        : 0
% 0.13/0.36  #    Propositional check unsatisfiable : 0
% 0.13/0.36  #    Propositional clauses             : 0
% 0.13/0.36  #    Propositional clauses after purity: 0
% 0.13/0.36  #    Propositional unsat core size     : 0
% 0.13/0.36  #    Propositional preprocessing time  : 0.000
% 0.13/0.36  #    Propositional encoding time       : 0.000
% 0.13/0.36  #    Propositional solver time         : 0.000
% 0.13/0.36  #    Success case prop preproc time    : 0.000
% 0.13/0.36  #    Success case prop encoding time   : 0.000
% 0.13/0.36  #    Success case prop solver time     : 0.000
% 0.13/0.36  # Current number of processed clauses  : 6
% 0.13/0.36  #    Positive orientable unit clauses  : 4
% 0.13/0.36  #    Positive unorientable unit clauses: 0
% 0.13/0.36  #    Negative unit clauses             : 1
% 0.13/0.36  #    Non-unit-clauses                  : 1
% 0.13/0.36  # Current number of unprocessed clauses: 2
% 0.13/0.36  # ...number of literals in the above   : 2
% 0.13/0.36  # Current number of archived formulas  : 0
% 0.13/0.36  # Current number of archived clauses   : 5
% 0.13/0.36  # Clause-clause subsumption calls (NU) : 0
% 0.13/0.36  # Rec. Clause-clause subsumption calls : 0
% 0.13/0.36  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.36  # Unit Clause-clause subsumption calls : 0
% 0.13/0.36  # Rewrite failures with RHS unbound    : 0
% 0.13/0.36  # BW rewrite match attempts            : 0
% 0.13/0.36  # BW rewrite match successes           : 0
% 0.13/0.36  # Condensation attempts                : 0
% 0.13/0.36  # Condensation successes               : 0
% 0.13/0.36  # Termbank termtop insertions          : 288
% 0.13/0.36  
% 0.13/0.36  # -------------------------------------------------
% 0.13/0.36  # User time                : 0.026 s
% 0.13/0.36  # System time              : 0.003 s
% 0.13/0.36  # Total time               : 0.029 s
% 0.13/0.36  # Maximum resident set size: 1556 pages
%------------------------------------------------------------------------------

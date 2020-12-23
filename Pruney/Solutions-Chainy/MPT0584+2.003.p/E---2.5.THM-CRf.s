%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:51:58 EST 2020

% Result     : Theorem 0.22s
% Output     : CNFRefutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   14 (  34 expanded)
%              Number of clauses        :    9 (  12 expanded)
%              Number of leaves         :    2 (   8 expanded)
%              Depth                    :    6
%              Number of atoms          :   33 ( 120 expanded)
%              Number of equality atoms :   13 (  47 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    5 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t188_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3,X4] :
              ( ( r1_tarski(X3,X4)
                & k7_relat_1(X1,X4) = k7_relat_1(X2,X4) )
             => k7_relat_1(X1,X3) = k7_relat_1(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t188_relat_1)).

fof(t103_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => k7_relat_1(k7_relat_1(X3,X2),X1) = k7_relat_1(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_relat_1)).

fof(c_0_2,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ! [X3,X4] :
                ( ( r1_tarski(X3,X4)
                  & k7_relat_1(X1,X4) = k7_relat_1(X2,X4) )
               => k7_relat_1(X1,X3) = k7_relat_1(X2,X3) ) ) ) ),
    inference(assume_negation,[status(cth)],[t188_relat_1])).

fof(c_0_3,plain,(
    ! [X5,X6,X7] :
      ( ~ v1_relat_1(X7)
      | ~ r1_tarski(X5,X6)
      | k7_relat_1(k7_relat_1(X7,X6),X5) = k7_relat_1(X7,X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t103_relat_1])])).

fof(c_0_4,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_relat_1(esk2_0)
    & r1_tarski(esk3_0,esk4_0)
    & k7_relat_1(esk1_0,esk4_0) = k7_relat_1(esk2_0,esk4_0)
    & k7_relat_1(esk1_0,esk3_0) != k7_relat_1(esk2_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_2])])])).

cnf(c_0_5,plain,
    ( k7_relat_1(k7_relat_1(X1,X3),X2) = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_6,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( k7_relat_1(k7_relat_1(X1,esk4_0),esk3_0) = k7_relat_1(X1,esk3_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_5,c_0_6])).

cnf(c_0_8,negated_conjecture,
    ( k7_relat_1(esk1_0,esk4_0) = k7_relat_1(esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_9,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_10,negated_conjecture,
    ( k7_relat_1(k7_relat_1(esk2_0,esk4_0),esk3_0) = k7_relat_1(esk1_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8]),c_0_9])])).

cnf(c_0_11,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_12,negated_conjecture,
    ( k7_relat_1(esk1_0,esk3_0) != k7_relat_1(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_13,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_10]),c_0_11])]),c_0_12]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.36  % Computer   : n024.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 20:36:51 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  # Version: 2.5pre002
% 0.14/0.36  # No SInE strategy applied
% 0.14/0.36  # Trying AutoSched0 for 299 seconds
% 0.22/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.22/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.22/0.39  #
% 0.22/0.39  # Preprocessing time       : 0.026 s
% 0.22/0.39  # Presaturation interreduction done
% 0.22/0.39  
% 0.22/0.39  # Proof found!
% 0.22/0.39  # SZS status Theorem
% 0.22/0.39  # SZS output start CNFRefutation
% 0.22/0.39  fof(t188_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3, X4]:((r1_tarski(X3,X4)&k7_relat_1(X1,X4)=k7_relat_1(X2,X4))=>k7_relat_1(X1,X3)=k7_relat_1(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t188_relat_1)).
% 0.22/0.39  fof(t103_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>k7_relat_1(k7_relat_1(X3,X2),X1)=k7_relat_1(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_relat_1)).
% 0.22/0.39  fof(c_0_2, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3, X4]:((r1_tarski(X3,X4)&k7_relat_1(X1,X4)=k7_relat_1(X2,X4))=>k7_relat_1(X1,X3)=k7_relat_1(X2,X3))))), inference(assume_negation,[status(cth)],[t188_relat_1])).
% 0.22/0.39  fof(c_0_3, plain, ![X5, X6, X7]:(~v1_relat_1(X7)|(~r1_tarski(X5,X6)|k7_relat_1(k7_relat_1(X7,X6),X5)=k7_relat_1(X7,X5))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t103_relat_1])])).
% 0.22/0.39  fof(c_0_4, negated_conjecture, (v1_relat_1(esk1_0)&(v1_relat_1(esk2_0)&((r1_tarski(esk3_0,esk4_0)&k7_relat_1(esk1_0,esk4_0)=k7_relat_1(esk2_0,esk4_0))&k7_relat_1(esk1_0,esk3_0)!=k7_relat_1(esk2_0,esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_2])])])).
% 0.22/0.39  cnf(c_0_5, plain, (k7_relat_1(k7_relat_1(X1,X3),X2)=k7_relat_1(X1,X2)|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.22/0.39  cnf(c_0_6, negated_conjecture, (r1_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.22/0.39  cnf(c_0_7, negated_conjecture, (k7_relat_1(k7_relat_1(X1,esk4_0),esk3_0)=k7_relat_1(X1,esk3_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_5, c_0_6])).
% 0.22/0.39  cnf(c_0_8, negated_conjecture, (k7_relat_1(esk1_0,esk4_0)=k7_relat_1(esk2_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.22/0.39  cnf(c_0_9, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.22/0.39  cnf(c_0_10, negated_conjecture, (k7_relat_1(k7_relat_1(esk2_0,esk4_0),esk3_0)=k7_relat_1(esk1_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7, c_0_8]), c_0_9])])).
% 0.22/0.39  cnf(c_0_11, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.22/0.39  cnf(c_0_12, negated_conjecture, (k7_relat_1(esk1_0,esk3_0)!=k7_relat_1(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.22/0.39  cnf(c_0_13, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7, c_0_10]), c_0_11])]), c_0_12]), ['proof']).
% 0.22/0.39  # SZS output end CNFRefutation
% 0.22/0.39  # Proof object total steps             : 14
% 0.22/0.39  # Proof object clause steps            : 9
% 0.22/0.39  # Proof object formula steps           : 5
% 0.22/0.39  # Proof object conjectures             : 11
% 0.22/0.39  # Proof object clause conjectures      : 8
% 0.22/0.39  # Proof object formula conjectures     : 3
% 0.22/0.39  # Proof object initial clauses used    : 6
% 0.22/0.39  # Proof object initial formulas used   : 2
% 0.22/0.39  # Proof object generating inferences   : 3
% 0.22/0.39  # Proof object simplifying inferences  : 5
% 0.22/0.39  # Training examples: 0 positive, 0 negative
% 0.22/0.39  # Parsed axioms                        : 2
% 0.22/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.22/0.39  # Initial clauses                      : 6
% 0.22/0.39  # Removed in clause preprocessing      : 0
% 0.22/0.39  # Initial clauses in saturation        : 6
% 0.22/0.39  # Processed clauses                    : 14
% 0.22/0.39  # ...of these trivial                  : 0
% 0.22/0.39  # ...subsumed                          : 0
% 0.22/0.39  # ...remaining for further processing  : 14
% 0.22/0.39  # Other redundant clauses eliminated   : 0
% 0.22/0.39  # Clauses deleted for lack of memory   : 0
% 0.22/0.39  # Backward-subsumed                    : 0
% 0.22/0.39  # Backward-rewritten                   : 0
% 0.22/0.39  # Generated clauses                    : 3
% 0.22/0.39  # ...of the previous two non-trivial   : 2
% 0.22/0.39  # Contextual simplify-reflections      : 0
% 0.22/0.39  # Paramodulations                      : 3
% 0.22/0.39  # Factorizations                       : 0
% 0.22/0.39  # Equation resolutions                 : 0
% 0.22/0.39  # Propositional unsat checks           : 0
% 0.22/0.39  #    Propositional check models        : 0
% 0.22/0.39  #    Propositional check unsatisfiable : 0
% 0.22/0.39  #    Propositional clauses             : 0
% 0.22/0.39  #    Propositional clauses after purity: 0
% 0.22/0.39  #    Propositional unsat core size     : 0
% 0.22/0.39  #    Propositional preprocessing time  : 0.000
% 0.22/0.39  #    Propositional encoding time       : 0.000
% 0.22/0.39  #    Propositional solver time         : 0.000
% 0.22/0.39  #    Success case prop preproc time    : 0.000
% 0.22/0.39  #    Success case prop encoding time   : 0.000
% 0.22/0.39  #    Success case prop solver time     : 0.000
% 0.22/0.39  # Current number of processed clauses  : 8
% 0.22/0.39  #    Positive orientable unit clauses  : 5
% 0.22/0.39  #    Positive unorientable unit clauses: 0
% 0.22/0.39  #    Negative unit clauses             : 1
% 0.22/0.39  #    Non-unit-clauses                  : 2
% 0.22/0.39  # Current number of unprocessed clauses: 0
% 0.22/0.39  # ...number of literals in the above   : 0
% 0.22/0.39  # Current number of archived formulas  : 0
% 0.22/0.39  # Current number of archived clauses   : 6
% 0.22/0.39  # Clause-clause subsumption calls (NU) : 0
% 0.22/0.39  # Rec. Clause-clause subsumption calls : 0
% 0.22/0.39  # Non-unit clause-clause subsumptions  : 0
% 0.22/0.39  # Unit Clause-clause subsumption calls : 0
% 0.22/0.39  # Rewrite failures with RHS unbound    : 0
% 0.22/0.39  # BW rewrite match attempts            : 0
% 0.22/0.39  # BW rewrite match successes           : 0
% 0.22/0.39  # Condensation attempts                : 0
% 0.22/0.39  # Condensation successes               : 0
% 0.22/0.39  # Termbank termtop insertions          : 385
% 0.22/0.39  
% 0.22/0.39  # -------------------------------------------------
% 0.22/0.39  # User time                : 0.026 s
% 0.22/0.39  # System time              : 0.004 s
% 0.22/0.39  # Total time               : 0.030 s
% 0.22/0.39  # Maximum resident set size: 1556 pages
%------------------------------------------------------------------------------

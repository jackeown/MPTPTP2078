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
% DateTime   : Thu Dec  3 10:51:56 EST 2020

% Result     : Theorem 0.22s
% Output     : CNFRefutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   18 (  34 expanded)
%              Number of clauses        :   11 (  12 expanded)
%              Number of leaves         :    3 (   8 expanded)
%              Depth                    :    7
%              Number of atoms          :   48 ( 124 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t186_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(k1_relat_1(X3),X1)
              & r1_tarski(X3,X2) )
           => r1_tarski(X3,k7_relat_1(X2,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t186_relat_1)).

fof(t97_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X1)
       => k7_relat_1(X2,X1) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(t105_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( r1_tarski(X2,X3)
           => r1_tarski(k7_relat_1(X2,X1),k7_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_relat_1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ! [X3] :
            ( v1_relat_1(X3)
           => ( ( r1_tarski(k1_relat_1(X3),X1)
                & r1_tarski(X3,X2) )
             => r1_tarski(X3,k7_relat_1(X2,X1)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t186_relat_1])).

fof(c_0_4,plain,(
    ! [X7,X8] :
      ( ~ v1_relat_1(X8)
      | ~ r1_tarski(k1_relat_1(X8),X7)
      | k7_relat_1(X8,X7) = X8 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).

fof(c_0_5,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v1_relat_1(esk3_0)
    & r1_tarski(k1_relat_1(esk3_0),esk1_0)
    & r1_tarski(esk3_0,esk2_0)
    & ~ r1_tarski(esk3_0,k7_relat_1(esk2_0,esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

cnf(c_0_6,plain,
    ( k7_relat_1(X1,X2) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_8,plain,(
    ! [X4,X5,X6] :
      ( ~ v1_relat_1(X5)
      | ~ v1_relat_1(X6)
      | ~ r1_tarski(X5,X6)
      | r1_tarski(k7_relat_1(X5,X4),k7_relat_1(X6,X4)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t105_relat_1])])])).

cnf(c_0_9,negated_conjecture,
    ( k7_relat_1(esk3_0,X1) = esk3_0
    | ~ r1_tarski(k1_relat_1(esk3_0),X1) ),
    inference(spm,[status(thm)],[c_0_6,c_0_7])).

cnf(c_0_10,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk3_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_11,plain,
    ( r1_tarski(k7_relat_1(X1,X3),k7_relat_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( k7_relat_1(esk3_0,esk1_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( r1_tarski(esk3_0,k7_relat_1(X1,esk1_0))
    | ~ r1_tarski(esk3_0,X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_7])])).

cnf(c_0_14,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_15,negated_conjecture,
    ( r1_tarski(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_16,negated_conjecture,
    ( ~ r1_tarski(esk3_0,k7_relat_1(esk2_0,esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_17,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])]),c_0_16]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:25:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.22/0.38  # AutoSched0-Mode selected heuristic G_E___107_C00_02_nc_F1_PI_AE_Q4_CS_SP_PS_S00EN
% 0.22/0.38  # and selection function PSelectSmallestOrientable.
% 0.22/0.38  #
% 0.22/0.38  # Preprocessing time       : 0.026 s
% 0.22/0.38  # Presaturation interreduction done
% 0.22/0.38  
% 0.22/0.38  # Proof found!
% 0.22/0.38  # SZS status Theorem
% 0.22/0.38  # SZS output start CNFRefutation
% 0.22/0.38  fof(t186_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>((r1_tarski(k1_relat_1(X3),X1)&r1_tarski(X3,X2))=>r1_tarski(X3,k7_relat_1(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t186_relat_1)).
% 0.22/0.38  fof(t97_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X2),X1)=>k7_relat_1(X2,X1)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 0.22/0.38  fof(t105_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(r1_tarski(X2,X3)=>r1_tarski(k7_relat_1(X2,X1),k7_relat_1(X3,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_relat_1)).
% 0.22/0.38  fof(c_0_3, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>((r1_tarski(k1_relat_1(X3),X1)&r1_tarski(X3,X2))=>r1_tarski(X3,k7_relat_1(X2,X1)))))), inference(assume_negation,[status(cth)],[t186_relat_1])).
% 0.22/0.38  fof(c_0_4, plain, ![X7, X8]:(~v1_relat_1(X8)|(~r1_tarski(k1_relat_1(X8),X7)|k7_relat_1(X8,X7)=X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).
% 0.22/0.38  fof(c_0_5, negated_conjecture, (v1_relat_1(esk2_0)&(v1_relat_1(esk3_0)&((r1_tarski(k1_relat_1(esk3_0),esk1_0)&r1_tarski(esk3_0,esk2_0))&~r1_tarski(esk3_0,k7_relat_1(esk2_0,esk1_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).
% 0.22/0.38  cnf(c_0_6, plain, (k7_relat_1(X1,X2)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.22/0.38  cnf(c_0_7, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.22/0.38  fof(c_0_8, plain, ![X4, X5, X6]:(~v1_relat_1(X5)|(~v1_relat_1(X6)|(~r1_tarski(X5,X6)|r1_tarski(k7_relat_1(X5,X4),k7_relat_1(X6,X4))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t105_relat_1])])])).
% 0.22/0.38  cnf(c_0_9, negated_conjecture, (k7_relat_1(esk3_0,X1)=esk3_0|~r1_tarski(k1_relat_1(esk3_0),X1)), inference(spm,[status(thm)],[c_0_6, c_0_7])).
% 0.22/0.38  cnf(c_0_10, negated_conjecture, (r1_tarski(k1_relat_1(esk3_0),esk1_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.22/0.38  cnf(c_0_11, plain, (r1_tarski(k7_relat_1(X1,X3),k7_relat_1(X2,X3))|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.22/0.38  cnf(c_0_12, negated_conjecture, (k7_relat_1(esk3_0,esk1_0)=esk3_0), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.22/0.38  cnf(c_0_13, negated_conjecture, (r1_tarski(esk3_0,k7_relat_1(X1,esk1_0))|~r1_tarski(esk3_0,X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12]), c_0_7])])).
% 0.22/0.38  cnf(c_0_14, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.22/0.38  cnf(c_0_15, negated_conjecture, (r1_tarski(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.22/0.38  cnf(c_0_16, negated_conjecture, (~r1_tarski(esk3_0,k7_relat_1(esk2_0,esk1_0))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.22/0.38  cnf(c_0_17, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15])]), c_0_16]), ['proof']).
% 0.22/0.38  # SZS output end CNFRefutation
% 0.22/0.38  # Proof object total steps             : 18
% 0.22/0.38  # Proof object clause steps            : 11
% 0.22/0.38  # Proof object formula steps           : 7
% 0.22/0.38  # Proof object conjectures             : 12
% 0.22/0.38  # Proof object clause conjectures      : 9
% 0.22/0.38  # Proof object formula conjectures     : 3
% 0.22/0.38  # Proof object initial clauses used    : 7
% 0.22/0.38  # Proof object initial formulas used   : 3
% 0.22/0.38  # Proof object generating inferences   : 4
% 0.22/0.38  # Proof object simplifying inferences  : 5
% 0.22/0.38  # Training examples: 0 positive, 0 negative
% 0.22/0.38  # Parsed axioms                        : 3
% 0.22/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.22/0.38  # Initial clauses                      : 7
% 0.22/0.38  # Removed in clause preprocessing      : 0
% 0.22/0.38  # Initial clauses in saturation        : 7
% 0.22/0.38  # Processed clauses                    : 19
% 0.22/0.38  # ...of these trivial                  : 0
% 0.22/0.38  # ...subsumed                          : 0
% 0.22/0.38  # ...remaining for further processing  : 19
% 0.22/0.38  # Other redundant clauses eliminated   : 0
% 0.22/0.38  # Clauses deleted for lack of memory   : 0
% 0.22/0.38  # Backward-subsumed                    : 0
% 0.22/0.38  # Backward-rewritten                   : 0
% 0.22/0.38  # Generated clauses                    : 14
% 0.22/0.38  # ...of the previous two non-trivial   : 10
% 0.22/0.38  # Contextual simplify-reflections      : 0
% 0.22/0.38  # Paramodulations                      : 14
% 0.22/0.38  # Factorizations                       : 0
% 0.22/0.38  # Equation resolutions                 : 0
% 0.22/0.38  # Propositional unsat checks           : 0
% 0.22/0.38  #    Propositional check models        : 0
% 0.22/0.38  #    Propositional check unsatisfiable : 0
% 0.22/0.38  #    Propositional clauses             : 0
% 0.22/0.38  #    Propositional clauses after purity: 0
% 0.22/0.38  #    Propositional unsat core size     : 0
% 0.22/0.38  #    Propositional preprocessing time  : 0.000
% 0.22/0.38  #    Propositional encoding time       : 0.000
% 0.22/0.38  #    Propositional solver time         : 0.000
% 0.22/0.38  #    Success case prop preproc time    : 0.000
% 0.22/0.38  #    Success case prop encoding time   : 0.000
% 0.22/0.38  #    Success case prop solver time     : 0.000
% 0.22/0.38  # Current number of processed clauses  : 12
% 0.22/0.38  #    Positive orientable unit clauses  : 5
% 0.22/0.38  #    Positive unorientable unit clauses: 0
% 0.22/0.38  #    Negative unit clauses             : 1
% 0.22/0.38  #    Non-unit-clauses                  : 6
% 0.22/0.38  # Current number of unprocessed clauses: 5
% 0.22/0.38  # ...number of literals in the above   : 13
% 0.22/0.38  # Current number of archived formulas  : 0
% 0.22/0.38  # Current number of archived clauses   : 7
% 0.22/0.38  # Clause-clause subsumption calls (NU) : 0
% 0.22/0.38  # Rec. Clause-clause subsumption calls : 0
% 0.22/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.22/0.38  # Unit Clause-clause subsumption calls : 0
% 0.22/0.38  # Rewrite failures with RHS unbound    : 0
% 0.22/0.38  # BW rewrite match attempts            : 0
% 0.22/0.38  # BW rewrite match successes           : 0
% 0.22/0.38  # Condensation attempts                : 0
% 0.22/0.38  # Condensation successes               : 0
% 0.22/0.38  # Termbank termtop insertions          : 673
% 0.22/0.38  
% 0.22/0.38  # -------------------------------------------------
% 0.22/0.38  # User time                : 0.025 s
% 0.22/0.38  # System time              : 0.005 s
% 0.22/0.38  # Total time               : 0.030 s
% 0.22/0.38  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------

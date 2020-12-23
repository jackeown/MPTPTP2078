%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:21 EST 2020

% Result     : CounterSatisfiable 0.12s
% Output     : Saturation 0.12s
% Verified   : 
% Statistics : Number of formulae       :    8 (  20 expanded)
%              Number of clauses        :    5 (   5 expanded)
%              Number of leaves         :    1 (   5 expanded)
%              Depth                    :    3
%              Number of atoms          :   20 (  80 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    5 (   1 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t35_yellow_0,conjecture,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( ( r1_tarski(X2,X3)
            & r2_yellow_0(X1,X2)
            & r2_yellow_0(X1,X3) )
         => r1_orders_2(X1,k2_yellow_0(X1,X3),k2_yellow_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_yellow_0)).

fof(c_0_1,negated_conjecture,(
    ~ ! [X1] :
        ( l1_orders_2(X1)
       => ! [X2,X3] :
            ( ( r1_tarski(X2,X3)
              & r2_yellow_0(X1,X2)
              & r2_yellow_0(X1,X3) )
           => r1_orders_2(X1,k2_yellow_0(X1,X3),k2_yellow_0(X1,X2)) ) ) ),
    inference(assume_negation,[status(cth)],[t35_yellow_0])).

fof(c_0_2,negated_conjecture,
    ( l1_orders_2(esk1_0)
    & r1_tarski(esk2_0,esk3_0)
    & r2_yellow_0(esk1_0,esk2_0)
    & r2_yellow_0(esk1_0,esk3_0)
    & ~ r1_orders_2(esk1_0,k2_yellow_0(esk1_0,esk3_0),k2_yellow_0(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_1])])])).

cnf(c_0_3,negated_conjecture,
    ( ~ r1_orders_2(esk1_0,k2_yellow_0(esk1_0,esk3_0),k2_yellow_0(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_2]),
    [final]).

cnf(c_0_4,negated_conjecture,
    ( r2_yellow_0(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_2]),
    [final]).

cnf(c_0_5,negated_conjecture,
    ( r2_yellow_0(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_2]),
    [final]).

cnf(c_0_6,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_2]),
    [final]).

cnf(c_0_7,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_2]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.32  % Computer   : n001.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 13:47:14 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.12/0.35  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.12/0.35  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.12/0.35  #
% 0.12/0.35  # Preprocessing time       : 0.026 s
% 0.12/0.35  # Presaturation interreduction done
% 0.12/0.35  
% 0.12/0.35  # No proof found!
% 0.12/0.35  # SZS status CounterSatisfiable
% 0.12/0.35  # SZS output start Saturation
% 0.12/0.35  fof(t35_yellow_0, conjecture, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(((r1_tarski(X2,X3)&r2_yellow_0(X1,X2))&r2_yellow_0(X1,X3))=>r1_orders_2(X1,k2_yellow_0(X1,X3),k2_yellow_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_yellow_0)).
% 0.12/0.35  fof(c_0_1, negated_conjecture, ~(![X1]:(l1_orders_2(X1)=>![X2, X3]:(((r1_tarski(X2,X3)&r2_yellow_0(X1,X2))&r2_yellow_0(X1,X3))=>r1_orders_2(X1,k2_yellow_0(X1,X3),k2_yellow_0(X1,X2))))), inference(assume_negation,[status(cth)],[t35_yellow_0])).
% 0.12/0.35  fof(c_0_2, negated_conjecture, (l1_orders_2(esk1_0)&(((r1_tarski(esk2_0,esk3_0)&r2_yellow_0(esk1_0,esk2_0))&r2_yellow_0(esk1_0,esk3_0))&~r1_orders_2(esk1_0,k2_yellow_0(esk1_0,esk3_0),k2_yellow_0(esk1_0,esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_1])])])).
% 0.12/0.35  cnf(c_0_3, negated_conjecture, (~r1_orders_2(esk1_0,k2_yellow_0(esk1_0,esk3_0),k2_yellow_0(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_2]), ['final']).
% 0.12/0.35  cnf(c_0_4, negated_conjecture, (r2_yellow_0(esk1_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_2]), ['final']).
% 0.12/0.35  cnf(c_0_5, negated_conjecture, (r2_yellow_0(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_2]), ['final']).
% 0.12/0.35  cnf(c_0_6, negated_conjecture, (r1_tarski(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_2]), ['final']).
% 0.12/0.35  cnf(c_0_7, negated_conjecture, (l1_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_2]), ['final']).
% 0.12/0.35  # SZS output end Saturation
% 0.12/0.35  # Proof object total steps             : 8
% 0.12/0.35  # Proof object clause steps            : 5
% 0.12/0.35  # Proof object formula steps           : 3
% 0.12/0.35  # Proof object conjectures             : 8
% 0.12/0.35  # Proof object clause conjectures      : 5
% 0.12/0.35  # Proof object formula conjectures     : 3
% 0.12/0.35  # Proof object initial clauses used    : 5
% 0.12/0.35  # Proof object initial formulas used   : 1
% 0.12/0.35  # Proof object generating inferences   : 0
% 0.12/0.35  # Proof object simplifying inferences  : 0
% 0.12/0.35  # Parsed axioms                        : 1
% 0.12/0.35  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.35  # Initial clauses                      : 5
% 0.12/0.35  # Removed in clause preprocessing      : 0
% 0.12/0.35  # Initial clauses in saturation        : 5
% 0.12/0.35  # Processed clauses                    : 10
% 0.12/0.35  # ...of these trivial                  : 0
% 0.12/0.35  # ...subsumed                          : 0
% 0.12/0.35  # ...remaining for further processing  : 10
% 0.12/0.35  # Other redundant clauses eliminated   : 0
% 0.12/0.35  # Clauses deleted for lack of memory   : 0
% 0.12/0.35  # Backward-subsumed                    : 0
% 0.12/0.35  # Backward-rewritten                   : 0
% 0.12/0.35  # Generated clauses                    : 0
% 0.12/0.35  # ...of the previous two non-trivial   : 0
% 0.12/0.35  # Contextual simplify-reflections      : 0
% 0.12/0.35  # Paramodulations                      : 0
% 0.12/0.35  # Factorizations                       : 0
% 0.12/0.35  # Equation resolutions                 : 0
% 0.12/0.35  # Propositional unsat checks           : 0
% 0.12/0.35  #    Propositional check models        : 0
% 0.12/0.35  #    Propositional check unsatisfiable : 0
% 0.12/0.35  #    Propositional clauses             : 0
% 0.12/0.35  #    Propositional clauses after purity: 0
% 0.12/0.35  #    Propositional unsat core size     : 0
% 0.12/0.35  #    Propositional preprocessing time  : 0.000
% 0.12/0.35  #    Propositional encoding time       : 0.000
% 0.12/0.35  #    Propositional solver time         : 0.000
% 0.12/0.35  #    Success case prop preproc time    : 0.000
% 0.12/0.35  #    Success case prop encoding time   : 0.000
% 0.12/0.35  #    Success case prop solver time     : 0.000
% 0.12/0.35  # Current number of processed clauses  : 5
% 0.12/0.35  #    Positive orientable unit clauses  : 4
% 0.12/0.35  #    Positive unorientable unit clauses: 0
% 0.12/0.35  #    Negative unit clauses             : 1
% 0.12/0.35  #    Non-unit-clauses                  : 0
% 0.12/0.35  # Current number of unprocessed clauses: 0
% 0.12/0.35  # ...number of literals in the above   : 0
% 0.12/0.35  # Current number of archived formulas  : 0
% 0.12/0.35  # Current number of archived clauses   : 5
% 0.12/0.35  # Clause-clause subsumption calls (NU) : 0
% 0.12/0.35  # Rec. Clause-clause subsumption calls : 0
% 0.12/0.35  # Non-unit clause-clause subsumptions  : 0
% 0.12/0.35  # Unit Clause-clause subsumption calls : 0
% 0.12/0.35  # Rewrite failures with RHS unbound    : 0
% 0.12/0.35  # BW rewrite match attempts            : 0
% 0.12/0.35  # BW rewrite match successes           : 0
% 0.12/0.35  # Condensation attempts                : 0
% 0.12/0.35  # Condensation successes               : 0
% 0.12/0.35  # Termbank termtop insertions          : 214
% 0.12/0.35  
% 0.12/0.35  # -------------------------------------------------
% 0.12/0.35  # User time                : 0.024 s
% 0.12/0.35  # System time              : 0.005 s
% 0.12/0.35  # Total time               : 0.029 s
% 0.12/0.35  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------

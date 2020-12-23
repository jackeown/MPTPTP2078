%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:33 EST 2020

% Result     : CounterSatisfiable 0.19s
% Output     : Saturation 0.19s
% Verified   : 
% Statistics : Number of formulae       :    9 (  24 expanded)
%              Number of clauses        :    6 (   6 expanded)
%              Number of leaves         :    1 (   6 expanded)
%              Depth                    :    3
%              Number of atoms          :   24 ( 114 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t45_yellow_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v2_yellow_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => r1_orders_2(X1,X2,k4_yellow_0(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_yellow_0)).

fof(c_0_1,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v5_orders_2(X1)
          & v2_yellow_0(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => r1_orders_2(X1,X2,k4_yellow_0(X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t45_yellow_0])).

fof(c_0_2,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v5_orders_2(esk1_0)
    & v2_yellow_0(esk1_0)
    & l1_orders_2(esk1_0)
    & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
    & ~ r1_orders_2(esk1_0,esk2_0,k4_yellow_0(esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_1])])])])).

cnf(c_0_3,negated_conjecture,
    ( ~ r1_orders_2(esk1_0,esk2_0,k4_yellow_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_2]),
    [final]).

cnf(c_0_4,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_2]),
    [final]).

cnf(c_0_5,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_2]),
    [final]).

cnf(c_0_6,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_2]),
    [final]).

cnf(c_0_7,negated_conjecture,
    ( v2_yellow_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_2]),
    [final]).

cnf(c_0_8,negated_conjecture,
    ( v5_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_2]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:00:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.39  #
% 0.19/0.39  # Preprocessing time       : 0.048 s
% 0.19/0.39  # Presaturation interreduction done
% 0.19/0.39  
% 0.19/0.39  # No proof found!
% 0.19/0.39  # SZS status CounterSatisfiable
% 0.19/0.39  # SZS output start Saturation
% 0.19/0.39  fof(t45_yellow_0, conjecture, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v2_yellow_0(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>r1_orders_2(X1,X2,k4_yellow_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_yellow_0)).
% 0.19/0.39  fof(c_0_1, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v2_yellow_0(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>r1_orders_2(X1,X2,k4_yellow_0(X1))))), inference(assume_negation,[status(cth)],[t45_yellow_0])).
% 0.19/0.39  fof(c_0_2, negated_conjecture, ((((~v2_struct_0(esk1_0)&v5_orders_2(esk1_0))&v2_yellow_0(esk1_0))&l1_orders_2(esk1_0))&(m1_subset_1(esk2_0,u1_struct_0(esk1_0))&~r1_orders_2(esk1_0,esk2_0,k4_yellow_0(esk1_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_1])])])])).
% 0.19/0.39  cnf(c_0_3, negated_conjecture, (~r1_orders_2(esk1_0,esk2_0,k4_yellow_0(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_2]), ['final']).
% 0.19/0.39  cnf(c_0_4, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_2]), ['final']).
% 0.19/0.39  cnf(c_0_5, negated_conjecture, (m1_subset_1(esk2_0,u1_struct_0(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_2]), ['final']).
% 0.19/0.39  cnf(c_0_6, negated_conjecture, (l1_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_2]), ['final']).
% 0.19/0.39  cnf(c_0_7, negated_conjecture, (v2_yellow_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_2]), ['final']).
% 0.19/0.39  cnf(c_0_8, negated_conjecture, (v5_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_2]), ['final']).
% 0.19/0.39  # SZS output end Saturation
% 0.19/0.39  # Proof object total steps             : 9
% 0.19/0.39  # Proof object clause steps            : 6
% 0.19/0.39  # Proof object formula steps           : 3
% 0.19/0.39  # Proof object conjectures             : 9
% 0.19/0.39  # Proof object clause conjectures      : 6
% 0.19/0.39  # Proof object formula conjectures     : 3
% 0.19/0.39  # Proof object initial clauses used    : 6
% 0.19/0.39  # Proof object initial formulas used   : 1
% 0.19/0.39  # Proof object generating inferences   : 0
% 0.19/0.39  # Proof object simplifying inferences  : 0
% 0.19/0.39  # Parsed axioms                        : 1
% 0.19/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.39  # Initial clauses                      : 6
% 0.19/0.39  # Removed in clause preprocessing      : 0
% 0.19/0.39  # Initial clauses in saturation        : 6
% 0.19/0.39  # Processed clauses                    : 12
% 0.19/0.39  # ...of these trivial                  : 0
% 0.19/0.39  # ...subsumed                          : 0
% 0.19/0.39  # ...remaining for further processing  : 12
% 0.19/0.39  # Other redundant clauses eliminated   : 0
% 0.19/0.39  # Clauses deleted for lack of memory   : 0
% 0.19/0.39  # Backward-subsumed                    : 0
% 0.19/0.39  # Backward-rewritten                   : 0
% 0.19/0.39  # Generated clauses                    : 0
% 0.19/0.39  # ...of the previous two non-trivial   : 0
% 0.19/0.39  # Contextual simplify-reflections      : 0
% 0.19/0.39  # Paramodulations                      : 0
% 0.19/0.39  # Factorizations                       : 0
% 0.19/0.39  # Equation resolutions                 : 0
% 0.19/0.39  # Propositional unsat checks           : 0
% 0.19/0.39  #    Propositional check models        : 0
% 0.19/0.39  #    Propositional check unsatisfiable : 0
% 0.19/0.39  #    Propositional clauses             : 0
% 0.19/0.39  #    Propositional clauses after purity: 0
% 0.19/0.39  #    Propositional unsat core size     : 0
% 0.19/0.39  #    Propositional preprocessing time  : 0.000
% 0.19/0.39  #    Propositional encoding time       : 0.000
% 0.19/0.39  #    Propositional solver time         : 0.000
% 0.19/0.39  #    Success case prop preproc time    : 0.000
% 0.19/0.39  #    Success case prop encoding time   : 0.000
% 0.19/0.39  #    Success case prop solver time     : 0.000
% 0.19/0.39  # Current number of processed clauses  : 6
% 0.19/0.39  #    Positive orientable unit clauses  : 4
% 0.19/0.39  #    Positive unorientable unit clauses: 0
% 0.19/0.39  #    Negative unit clauses             : 2
% 0.19/0.39  #    Non-unit-clauses                  : 0
% 0.19/0.39  # Current number of unprocessed clauses: 0
% 0.19/0.39  # ...number of literals in the above   : 0
% 0.19/0.39  # Current number of archived formulas  : 0
% 0.19/0.39  # Current number of archived clauses   : 6
% 0.19/0.39  # Clause-clause subsumption calls (NU) : 0
% 0.19/0.39  # Rec. Clause-clause subsumption calls : 0
% 0.19/0.39  # Non-unit clause-clause subsumptions  : 0
% 0.19/0.39  # Unit Clause-clause subsumption calls : 0
% 0.19/0.39  # Rewrite failures with RHS unbound    : 0
% 0.19/0.39  # BW rewrite match attempts            : 0
% 0.19/0.39  # BW rewrite match successes           : 0
% 0.19/0.39  # Condensation attempts                : 0
% 0.19/0.39  # Condensation successes               : 0
% 0.19/0.39  # Termbank termtop insertions          : 236
% 0.19/0.39  
% 0.19/0.39  # -------------------------------------------------
% 0.19/0.39  # User time                : 0.047 s
% 0.19/0.39  # System time              : 0.005 s
% 0.19/0.39  # Total time               : 0.052 s
% 0.19/0.39  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------

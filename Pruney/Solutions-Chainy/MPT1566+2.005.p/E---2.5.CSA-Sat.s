%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:32 EST 2020

% Result     : CounterSatisfiable 0.06s
% Output     : Saturation 0.06s
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
fof(t44_yellow_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v1_yellow_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => r1_orders_2(X1,k3_yellow_0(X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_yellow_0)).

fof(c_0_1,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v5_orders_2(X1)
          & v1_yellow_0(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => r1_orders_2(X1,k3_yellow_0(X1),X2) ) ) ),
    inference(assume_negation,[status(cth)],[t44_yellow_0])).

fof(c_0_2,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v5_orders_2(esk1_0)
    & v1_yellow_0(esk1_0)
    & l1_orders_2(esk1_0)
    & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
    & ~ r1_orders_2(esk1_0,k3_yellow_0(esk1_0),esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_1])])])])).

cnf(c_0_3,negated_conjecture,
    ( ~ r1_orders_2(esk1_0,k3_yellow_0(esk1_0),esk2_0) ),
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
    ( v1_yellow_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_2]),
    [final]).

cnf(c_0_8,negated_conjecture,
    ( v5_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_2]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.06  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.07  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.06/0.25  % Computer   : n012.cluster.edu
% 0.06/0.25  % Model      : x86_64 x86_64
% 0.06/0.25  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.06/0.25  % Memory     : 8042.1875MB
% 0.06/0.25  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.06/0.25  % CPULimit   : 60
% 0.06/0.25  % WCLimit    : 600
% 0.06/0.25  % DateTime   : Tue Dec  1 11:34:37 EST 2020
% 0.06/0.25  % CPUTime    : 
% 0.06/0.25  # Version: 2.5pre002
% 0.06/0.25  # No SInE strategy applied
% 0.06/0.25  # Trying AutoSched0 for 299 seconds
% 0.06/0.27  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.06/0.27  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.06/0.27  #
% 0.06/0.27  # Preprocessing time       : 0.012 s
% 0.06/0.27  # Presaturation interreduction done
% 0.06/0.27  
% 0.06/0.27  # No proof found!
% 0.06/0.27  # SZS status CounterSatisfiable
% 0.06/0.27  # SZS output start Saturation
% 0.06/0.27  fof(t44_yellow_0, conjecture, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>r1_orders_2(X1,k3_yellow_0(X1),X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_yellow_0)).
% 0.06/0.27  fof(c_0_1, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>r1_orders_2(X1,k3_yellow_0(X1),X2)))), inference(assume_negation,[status(cth)],[t44_yellow_0])).
% 0.06/0.27  fof(c_0_2, negated_conjecture, ((((~v2_struct_0(esk1_0)&v5_orders_2(esk1_0))&v1_yellow_0(esk1_0))&l1_orders_2(esk1_0))&(m1_subset_1(esk2_0,u1_struct_0(esk1_0))&~r1_orders_2(esk1_0,k3_yellow_0(esk1_0),esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_1])])])])).
% 0.06/0.27  cnf(c_0_3, negated_conjecture, (~r1_orders_2(esk1_0,k3_yellow_0(esk1_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_2]), ['final']).
% 0.06/0.27  cnf(c_0_4, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_2]), ['final']).
% 0.06/0.27  cnf(c_0_5, negated_conjecture, (m1_subset_1(esk2_0,u1_struct_0(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_2]), ['final']).
% 0.06/0.27  cnf(c_0_6, negated_conjecture, (l1_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_2]), ['final']).
% 0.06/0.27  cnf(c_0_7, negated_conjecture, (v1_yellow_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_2]), ['final']).
% 0.06/0.27  cnf(c_0_8, negated_conjecture, (v5_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_2]), ['final']).
% 0.06/0.27  # SZS output end Saturation
% 0.06/0.27  # Proof object total steps             : 9
% 0.06/0.27  # Proof object clause steps            : 6
% 0.06/0.27  # Proof object formula steps           : 3
% 0.06/0.27  # Proof object conjectures             : 9
% 0.06/0.27  # Proof object clause conjectures      : 6
% 0.06/0.27  # Proof object formula conjectures     : 3
% 0.06/0.27  # Proof object initial clauses used    : 6
% 0.06/0.27  # Proof object initial formulas used   : 1
% 0.06/0.27  # Proof object generating inferences   : 0
% 0.06/0.27  # Proof object simplifying inferences  : 0
% 0.06/0.27  # Parsed axioms                        : 1
% 0.06/0.27  # Removed by relevancy pruning/SinE    : 0
% 0.06/0.27  # Initial clauses                      : 6
% 0.06/0.27  # Removed in clause preprocessing      : 0
% 0.06/0.27  # Initial clauses in saturation        : 6
% 0.06/0.27  # Processed clauses                    : 12
% 0.06/0.27  # ...of these trivial                  : 0
% 0.06/0.27  # ...subsumed                          : 0
% 0.06/0.27  # ...remaining for further processing  : 12
% 0.06/0.27  # Other redundant clauses eliminated   : 0
% 0.06/0.27  # Clauses deleted for lack of memory   : 0
% 0.06/0.27  # Backward-subsumed                    : 0
% 0.06/0.27  # Backward-rewritten                   : 0
% 0.06/0.27  # Generated clauses                    : 0
% 0.06/0.27  # ...of the previous two non-trivial   : 0
% 0.06/0.27  # Contextual simplify-reflections      : 0
% 0.06/0.27  # Paramodulations                      : 0
% 0.06/0.27  # Factorizations                       : 0
% 0.06/0.27  # Equation resolutions                 : 0
% 0.06/0.27  # Propositional unsat checks           : 0
% 0.06/0.27  #    Propositional check models        : 0
% 0.06/0.27  #    Propositional check unsatisfiable : 0
% 0.06/0.27  #    Propositional clauses             : 0
% 0.06/0.27  #    Propositional clauses after purity: 0
% 0.06/0.27  #    Propositional unsat core size     : 0
% 0.06/0.27  #    Propositional preprocessing time  : 0.000
% 0.06/0.27  #    Propositional encoding time       : 0.000
% 0.06/0.27  #    Propositional solver time         : 0.000
% 0.06/0.27  #    Success case prop preproc time    : 0.000
% 0.06/0.27  #    Success case prop encoding time   : 0.000
% 0.06/0.27  #    Success case prop solver time     : 0.000
% 0.06/0.27  # Current number of processed clauses  : 6
% 0.06/0.27  #    Positive orientable unit clauses  : 4
% 0.06/0.27  #    Positive unorientable unit clauses: 0
% 0.06/0.27  #    Negative unit clauses             : 2
% 0.06/0.27  #    Non-unit-clauses                  : 0
% 0.06/0.27  # Current number of unprocessed clauses: 0
% 0.06/0.27  # ...number of literals in the above   : 0
% 0.06/0.27  # Current number of archived formulas  : 0
% 0.06/0.27  # Current number of archived clauses   : 6
% 0.06/0.27  # Clause-clause subsumption calls (NU) : 0
% 0.06/0.27  # Rec. Clause-clause subsumption calls : 0
% 0.06/0.27  # Non-unit clause-clause subsumptions  : 0
% 0.06/0.27  # Unit Clause-clause subsumption calls : 0
% 0.06/0.27  # Rewrite failures with RHS unbound    : 0
% 0.06/0.27  # BW rewrite match attempts            : 0
% 0.06/0.27  # BW rewrite match successes           : 0
% 0.06/0.27  # Condensation attempts                : 0
% 0.06/0.27  # Condensation successes               : 0
% 0.06/0.27  # Termbank termtop insertions          : 236
% 0.06/0.27  
% 0.06/0.27  # -------------------------------------------------
% 0.06/0.27  # User time                : 0.011 s
% 0.06/0.27  # System time              : 0.002 s
% 0.06/0.27  # Total time               : 0.013 s
% 0.06/0.27  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------

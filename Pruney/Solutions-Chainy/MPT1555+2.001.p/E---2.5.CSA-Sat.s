%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:20 EST 2020

% Result     : CounterSatisfiable 0.13s
% Output     : Saturation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   13 (  40 expanded)
%              Number of clauses        :   10 (  10 expanded)
%              Number of leaves         :    1 (  10 expanded)
%              Depth                    :    3
%              Number of atoms          :   60 ( 420 expanded)
%              Number of equality atoms :   12 (  75 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t33_yellow_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v3_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( X2 = k2_yellow_0(X1,X3)
            <=> ( r1_lattice3(X1,X3,X2)
                & ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r1_lattice3(X1,X3,X4)
                     => r1_orders_2(X1,X4,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_yellow_0)).

fof(c_0_1,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v5_orders_2(X1)
          & v3_lattice3(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( X2 = k2_yellow_0(X1,X3)
              <=> ( r1_lattice3(X1,X3,X2)
                  & ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r1_lattice3(X1,X3,X4)
                       => r1_orders_2(X1,X4,X2) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t33_yellow_0])).

fof(c_0_2,negated_conjecture,(
    ! [X9] :
      ( ~ v2_struct_0(esk1_0)
      & v5_orders_2(esk1_0)
      & v3_lattice3(esk1_0)
      & l1_orders_2(esk1_0)
      & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
      & ( m1_subset_1(esk4_0,u1_struct_0(esk1_0))
        | ~ r1_lattice3(esk1_0,esk3_0,esk2_0)
        | esk2_0 != k2_yellow_0(esk1_0,esk3_0) )
      & ( r1_lattice3(esk1_0,esk3_0,esk4_0)
        | ~ r1_lattice3(esk1_0,esk3_0,esk2_0)
        | esk2_0 != k2_yellow_0(esk1_0,esk3_0) )
      & ( ~ r1_orders_2(esk1_0,esk4_0,esk2_0)
        | ~ r1_lattice3(esk1_0,esk3_0,esk2_0)
        | esk2_0 != k2_yellow_0(esk1_0,esk3_0) )
      & ( r1_lattice3(esk1_0,esk3_0,esk2_0)
        | esk2_0 = k2_yellow_0(esk1_0,esk3_0) )
      & ( ~ m1_subset_1(X9,u1_struct_0(esk1_0))
        | ~ r1_lattice3(esk1_0,esk3_0,X9)
        | r1_orders_2(esk1_0,X9,esk2_0)
        | esk2_0 = k2_yellow_0(esk1_0,esk3_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_1])])])])])])).

cnf(c_0_3,negated_conjecture,
    ( r1_orders_2(esk1_0,X1,esk2_0)
    | esk2_0 = k2_yellow_0(esk1_0,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ r1_lattice3(esk1_0,esk3_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_2]),
    [final]).

cnf(c_0_4,negated_conjecture,
    ( r1_lattice3(esk1_0,esk3_0,esk4_0)
    | ~ r1_lattice3(esk1_0,esk3_0,esk2_0)
    | esk2_0 != k2_yellow_0(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_2]),
    [final]).

cnf(c_0_5,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk1_0))
    | ~ r1_lattice3(esk1_0,esk3_0,esk2_0)
    | esk2_0 != k2_yellow_0(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_2]),
    [final]).

cnf(c_0_6,negated_conjecture,
    ( r1_lattice3(esk1_0,esk3_0,esk2_0)
    | esk2_0 = k2_yellow_0(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_2]),
    [final]).

cnf(c_0_7,negated_conjecture,
    ( ~ r1_orders_2(esk1_0,esk4_0,esk2_0)
    | ~ r1_lattice3(esk1_0,esk3_0,esk2_0)
    | esk2_0 != k2_yellow_0(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_2]),
    [final]).

cnf(c_0_8,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_2]),
    [final]).

cnf(c_0_9,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_2]),
    [final]).

cnf(c_0_10,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_2]),
    [final]).

cnf(c_0_11,negated_conjecture,
    ( v3_lattice3(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_2]),
    [final]).

cnf(c_0_12,negated_conjecture,
    ( v5_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_2]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:38:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.39  # AutoSched0-Mode selected heuristic H_____047_C18_F1_PI_AE_R8_CS_SP_S2S
% 0.13/0.39  # and selection function SelectNewComplexAHP.
% 0.13/0.39  #
% 0.13/0.39  # Preprocessing time       : 0.040 s
% 0.13/0.39  
% 0.13/0.39  # No proof found!
% 0.13/0.39  # SZS status CounterSatisfiable
% 0.13/0.39  # SZS output start Saturation
% 0.13/0.39  fof(t33_yellow_0, conjecture, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v3_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(X2=k2_yellow_0(X1,X3)<=>(r1_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r1_lattice3(X1,X3,X4)=>r1_orders_2(X1,X4,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_yellow_0)).
% 0.13/0.39  fof(c_0_1, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v3_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(X2=k2_yellow_0(X1,X3)<=>(r1_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r1_lattice3(X1,X3,X4)=>r1_orders_2(X1,X4,X2)))))))), inference(assume_negation,[status(cth)],[t33_yellow_0])).
% 0.13/0.39  fof(c_0_2, negated_conjecture, ![X9]:((((~v2_struct_0(esk1_0)&v5_orders_2(esk1_0))&v3_lattice3(esk1_0))&l1_orders_2(esk1_0))&(m1_subset_1(esk2_0,u1_struct_0(esk1_0))&(((m1_subset_1(esk4_0,u1_struct_0(esk1_0))|~r1_lattice3(esk1_0,esk3_0,esk2_0)|esk2_0!=k2_yellow_0(esk1_0,esk3_0))&((r1_lattice3(esk1_0,esk3_0,esk4_0)|~r1_lattice3(esk1_0,esk3_0,esk2_0)|esk2_0!=k2_yellow_0(esk1_0,esk3_0))&(~r1_orders_2(esk1_0,esk4_0,esk2_0)|~r1_lattice3(esk1_0,esk3_0,esk2_0)|esk2_0!=k2_yellow_0(esk1_0,esk3_0))))&((r1_lattice3(esk1_0,esk3_0,esk2_0)|esk2_0=k2_yellow_0(esk1_0,esk3_0))&(~m1_subset_1(X9,u1_struct_0(esk1_0))|(~r1_lattice3(esk1_0,esk3_0,X9)|r1_orders_2(esk1_0,X9,esk2_0))|esk2_0=k2_yellow_0(esk1_0,esk3_0)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_1])])])])])])).
% 0.13/0.39  cnf(c_0_3, negated_conjecture, (r1_orders_2(esk1_0,X1,esk2_0)|esk2_0=k2_yellow_0(esk1_0,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk1_0))|~r1_lattice3(esk1_0,esk3_0,X1)), inference(split_conjunct,[status(thm)],[c_0_2]), ['final']).
% 0.13/0.39  cnf(c_0_4, negated_conjecture, (r1_lattice3(esk1_0,esk3_0,esk4_0)|~r1_lattice3(esk1_0,esk3_0,esk2_0)|esk2_0!=k2_yellow_0(esk1_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_2]), ['final']).
% 0.13/0.39  cnf(c_0_5, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk1_0))|~r1_lattice3(esk1_0,esk3_0,esk2_0)|esk2_0!=k2_yellow_0(esk1_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_2]), ['final']).
% 0.13/0.39  cnf(c_0_6, negated_conjecture, (r1_lattice3(esk1_0,esk3_0,esk2_0)|esk2_0=k2_yellow_0(esk1_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_2]), ['final']).
% 0.13/0.39  cnf(c_0_7, negated_conjecture, (~r1_orders_2(esk1_0,esk4_0,esk2_0)|~r1_lattice3(esk1_0,esk3_0,esk2_0)|esk2_0!=k2_yellow_0(esk1_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_2]), ['final']).
% 0.13/0.39  cnf(c_0_8, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_2]), ['final']).
% 0.13/0.39  cnf(c_0_9, negated_conjecture, (m1_subset_1(esk2_0,u1_struct_0(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_2]), ['final']).
% 0.13/0.39  cnf(c_0_10, negated_conjecture, (l1_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_2]), ['final']).
% 0.13/0.39  cnf(c_0_11, negated_conjecture, (v3_lattice3(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_2]), ['final']).
% 0.13/0.39  cnf(c_0_12, negated_conjecture, (v5_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_2]), ['final']).
% 0.13/0.39  # SZS output end Saturation
% 0.13/0.39  # Proof object total steps             : 13
% 0.13/0.39  # Proof object clause steps            : 10
% 0.13/0.39  # Proof object formula steps           : 3
% 0.13/0.39  # Proof object conjectures             : 13
% 0.13/0.39  # Proof object clause conjectures      : 10
% 0.13/0.39  # Proof object formula conjectures     : 3
% 0.13/0.39  # Proof object initial clauses used    : 10
% 0.13/0.39  # Proof object initial formulas used   : 1
% 0.13/0.39  # Proof object generating inferences   : 0
% 0.13/0.39  # Proof object simplifying inferences  : 0
% 0.13/0.39  # Parsed axioms                        : 1
% 0.13/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.39  # Initial clauses                      : 10
% 0.13/0.39  # Removed in clause preprocessing      : 0
% 0.13/0.39  # Initial clauses in saturation        : 10
% 0.13/0.39  # Processed clauses                    : 10
% 0.13/0.39  # ...of these trivial                  : 0
% 0.13/0.39  # ...subsumed                          : 0
% 0.13/0.39  # ...remaining for further processing  : 10
% 0.13/0.39  # Other redundant clauses eliminated   : 0
% 0.13/0.39  # Clauses deleted for lack of memory   : 0
% 0.13/0.39  # Backward-subsumed                    : 0
% 0.13/0.39  # Backward-rewritten                   : 0
% 0.13/0.39  # Generated clauses                    : 3
% 0.13/0.39  # ...of the previous two non-trivial   : 0
% 0.13/0.39  # Contextual simplify-reflections      : 0
% 0.13/0.39  # Paramodulations                      : 3
% 0.13/0.39  # Factorizations                       : 0
% 0.13/0.39  # Equation resolutions                 : 0
% 0.13/0.39  # Propositional unsat checks           : 0
% 0.13/0.39  #    Propositional check models        : 0
% 0.13/0.39  #    Propositional check unsatisfiable : 0
% 0.13/0.39  #    Propositional clauses             : 0
% 0.13/0.39  #    Propositional clauses after purity: 0
% 0.13/0.39  #    Propositional unsat core size     : 0
% 0.13/0.39  #    Propositional preprocessing time  : 0.000
% 0.13/0.39  #    Propositional encoding time       : 0.000
% 0.13/0.39  #    Propositional solver time         : 0.000
% 0.13/0.39  #    Success case prop preproc time    : 0.000
% 0.13/0.39  #    Success case prop encoding time   : 0.000
% 0.13/0.39  #    Success case prop solver time     : 0.000
% 0.13/0.39  # Current number of processed clauses  : 10
% 0.13/0.39  #    Positive orientable unit clauses  : 4
% 0.13/0.39  #    Positive unorientable unit clauses: 0
% 0.13/0.39  #    Negative unit clauses             : 1
% 0.13/0.39  #    Non-unit-clauses                  : 5
% 0.13/0.39  # Current number of unprocessed clauses: 0
% 0.13/0.39  # ...number of literals in the above   : 0
% 0.13/0.39  # Current number of archived formulas  : 0
% 0.13/0.39  # Current number of archived clauses   : 0
% 0.13/0.39  # Clause-clause subsumption calls (NU) : 1
% 0.13/0.39  # Rec. Clause-clause subsumption calls : 0
% 0.13/0.39  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.39  # Unit Clause-clause subsumption calls : 0
% 0.13/0.39  # Rewrite failures with RHS unbound    : 0
% 0.13/0.39  # BW rewrite match attempts            : 0
% 0.13/0.39  # BW rewrite match successes           : 0
% 0.13/0.39  # Condensation attempts                : 0
% 0.13/0.39  # Condensation successes               : 0
% 0.13/0.39  # Termbank termtop insertions          : 685
% 0.13/0.39  
% 0.13/0.39  # -------------------------------------------------
% 0.13/0.39  # User time                : 0.041 s
% 0.13/0.39  # System time              : 0.003 s
% 0.13/0.39  # Total time               : 0.044 s
% 0.13/0.39  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:20 EST 2020

% Result     : CounterSatisfiable 0.19s
% Output     : Saturation 0.19s
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
fof(t32_yellow_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v3_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( X2 = k1_yellow_0(X1,X3)
            <=> ( r2_lattice3(X1,X3,X2)
                & ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r2_lattice3(X1,X3,X4)
                     => r1_orders_2(X1,X2,X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_yellow_0)).

fof(c_0_1,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v5_orders_2(X1)
          & v3_lattice3(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( X2 = k1_yellow_0(X1,X3)
              <=> ( r2_lattice3(X1,X3,X2)
                  & ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r2_lattice3(X1,X3,X4)
                       => r1_orders_2(X1,X2,X4) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t32_yellow_0])).

fof(c_0_2,negated_conjecture,(
    ! [X9] :
      ( ~ v2_struct_0(esk1_0)
      & v5_orders_2(esk1_0)
      & v3_lattice3(esk1_0)
      & l1_orders_2(esk1_0)
      & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
      & ( m1_subset_1(esk4_0,u1_struct_0(esk1_0))
        | ~ r2_lattice3(esk1_0,esk3_0,esk2_0)
        | esk2_0 != k1_yellow_0(esk1_0,esk3_0) )
      & ( r2_lattice3(esk1_0,esk3_0,esk4_0)
        | ~ r2_lattice3(esk1_0,esk3_0,esk2_0)
        | esk2_0 != k1_yellow_0(esk1_0,esk3_0) )
      & ( ~ r1_orders_2(esk1_0,esk2_0,esk4_0)
        | ~ r2_lattice3(esk1_0,esk3_0,esk2_0)
        | esk2_0 != k1_yellow_0(esk1_0,esk3_0) )
      & ( r2_lattice3(esk1_0,esk3_0,esk2_0)
        | esk2_0 = k1_yellow_0(esk1_0,esk3_0) )
      & ( ~ m1_subset_1(X9,u1_struct_0(esk1_0))
        | ~ r2_lattice3(esk1_0,esk3_0,X9)
        | r1_orders_2(esk1_0,esk2_0,X9)
        | esk2_0 = k1_yellow_0(esk1_0,esk3_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_1])])])])])])).

cnf(c_0_3,negated_conjecture,
    ( r1_orders_2(esk1_0,esk2_0,X1)
    | esk2_0 = k1_yellow_0(esk1_0,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ r2_lattice3(esk1_0,esk3_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_2]),
    [final]).

cnf(c_0_4,negated_conjecture,
    ( r2_lattice3(esk1_0,esk3_0,esk4_0)
    | ~ r2_lattice3(esk1_0,esk3_0,esk2_0)
    | esk2_0 != k1_yellow_0(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_2]),
    [final]).

cnf(c_0_5,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk1_0))
    | ~ r2_lattice3(esk1_0,esk3_0,esk2_0)
    | esk2_0 != k1_yellow_0(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_2]),
    [final]).

cnf(c_0_6,negated_conjecture,
    ( r2_lattice3(esk1_0,esk3_0,esk2_0)
    | esk2_0 = k1_yellow_0(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_2]),
    [final]).

cnf(c_0_7,negated_conjecture,
    ( ~ r1_orders_2(esk1_0,esk2_0,esk4_0)
    | ~ r2_lattice3(esk1_0,esk3_0,esk2_0)
    | esk2_0 != k1_yellow_0(esk1_0,esk3_0) ),
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
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:43:38 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.19/0.36  # AutoSched0-Mode selected heuristic H_____047_C18_F1_PI_AE_R8_CS_SP_S2S
% 0.19/0.36  # and selection function SelectNewComplexAHP.
% 0.19/0.36  #
% 0.19/0.36  # Preprocessing time       : 0.025 s
% 0.19/0.36  
% 0.19/0.36  # No proof found!
% 0.19/0.36  # SZS status CounterSatisfiable
% 0.19/0.36  # SZS output start Saturation
% 0.19/0.36  fof(t32_yellow_0, conjecture, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v3_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(X2=k1_yellow_0(X1,X3)<=>(r2_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X3,X4)=>r1_orders_2(X1,X2,X4))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_yellow_0)).
% 0.19/0.36  fof(c_0_1, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v3_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(X2=k1_yellow_0(X1,X3)<=>(r2_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X3,X4)=>r1_orders_2(X1,X2,X4)))))))), inference(assume_negation,[status(cth)],[t32_yellow_0])).
% 0.19/0.36  fof(c_0_2, negated_conjecture, ![X9]:((((~v2_struct_0(esk1_0)&v5_orders_2(esk1_0))&v3_lattice3(esk1_0))&l1_orders_2(esk1_0))&(m1_subset_1(esk2_0,u1_struct_0(esk1_0))&(((m1_subset_1(esk4_0,u1_struct_0(esk1_0))|~r2_lattice3(esk1_0,esk3_0,esk2_0)|esk2_0!=k1_yellow_0(esk1_0,esk3_0))&((r2_lattice3(esk1_0,esk3_0,esk4_0)|~r2_lattice3(esk1_0,esk3_0,esk2_0)|esk2_0!=k1_yellow_0(esk1_0,esk3_0))&(~r1_orders_2(esk1_0,esk2_0,esk4_0)|~r2_lattice3(esk1_0,esk3_0,esk2_0)|esk2_0!=k1_yellow_0(esk1_0,esk3_0))))&((r2_lattice3(esk1_0,esk3_0,esk2_0)|esk2_0=k1_yellow_0(esk1_0,esk3_0))&(~m1_subset_1(X9,u1_struct_0(esk1_0))|(~r2_lattice3(esk1_0,esk3_0,X9)|r1_orders_2(esk1_0,esk2_0,X9))|esk2_0=k1_yellow_0(esk1_0,esk3_0)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_1])])])])])])).
% 0.19/0.36  cnf(c_0_3, negated_conjecture, (r1_orders_2(esk1_0,esk2_0,X1)|esk2_0=k1_yellow_0(esk1_0,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk1_0))|~r2_lattice3(esk1_0,esk3_0,X1)), inference(split_conjunct,[status(thm)],[c_0_2]), ['final']).
% 0.19/0.36  cnf(c_0_4, negated_conjecture, (r2_lattice3(esk1_0,esk3_0,esk4_0)|~r2_lattice3(esk1_0,esk3_0,esk2_0)|esk2_0!=k1_yellow_0(esk1_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_2]), ['final']).
% 0.19/0.36  cnf(c_0_5, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk1_0))|~r2_lattice3(esk1_0,esk3_0,esk2_0)|esk2_0!=k1_yellow_0(esk1_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_2]), ['final']).
% 0.19/0.36  cnf(c_0_6, negated_conjecture, (r2_lattice3(esk1_0,esk3_0,esk2_0)|esk2_0=k1_yellow_0(esk1_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_2]), ['final']).
% 0.19/0.36  cnf(c_0_7, negated_conjecture, (~r1_orders_2(esk1_0,esk2_0,esk4_0)|~r2_lattice3(esk1_0,esk3_0,esk2_0)|esk2_0!=k1_yellow_0(esk1_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_2]), ['final']).
% 0.19/0.36  cnf(c_0_8, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_2]), ['final']).
% 0.19/0.36  cnf(c_0_9, negated_conjecture, (m1_subset_1(esk2_0,u1_struct_0(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_2]), ['final']).
% 0.19/0.36  cnf(c_0_10, negated_conjecture, (l1_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_2]), ['final']).
% 0.19/0.36  cnf(c_0_11, negated_conjecture, (v3_lattice3(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_2]), ['final']).
% 0.19/0.36  cnf(c_0_12, negated_conjecture, (v5_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_2]), ['final']).
% 0.19/0.36  # SZS output end Saturation
% 0.19/0.36  # Proof object total steps             : 13
% 0.19/0.36  # Proof object clause steps            : 10
% 0.19/0.36  # Proof object formula steps           : 3
% 0.19/0.36  # Proof object conjectures             : 13
% 0.19/0.36  # Proof object clause conjectures      : 10
% 0.19/0.36  # Proof object formula conjectures     : 3
% 0.19/0.36  # Proof object initial clauses used    : 10
% 0.19/0.36  # Proof object initial formulas used   : 1
% 0.19/0.36  # Proof object generating inferences   : 0
% 0.19/0.36  # Proof object simplifying inferences  : 0
% 0.19/0.36  # Parsed axioms                        : 1
% 0.19/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.36  # Initial clauses                      : 10
% 0.19/0.36  # Removed in clause preprocessing      : 0
% 0.19/0.36  # Initial clauses in saturation        : 10
% 0.19/0.36  # Processed clauses                    : 10
% 0.19/0.36  # ...of these trivial                  : 0
% 0.19/0.36  # ...subsumed                          : 0
% 0.19/0.36  # ...remaining for further processing  : 10
% 0.19/0.36  # Other redundant clauses eliminated   : 0
% 0.19/0.36  # Clauses deleted for lack of memory   : 0
% 0.19/0.36  # Backward-subsumed                    : 0
% 0.19/0.36  # Backward-rewritten                   : 0
% 0.19/0.36  # Generated clauses                    : 3
% 0.19/0.36  # ...of the previous two non-trivial   : 0
% 0.19/0.36  # Contextual simplify-reflections      : 0
% 0.19/0.36  # Paramodulations                      : 3
% 0.19/0.36  # Factorizations                       : 0
% 0.19/0.36  # Equation resolutions                 : 0
% 0.19/0.36  # Propositional unsat checks           : 0
% 0.19/0.36  #    Propositional check models        : 0
% 0.19/0.36  #    Propositional check unsatisfiable : 0
% 0.19/0.36  #    Propositional clauses             : 0
% 0.19/0.36  #    Propositional clauses after purity: 0
% 0.19/0.36  #    Propositional unsat core size     : 0
% 0.19/0.36  #    Propositional preprocessing time  : 0.000
% 0.19/0.36  #    Propositional encoding time       : 0.000
% 0.19/0.36  #    Propositional solver time         : 0.000
% 0.19/0.36  #    Success case prop preproc time    : 0.000
% 0.19/0.36  #    Success case prop encoding time   : 0.000
% 0.19/0.36  #    Success case prop solver time     : 0.000
% 0.19/0.36  # Current number of processed clauses  : 10
% 0.19/0.36  #    Positive orientable unit clauses  : 4
% 0.19/0.36  #    Positive unorientable unit clauses: 0
% 0.19/0.36  #    Negative unit clauses             : 1
% 0.19/0.36  #    Non-unit-clauses                  : 5
% 0.19/0.36  # Current number of unprocessed clauses: 0
% 0.19/0.36  # ...number of literals in the above   : 0
% 0.19/0.36  # Current number of archived formulas  : 0
% 0.19/0.36  # Current number of archived clauses   : 0
% 0.19/0.36  # Clause-clause subsumption calls (NU) : 1
% 0.19/0.36  # Rec. Clause-clause subsumption calls : 0
% 0.19/0.36  # Non-unit clause-clause subsumptions  : 0
% 0.19/0.36  # Unit Clause-clause subsumption calls : 0
% 0.19/0.36  # Rewrite failures with RHS unbound    : 0
% 0.19/0.36  # BW rewrite match attempts            : 0
% 0.19/0.36  # BW rewrite match successes           : 0
% 0.19/0.36  # Condensation attempts                : 0
% 0.19/0.36  # Condensation successes               : 0
% 0.19/0.36  # Termbank termtop insertions          : 685
% 0.19/0.36  
% 0.19/0.36  # -------------------------------------------------
% 0.19/0.36  # User time                : 0.025 s
% 0.19/0.36  # System time              : 0.003 s
% 0.19/0.36  # Total time               : 0.029 s
% 0.19/0.36  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------

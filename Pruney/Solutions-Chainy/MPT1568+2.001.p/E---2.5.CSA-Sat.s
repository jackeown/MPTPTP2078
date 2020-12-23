%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:33 EST 2020

% Result     : CounterSatisfiable 0.13s
% Output     : Saturation 0.13s
% Verified   : 
% Statistics : Number of formulae       :    9 (  24 expanded)
%              Number of clauses        :    6 (   6 expanded)
%              Number of leaves         :    1 (   6 expanded)
%              Depth                    :    3
%              Number of atoms          :   34 ( 154 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t46_yellow_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2,X3] :
          ( ( ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_lattice3(X1,X2,X4)
                <=> r2_lattice3(X1,X3,X4) ) )
            & r1_yellow_0(X1,X2) )
         => r1_yellow_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_yellow_0)).

fof(c_0_1,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_orders_2(X1) )
       => ! [X2,X3] :
            ( ( ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( r2_lattice3(X1,X2,X4)
                  <=> r2_lattice3(X1,X3,X4) ) )
              & r1_yellow_0(X1,X2) )
           => r1_yellow_0(X1,X3) ) ) ),
    inference(assume_negation,[status(cth)],[t46_yellow_0])).

fof(c_0_2,negated_conjecture,(
    ! [X8] :
      ( ~ v2_struct_0(esk1_0)
      & l1_orders_2(esk1_0)
      & ( ~ r2_lattice3(esk1_0,esk2_0,X8)
        | r2_lattice3(esk1_0,esk3_0,X8)
        | ~ m1_subset_1(X8,u1_struct_0(esk1_0)) )
      & ( ~ r2_lattice3(esk1_0,esk3_0,X8)
        | r2_lattice3(esk1_0,esk2_0,X8)
        | ~ m1_subset_1(X8,u1_struct_0(esk1_0)) )
      & r1_yellow_0(esk1_0,esk2_0)
      & ~ r1_yellow_0(esk1_0,esk3_0) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_1])])])])])])).

cnf(c_0_3,negated_conjecture,
    ( r2_lattice3(esk1_0,esk3_0,X1)
    | ~ r2_lattice3(esk1_0,esk2_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_2]),
    [final]).

cnf(c_0_4,negated_conjecture,
    ( r2_lattice3(esk1_0,esk2_0,X1)
    | ~ r2_lattice3(esk1_0,esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_2]),
    [final]).

cnf(c_0_5,negated_conjecture,
    ( ~ r1_yellow_0(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_2]),
    [final]).

cnf(c_0_6,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_2]),
    [final]).

cnf(c_0_7,negated_conjecture,
    ( r1_yellow_0(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_2]),
    [final]).

cnf(c_0_8,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_2]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 10:29:12 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.36  # AutoSched0-Mode selected heuristic G_E___107_C41_F1_PI_AE_Q4_CS_SP_PS_S2U
% 0.13/0.36  # and selection function SelectNewComplexAHPExceptRRHorn.
% 0.13/0.36  #
% 0.13/0.36  # Preprocessing time       : 0.025 s
% 0.13/0.36  # Presaturation interreduction done
% 0.13/0.36  
% 0.13/0.36  # No proof found!
% 0.13/0.36  # SZS status CounterSatisfiable
% 0.13/0.36  # SZS output start Saturation
% 0.13/0.36  fof(t46_yellow_0, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_orders_2(X1))=>![X2, X3]:((![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X4)<=>r2_lattice3(X1,X3,X4)))&r1_yellow_0(X1,X2))=>r1_yellow_0(X1,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_yellow_0)).
% 0.13/0.36  fof(c_0_1, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_orders_2(X1))=>![X2, X3]:((![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X4)<=>r2_lattice3(X1,X3,X4)))&r1_yellow_0(X1,X2))=>r1_yellow_0(X1,X3)))), inference(assume_negation,[status(cth)],[t46_yellow_0])).
% 0.13/0.36  fof(c_0_2, negated_conjecture, ![X8]:((~v2_struct_0(esk1_0)&l1_orders_2(esk1_0))&((((~r2_lattice3(esk1_0,esk2_0,X8)|r2_lattice3(esk1_0,esk3_0,X8)|~m1_subset_1(X8,u1_struct_0(esk1_0)))&(~r2_lattice3(esk1_0,esk3_0,X8)|r2_lattice3(esk1_0,esk2_0,X8)|~m1_subset_1(X8,u1_struct_0(esk1_0))))&r1_yellow_0(esk1_0,esk2_0))&~r1_yellow_0(esk1_0,esk3_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_1])])])])])])).
% 0.13/0.36  cnf(c_0_3, negated_conjecture, (r2_lattice3(esk1_0,esk3_0,X1)|~r2_lattice3(esk1_0,esk2_0,X1)|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_2]), ['final']).
% 0.13/0.36  cnf(c_0_4, negated_conjecture, (r2_lattice3(esk1_0,esk2_0,X1)|~r2_lattice3(esk1_0,esk3_0,X1)|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_2]), ['final']).
% 0.13/0.36  cnf(c_0_5, negated_conjecture, (~r1_yellow_0(esk1_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_2]), ['final']).
% 0.13/0.36  cnf(c_0_6, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_2]), ['final']).
% 0.13/0.36  cnf(c_0_7, negated_conjecture, (r1_yellow_0(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_2]), ['final']).
% 0.13/0.36  cnf(c_0_8, negated_conjecture, (l1_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_2]), ['final']).
% 0.13/0.36  # SZS output end Saturation
% 0.13/0.36  # Proof object total steps             : 9
% 0.13/0.36  # Proof object clause steps            : 6
% 0.13/0.36  # Proof object formula steps           : 3
% 0.13/0.36  # Proof object conjectures             : 9
% 0.13/0.36  # Proof object clause conjectures      : 6
% 0.13/0.36  # Proof object formula conjectures     : 3
% 0.13/0.36  # Proof object initial clauses used    : 6
% 0.13/0.36  # Proof object initial formulas used   : 1
% 0.13/0.36  # Proof object generating inferences   : 0
% 0.13/0.36  # Proof object simplifying inferences  : 0
% 0.13/0.36  # Parsed axioms                        : 1
% 0.13/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.36  # Initial clauses                      : 6
% 0.13/0.36  # Removed in clause preprocessing      : 0
% 0.13/0.36  # Initial clauses in saturation        : 6
% 0.13/0.36  # Processed clauses                    : 12
% 0.13/0.36  # ...of these trivial                  : 0
% 0.13/0.36  # ...subsumed                          : 0
% 0.13/0.36  # ...remaining for further processing  : 12
% 0.13/0.36  # Other redundant clauses eliminated   : 0
% 0.13/0.36  # Clauses deleted for lack of memory   : 0
% 0.13/0.36  # Backward-subsumed                    : 0
% 0.13/0.36  # Backward-rewritten                   : 0
% 0.13/0.36  # Generated clauses                    : 0
% 0.13/0.36  # ...of the previous two non-trivial   : 0
% 0.13/0.36  # Contextual simplify-reflections      : 0
% 0.13/0.36  # Paramodulations                      : 0
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
% 0.13/0.36  #    Positive orientable unit clauses  : 2
% 0.13/0.36  #    Positive unorientable unit clauses: 0
% 0.13/0.36  #    Negative unit clauses             : 2
% 0.13/0.36  #    Non-unit-clauses                  : 2
% 0.13/0.36  # Current number of unprocessed clauses: 0
% 0.13/0.36  # ...number of literals in the above   : 0
% 0.13/0.36  # Current number of archived formulas  : 0
% 0.13/0.36  # Current number of archived clauses   : 6
% 0.13/0.36  # Clause-clause subsumption calls (NU) : 0
% 0.13/0.36  # Rec. Clause-clause subsumption calls : 0
% 0.13/0.36  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.36  # Unit Clause-clause subsumption calls : 0
% 0.13/0.36  # Rewrite failures with RHS unbound    : 0
% 0.13/0.36  # BW rewrite match attempts            : 0
% 0.13/0.36  # BW rewrite match successes           : 0
% 0.13/0.36  # Condensation attempts                : 0
% 0.13/0.36  # Condensation successes               : 0
% 0.13/0.36  # Termbank termtop insertions          : 436
% 0.13/0.36  
% 0.13/0.36  # -------------------------------------------------
% 0.13/0.36  # User time                : 0.024 s
% 0.13/0.36  # System time              : 0.005 s
% 0.13/0.36  # Total time               : 0.029 s
% 0.13/0.36  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------

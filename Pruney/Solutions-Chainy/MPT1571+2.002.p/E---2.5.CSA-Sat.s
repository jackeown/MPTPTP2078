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
% DateTime   : Thu Dec  3 11:15:33 EST 2020

% Result     : CounterSatisfiable 0.14s
% Output     : Saturation 0.14s
% Verified   : 
% Statistics : Number of formulae       :    9 (  24 expanded)
%              Number of clauses        :    6 (   6 expanded)
%              Number of leaves         :    1 (   6 expanded)
%              Depth                    :    3
%              Number of atoms          :   34 ( 154 expanded)
%              Number of equality atoms :    4 (  19 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t49_yellow_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2,X3] :
          ( ( r2_yellow_0(X1,X2)
            & ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r1_lattice3(X1,X2,X4)
                <=> r1_lattice3(X1,X3,X4) ) ) )
         => k2_yellow_0(X1,X2) = k2_yellow_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_yellow_0)).

fof(c_0_1,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_orders_2(X1) )
       => ! [X2,X3] :
            ( ( r2_yellow_0(X1,X2)
              & ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( r1_lattice3(X1,X2,X4)
                  <=> r1_lattice3(X1,X3,X4) ) ) )
           => k2_yellow_0(X1,X2) = k2_yellow_0(X1,X3) ) ) ),
    inference(assume_negation,[status(cth)],[t49_yellow_0])).

fof(c_0_2,negated_conjecture,(
    ! [X8] :
      ( ~ v2_struct_0(esk1_0)
      & l1_orders_2(esk1_0)
      & r2_yellow_0(esk1_0,esk2_0)
      & ( ~ r1_lattice3(esk1_0,esk2_0,X8)
        | r1_lattice3(esk1_0,esk3_0,X8)
        | ~ m1_subset_1(X8,u1_struct_0(esk1_0)) )
      & ( ~ r1_lattice3(esk1_0,esk3_0,X8)
        | r1_lattice3(esk1_0,esk2_0,X8)
        | ~ m1_subset_1(X8,u1_struct_0(esk1_0)) )
      & k2_yellow_0(esk1_0,esk2_0) != k2_yellow_0(esk1_0,esk3_0) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_1])])])])])])).

cnf(c_0_3,negated_conjecture,
    ( r1_lattice3(esk1_0,esk3_0,X1)
    | ~ r1_lattice3(esk1_0,esk2_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_2]),
    [final]).

cnf(c_0_4,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,X1)
    | ~ r1_lattice3(esk1_0,esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_2]),
    [final]).

cnf(c_0_5,negated_conjecture,
    ( k2_yellow_0(esk1_0,esk2_0) != k2_yellow_0(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_2]),
    [final]).

cnf(c_0_6,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_2]),
    [final]).

cnf(c_0_7,negated_conjecture,
    ( r2_yellow_0(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_2]),
    [final]).

cnf(c_0_8,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_2]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:33:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.14/0.38  # and selection function SelectCQIPrecWNTNp.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.025 s
% 0.14/0.38  # Presaturation interreduction done
% 0.14/0.38  
% 0.14/0.38  # No proof found!
% 0.14/0.38  # SZS status CounterSatisfiable
% 0.14/0.38  # SZS output start Saturation
% 0.14/0.38  fof(t49_yellow_0, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_orders_2(X1))=>![X2, X3]:((r2_yellow_0(X1,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r1_lattice3(X1,X2,X4)<=>r1_lattice3(X1,X3,X4))))=>k2_yellow_0(X1,X2)=k2_yellow_0(X1,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_yellow_0)).
% 0.14/0.38  fof(c_0_1, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_orders_2(X1))=>![X2, X3]:((r2_yellow_0(X1,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r1_lattice3(X1,X2,X4)<=>r1_lattice3(X1,X3,X4))))=>k2_yellow_0(X1,X2)=k2_yellow_0(X1,X3)))), inference(assume_negation,[status(cth)],[t49_yellow_0])).
% 0.14/0.38  fof(c_0_2, negated_conjecture, ![X8]:((~v2_struct_0(esk1_0)&l1_orders_2(esk1_0))&((r2_yellow_0(esk1_0,esk2_0)&((~r1_lattice3(esk1_0,esk2_0,X8)|r1_lattice3(esk1_0,esk3_0,X8)|~m1_subset_1(X8,u1_struct_0(esk1_0)))&(~r1_lattice3(esk1_0,esk3_0,X8)|r1_lattice3(esk1_0,esk2_0,X8)|~m1_subset_1(X8,u1_struct_0(esk1_0)))))&k2_yellow_0(esk1_0,esk2_0)!=k2_yellow_0(esk1_0,esk3_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_1])])])])])])).
% 0.14/0.38  cnf(c_0_3, negated_conjecture, (r1_lattice3(esk1_0,esk3_0,X1)|~r1_lattice3(esk1_0,esk2_0,X1)|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_2]), ['final']).
% 0.14/0.38  cnf(c_0_4, negated_conjecture, (r1_lattice3(esk1_0,esk2_0,X1)|~r1_lattice3(esk1_0,esk3_0,X1)|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_2]), ['final']).
% 0.14/0.38  cnf(c_0_5, negated_conjecture, (k2_yellow_0(esk1_0,esk2_0)!=k2_yellow_0(esk1_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_2]), ['final']).
% 0.14/0.38  cnf(c_0_6, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_2]), ['final']).
% 0.14/0.38  cnf(c_0_7, negated_conjecture, (r2_yellow_0(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_2]), ['final']).
% 0.14/0.38  cnf(c_0_8, negated_conjecture, (l1_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_2]), ['final']).
% 0.14/0.38  # SZS output end Saturation
% 0.14/0.38  # Proof object total steps             : 9
% 0.14/0.38  # Proof object clause steps            : 6
% 0.14/0.38  # Proof object formula steps           : 3
% 0.14/0.38  # Proof object conjectures             : 9
% 0.14/0.38  # Proof object clause conjectures      : 6
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 6
% 0.14/0.38  # Proof object initial formulas used   : 1
% 0.14/0.38  # Proof object generating inferences   : 0
% 0.14/0.38  # Proof object simplifying inferences  : 0
% 0.14/0.38  # Parsed axioms                        : 1
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 6
% 0.14/0.38  # Removed in clause preprocessing      : 0
% 0.14/0.38  # Initial clauses in saturation        : 6
% 0.14/0.38  # Processed clauses                    : 12
% 0.14/0.38  # ...of these trivial                  : 0
% 0.14/0.38  # ...subsumed                          : 0
% 0.14/0.38  # ...remaining for further processing  : 12
% 0.14/0.38  # Other redundant clauses eliminated   : 0
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 0
% 0.14/0.38  # Backward-rewritten                   : 0
% 0.14/0.38  # Generated clauses                    : 0
% 0.14/0.38  # ...of the previous two non-trivial   : 0
% 0.14/0.38  # Contextual simplify-reflections      : 0
% 0.14/0.38  # Paramodulations                      : 0
% 0.14/0.38  # Factorizations                       : 0
% 0.14/0.38  # Equation resolutions                 : 0
% 0.14/0.38  # Propositional unsat checks           : 0
% 0.14/0.38  #    Propositional check models        : 0
% 0.14/0.38  #    Propositional check unsatisfiable : 0
% 0.14/0.38  #    Propositional clauses             : 0
% 0.14/0.38  #    Propositional clauses after purity: 0
% 0.14/0.38  #    Propositional unsat core size     : 0
% 0.14/0.38  #    Propositional preprocessing time  : 0.000
% 0.14/0.38  #    Propositional encoding time       : 0.000
% 0.14/0.38  #    Propositional solver time         : 0.000
% 0.14/0.38  #    Success case prop preproc time    : 0.000
% 0.14/0.38  #    Success case prop encoding time   : 0.000
% 0.14/0.38  #    Success case prop solver time     : 0.000
% 0.14/0.38  # Current number of processed clauses  : 6
% 0.14/0.38  #    Positive orientable unit clauses  : 2
% 0.14/0.38  #    Positive unorientable unit clauses: 0
% 0.14/0.38  #    Negative unit clauses             : 2
% 0.14/0.38  #    Non-unit-clauses                  : 2
% 0.14/0.38  # Current number of unprocessed clauses: 0
% 0.14/0.38  # ...number of literals in the above   : 0
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 6
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 0
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 0
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.14/0.38  # Unit Clause-clause subsumption calls : 0
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 0
% 0.14/0.38  # BW rewrite match successes           : 0
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 443
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.027 s
% 0.14/0.38  # System time              : 0.001 s
% 0.14/0.38  # Total time               : 0.028 s
% 0.14/0.38  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------

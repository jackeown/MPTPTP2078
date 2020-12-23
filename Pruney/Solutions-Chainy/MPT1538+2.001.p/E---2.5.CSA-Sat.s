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
% DateTime   : Thu Dec  3 11:15:15 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   16 (  41 expanded)
%              Number of clauses        :   11 (  12 expanded)
%              Number of leaves         :    2 (  10 expanded)
%              Depth                    :    4
%              Number of atoms          :   88 ( 394 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t16_yellow_0,conjecture,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( r2_yellow_0(X1,X2)
        <=> ? [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
              & r1_lattice3(X1,X2,X3)
              & ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( r1_lattice3(X1,X2,X4)
                   => r1_orders_2(X1,X4,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_yellow_0)).

fof(t25_orders_2,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( ( r1_orders_2(X1,X2,X3)
                  & r1_orders_2(X1,X3,X2) )
               => X2 = X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_orders_2)).

fof(c_0_2,negated_conjecture,(
    ~ ! [X1] :
        ( ( v5_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( r2_yellow_0(X1,X2)
          <=> ? [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
                & r1_lattice3(X1,X2,X3)
                & ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r1_lattice3(X1,X2,X4)
                     => r1_orders_2(X1,X4,X3) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t16_yellow_0])).

fof(c_0_3,plain,(
    ! [X5,X6,X7] :
      ( ~ v5_orders_2(X5)
      | ~ l1_orders_2(X5)
      | ~ m1_subset_1(X6,u1_struct_0(X5))
      | ~ m1_subset_1(X7,u1_struct_0(X5))
      | ~ r1_orders_2(X5,X6,X7)
      | ~ r1_orders_2(X5,X7,X6)
      | X6 = X7 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_orders_2])])])).

fof(c_0_4,negated_conjecture,(
    ! [X10,X13] :
      ( v5_orders_2(esk1_0)
      & l1_orders_2(esk1_0)
      & ( m1_subset_1(esk3_1(X10),u1_struct_0(esk1_0))
        | ~ m1_subset_1(X10,u1_struct_0(esk1_0))
        | ~ r1_lattice3(esk1_0,esk2_0,X10)
        | ~ r2_yellow_0(esk1_0,esk2_0) )
      & ( r1_lattice3(esk1_0,esk2_0,esk3_1(X10))
        | ~ m1_subset_1(X10,u1_struct_0(esk1_0))
        | ~ r1_lattice3(esk1_0,esk2_0,X10)
        | ~ r2_yellow_0(esk1_0,esk2_0) )
      & ( ~ r1_orders_2(esk1_0,esk3_1(X10),X10)
        | ~ m1_subset_1(X10,u1_struct_0(esk1_0))
        | ~ r1_lattice3(esk1_0,esk2_0,X10)
        | ~ r2_yellow_0(esk1_0,esk2_0) )
      & ( m1_subset_1(esk4_0,u1_struct_0(esk1_0))
        | r2_yellow_0(esk1_0,esk2_0) )
      & ( r1_lattice3(esk1_0,esk2_0,esk4_0)
        | r2_yellow_0(esk1_0,esk2_0) )
      & ( ~ m1_subset_1(X13,u1_struct_0(esk1_0))
        | ~ r1_lattice3(esk1_0,esk2_0,X13)
        | r1_orders_2(esk1_0,X13,esk4_0)
        | r2_yellow_0(esk1_0,esk2_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_2])])])])])).

cnf(c_0_5,plain,
    ( X2 = X3
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ r1_orders_2(X1,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3]),
    [final]).

cnf(c_0_6,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk1_0))
    | r2_yellow_0(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_7,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_8,negated_conjecture,
    ( v5_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_9,negated_conjecture,
    ( r1_orders_2(esk1_0,X1,esk4_0)
    | r2_yellow_0(esk1_0,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ r1_lattice3(esk1_0,esk2_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_10,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,esk4_0)
    | r2_yellow_0(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_11,negated_conjecture,
    ( X1 = esk4_0
    | r2_yellow_0(esk1_0,esk2_0)
    | ~ r1_orders_2(esk1_0,esk4_0,X1)
    | ~ r1_orders_2(esk1_0,X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_5,c_0_6]),c_0_7]),c_0_8])]),
    [final]).

cnf(c_0_12,negated_conjecture,
    ( ~ r1_orders_2(esk1_0,esk3_1(X1),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ r1_lattice3(esk1_0,esk2_0,X1)
    | ~ r2_yellow_0(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_13,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,esk3_1(X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ r1_lattice3(esk1_0,esk2_0,X1)
    | ~ r2_yellow_0(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk3_1(X1),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ r1_lattice3(esk1_0,esk2_0,X1)
    | ~ r2_yellow_0(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_15,negated_conjecture,
    ( r2_yellow_0(esk1_0,esk2_0)
    | r1_orders_2(esk1_0,esk4_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_6]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:01:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.37  # AutoSched0-Mode selected heuristic G_____0026_C18_F1_SE_CS_SP_S4S
% 0.20/0.37  # and selection function SelectNewComplexAHPNS.
% 0.20/0.37  #
% 0.20/0.37  # Preprocessing time       : 0.026 s
% 0.20/0.37  
% 0.20/0.37  # No proof found!
% 0.20/0.37  # SZS status CounterSatisfiable
% 0.20/0.37  # SZS output start Saturation
% 0.20/0.37  fof(t16_yellow_0, conjecture, ![X1]:((v5_orders_2(X1)&l1_orders_2(X1))=>![X2]:(r2_yellow_0(X1,X2)<=>?[X3]:((m1_subset_1(X3,u1_struct_0(X1))&r1_lattice3(X1,X2,X3))&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r1_lattice3(X1,X2,X4)=>r1_orders_2(X1,X4,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_yellow_0)).
% 0.20/0.37  fof(t25_orders_2, axiom, ![X1]:((v5_orders_2(X1)&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>((r1_orders_2(X1,X2,X3)&r1_orders_2(X1,X3,X2))=>X2=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_orders_2)).
% 0.20/0.37  fof(c_0_2, negated_conjecture, ~(![X1]:((v5_orders_2(X1)&l1_orders_2(X1))=>![X2]:(r2_yellow_0(X1,X2)<=>?[X3]:((m1_subset_1(X3,u1_struct_0(X1))&r1_lattice3(X1,X2,X3))&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r1_lattice3(X1,X2,X4)=>r1_orders_2(X1,X4,X3))))))), inference(assume_negation,[status(cth)],[t16_yellow_0])).
% 0.20/0.37  fof(c_0_3, plain, ![X5, X6, X7]:(~v5_orders_2(X5)|~l1_orders_2(X5)|(~m1_subset_1(X6,u1_struct_0(X5))|(~m1_subset_1(X7,u1_struct_0(X5))|(~r1_orders_2(X5,X6,X7)|~r1_orders_2(X5,X7,X6)|X6=X7)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_orders_2])])])).
% 0.20/0.37  fof(c_0_4, negated_conjecture, ![X10, X13]:((v5_orders_2(esk1_0)&l1_orders_2(esk1_0))&(((m1_subset_1(esk3_1(X10),u1_struct_0(esk1_0))|(~m1_subset_1(X10,u1_struct_0(esk1_0))|~r1_lattice3(esk1_0,esk2_0,X10))|~r2_yellow_0(esk1_0,esk2_0))&((r1_lattice3(esk1_0,esk2_0,esk3_1(X10))|(~m1_subset_1(X10,u1_struct_0(esk1_0))|~r1_lattice3(esk1_0,esk2_0,X10))|~r2_yellow_0(esk1_0,esk2_0))&(~r1_orders_2(esk1_0,esk3_1(X10),X10)|(~m1_subset_1(X10,u1_struct_0(esk1_0))|~r1_lattice3(esk1_0,esk2_0,X10))|~r2_yellow_0(esk1_0,esk2_0))))&(((m1_subset_1(esk4_0,u1_struct_0(esk1_0))|r2_yellow_0(esk1_0,esk2_0))&(r1_lattice3(esk1_0,esk2_0,esk4_0)|r2_yellow_0(esk1_0,esk2_0)))&(~m1_subset_1(X13,u1_struct_0(esk1_0))|(~r1_lattice3(esk1_0,esk2_0,X13)|r1_orders_2(esk1_0,X13,esk4_0))|r2_yellow_0(esk1_0,esk2_0))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_2])])])])])).
% 0.20/0.37  cnf(c_0_5, plain, (X2=X3|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~r1_orders_2(X1,X2,X3)|~r1_orders_2(X1,X3,X2)), inference(split_conjunct,[status(thm)],[c_0_3]), ['final']).
% 0.20/0.37  cnf(c_0_6, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk1_0))|r2_yellow_0(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.20/0.37  cnf(c_0_7, negated_conjecture, (l1_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.20/0.37  cnf(c_0_8, negated_conjecture, (v5_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.20/0.37  cnf(c_0_9, negated_conjecture, (r1_orders_2(esk1_0,X1,esk4_0)|r2_yellow_0(esk1_0,esk2_0)|~m1_subset_1(X1,u1_struct_0(esk1_0))|~r1_lattice3(esk1_0,esk2_0,X1)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.20/0.37  cnf(c_0_10, negated_conjecture, (r1_lattice3(esk1_0,esk2_0,esk4_0)|r2_yellow_0(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.20/0.37  cnf(c_0_11, negated_conjecture, (X1=esk4_0|r2_yellow_0(esk1_0,esk2_0)|~r1_orders_2(esk1_0,esk4_0,X1)|~r1_orders_2(esk1_0,X1,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_5, c_0_6]), c_0_7]), c_0_8])]), ['final']).
% 0.20/0.37  cnf(c_0_12, negated_conjecture, (~r1_orders_2(esk1_0,esk3_1(X1),X1)|~m1_subset_1(X1,u1_struct_0(esk1_0))|~r1_lattice3(esk1_0,esk2_0,X1)|~r2_yellow_0(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.20/0.37  cnf(c_0_13, negated_conjecture, (r1_lattice3(esk1_0,esk2_0,esk3_1(X1))|~m1_subset_1(X1,u1_struct_0(esk1_0))|~r1_lattice3(esk1_0,esk2_0,X1)|~r2_yellow_0(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.20/0.37  cnf(c_0_14, negated_conjecture, (m1_subset_1(esk3_1(X1),u1_struct_0(esk1_0))|~m1_subset_1(X1,u1_struct_0(esk1_0))|~r1_lattice3(esk1_0,esk2_0,X1)|~r2_yellow_0(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.20/0.37  cnf(c_0_15, negated_conjecture, (r2_yellow_0(esk1_0,esk2_0)|r1_orders_2(esk1_0,esk4_0,esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_10]), c_0_6]), ['final']).
% 0.20/0.37  # SZS output end Saturation
% 0.20/0.37  # Proof object total steps             : 16
% 0.20/0.37  # Proof object clause steps            : 11
% 0.20/0.37  # Proof object formula steps           : 5
% 0.20/0.37  # Proof object conjectures             : 13
% 0.20/0.37  # Proof object clause conjectures      : 10
% 0.20/0.37  # Proof object formula conjectures     : 3
% 0.20/0.37  # Proof object initial clauses used    : 9
% 0.20/0.37  # Proof object initial formulas used   : 2
% 0.20/0.37  # Proof object generating inferences   : 2
% 0.20/0.37  # Proof object simplifying inferences  : 4
% 0.20/0.37  # Parsed axioms                        : 2
% 0.20/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.37  # Initial clauses                      : 9
% 0.20/0.37  # Removed in clause preprocessing      : 0
% 0.20/0.37  # Initial clauses in saturation        : 9
% 0.20/0.37  # Processed clauses                    : 11
% 0.20/0.37  # ...of these trivial                  : 0
% 0.20/0.37  # ...subsumed                          : 0
% 0.20/0.37  # ...remaining for further processing  : 11
% 0.20/0.37  # Other redundant clauses eliminated   : 0
% 0.20/0.37  # Clauses deleted for lack of memory   : 0
% 0.20/0.37  # Backward-subsumed                    : 0
% 0.20/0.37  # Backward-rewritten                   : 0
% 0.20/0.37  # Generated clauses                    : 2
% 0.20/0.37  # ...of the previous two non-trivial   : 2
% 0.20/0.37  # Contextual simplify-reflections      : 1
% 0.20/0.37  # Paramodulations                      : 2
% 0.20/0.37  # Factorizations                       : 0
% 0.20/0.37  # Equation resolutions                 : 0
% 0.20/0.37  # Propositional unsat checks           : 0
% 0.20/0.37  #    Propositional check models        : 0
% 0.20/0.37  #    Propositional check unsatisfiable : 0
% 0.20/0.37  #    Propositional clauses             : 0
% 0.20/0.37  #    Propositional clauses after purity: 0
% 0.20/0.37  #    Propositional unsat core size     : 0
% 0.20/0.37  #    Propositional preprocessing time  : 0.000
% 0.20/0.37  #    Propositional encoding time       : 0.000
% 0.20/0.37  #    Propositional solver time         : 0.000
% 0.20/0.37  #    Success case prop preproc time    : 0.000
% 0.20/0.37  #    Success case prop encoding time   : 0.000
% 0.20/0.37  #    Success case prop solver time     : 0.000
% 0.20/0.37  # Current number of processed clauses  : 11
% 0.20/0.37  #    Positive orientable unit clauses  : 2
% 0.20/0.37  #    Positive unorientable unit clauses: 0
% 0.20/0.37  #    Negative unit clauses             : 0
% 0.20/0.37  #    Non-unit-clauses                  : 9
% 0.20/0.37  # Current number of unprocessed clauses: 0
% 0.20/0.37  # ...number of literals in the above   : 0
% 0.20/0.37  # Current number of archived formulas  : 0
% 0.20/0.37  # Current number of archived clauses   : 0
% 0.20/0.37  # Clause-clause subsumption calls (NU) : 6
% 0.20/0.37  # Rec. Clause-clause subsumption calls : 1
% 0.20/0.37  # Non-unit clause-clause subsumptions  : 1
% 0.20/0.37  # Unit Clause-clause subsumption calls : 0
% 0.20/0.37  # Rewrite failures with RHS unbound    : 0
% 0.20/0.37  # BW rewrite match attempts            : 0
% 0.20/0.37  # BW rewrite match successes           : 0
% 0.20/0.37  # Condensation attempts                : 0
% 0.20/0.37  # Condensation successes               : 0
% 0.20/0.37  # Termbank termtop insertions          : 959
% 0.20/0.37  
% 0.20/0.37  # -------------------------------------------------
% 0.20/0.37  # User time                : 0.024 s
% 0.20/0.37  # System time              : 0.006 s
% 0.20/0.37  # Total time               : 0.030 s
% 0.20/0.37  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------

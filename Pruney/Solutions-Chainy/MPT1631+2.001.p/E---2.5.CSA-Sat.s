%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:08 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   17 (  44 expanded)
%              Number of clauses        :   12 (  12 expanded)
%              Number of leaves         :    2 (  11 expanded)
%              Depth                    :    4
%              Number of atoms          :   73 ( 460 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   23 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t11_waybel_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => ( v10_waybel_0(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X2))
               => ? [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X2))
                    & ! [X5] :
                        ( m1_subset_1(X5,u1_struct_0(X2))
                       => ( r1_orders_2(X2,X4,X5)
                         => r1_orders_2(X1,k2_waybel_0(X1,X2,X3),k2_waybel_0(X1,X2,X5)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_waybel_0)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(c_0_2,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & l1_waybel_0(X2,X1) )
           => ( v10_waybel_0(X2,X1)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X2))
                 => ? [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X2))
                      & ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X2))
                         => ( r1_orders_2(X2,X4,X5)
                           => r1_orders_2(X1,k2_waybel_0(X1,X2,X3),k2_waybel_0(X1,X2,X5)) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t11_waybel_0])).

fof(c_0_3,plain,(
    ! [X6] :
      ( ~ l1_orders_2(X6)
      | l1_struct_0(X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

fof(c_0_4,negated_conjecture,(
    ! [X10,X12,X14] :
      ( ~ v2_struct_0(esk1_0)
      & l1_orders_2(esk1_0)
      & ~ v2_struct_0(esk2_0)
      & l1_waybel_0(esk2_0,esk1_0)
      & ( m1_subset_1(esk3_0,u1_struct_0(esk2_0))
        | ~ v10_waybel_0(esk2_0,esk1_0) )
      & ( m1_subset_1(esk4_1(X10),u1_struct_0(esk2_0))
        | ~ m1_subset_1(X10,u1_struct_0(esk2_0))
        | ~ v10_waybel_0(esk2_0,esk1_0) )
      & ( r1_orders_2(esk2_0,X10,esk4_1(X10))
        | ~ m1_subset_1(X10,u1_struct_0(esk2_0))
        | ~ v10_waybel_0(esk2_0,esk1_0) )
      & ( ~ r1_orders_2(esk1_0,k2_waybel_0(esk1_0,esk2_0,esk3_0),k2_waybel_0(esk1_0,esk2_0,esk4_1(X10)))
        | ~ m1_subset_1(X10,u1_struct_0(esk2_0))
        | ~ v10_waybel_0(esk2_0,esk1_0) )
      & ( m1_subset_1(esk5_1(X12),u1_struct_0(esk2_0))
        | ~ m1_subset_1(X12,u1_struct_0(esk2_0))
        | v10_waybel_0(esk2_0,esk1_0) )
      & ( ~ m1_subset_1(X14,u1_struct_0(esk2_0))
        | ~ r1_orders_2(esk2_0,esk5_1(X12),X14)
        | r1_orders_2(esk1_0,k2_waybel_0(esk1_0,esk2_0,X12),k2_waybel_0(esk1_0,esk2_0,X14))
        | ~ m1_subset_1(X12,u1_struct_0(esk2_0))
        | v10_waybel_0(esk2_0,esk1_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_2])])])])])])).

cnf(c_0_5,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_3]),
    [final]).

cnf(c_0_6,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_7,negated_conjecture,
    ( r1_orders_2(esk1_0,k2_waybel_0(esk1_0,esk2_0,X2),k2_waybel_0(esk1_0,esk2_0,X1))
    | v10_waybel_0(esk2_0,esk1_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r1_orders_2(esk2_0,esk5_1(X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_8,negated_conjecture,
    ( ~ r1_orders_2(esk1_0,k2_waybel_0(esk1_0,esk2_0,esk3_0),k2_waybel_0(esk1_0,esk2_0,esk4_1(X1)))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ v10_waybel_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_9,negated_conjecture,
    ( m1_subset_1(esk5_1(X1),u1_struct_0(esk2_0))
    | v10_waybel_0(esk2_0,esk1_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_10,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk4_1(X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ v10_waybel_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_11,negated_conjecture,
    ( m1_subset_1(esk4_1(X1),u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ v10_waybel_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_12,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0))
    | ~ v10_waybel_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_13,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_14,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_15,negated_conjecture,
    ( l1_struct_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_5,c_0_6]),
    [final]).

cnf(c_0_16,negated_conjecture,
    ( l1_waybel_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:26:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  # Version: 2.5pre002
% 0.20/0.35  # No SInE strategy applied
% 0.20/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S079A
% 0.20/0.39  # and selection function SelectGrCQArEqFirst.
% 0.20/0.39  #
% 0.20/0.39  # Preprocessing time       : 0.039 s
% 0.20/0.39  # Presaturation interreduction done
% 0.20/0.39  
% 0.20/0.39  # No proof found!
% 0.20/0.39  # SZS status CounterSatisfiable
% 0.20/0.39  # SZS output start Saturation
% 0.20/0.39  fof(t11_waybel_0, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_orders_2(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>(v10_waybel_0(X2,X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>?[X4]:(m1_subset_1(X4,u1_struct_0(X2))&![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>(r1_orders_2(X2,X4,X5)=>r1_orders_2(X1,k2_waybel_0(X1,X2,X3),k2_waybel_0(X1,X2,X5))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_waybel_0)).
% 0.20/0.39  fof(dt_l1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 0.20/0.39  fof(c_0_2, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_orders_2(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>(v10_waybel_0(X2,X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>?[X4]:(m1_subset_1(X4,u1_struct_0(X2))&![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>(r1_orders_2(X2,X4,X5)=>r1_orders_2(X1,k2_waybel_0(X1,X2,X3),k2_waybel_0(X1,X2,X5)))))))))), inference(assume_negation,[status(cth)],[t11_waybel_0])).
% 0.20/0.39  fof(c_0_3, plain, ![X6]:(~l1_orders_2(X6)|l1_struct_0(X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).
% 0.20/0.39  fof(c_0_4, negated_conjecture, ![X10, X12, X14]:((~v2_struct_0(esk1_0)&l1_orders_2(esk1_0))&((~v2_struct_0(esk2_0)&l1_waybel_0(esk2_0,esk1_0))&(((m1_subset_1(esk3_0,u1_struct_0(esk2_0))|~v10_waybel_0(esk2_0,esk1_0))&((m1_subset_1(esk4_1(X10),u1_struct_0(esk2_0))|~m1_subset_1(X10,u1_struct_0(esk2_0))|~v10_waybel_0(esk2_0,esk1_0))&((r1_orders_2(esk2_0,X10,esk4_1(X10))|~m1_subset_1(X10,u1_struct_0(esk2_0))|~v10_waybel_0(esk2_0,esk1_0))&(~r1_orders_2(esk1_0,k2_waybel_0(esk1_0,esk2_0,esk3_0),k2_waybel_0(esk1_0,esk2_0,esk4_1(X10)))|~m1_subset_1(X10,u1_struct_0(esk2_0))|~v10_waybel_0(esk2_0,esk1_0)))))&((m1_subset_1(esk5_1(X12),u1_struct_0(esk2_0))|~m1_subset_1(X12,u1_struct_0(esk2_0))|v10_waybel_0(esk2_0,esk1_0))&(~m1_subset_1(X14,u1_struct_0(esk2_0))|(~r1_orders_2(esk2_0,esk5_1(X12),X14)|r1_orders_2(esk1_0,k2_waybel_0(esk1_0,esk2_0,X12),k2_waybel_0(esk1_0,esk2_0,X14)))|~m1_subset_1(X12,u1_struct_0(esk2_0))|v10_waybel_0(esk2_0,esk1_0)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_2])])])])])])).
% 0.20/0.39  cnf(c_0_5, plain, (l1_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_3]), ['final']).
% 0.20/0.39  cnf(c_0_6, negated_conjecture, (l1_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.20/0.39  cnf(c_0_7, negated_conjecture, (r1_orders_2(esk1_0,k2_waybel_0(esk1_0,esk2_0,X2),k2_waybel_0(esk1_0,esk2_0,X1))|v10_waybel_0(esk2_0,esk1_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~r1_orders_2(esk2_0,esk5_1(X2),X1)|~m1_subset_1(X2,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.20/0.39  cnf(c_0_8, negated_conjecture, (~r1_orders_2(esk1_0,k2_waybel_0(esk1_0,esk2_0,esk3_0),k2_waybel_0(esk1_0,esk2_0,esk4_1(X1)))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~v10_waybel_0(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.20/0.39  cnf(c_0_9, negated_conjecture, (m1_subset_1(esk5_1(X1),u1_struct_0(esk2_0))|v10_waybel_0(esk2_0,esk1_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.20/0.39  cnf(c_0_10, negated_conjecture, (r1_orders_2(esk2_0,X1,esk4_1(X1))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~v10_waybel_0(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.20/0.39  cnf(c_0_11, negated_conjecture, (m1_subset_1(esk4_1(X1),u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~v10_waybel_0(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.20/0.39  cnf(c_0_12, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(esk2_0))|~v10_waybel_0(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.20/0.39  cnf(c_0_13, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.20/0.39  cnf(c_0_14, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.20/0.39  cnf(c_0_15, negated_conjecture, (l1_struct_0(esk1_0)), inference(spm,[status(thm)],[c_0_5, c_0_6]), ['final']).
% 0.20/0.39  cnf(c_0_16, negated_conjecture, (l1_waybel_0(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.20/0.39  # SZS output end Saturation
% 0.20/0.39  # Proof object total steps             : 17
% 0.20/0.39  # Proof object clause steps            : 12
% 0.20/0.39  # Proof object formula steps           : 5
% 0.20/0.39  # Proof object conjectures             : 14
% 0.20/0.39  # Proof object clause conjectures      : 11
% 0.20/0.39  # Proof object formula conjectures     : 3
% 0.20/0.39  # Proof object initial clauses used    : 11
% 0.20/0.39  # Proof object initial formulas used   : 2
% 0.20/0.39  # Proof object generating inferences   : 1
% 0.20/0.39  # Proof object simplifying inferences  : 0
% 0.20/0.39  # Parsed axioms                        : 2
% 0.20/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.39  # Initial clauses                      : 11
% 0.20/0.39  # Removed in clause preprocessing      : 0
% 0.20/0.39  # Initial clauses in saturation        : 11
% 0.20/0.39  # Processed clauses                    : 23
% 0.20/0.39  # ...of these trivial                  : 0
% 0.20/0.39  # ...subsumed                          : 0
% 0.20/0.39  # ...remaining for further processing  : 23
% 0.20/0.39  # Other redundant clauses eliminated   : 0
% 0.20/0.39  # Clauses deleted for lack of memory   : 0
% 0.20/0.39  # Backward-subsumed                    : 0
% 0.20/0.39  # Backward-rewritten                   : 0
% 0.20/0.39  # Generated clauses                    : 1
% 0.20/0.39  # ...of the previous two non-trivial   : 1
% 0.20/0.39  # Contextual simplify-reflections      : 0
% 0.20/0.39  # Paramodulations                      : 1
% 0.20/0.39  # Factorizations                       : 0
% 0.20/0.39  # Equation resolutions                 : 0
% 0.20/0.39  # Propositional unsat checks           : 0
% 0.20/0.39  #    Propositional check models        : 0
% 0.20/0.39  #    Propositional check unsatisfiable : 0
% 0.20/0.39  #    Propositional clauses             : 0
% 0.20/0.39  #    Propositional clauses after purity: 0
% 0.20/0.39  #    Propositional unsat core size     : 0
% 0.20/0.39  #    Propositional preprocessing time  : 0.000
% 0.20/0.39  #    Propositional encoding time       : 0.000
% 0.20/0.39  #    Propositional solver time         : 0.000
% 0.20/0.39  #    Success case prop preproc time    : 0.000
% 0.20/0.39  #    Success case prop encoding time   : 0.000
% 0.20/0.39  #    Success case prop solver time     : 0.000
% 0.20/0.39  # Current number of processed clauses  : 12
% 0.20/0.39  #    Positive orientable unit clauses  : 3
% 0.20/0.39  #    Positive unorientable unit clauses: 0
% 0.20/0.39  #    Negative unit clauses             : 2
% 0.20/0.39  #    Non-unit-clauses                  : 7
% 0.20/0.39  # Current number of unprocessed clauses: 0
% 0.20/0.39  # ...number of literals in the above   : 0
% 0.20/0.39  # Current number of archived formulas  : 0
% 0.20/0.39  # Current number of archived clauses   : 11
% 0.20/0.39  # Clause-clause subsumption calls (NU) : 38
% 0.20/0.39  # Rec. Clause-clause subsumption calls : 24
% 0.20/0.39  # Non-unit clause-clause subsumptions  : 0
% 0.20/0.39  # Unit Clause-clause subsumption calls : 0
% 0.20/0.39  # Rewrite failures with RHS unbound    : 0
% 0.20/0.39  # BW rewrite match attempts            : 0
% 0.20/0.39  # BW rewrite match successes           : 0
% 0.20/0.39  # Condensation attempts                : 0
% 0.20/0.39  # Condensation successes               : 0
% 0.20/0.39  # Termbank termtop insertions          : 1027
% 0.20/0.39  
% 0.20/0.39  # -------------------------------------------------
% 0.20/0.39  # User time                : 0.038 s
% 0.20/0.39  # System time              : 0.006 s
% 0.20/0.39  # Total time               : 0.044 s
% 0.20/0.39  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------

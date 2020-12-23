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
% DateTime   : Thu Dec  3 11:16:22 EST 2020

% Result     : CounterSatisfiable 0.13s
% Output     : Saturation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   17 (  51 expanded)
%              Number of clauses        :   12 (  15 expanded)
%              Number of leaves         :    2 (  13 expanded)
%              Depth                    :    4
%              Number of atoms          :   80 ( 339 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   17 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t37_waybel_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( r2_yellow_0(X1,X2)
          <=> r2_yellow_0(X1,k4_waybel_0(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_waybel_0)).

fof(t48_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2,X3] :
          ( ( ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r1_lattice3(X1,X2,X4)
                <=> r1_lattice3(X1,X3,X4) ) )
            & r2_yellow_0(X1,X2) )
         => r2_yellow_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_yellow_0)).

fof(c_0_2,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( r2_yellow_0(X1,X2)
            <=> r2_yellow_0(X1,k4_waybel_0(X1,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t37_waybel_0])).

fof(c_0_3,plain,(
    ! [X5,X6,X7] :
      ( ( m1_subset_1(esk1_3(X5,X6,X7),u1_struct_0(X5))
        | ~ r2_yellow_0(X5,X6)
        | r2_yellow_0(X5,X7)
        | v2_struct_0(X5)
        | ~ l1_orders_2(X5) )
      & ( ~ r1_lattice3(X5,X6,esk1_3(X5,X6,X7))
        | ~ r1_lattice3(X5,X7,esk1_3(X5,X6,X7))
        | ~ r2_yellow_0(X5,X6)
        | r2_yellow_0(X5,X7)
        | v2_struct_0(X5)
        | ~ l1_orders_2(X5) )
      & ( r1_lattice3(X5,X6,esk1_3(X5,X6,X7))
        | r1_lattice3(X5,X7,esk1_3(X5,X6,X7))
        | ~ r2_yellow_0(X5,X6)
        | r2_yellow_0(X5,X7)
        | v2_struct_0(X5)
        | ~ l1_orders_2(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t48_yellow_0])])])])])])).

fof(c_0_4,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v3_orders_2(esk2_0)
    & v4_orders_2(esk2_0)
    & l1_orders_2(esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & ( ~ r2_yellow_0(esk2_0,esk3_0)
      | ~ r2_yellow_0(esk2_0,k4_waybel_0(esk2_0,esk3_0)) )
    & ( r2_yellow_0(esk2_0,esk3_0)
      | r2_yellow_0(esk2_0,k4_waybel_0(esk2_0,esk3_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_2])])])])).

cnf(c_0_5,plain,
    ( r1_lattice3(X1,X2,esk1_3(X1,X2,X3))
    | r1_lattice3(X1,X3,esk1_3(X1,X2,X3))
    | r2_yellow_0(X1,X3)
    | v2_struct_0(X1)
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_3]),
    [final]).

cnf(c_0_6,negated_conjecture,
    ( r2_yellow_0(esk2_0,esk3_0)
    | r2_yellow_0(esk2_0,k4_waybel_0(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_7,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_8,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_9,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))
    | r2_yellow_0(X1,X3)
    | v2_struct_0(X1)
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_3]),
    [final]).

cnf(c_0_10,negated_conjecture,
    ( r2_yellow_0(esk2_0,esk3_0)
    | r2_yellow_0(esk2_0,X1)
    | r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),X1))
    | r1_lattice3(esk2_0,X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_5,c_0_6]),c_0_7])]),c_0_8]),
    [final]).

cnf(c_0_11,negated_conjecture,
    ( r2_yellow_0(esk2_0,esk3_0)
    | r2_yellow_0(esk2_0,X1)
    | m1_subset_1(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),X1),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_6]),c_0_7])]),c_0_8]),
    [final]).

cnf(c_0_12,plain,
    ( r2_yellow_0(X1,X3)
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,esk1_3(X1,X2,X3))
    | ~ r1_lattice3(X1,X3,esk1_3(X1,X2,X3))
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_3]),
    [final]).

cnf(c_0_13,negated_conjecture,
    ( ~ r2_yellow_0(esk2_0,esk3_0)
    | ~ r2_yellow_0(esk2_0,k4_waybel_0(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_15,negated_conjecture,
    ( v4_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_16,negated_conjecture,
    ( v3_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:11:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.026 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # No proof found!
% 0.13/0.38  # SZS status CounterSatisfiable
% 0.13/0.38  # SZS output start Saturation
% 0.13/0.38  fof(t37_waybel_0, conjecture, ![X1]:((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_yellow_0(X1,X2)<=>r2_yellow_0(X1,k4_waybel_0(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_waybel_0)).
% 0.13/0.38  fof(t48_yellow_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_orders_2(X1))=>![X2, X3]:((![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r1_lattice3(X1,X2,X4)<=>r1_lattice3(X1,X3,X4)))&r2_yellow_0(X1,X2))=>r2_yellow_0(X1,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_yellow_0)).
% 0.13/0.38  fof(c_0_2, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_yellow_0(X1,X2)<=>r2_yellow_0(X1,k4_waybel_0(X1,X2)))))), inference(assume_negation,[status(cth)],[t37_waybel_0])).
% 0.13/0.38  fof(c_0_3, plain, ![X5, X6, X7]:((m1_subset_1(esk1_3(X5,X6,X7),u1_struct_0(X5))|~r2_yellow_0(X5,X6)|r2_yellow_0(X5,X7)|(v2_struct_0(X5)|~l1_orders_2(X5)))&((~r1_lattice3(X5,X6,esk1_3(X5,X6,X7))|~r1_lattice3(X5,X7,esk1_3(X5,X6,X7))|~r2_yellow_0(X5,X6)|r2_yellow_0(X5,X7)|(v2_struct_0(X5)|~l1_orders_2(X5)))&(r1_lattice3(X5,X6,esk1_3(X5,X6,X7))|r1_lattice3(X5,X7,esk1_3(X5,X6,X7))|~r2_yellow_0(X5,X6)|r2_yellow_0(X5,X7)|(v2_struct_0(X5)|~l1_orders_2(X5))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t48_yellow_0])])])])])])).
% 0.13/0.38  fof(c_0_4, negated_conjecture, ((((~v2_struct_0(esk2_0)&v3_orders_2(esk2_0))&v4_orders_2(esk2_0))&l1_orders_2(esk2_0))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&((~r2_yellow_0(esk2_0,esk3_0)|~r2_yellow_0(esk2_0,k4_waybel_0(esk2_0,esk3_0)))&(r2_yellow_0(esk2_0,esk3_0)|r2_yellow_0(esk2_0,k4_waybel_0(esk2_0,esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_2])])])])).
% 0.13/0.38  cnf(c_0_5, plain, (r1_lattice3(X1,X2,esk1_3(X1,X2,X3))|r1_lattice3(X1,X3,esk1_3(X1,X2,X3))|r2_yellow_0(X1,X3)|v2_struct_0(X1)|~r2_yellow_0(X1,X2)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_3]), ['final']).
% 0.13/0.38  cnf(c_0_6, negated_conjecture, (r2_yellow_0(esk2_0,esk3_0)|r2_yellow_0(esk2_0,k4_waybel_0(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.13/0.38  cnf(c_0_7, negated_conjecture, (l1_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.13/0.38  cnf(c_0_8, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.13/0.38  cnf(c_0_9, plain, (m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))|r2_yellow_0(X1,X3)|v2_struct_0(X1)|~r2_yellow_0(X1,X2)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_3]), ['final']).
% 0.13/0.38  cnf(c_0_10, negated_conjecture, (r2_yellow_0(esk2_0,esk3_0)|r2_yellow_0(esk2_0,X1)|r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),X1))|r1_lattice3(esk2_0,X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_5, c_0_6]), c_0_7])]), c_0_8]), ['final']).
% 0.13/0.38  cnf(c_0_11, negated_conjecture, (r2_yellow_0(esk2_0,esk3_0)|r2_yellow_0(esk2_0,X1)|m1_subset_1(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),X1),u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_6]), c_0_7])]), c_0_8]), ['final']).
% 0.13/0.38  cnf(c_0_12, plain, (r2_yellow_0(X1,X3)|v2_struct_0(X1)|~r1_lattice3(X1,X2,esk1_3(X1,X2,X3))|~r1_lattice3(X1,X3,esk1_3(X1,X2,X3))|~r2_yellow_0(X1,X2)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_3]), ['final']).
% 0.13/0.38  cnf(c_0_13, negated_conjecture, (~r2_yellow_0(esk2_0,esk3_0)|~r2_yellow_0(esk2_0,k4_waybel_0(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.13/0.38  cnf(c_0_14, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.13/0.38  cnf(c_0_15, negated_conjecture, (v4_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.13/0.38  cnf(c_0_16, negated_conjecture, (v3_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.13/0.38  # SZS output end Saturation
% 0.13/0.38  # Proof object total steps             : 17
% 0.13/0.38  # Proof object clause steps            : 12
% 0.13/0.38  # Proof object formula steps           : 5
% 0.13/0.38  # Proof object conjectures             : 12
% 0.13/0.38  # Proof object clause conjectures      : 9
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 10
% 0.13/0.38  # Proof object initial formulas used   : 2
% 0.13/0.38  # Proof object generating inferences   : 2
% 0.13/0.38  # Proof object simplifying inferences  : 6
% 0.13/0.38  # Parsed axioms                        : 2
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 10
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 10
% 0.13/0.38  # Processed clauses                    : 24
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 2
% 0.13/0.38  # ...remaining for further processing  : 22
% 0.13/0.38  # Other redundant clauses eliminated   : 0
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 0
% 0.13/0.38  # Generated clauses                    : 6
% 0.13/0.38  # ...of the previous two non-trivial   : 4
% 0.13/0.38  # Contextual simplify-reflections      : 0
% 0.13/0.38  # Paramodulations                      : 4
% 0.13/0.38  # Factorizations                       : 2
% 0.13/0.38  # Equation resolutions                 : 0
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 12
% 0.13/0.38  #    Positive orientable unit clauses  : 4
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 1
% 0.13/0.38  #    Non-unit-clauses                  : 7
% 0.13/0.38  # Current number of unprocessed clauses: 0
% 0.13/0.38  # ...number of literals in the above   : 0
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 10
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 6
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 2
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 2
% 0.13/0.38  # Unit Clause-clause subsumption calls : 0
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 0
% 0.13/0.38  # BW rewrite match successes           : 0
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 934
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.027 s
% 0.13/0.38  # System time              : 0.003 s
% 0.13/0.38  # Total time               : 0.030 s
% 0.13/0.38  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------

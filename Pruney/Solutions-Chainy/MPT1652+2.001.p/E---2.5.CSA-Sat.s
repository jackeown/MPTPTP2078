%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:18 EST 2020

% Result     : CounterSatisfiable 0.12s
% Output     : Saturation 0.12s
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
fof(t32_waybel_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( r1_yellow_0(X1,X2)
          <=> r1_yellow_0(X1,k3_waybel_0(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_waybel_0)).

fof(t46_yellow_0,axiom,(
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

fof(c_0_2,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( r1_yellow_0(X1,X2)
            <=> r1_yellow_0(X1,k3_waybel_0(X1,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t32_waybel_0])).

fof(c_0_3,plain,(
    ! [X5,X6,X7] :
      ( ( m1_subset_1(esk1_3(X5,X6,X7),u1_struct_0(X5))
        | ~ r1_yellow_0(X5,X6)
        | r1_yellow_0(X5,X7)
        | v2_struct_0(X5)
        | ~ l1_orders_2(X5) )
      & ( ~ r2_lattice3(X5,X6,esk1_3(X5,X6,X7))
        | ~ r2_lattice3(X5,X7,esk1_3(X5,X6,X7))
        | ~ r1_yellow_0(X5,X6)
        | r1_yellow_0(X5,X7)
        | v2_struct_0(X5)
        | ~ l1_orders_2(X5) )
      & ( r2_lattice3(X5,X6,esk1_3(X5,X6,X7))
        | r2_lattice3(X5,X7,esk1_3(X5,X6,X7))
        | ~ r1_yellow_0(X5,X6)
        | r1_yellow_0(X5,X7)
        | v2_struct_0(X5)
        | ~ l1_orders_2(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t46_yellow_0])])])])])])).

fof(c_0_4,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v3_orders_2(esk2_0)
    & v4_orders_2(esk2_0)
    & l1_orders_2(esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & ( ~ r1_yellow_0(esk2_0,esk3_0)
      | ~ r1_yellow_0(esk2_0,k3_waybel_0(esk2_0,esk3_0)) )
    & ( r1_yellow_0(esk2_0,esk3_0)
      | r1_yellow_0(esk2_0,k3_waybel_0(esk2_0,esk3_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_2])])])])).

cnf(c_0_5,plain,
    ( r2_lattice3(X1,X2,esk1_3(X1,X2,X3))
    | r2_lattice3(X1,X3,esk1_3(X1,X2,X3))
    | r1_yellow_0(X1,X3)
    | v2_struct_0(X1)
    | ~ r1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_3]),
    [final]).

cnf(c_0_6,negated_conjecture,
    ( r1_yellow_0(esk2_0,esk3_0)
    | r1_yellow_0(esk2_0,k3_waybel_0(esk2_0,esk3_0)) ),
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
    | r1_yellow_0(X1,X3)
    | v2_struct_0(X1)
    | ~ r1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_3]),
    [final]).

cnf(c_0_10,negated_conjecture,
    ( r1_yellow_0(esk2_0,esk3_0)
    | r1_yellow_0(esk2_0,X1)
    | r2_lattice3(esk2_0,k3_waybel_0(esk2_0,esk3_0),esk1_3(esk2_0,k3_waybel_0(esk2_0,esk3_0),X1))
    | r2_lattice3(esk2_0,X1,esk1_3(esk2_0,k3_waybel_0(esk2_0,esk3_0),X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_5,c_0_6]),c_0_7])]),c_0_8]),
    [final]).

cnf(c_0_11,negated_conjecture,
    ( r1_yellow_0(esk2_0,esk3_0)
    | r1_yellow_0(esk2_0,X1)
    | m1_subset_1(esk1_3(esk2_0,k3_waybel_0(esk2_0,esk3_0),X1),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_6]),c_0_7])]),c_0_8]),
    [final]).

cnf(c_0_12,plain,
    ( r1_yellow_0(X1,X3)
    | v2_struct_0(X1)
    | ~ r2_lattice3(X1,X2,esk1_3(X1,X2,X3))
    | ~ r2_lattice3(X1,X3,esk1_3(X1,X2,X3))
    | ~ r1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_3]),
    [final]).

cnf(c_0_13,negated_conjecture,
    ( ~ r1_yellow_0(esk2_0,esk3_0)
    | ~ r1_yellow_0(esk2_0,k3_waybel_0(esk2_0,esk3_0)) ),
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
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:46:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.12/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.027 s
% 0.12/0.37  # Presaturation interreduction done
% 0.12/0.37  
% 0.12/0.37  # No proof found!
% 0.12/0.37  # SZS status CounterSatisfiable
% 0.12/0.37  # SZS output start Saturation
% 0.12/0.37  fof(t32_waybel_0, conjecture, ![X1]:((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_yellow_0(X1,X2)<=>r1_yellow_0(X1,k3_waybel_0(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_waybel_0)).
% 0.12/0.37  fof(t46_yellow_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_orders_2(X1))=>![X2, X3]:((![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X4)<=>r2_lattice3(X1,X3,X4)))&r1_yellow_0(X1,X2))=>r1_yellow_0(X1,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_yellow_0)).
% 0.12/0.37  fof(c_0_2, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_yellow_0(X1,X2)<=>r1_yellow_0(X1,k3_waybel_0(X1,X2)))))), inference(assume_negation,[status(cth)],[t32_waybel_0])).
% 0.12/0.37  fof(c_0_3, plain, ![X5, X6, X7]:((m1_subset_1(esk1_3(X5,X6,X7),u1_struct_0(X5))|~r1_yellow_0(X5,X6)|r1_yellow_0(X5,X7)|(v2_struct_0(X5)|~l1_orders_2(X5)))&((~r2_lattice3(X5,X6,esk1_3(X5,X6,X7))|~r2_lattice3(X5,X7,esk1_3(X5,X6,X7))|~r1_yellow_0(X5,X6)|r1_yellow_0(X5,X7)|(v2_struct_0(X5)|~l1_orders_2(X5)))&(r2_lattice3(X5,X6,esk1_3(X5,X6,X7))|r2_lattice3(X5,X7,esk1_3(X5,X6,X7))|~r1_yellow_0(X5,X6)|r1_yellow_0(X5,X7)|(v2_struct_0(X5)|~l1_orders_2(X5))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t46_yellow_0])])])])])])).
% 0.12/0.37  fof(c_0_4, negated_conjecture, ((((~v2_struct_0(esk2_0)&v3_orders_2(esk2_0))&v4_orders_2(esk2_0))&l1_orders_2(esk2_0))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&((~r1_yellow_0(esk2_0,esk3_0)|~r1_yellow_0(esk2_0,k3_waybel_0(esk2_0,esk3_0)))&(r1_yellow_0(esk2_0,esk3_0)|r1_yellow_0(esk2_0,k3_waybel_0(esk2_0,esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_2])])])])).
% 0.12/0.37  cnf(c_0_5, plain, (r2_lattice3(X1,X2,esk1_3(X1,X2,X3))|r2_lattice3(X1,X3,esk1_3(X1,X2,X3))|r1_yellow_0(X1,X3)|v2_struct_0(X1)|~r1_yellow_0(X1,X2)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_3]), ['final']).
% 0.12/0.37  cnf(c_0_6, negated_conjecture, (r1_yellow_0(esk2_0,esk3_0)|r1_yellow_0(esk2_0,k3_waybel_0(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.12/0.37  cnf(c_0_7, negated_conjecture, (l1_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.12/0.37  cnf(c_0_8, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.12/0.37  cnf(c_0_9, plain, (m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))|r1_yellow_0(X1,X3)|v2_struct_0(X1)|~r1_yellow_0(X1,X2)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_3]), ['final']).
% 0.12/0.37  cnf(c_0_10, negated_conjecture, (r1_yellow_0(esk2_0,esk3_0)|r1_yellow_0(esk2_0,X1)|r2_lattice3(esk2_0,k3_waybel_0(esk2_0,esk3_0),esk1_3(esk2_0,k3_waybel_0(esk2_0,esk3_0),X1))|r2_lattice3(esk2_0,X1,esk1_3(esk2_0,k3_waybel_0(esk2_0,esk3_0),X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_5, c_0_6]), c_0_7])]), c_0_8]), ['final']).
% 0.12/0.37  cnf(c_0_11, negated_conjecture, (r1_yellow_0(esk2_0,esk3_0)|r1_yellow_0(esk2_0,X1)|m1_subset_1(esk1_3(esk2_0,k3_waybel_0(esk2_0,esk3_0),X1),u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_6]), c_0_7])]), c_0_8]), ['final']).
% 0.12/0.37  cnf(c_0_12, plain, (r1_yellow_0(X1,X3)|v2_struct_0(X1)|~r2_lattice3(X1,X2,esk1_3(X1,X2,X3))|~r2_lattice3(X1,X3,esk1_3(X1,X2,X3))|~r1_yellow_0(X1,X2)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_3]), ['final']).
% 0.12/0.37  cnf(c_0_13, negated_conjecture, (~r1_yellow_0(esk2_0,esk3_0)|~r1_yellow_0(esk2_0,k3_waybel_0(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.12/0.37  cnf(c_0_14, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.12/0.37  cnf(c_0_15, negated_conjecture, (v4_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.12/0.37  cnf(c_0_16, negated_conjecture, (v3_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.12/0.37  # SZS output end Saturation
% 0.12/0.37  # Proof object total steps             : 17
% 0.12/0.37  # Proof object clause steps            : 12
% 0.12/0.37  # Proof object formula steps           : 5
% 0.12/0.37  # Proof object conjectures             : 12
% 0.12/0.37  # Proof object clause conjectures      : 9
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 10
% 0.12/0.37  # Proof object initial formulas used   : 2
% 0.12/0.37  # Proof object generating inferences   : 2
% 0.12/0.37  # Proof object simplifying inferences  : 6
% 0.12/0.37  # Parsed axioms                        : 2
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 10
% 0.12/0.37  # Removed in clause preprocessing      : 0
% 0.12/0.37  # Initial clauses in saturation        : 10
% 0.12/0.37  # Processed clauses                    : 24
% 0.12/0.37  # ...of these trivial                  : 0
% 0.12/0.37  # ...subsumed                          : 2
% 0.12/0.37  # ...remaining for further processing  : 22
% 0.12/0.37  # Other redundant clauses eliminated   : 0
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 0
% 0.12/0.37  # Backward-rewritten                   : 0
% 0.12/0.37  # Generated clauses                    : 6
% 0.12/0.37  # ...of the previous two non-trivial   : 4
% 0.12/0.37  # Contextual simplify-reflections      : 0
% 0.12/0.37  # Paramodulations                      : 4
% 0.12/0.37  # Factorizations                       : 2
% 0.12/0.37  # Equation resolutions                 : 0
% 0.12/0.37  # Propositional unsat checks           : 0
% 0.12/0.37  #    Propositional check models        : 0
% 0.12/0.37  #    Propositional check unsatisfiable : 0
% 0.12/0.37  #    Propositional clauses             : 0
% 0.12/0.37  #    Propositional clauses after purity: 0
% 0.12/0.37  #    Propositional unsat core size     : 0
% 0.12/0.37  #    Propositional preprocessing time  : 0.000
% 0.12/0.37  #    Propositional encoding time       : 0.000
% 0.12/0.37  #    Propositional solver time         : 0.000
% 0.12/0.37  #    Success case prop preproc time    : 0.000
% 0.12/0.37  #    Success case prop encoding time   : 0.000
% 0.12/0.37  #    Success case prop solver time     : 0.000
% 0.12/0.37  # Current number of processed clauses  : 12
% 0.12/0.37  #    Positive orientable unit clauses  : 4
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 1
% 0.12/0.37  #    Non-unit-clauses                  : 7
% 0.12/0.37  # Current number of unprocessed clauses: 0
% 0.12/0.37  # ...number of literals in the above   : 0
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 10
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 6
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 2
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 2
% 0.12/0.37  # Unit Clause-clause subsumption calls : 0
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 0
% 0.12/0.37  # BW rewrite match successes           : 0
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 934
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.029 s
% 0.12/0.37  # System time              : 0.003 s
% 0.12/0.37  # Total time               : 0.031 s
% 0.12/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:16 EST 2020

% Result     : CounterSatisfiable 0.12s
% Output     : Saturation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   17 (  60 expanded)
%              Number of clauses        :   14 (  18 expanded)
%              Number of leaves         :    1 (  14 expanded)
%              Depth                    :    4
%              Number of atoms          :   55 ( 501 expanded)
%              Number of equality atoms :    8 (  90 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t25_waybel_0,conjecture,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( l1_orders_2(X2)
         => ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X3 = X4
                     => ( ( v12_waybel_0(X3,X1)
                         => v12_waybel_0(X4,X2) )
                        & ( v13_waybel_0(X3,X1)
                         => v13_waybel_0(X4,X2) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_waybel_0)).

fof(c_0_1,negated_conjecture,(
    ~ ! [X1] :
        ( l1_orders_2(X1)
       => ! [X2] :
            ( l1_orders_2(X2)
           => ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                     => ( X3 = X4
                       => ( ( v12_waybel_0(X3,X1)
                           => v12_waybel_0(X4,X2) )
                          & ( v13_waybel_0(X3,X1)
                           => v13_waybel_0(X4,X2) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t25_waybel_0])).

fof(c_0_2,negated_conjecture,
    ( l1_orders_2(esk1_0)
    & l1_orders_2(esk2_0)
    & g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0)) = g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0))
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & esk3_0 = esk4_0
    & ( v13_waybel_0(esk3_0,esk1_0)
      | v12_waybel_0(esk3_0,esk1_0) )
    & ( ~ v13_waybel_0(esk4_0,esk2_0)
      | v12_waybel_0(esk3_0,esk1_0) )
    & ( v13_waybel_0(esk3_0,esk1_0)
      | ~ v12_waybel_0(esk4_0,esk2_0) )
    & ( ~ v13_waybel_0(esk4_0,esk2_0)
      | ~ v12_waybel_0(esk4_0,esk2_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_1])])])])).

cnf(c_0_3,negated_conjecture,
    ( v13_waybel_0(esk3_0,esk1_0)
    | ~ v12_waybel_0(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_2])).

cnf(c_0_4,negated_conjecture,
    ( esk3_0 = esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_2]),
    [final]).

cnf(c_0_5,negated_conjecture,
    ( v12_waybel_0(esk3_0,esk1_0)
    | ~ v13_waybel_0(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_2])).

cnf(c_0_6,negated_conjecture,
    ( ~ v13_waybel_0(esk4_0,esk2_0)
    | ~ v12_waybel_0(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_2])).

cnf(c_0_7,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_2])).

cnf(c_0_8,negated_conjecture,
    ( v13_waybel_0(esk3_0,esk1_0)
    | v12_waybel_0(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_2]),
    [final]).

cnf(c_0_9,negated_conjecture,
    ( v13_waybel_0(esk3_0,esk1_0)
    | ~ v12_waybel_0(esk3_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_3,c_0_4]),
    [final]).

cnf(c_0_10,negated_conjecture,
    ( v12_waybel_0(esk3_0,esk1_0)
    | ~ v13_waybel_0(esk3_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_5,c_0_4]),
    [final]).

cnf(c_0_11,negated_conjecture,
    ( ~ v13_waybel_0(esk3_0,esk2_0)
    | ~ v12_waybel_0(esk3_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_6,c_0_4]),c_0_4]),
    [final]).

cnf(c_0_12,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0)) = g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_2]),
    [final]).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(rw,[status(thm)],[c_0_7,c_0_4]),
    [final]).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_2]),
    [final]).

cnf(c_0_15,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_2]),
    [final]).

cnf(c_0_16,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_2]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:19:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.12/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S01BI
% 0.12/0.36  # and selection function PSelectMinOptimalNoXTypePred.
% 0.12/0.36  #
% 0.12/0.36  # Preprocessing time       : 0.029 s
% 0.12/0.36  # Presaturation interreduction done
% 0.12/0.36  
% 0.12/0.36  # No proof found!
% 0.12/0.36  # SZS status CounterSatisfiable
% 0.12/0.36  # SZS output start Saturation
% 0.12/0.36  fof(t25_waybel_0, conjecture, ![X1]:(l1_orders_2(X1)=>![X2]:(l1_orders_2(X2)=>(g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))=g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>(X3=X4=>((v12_waybel_0(X3,X1)=>v12_waybel_0(X4,X2))&(v13_waybel_0(X3,X1)=>v13_waybel_0(X4,X2))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_waybel_0)).
% 0.12/0.36  fof(c_0_1, negated_conjecture, ~(![X1]:(l1_orders_2(X1)=>![X2]:(l1_orders_2(X2)=>(g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))=g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>(X3=X4=>((v12_waybel_0(X3,X1)=>v12_waybel_0(X4,X2))&(v13_waybel_0(X3,X1)=>v13_waybel_0(X4,X2)))))))))), inference(assume_negation,[status(cth)],[t25_waybel_0])).
% 0.12/0.36  fof(c_0_2, negated_conjecture, (l1_orders_2(esk1_0)&(l1_orders_2(esk2_0)&(g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0))=g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&(esk3_0=esk4_0&(((v13_waybel_0(esk3_0,esk1_0)|v12_waybel_0(esk3_0,esk1_0))&(~v13_waybel_0(esk4_0,esk2_0)|v12_waybel_0(esk3_0,esk1_0)))&((v13_waybel_0(esk3_0,esk1_0)|~v12_waybel_0(esk4_0,esk2_0))&(~v13_waybel_0(esk4_0,esk2_0)|~v12_waybel_0(esk4_0,esk2_0)))))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_1])])])])).
% 0.12/0.36  cnf(c_0_3, negated_conjecture, (v13_waybel_0(esk3_0,esk1_0)|~v12_waybel_0(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_2])).
% 0.12/0.36  cnf(c_0_4, negated_conjecture, (esk3_0=esk4_0), inference(split_conjunct,[status(thm)],[c_0_2]), ['final']).
% 0.12/0.36  cnf(c_0_5, negated_conjecture, (v12_waybel_0(esk3_0,esk1_0)|~v13_waybel_0(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_2])).
% 0.12/0.36  cnf(c_0_6, negated_conjecture, (~v13_waybel_0(esk4_0,esk2_0)|~v12_waybel_0(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_2])).
% 0.12/0.36  cnf(c_0_7, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_2])).
% 0.12/0.36  cnf(c_0_8, negated_conjecture, (v13_waybel_0(esk3_0,esk1_0)|v12_waybel_0(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_2]), ['final']).
% 0.12/0.36  cnf(c_0_9, negated_conjecture, (v13_waybel_0(esk3_0,esk1_0)|~v12_waybel_0(esk3_0,esk2_0)), inference(rw,[status(thm)],[c_0_3, c_0_4]), ['final']).
% 0.12/0.36  cnf(c_0_10, negated_conjecture, (v12_waybel_0(esk3_0,esk1_0)|~v13_waybel_0(esk3_0,esk2_0)), inference(rw,[status(thm)],[c_0_5, c_0_4]), ['final']).
% 0.12/0.36  cnf(c_0_11, negated_conjecture, (~v13_waybel_0(esk3_0,esk2_0)|~v12_waybel_0(esk3_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_6, c_0_4]), c_0_4]), ['final']).
% 0.12/0.36  cnf(c_0_12, negated_conjecture, (g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0))=g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_2]), ['final']).
% 0.12/0.36  cnf(c_0_13, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(rw,[status(thm)],[c_0_7, c_0_4]), ['final']).
% 0.12/0.36  cnf(c_0_14, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_2]), ['final']).
% 0.12/0.36  cnf(c_0_15, negated_conjecture, (l1_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_2]), ['final']).
% 0.12/0.36  cnf(c_0_16, negated_conjecture, (l1_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_2]), ['final']).
% 0.12/0.36  # SZS output end Saturation
% 0.12/0.36  # Proof object total steps             : 17
% 0.12/0.36  # Proof object clause steps            : 14
% 0.12/0.36  # Proof object formula steps           : 3
% 0.12/0.36  # Proof object conjectures             : 17
% 0.12/0.37  # Proof object clause conjectures      : 14
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 10
% 0.12/0.37  # Proof object initial formulas used   : 1
% 0.12/0.37  # Proof object generating inferences   : 0
% 0.12/0.37  # Proof object simplifying inferences  : 5
% 0.12/0.37  # Parsed axioms                        : 1
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 10
% 0.12/0.37  # Removed in clause preprocessing      : 0
% 0.12/0.37  # Initial clauses in saturation        : 10
% 0.12/0.37  # Processed clauses                    : 20
% 0.12/0.37  # ...of these trivial                  : 0
% 0.12/0.37  # ...subsumed                          : 0
% 0.12/0.37  # ...remaining for further processing  : 20
% 0.12/0.37  # Other redundant clauses eliminated   : 0
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 0
% 0.12/0.37  # Backward-rewritten                   : 0
% 0.12/0.37  # Generated clauses                    : 0
% 0.12/0.37  # ...of the previous two non-trivial   : 0
% 0.12/0.37  # Contextual simplify-reflections      : 0
% 0.12/0.37  # Paramodulations                      : 0
% 0.12/0.37  # Factorizations                       : 0
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
% 0.12/0.37  # Current number of processed clauses  : 10
% 0.12/0.37  #    Positive orientable unit clauses  : 6
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 0
% 0.12/0.37  #    Non-unit-clauses                  : 4
% 0.12/0.37  # Current number of unprocessed clauses: 0
% 0.12/0.37  # ...number of literals in the above   : 0
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 10
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 0
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 0
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.12/0.37  # Unit Clause-clause subsumption calls : 0
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 2
% 0.12/0.37  # BW rewrite match successes           : 0
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 478
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.027 s
% 0.12/0.37  # System time              : 0.006 s
% 0.12/0.37  # Total time               : 0.033 s
% 0.12/0.37  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------

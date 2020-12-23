%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:19 EST 2020

% Result     : CounterSatisfiable 0.19s
% Output     : Saturation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   25 ( 279 expanded)
%              Number of clauses        :   18 ( 115 expanded)
%              Number of leaves         :    3 (  65 expanded)
%              Depth                    :    9
%              Number of atoms          :   60 ( 932 expanded)
%              Number of equality atoms :   34 ( 436 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(free_g1_orders_2,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
     => ! [X3,X4] :
          ( g1_orders_2(X1,X2) = g1_orders_2(X3,X4)
         => ( X1 = X3
            & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_orders_2)).

fof(dt_u1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(t26_yellow_0,conjecture,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( l1_orders_2(X2)
         => ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
           => ! [X3] :
                ( r1_yellow_0(X1,X3)
               => k1_yellow_0(X1,X3) = k1_yellow_0(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_yellow_0)).

fof(c_0_3,plain,(
    ! [X6,X7,X8,X9] :
      ( ( X6 = X8
        | g1_orders_2(X6,X7) != g1_orders_2(X8,X9)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,X6))) )
      & ( X7 = X9
        | g1_orders_2(X6,X7) != g1_orders_2(X8,X9)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,X6))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_orders_2])])])])).

fof(c_0_4,plain,(
    ! [X5] :
      ( ~ l1_orders_2(X5)
      | m1_subset_1(u1_orders_2(X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X5)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( l1_orders_2(X1)
       => ! [X2] :
            ( l1_orders_2(X2)
           => ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
             => ! [X3] :
                  ( r1_yellow_0(X1,X3)
                 => k1_yellow_0(X1,X3) = k1_yellow_0(X2,X3) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t26_yellow_0])).

cnf(c_0_6,plain,
    ( X1 = X2
    | g1_orders_2(X3,X1) != g1_orders_2(X4,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_3]),
    [final]).

cnf(c_0_7,plain,
    ( m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

fof(c_0_8,negated_conjecture,
    ( l1_orders_2(esk1_0)
    & l1_orders_2(esk2_0)
    & g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0)) = g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0))
    & r1_yellow_0(esk1_0,esk3_0)
    & k1_yellow_0(esk1_0,esk3_0) != k1_yellow_0(esk2_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

cnf(c_0_9,plain,
    ( u1_orders_2(X1) = X2
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(X3,X2)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_6,c_0_7]),
    [final]).

cnf(c_0_10,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0)) = g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_12,negated_conjecture,
    ( u1_orders_2(esk2_0) = X1
    | g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0)) != g1_orders_2(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11])])).

cnf(c_0_13,plain,
    ( X1 = X2
    | g1_orders_2(X1,X3) != g1_orders_2(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_3]),
    [final]).

cnf(c_0_14,negated_conjecture,
    ( u1_orders_2(esk2_0) = u1_orders_2(esk1_0) ),
    inference(er,[status(thm)],[c_0_12]),
    [final]).

cnf(c_0_15,plain,
    ( u1_struct_0(X1) = X2
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_7]),
    [final]).

cnf(c_0_16,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk1_0)) = g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_10,c_0_14])).

cnf(c_0_17,negated_conjecture,
    ( u1_struct_0(esk2_0) = X1
    | g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0)) != g1_orders_2(X1,X2) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_14]),c_0_11])]),c_0_16])).

cnf(c_0_18,negated_conjecture,
    ( u1_struct_0(esk2_0) = u1_struct_0(esk1_0) ),
    inference(er,[status(thm)],[c_0_17]),
    [final]).

cnf(c_0_19,negated_conjecture,
    ( u1_struct_0(esk1_0) = X1
    | g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0)) != g1_orders_2(X1,X2) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18]),
    [final]).

cnf(c_0_20,negated_conjecture,
    ( u1_orders_2(esk1_0) = X1
    | g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0)) != g1_orders_2(X2,X1) ),
    inference(rw,[status(thm)],[c_0_12,c_0_14]),
    [final]).

cnf(c_0_21,negated_conjecture,
    ( k1_yellow_0(esk1_0,esk3_0) != k1_yellow_0(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(u1_orders_2(esk1_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_14]),c_0_11])]),c_0_18]),c_0_18]),
    [final]).

cnf(c_0_23,negated_conjecture,
    ( r1_yellow_0(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_24,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:04:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.026 s
% 0.19/0.37  # Presaturation interreduction done
% 0.19/0.37  
% 0.19/0.37  # No proof found!
% 0.19/0.37  # SZS status CounterSatisfiable
% 0.19/0.37  # SZS output start Saturation
% 0.19/0.37  fof(free_g1_orders_2, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))=>![X3, X4]:(g1_orders_2(X1,X2)=g1_orders_2(X3,X4)=>(X1=X3&X2=X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', free_g1_orders_2)).
% 0.19/0.37  fof(dt_u1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 0.19/0.37  fof(t26_yellow_0, conjecture, ![X1]:(l1_orders_2(X1)=>![X2]:(l1_orders_2(X2)=>(g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))=g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))=>![X3]:(r1_yellow_0(X1,X3)=>k1_yellow_0(X1,X3)=k1_yellow_0(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_yellow_0)).
% 0.19/0.37  fof(c_0_3, plain, ![X6, X7, X8, X9]:((X6=X8|g1_orders_2(X6,X7)!=g1_orders_2(X8,X9)|~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,X6))))&(X7=X9|g1_orders_2(X6,X7)!=g1_orders_2(X8,X9)|~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,X6))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_orders_2])])])])).
% 0.19/0.37  fof(c_0_4, plain, ![X5]:(~l1_orders_2(X5)|m1_subset_1(u1_orders_2(X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X5))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).
% 0.19/0.37  fof(c_0_5, negated_conjecture, ~(![X1]:(l1_orders_2(X1)=>![X2]:(l1_orders_2(X2)=>(g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))=g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))=>![X3]:(r1_yellow_0(X1,X3)=>k1_yellow_0(X1,X3)=k1_yellow_0(X2,X3)))))), inference(assume_negation,[status(cth)],[t26_yellow_0])).
% 0.19/0.37  cnf(c_0_6, plain, (X1=X2|g1_orders_2(X3,X1)!=g1_orders_2(X4,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3)))), inference(split_conjunct,[status(thm)],[c_0_3]), ['final']).
% 0.19/0.37  cnf(c_0_7, plain, (m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.19/0.37  fof(c_0_8, negated_conjecture, (l1_orders_2(esk1_0)&(l1_orders_2(esk2_0)&(g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0))=g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0))&(r1_yellow_0(esk1_0,esk3_0)&k1_yellow_0(esk1_0,esk3_0)!=k1_yellow_0(esk2_0,esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).
% 0.19/0.37  cnf(c_0_9, plain, (u1_orders_2(X1)=X2|g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))!=g1_orders_2(X3,X2)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_6, c_0_7]), ['final']).
% 0.19/0.37  cnf(c_0_10, negated_conjecture, (g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0))=g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.37  cnf(c_0_11, negated_conjecture, (l1_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.19/0.37  cnf(c_0_12, negated_conjecture, (u1_orders_2(esk2_0)=X1|g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0))!=g1_orders_2(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_10]), c_0_11])])).
% 0.19/0.37  cnf(c_0_13, plain, (X1=X2|g1_orders_2(X1,X3)!=g1_orders_2(X2,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_3]), ['final']).
% 0.19/0.37  cnf(c_0_14, negated_conjecture, (u1_orders_2(esk2_0)=u1_orders_2(esk1_0)), inference(er,[status(thm)],[c_0_12]), ['final']).
% 0.19/0.37  cnf(c_0_15, plain, (u1_struct_0(X1)=X2|g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))!=g1_orders_2(X2,X3)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_13, c_0_7]), ['final']).
% 0.19/0.37  cnf(c_0_16, negated_conjecture, (g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk1_0))=g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0))), inference(rw,[status(thm)],[c_0_10, c_0_14])).
% 0.19/0.37  cnf(c_0_17, negated_conjecture, (u1_struct_0(esk2_0)=X1|g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0))!=g1_orders_2(X1,X2)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_14]), c_0_11])]), c_0_16])).
% 0.19/0.37  cnf(c_0_18, negated_conjecture, (u1_struct_0(esk2_0)=u1_struct_0(esk1_0)), inference(er,[status(thm)],[c_0_17]), ['final']).
% 0.19/0.37  cnf(c_0_19, negated_conjecture, (u1_struct_0(esk1_0)=X1|g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0))!=g1_orders_2(X1,X2)), inference(rw,[status(thm)],[c_0_17, c_0_18]), ['final']).
% 0.19/0.37  cnf(c_0_20, negated_conjecture, (u1_orders_2(esk1_0)=X1|g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0))!=g1_orders_2(X2,X1)), inference(rw,[status(thm)],[c_0_12, c_0_14]), ['final']).
% 0.19/0.37  cnf(c_0_21, negated_conjecture, (k1_yellow_0(esk1_0,esk3_0)!=k1_yellow_0(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.19/0.37  cnf(c_0_22, negated_conjecture, (m1_subset_1(u1_orders_2(esk1_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7, c_0_14]), c_0_11])]), c_0_18]), c_0_18]), ['final']).
% 0.19/0.37  cnf(c_0_23, negated_conjecture, (r1_yellow_0(esk1_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.19/0.37  cnf(c_0_24, negated_conjecture, (l1_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.19/0.37  # SZS output end Saturation
% 0.19/0.37  # Proof object total steps             : 25
% 0.19/0.37  # Proof object clause steps            : 18
% 0.19/0.37  # Proof object formula steps           : 7
% 0.19/0.37  # Proof object conjectures             : 16
% 0.19/0.37  # Proof object clause conjectures      : 13
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 8
% 0.19/0.37  # Proof object initial formulas used   : 3
% 0.19/0.37  # Proof object generating inferences   : 7
% 0.19/0.37  # Proof object simplifying inferences  : 12
% 0.19/0.37  # Parsed axioms                        : 3
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 8
% 0.19/0.37  # Removed in clause preprocessing      : 0
% 0.19/0.37  # Initial clauses in saturation        : 8
% 0.19/0.37  # Processed clauses                    : 33
% 0.19/0.37  # ...of these trivial                  : 1
% 0.19/0.37  # ...subsumed                          : 5
% 0.19/0.37  # ...remaining for further processing  : 27
% 0.19/0.37  # Other redundant clauses eliminated   : 0
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 0
% 0.19/0.37  # Backward-rewritten                   : 5
% 0.19/0.37  # Generated clauses                    : 21
% 0.19/0.37  # ...of the previous two non-trivial   : 20
% 0.19/0.37  # Contextual simplify-reflections      : 0
% 0.19/0.37  # Paramodulations                      : 14
% 0.19/0.37  # Factorizations                       : 0
% 0.19/0.37  # Equation resolutions                 : 7
% 0.19/0.37  # Propositional unsat checks           : 0
% 0.19/0.37  #    Propositional check models        : 0
% 0.19/0.37  #    Propositional check unsatisfiable : 0
% 0.19/0.37  #    Propositional clauses             : 0
% 0.19/0.37  #    Propositional clauses after purity: 0
% 0.19/0.37  #    Propositional unsat core size     : 0
% 0.19/0.37  #    Propositional preprocessing time  : 0.000
% 0.19/0.37  #    Propositional encoding time       : 0.000
% 0.19/0.37  #    Propositional solver time         : 0.000
% 0.19/0.37  #    Success case prop preproc time    : 0.000
% 0.19/0.37  #    Success case prop encoding time   : 0.000
% 0.19/0.37  #    Success case prop solver time     : 0.000
% 0.19/0.37  # Current number of processed clauses  : 14
% 0.19/0.37  #    Positive orientable unit clauses  : 6
% 0.19/0.37  #    Positive unorientable unit clauses: 0
% 0.19/0.37  #    Negative unit clauses             : 1
% 0.19/0.37  #    Non-unit-clauses                  : 7
% 0.19/0.37  # Current number of unprocessed clauses: 0
% 0.19/0.37  # ...number of literals in the above   : 0
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 13
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 11
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 11
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 5
% 0.19/0.37  # Unit Clause-clause subsumption calls : 0
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 3
% 0.19/0.37  # BW rewrite match successes           : 3
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 805
% 0.19/0.37  
% 0.19/0.37  # -------------------------------------------------
% 0.19/0.37  # User time                : 0.025 s
% 0.19/0.37  # System time              : 0.006 s
% 0.19/0.37  # Total time               : 0.031 s
% 0.19/0.37  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------

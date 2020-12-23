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
% DateTime   : Thu Dec  3 11:08:49 EST 2020

% Result     : CounterSatisfiable 0.13s
% Output     : Saturation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 980 expanded)
%              Number of clauses        :   46 ( 466 expanded)
%              Number of leaves         :   10 ( 252 expanded)
%              Depth                    :   11
%              Number of atoms          :  200 (1726 expanded)
%              Number of equality atoms :   77 (1021 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t22_pre_topc,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_pre_topc)).

fof(t23_pre_topc,conjecture,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ~ ( X2 != k2_struct_0(X1)
                & k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2) = k1_xboole_0 )
            & ~ ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2) != k1_xboole_0
                & X2 = k2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_pre_topc)).

fof(c_0_10,plain,(
    ! [X4,X5] : k4_xboole_0(X4,X5) = k5_xboole_0(X4,k3_xboole_0(X4,X5)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_11,plain,(
    ! [X14,X15] : k1_setfam_1(k2_tarski(X14,X15)) = k3_xboole_0(X14,X15) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_12,plain,(
    ! [X11,X12,X13] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(X11))
      | k7_subset_1(X11,X12,X13) = k4_xboole_0(X12,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

cnf(c_0_13,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,plain,(
    ! [X6,X7] :
      ( ~ r1_tarski(X6,X7)
      | k3_xboole_0(X6,X7) = X6 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_16,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,plain,(
    ! [X8] : k5_xboole_0(X8,X8) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

fof(c_0_20,plain,(
    ! [X10] : m1_subset_1(k2_subset_1(X10),k1_zfmisc_1(X10)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_21,plain,(
    ! [X9] : k2_subset_1(X9) = X9 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_22,plain,
    ( k7_subset_1(X2,X1,X3) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17]),
    [final]).

cnf(c_0_23,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_18,c_0_14]),
    [final]).

cnf(c_0_24,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19]),
    [final]).

cnf(c_0_25,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( k7_subset_1(X1,X2,X3) = k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),
    [final]).

cnf(c_0_28,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26]),
    [final]).

fof(c_0_29,plain,(
    ! [X16,X17] :
      ( ( ~ m1_subset_1(X16,k1_zfmisc_1(X17))
        | r1_tarski(X16,X17) )
      & ( ~ r1_tarski(X16,X17)
        | m1_subset_1(X16,k1_zfmisc_1(X17)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_30,plain,
    ( k7_subset_1(X1,X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28]),
    [final]).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_29]),
    [final]).

fof(c_0_32,plain,(
    ! [X18,X19] :
      ( ~ l1_struct_0(X18)
      | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
      | k7_subset_1(u1_struct_0(X18),k2_struct_0(X18),k7_subset_1(u1_struct_0(X18),k2_struct_0(X18),X19)) = X19 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_pre_topc])])])).

cnf(c_0_33,plain,
    ( k7_subset_1(X1,X2,X3) = k7_subset_1(X4,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_22]),
    [final]).

cnf(c_0_34,plain,
    ( k7_subset_1(X1,X1,X2) = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31]),
    [final]).

cnf(c_0_35,plain,
    ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)) = X2
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_32]),
    [final]).

fof(c_0_36,negated_conjecture,(
    ~ ! [X1] :
        ( l1_struct_0(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( ~ ( X2 != k2_struct_0(X1)
                  & k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2) = k1_xboole_0 )
              & ~ ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2) != k1_xboole_0
                  & X2 = k2_struct_0(X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t23_pre_topc])).

cnf(c_0_37,plain,
    ( k7_subset_1(X1,X2,X3) = k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_28])]),
    [final]).

cnf(c_0_38,plain,
    ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(X2,k2_struct_0(X1),X3)) = X3
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_33]),
    [final]).

fof(c_0_39,negated_conjecture,
    ( l1_struct_0(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & ( k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0) != k1_xboole_0
      | esk2_0 != k2_struct_0(esk1_0) )
    & ( esk2_0 = k2_struct_0(esk1_0)
      | esk2_0 != k2_struct_0(esk1_0) )
    & ( k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0) != k1_xboole_0
      | k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0) = k1_xboole_0 )
    & ( esk2_0 = k2_struct_0(esk1_0)
      | k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0) = k1_xboole_0 ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_36])])])])).

cnf(c_0_40,plain,
    ( k7_subset_1(X1,k2_struct_0(X2),k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X3)) = X3
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_33]),
    [final]).

cnf(c_0_41,plain,
    ( X1 = k1_xboole_0
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(k7_subset_1(X3,k2_struct_0(X2),X1)))
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38]),
    [final]).

cnf(c_0_42,negated_conjecture,
    ( esk2_0 = k2_struct_0(esk1_0)
    | k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_39]),
    [final]).

cnf(c_0_43,negated_conjecture,
    ( l1_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_39]),
    [final]).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_39]),
    [final]).

cnf(c_0_45,plain,
    ( k7_subset_1(X1,k2_struct_0(X2),k7_subset_1(X3,k2_struct_0(X2),X4)) = X4
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_33]),
    [final]).

cnf(c_0_46,plain,
    ( X1 = k1_xboole_0
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(k5_xboole_0(k2_struct_0(X2),k1_setfam_1(k2_tarski(k2_struct_0(X2),X1)))))
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_22]),
    [final]).

cnf(c_0_47,plain,
    ( k1_xboole_0 = X1
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X1)))
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_37]),
    [final]).

cnf(c_0_48,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_37])).

cnf(c_0_49,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),k1_xboole_0) = esk2_0
    | k2_struct_0(esk1_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_42]),c_0_43]),c_0_44])]),
    [final]).

cnf(c_0_50,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0) != k1_xboole_0
    | esk2_0 != k2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_39]),
    [final]).

cnf(c_0_51,plain,
    ( k7_subset_1(X1,k2_struct_0(X2),k5_xboole_0(k2_struct_0(X2),k1_setfam_1(k2_tarski(k2_struct_0(X2),X3)))) = X3
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_22]),
    [final]).

cnf(c_0_52,plain,
    ( k5_xboole_0(k2_struct_0(X1),k1_setfam_1(k2_tarski(k2_struct_0(X1),k7_subset_1(X2,k2_struct_0(X1),X3)))) = X3
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_45]),
    [final]).

cnf(c_0_53,plain,
    ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k5_xboole_0(k2_struct_0(X1),k1_setfam_1(k2_tarski(k2_struct_0(X1),X2)))) = X2
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_22]),
    [final]).

cnf(c_0_54,plain,
    ( k5_xboole_0(k2_struct_0(X1),k1_setfam_1(k2_tarski(k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)))) = X2
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_40]),
    [final]).

cnf(c_0_55,plain,
    ( X1 = k1_xboole_0
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X3))
    | ~ r1_tarski(k2_struct_0(X2),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_23]),c_0_24]),
    [final]).

cnf(c_0_56,plain,
    ( k7_subset_1(X1,k2_struct_0(X2),k1_xboole_0) = X3
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_37]),
    [final]).

cnf(c_0_57,plain,
    ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k1_xboole_0) = X2
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_37]),
    [final]).

cnf(c_0_58,plain,
    ( k1_xboole_0 = X1
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_37]),
    [final]).

cnf(c_0_59,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_28]),
    [final]).

cnf(c_0_60,negated_conjecture,
    ( k7_subset_1(X1,k2_struct_0(esk1_0),k1_xboole_0) = esk2_0
    | k2_struct_0(esk1_0) = esk2_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_33]),
    [final]).

cnf(c_0_61,negated_conjecture,
    ( k7_subset_1(X1,k2_struct_0(esk1_0),esk2_0) = k1_xboole_0
    | k2_struct_0(esk1_0) = esk2_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_33]),
    [final]).

cnf(c_0_62,negated_conjecture,
    ( k2_struct_0(esk1_0) = esk2_0
    | esk2_0 = k1_xboole_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_37]),
    [final]).

cnf(c_0_63,negated_conjecture,
    ( k2_struct_0(esk1_0) != esk2_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_37]),
    [final]).

cnf(c_0_64,negated_conjecture,
    ( k7_subset_1(X1,k2_struct_0(esk1_0),esk2_0) != k1_xboole_0
    | k2_struct_0(esk1_0) != esk2_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_33]),
    [final]).

cnf(c_0_65,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1) = k1_xboole_0
    | ~ r1_tarski(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_44]),
    [final]).

cnf(c_0_66,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:07:46 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.027 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # No proof found!
% 0.13/0.38  # SZS status CounterSatisfiable
% 0.13/0.38  # SZS output start Saturation
% 0.13/0.38  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.13/0.38  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.13/0.38  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 0.13/0.38  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.13/0.38  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.13/0.38  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.13/0.38  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 0.13/0.38  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.13/0.38  fof(t22_pre_topc, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_pre_topc)).
% 0.13/0.38  fof(t23_pre_topc, conjecture, ![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(~((X2!=k2_struct_0(X1)&k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)=k1_xboole_0))&~((k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)!=k1_xboole_0&X2=k2_struct_0(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_pre_topc)).
% 0.13/0.38  fof(c_0_10, plain, ![X4, X5]:k4_xboole_0(X4,X5)=k5_xboole_0(X4,k3_xboole_0(X4,X5)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.13/0.38  fof(c_0_11, plain, ![X14, X15]:k1_setfam_1(k2_tarski(X14,X15))=k3_xboole_0(X14,X15), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.13/0.38  fof(c_0_12, plain, ![X11, X12, X13]:(~m1_subset_1(X12,k1_zfmisc_1(X11))|k7_subset_1(X11,X12,X13)=k4_xboole_0(X12,X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 0.13/0.38  cnf(c_0_13, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  cnf(c_0_14, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  fof(c_0_15, plain, ![X6, X7]:(~r1_tarski(X6,X7)|k3_xboole_0(X6,X7)=X6), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.13/0.38  cnf(c_0_16, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_17, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_13, c_0_14])).
% 0.13/0.38  cnf(c_0_18, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  fof(c_0_19, plain, ![X8]:k5_xboole_0(X8,X8)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.13/0.38  fof(c_0_20, plain, ![X10]:m1_subset_1(k2_subset_1(X10),k1_zfmisc_1(X10)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.13/0.38  fof(c_0_21, plain, ![X9]:k2_subset_1(X9)=X9, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.13/0.38  cnf(c_0_22, plain, (k7_subset_1(X2,X1,X3)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_16, c_0_17]), ['final']).
% 0.13/0.38  cnf(c_0_23, plain, (k1_setfam_1(k2_tarski(X1,X2))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_18, c_0_14]), ['final']).
% 0.13/0.38  cnf(c_0_24, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19]), ['final']).
% 0.13/0.38  cnf(c_0_25, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  cnf(c_0_26, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.38  cnf(c_0_27, plain, (k7_subset_1(X1,X2,X3)=k1_xboole_0|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X2,X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24]), ['final']).
% 0.13/0.38  cnf(c_0_28, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_25, c_0_26]), ['final']).
% 0.13/0.38  fof(c_0_29, plain, ![X16, X17]:((~m1_subset_1(X16,k1_zfmisc_1(X17))|r1_tarski(X16,X17))&(~r1_tarski(X16,X17)|m1_subset_1(X16,k1_zfmisc_1(X17)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.13/0.38  cnf(c_0_30, plain, (k7_subset_1(X1,X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_27, c_0_28]), ['final']).
% 0.13/0.38  cnf(c_0_31, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_29]), ['final']).
% 0.13/0.38  fof(c_0_32, plain, ![X18, X19]:(~l1_struct_0(X18)|(~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|k7_subset_1(u1_struct_0(X18),k2_struct_0(X18),k7_subset_1(u1_struct_0(X18),k2_struct_0(X18),X19))=X19)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_pre_topc])])])).
% 0.13/0.38  cnf(c_0_33, plain, (k7_subset_1(X1,X2,X3)=k7_subset_1(X4,X2,X3)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X4))), inference(spm,[status(thm)],[c_0_22, c_0_22]), ['final']).
% 0.13/0.38  cnf(c_0_34, plain, (k7_subset_1(X1,X1,X2)=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_30, c_0_31]), ['final']).
% 0.13/0.38  cnf(c_0_35, plain, (k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))=X2|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_32]), ['final']).
% 0.13/0.38  fof(c_0_36, negated_conjecture, ~(![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(~((X2!=k2_struct_0(X1)&k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)=k1_xboole_0))&~((k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)!=k1_xboole_0&X2=k2_struct_0(X1))))))), inference(assume_negation,[status(cth)],[t23_pre_topc])).
% 0.13/0.38  cnf(c_0_37, plain, (k7_subset_1(X1,X2,X3)=k1_xboole_0|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_28])]), ['final']).
% 0.13/0.38  cnf(c_0_38, plain, (k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(X2,k2_struct_0(X1),X3))=X3|~l1_struct_0(X1)|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_35, c_0_33]), ['final']).
% 0.13/0.38  fof(c_0_39, negated_conjecture, (l1_struct_0(esk1_0)&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(((k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)!=k1_xboole_0|esk2_0!=k2_struct_0(esk1_0))&(esk2_0=k2_struct_0(esk1_0)|esk2_0!=k2_struct_0(esk1_0)))&((k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)!=k1_xboole_0|k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)=k1_xboole_0)&(esk2_0=k2_struct_0(esk1_0)|k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)=k1_xboole_0))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_36])])])])).
% 0.13/0.38  cnf(c_0_40, plain, (k7_subset_1(X1,k2_struct_0(X2),k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X3))=X3|~l1_struct_0(X2)|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_35, c_0_33]), ['final']).
% 0.13/0.38  cnf(c_0_41, plain, (X1=k1_xboole_0|~l1_struct_0(X2)|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(k7_subset_1(X3,k2_struct_0(X2),X1)))|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_37, c_0_38]), ['final']).
% 0.13/0.38  cnf(c_0_42, negated_conjecture, (esk2_0=k2_struct_0(esk1_0)|k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_39]), ['final']).
% 0.13/0.38  cnf(c_0_43, negated_conjecture, (l1_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_39]), ['final']).
% 0.13/0.38  cnf(c_0_44, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_39]), ['final']).
% 0.13/0.38  cnf(c_0_45, plain, (k7_subset_1(X1,k2_struct_0(X2),k7_subset_1(X3,k2_struct_0(X2),X4))=X4|~l1_struct_0(X2)|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X1))|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_40, c_0_33]), ['final']).
% 0.13/0.38  cnf(c_0_46, plain, (X1=k1_xboole_0|~l1_struct_0(X2)|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(k5_xboole_0(k2_struct_0(X2),k1_setfam_1(k2_tarski(k2_struct_0(X2),X1)))))|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_41, c_0_22]), ['final']).
% 0.13/0.38  cnf(c_0_47, plain, (k1_xboole_0=X1|~l1_struct_0(X2)|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X1)))|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(spm,[status(thm)],[c_0_35, c_0_37]), ['final']).
% 0.13/0.38  cnf(c_0_48, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_22, c_0_37])).
% 0.13/0.38  cnf(c_0_49, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),k1_xboole_0)=esk2_0|k2_struct_0(esk1_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_42]), c_0_43]), c_0_44])]), ['final']).
% 0.13/0.38  cnf(c_0_50, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)!=k1_xboole_0|esk2_0!=k2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_39]), ['final']).
% 0.13/0.38  cnf(c_0_51, plain, (k7_subset_1(X1,k2_struct_0(X2),k5_xboole_0(k2_struct_0(X2),k1_setfam_1(k2_tarski(k2_struct_0(X2),X3))))=X3|~l1_struct_0(X2)|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X1))|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X4))), inference(spm,[status(thm)],[c_0_45, c_0_22]), ['final']).
% 0.13/0.38  cnf(c_0_52, plain, (k5_xboole_0(k2_struct_0(X1),k1_setfam_1(k2_tarski(k2_struct_0(X1),k7_subset_1(X2,k2_struct_0(X1),X3))))=X3|~l1_struct_0(X1)|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X4))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_22, c_0_45]), ['final']).
% 0.13/0.38  cnf(c_0_53, plain, (k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k5_xboole_0(k2_struct_0(X1),k1_setfam_1(k2_tarski(k2_struct_0(X1),X2))))=X2|~l1_struct_0(X1)|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_38, c_0_22]), ['final']).
% 0.13/0.38  cnf(c_0_54, plain, (k5_xboole_0(k2_struct_0(X1),k1_setfam_1(k2_tarski(k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2))))=X2|~l1_struct_0(X1)|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_22, c_0_40]), ['final']).
% 0.13/0.38  cnf(c_0_55, plain, (X1=k1_xboole_0|~l1_struct_0(X2)|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(k1_xboole_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X3))|~r1_tarski(k2_struct_0(X2),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_23]), c_0_24]), ['final']).
% 0.13/0.38  cnf(c_0_56, plain, (k7_subset_1(X1,k2_struct_0(X2),k1_xboole_0)=X3|~l1_struct_0(X2)|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X1))|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_40, c_0_37]), ['final']).
% 0.13/0.38  cnf(c_0_57, plain, (k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k1_xboole_0)=X2|~l1_struct_0(X1)|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_35, c_0_37]), ['final']).
% 0.13/0.38  cnf(c_0_58, plain, (k1_xboole_0=X1|~l1_struct_0(X2)|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(k1_xboole_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_47, c_0_37]), ['final']).
% 0.13/0.38  cnf(c_0_59, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_48, c_0_28]), ['final']).
% 0.13/0.38  cnf(c_0_60, negated_conjecture, (k7_subset_1(X1,k2_struct_0(esk1_0),k1_xboole_0)=esk2_0|k2_struct_0(esk1_0)=esk2_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_49, c_0_33]), ['final']).
% 0.13/0.38  cnf(c_0_61, negated_conjecture, (k7_subset_1(X1,k2_struct_0(esk1_0),esk2_0)=k1_xboole_0|k2_struct_0(esk1_0)=esk2_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_42, c_0_33]), ['final']).
% 0.13/0.38  cnf(c_0_62, negated_conjecture, (k2_struct_0(esk1_0)=esk2_0|esk2_0=k1_xboole_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_49, c_0_37]), ['final']).
% 0.13/0.38  cnf(c_0_63, negated_conjecture, (k2_struct_0(esk1_0)!=esk2_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_50, c_0_37]), ['final']).
% 0.13/0.38  cnf(c_0_64, negated_conjecture, (k7_subset_1(X1,k2_struct_0(esk1_0),esk2_0)!=k1_xboole_0|k2_struct_0(esk1_0)!=esk2_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_50, c_0_33]), ['final']).
% 0.13/0.38  cnf(c_0_65, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)=k1_xboole_0|~r1_tarski(esk2_0,X1)), inference(spm,[status(thm)],[c_0_27, c_0_44]), ['final']).
% 0.13/0.38  cnf(c_0_66, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29]), ['final']).
% 0.13/0.38  # SZS output end Saturation
% 0.13/0.38  # Proof object total steps             : 67
% 0.13/0.38  # Proof object clause steps            : 46
% 0.13/0.38  # Proof object formula steps           : 21
% 0.13/0.38  # Proof object conjectures             : 14
% 0.13/0.38  # Proof object clause conjectures      : 11
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 14
% 0.13/0.38  # Proof object initial formulas used   : 10
% 0.13/0.38  # Proof object generating inferences   : 28
% 0.13/0.38  # Proof object simplifying inferences  : 11
% 0.13/0.38  # Parsed axioms                        : 10
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 16
% 0.13/0.38  # Removed in clause preprocessing      : 5
% 0.13/0.38  # Initial clauses in saturation        : 11
% 0.13/0.38  # Processed clauses                    : 123
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 73
% 0.13/0.38  # ...remaining for further processing  : 50
% 0.13/0.38  # Other redundant clauses eliminated   : 0
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 1
% 0.13/0.38  # Backward-rewritten                   : 0
% 0.13/0.38  # Generated clauses                    : 105
% 0.13/0.38  # ...of the previous two non-trivial   : 102
% 0.13/0.38  # Contextual simplify-reflections      : 0
% 0.13/0.38  # Paramodulations                      : 105
% 0.13/0.38  # Factorizations                       : 0
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
% 0.13/0.38  # Current number of processed clauses  : 38
% 0.13/0.38  #    Positive orientable unit clauses  : 4
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 0
% 0.13/0.38  #    Non-unit-clauses                  : 34
% 0.13/0.38  # Current number of unprocessed clauses: 0
% 0.13/0.38  # ...number of literals in the above   : 0
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 15
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 1123
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 237
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 74
% 0.13/0.38  # Unit Clause-clause subsumption calls : 0
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 2
% 0.13/0.38  # BW rewrite match successes           : 0
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 4199
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.032 s
% 0.13/0.38  # System time              : 0.005 s
% 0.13/0.38  # Total time               : 0.037 s
% 0.13/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------

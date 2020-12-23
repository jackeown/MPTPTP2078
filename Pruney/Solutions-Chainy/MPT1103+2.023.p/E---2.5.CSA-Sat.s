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
% DateTime   : Thu Dec  3 11:08:38 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  197 (16891 expanded)
%              Number of clauses        :  168 (7691 expanded)
%              Number of leaves         :   14 (4540 expanded)
%              Depth                    :   17
%              Number of atoms          :  390 (22045 expanded)
%              Number of equality atoms :  210 (17768 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    9 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

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

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(c_0_14,plain,(
    ! [X8,X9] : k4_xboole_0(X8,X9) = k5_xboole_0(X8,k3_xboole_0(X8,X9)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_15,plain,(
    ! [X22,X23] : k1_setfam_1(k2_tarski(X22,X23)) = k3_xboole_0(X22,X23) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_16,plain,(
    ! [X12,X13] : k4_xboole_0(X12,k2_xboole_0(X12,X13)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

fof(c_0_17,plain,(
    ! [X15,X16] : k2_xboole_0(X15,X16) = k5_xboole_0(X15,k4_xboole_0(X16,X15)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

cnf(c_0_18,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_20,plain,(
    ! [X19,X20,X21] :
      ( ~ m1_subset_1(X20,k1_zfmisc_1(X19))
      | k7_subset_1(X19,X20,X21) = k4_xboole_0(X20,X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

fof(c_0_21,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1))))))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_24]),
    [final]).

cnf(c_0_28,plain,
    ( k7_subset_1(X2,X1,X3) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_25,c_0_24]),
    [final]).

fof(c_0_29,plain,(
    ! [X14] : k5_xboole_0(X14,k1_xboole_0) = X14 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

cnf(c_0_30,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))) = k5_xboole_0(X2,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_23]),c_0_23]),c_0_24]),c_0_24]),
    [final]).

cnf(c_0_31,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k7_subset_1(X2,X3,X1))))) = k1_xboole_0
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28]),
    [final]).

cnf(c_0_32,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_29]),
    [final]).

cnf(c_0_33,plain,
    ( k7_subset_1(X1,X2,k5_xboole_0(X2,k5_xboole_0(X3,k1_setfam_1(k2_tarski(X3,X2))))) = k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_27]),
    [final]).

fof(c_0_34,negated_conjecture,(
    ~ ! [X1] :
        ( l1_struct_0(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( ~ ( X2 != k2_struct_0(X1)
                  & k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2) = k1_xboole_0 )
              & ~ ( k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2) != k1_xboole_0
                  & X2 = k2_struct_0(X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t23_pre_topc])).

cnf(c_0_35,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))) = k5_xboole_0(X2,k7_subset_1(X3,X1,X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_28]),
    [final]).

cnf(c_0_36,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,k7_subset_1(X2,X3,X1)),k1_setfam_1(k2_tarski(k5_xboole_0(X1,k7_subset_1(X2,X3,X1)),X1)))) = k5_xboole_0(X1,k7_subset_1(X2,X3,X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),
    [final]).

cnf(c_0_37,plain,
    ( k7_subset_1(X1,X2,k5_xboole_0(X2,k7_subset_1(X3,X4,X2))) = k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_28]),
    [final]).

fof(c_0_38,negated_conjecture,
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
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_34])])])])).

fof(c_0_39,plain,(
    ! [X18] : m1_subset_1(k2_subset_1(X18),k1_zfmisc_1(X18)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_40,plain,(
    ! [X17] : k2_subset_1(X17) = X17 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_41,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k7_subset_1(X2,X3,X1)),k7_subset_1(X4,X1,k5_xboole_0(X1,k7_subset_1(X2,X3,X1)))) = k5_xboole_0(X1,k7_subset_1(X2,X3,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36]),
    [final]).

cnf(c_0_42,plain,
    ( k5_xboole_0(X1,k7_subset_1(X2,X3,X1)) = k5_xboole_0(X3,k7_subset_1(X4,X1,X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_28]),
    [final]).

fof(c_0_43,plain,(
    ! [X6] : k2_xboole_0(X6,X6) = X6 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

fof(c_0_44,plain,(
    ! [X7] : k3_xboole_0(X7,X7) = X7 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_45,plain,
    ( k7_subset_1(X1,X2,k5_xboole_0(X3,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3))))) = k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_35])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_38]),
    [final]).

cnf(c_0_47,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_48,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_49,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k7_subset_1(X2,X3,X1)),k7_subset_1(X4,X3,k5_xboole_0(X1,k7_subset_1(X2,X3,X1)))) = k5_xboole_0(X1,k7_subset_1(X2,X3,X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_50,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_51,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_52,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk2_0,k5_xboole_0(X1,k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1))))) = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_53,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_47,c_0_48]),
    [final]).

cnf(c_0_54,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(X1,k7_subset_1(X2,esk2_0,X1)),k7_subset_1(u1_struct_0(esk1_0),esk2_0,k5_xboole_0(X1,k7_subset_1(X2,esk2_0,X1)))) = k5_xboole_0(X1,k7_subset_1(X2,esk2_0,X1))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_46]),
    [final]).

fof(c_0_55,plain,(
    ! [X10,X11] :
      ( ~ r1_tarski(X10,X11)
      | k3_xboole_0(X10,X11) = X10 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_56,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X1)))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_23]),c_0_24])).

cnf(c_0_57,plain,
    ( k1_setfam_1(k2_tarski(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_51,c_0_19]),
    [final]).

cnf(c_0_58,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk2_0,k5_xboole_0(X1,k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1))))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_52,c_0_53]),
    [final]).

cnf(c_0_59,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1)),k7_subset_1(u1_struct_0(esk1_0),esk2_0,k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1)))) = k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_53])).

cnf(c_0_60,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_61,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_62,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk2_0,k5_xboole_0(X1,k7_subset_1(X2,esk2_0,X1))) = k1_xboole_0
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_28]),
    [final]).

cnf(c_0_63,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1)),k7_subset_1(u1_struct_0(esk1_0),esk2_0,k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1)))) = k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_53])).

cnf(c_0_64,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k7_subset_1(X2,X3,X1)),k7_subset_1(X3,X3,k5_xboole_0(X1,k7_subset_1(X2,X3,X1)))) = k5_xboole_0(X1,k7_subset_1(X2,X3,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_53])).

cnf(c_0_65,plain,
    ( k7_subset_1(X1,X2,k5_xboole_0(X3,k7_subset_1(X4,X2,X3))) = k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_35]),
    [final]).

cnf(c_0_66,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_60,c_0_19]),
    [final]).

cnf(c_0_67,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_57]),c_0_61]),c_0_57]),
    [final]).

cnf(c_0_68,plain,
    ( k7_subset_1(X1,X2,X3) = k7_subset_1(X4,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_28]),
    [final]).

cnf(c_0_69,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk2_0,k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1))) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_46])]),
    [final]).

cnf(c_0_70,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(esk2_0,k7_subset_1(X1,X2,esk2_0)),k7_subset_1(X2,X2,k5_xboole_0(esk2_0,k7_subset_1(X1,X2,esk2_0)))) = k5_xboole_0(esk2_0,k7_subset_1(X1,X2,esk2_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_46])).

cnf(c_0_71,plain,
    ( k5_xboole_0(X1,k7_subset_1(X2,k5_xboole_0(X3,k7_subset_1(X4,X1,X3)),X1)) = k5_xboole_0(X3,k7_subset_1(X4,X1,X3))
    | ~ m1_subset_1(k5_xboole_0(X3,k7_subset_1(X4,X1,X3)),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X4)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_65]),c_0_32])).

cnf(c_0_72,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_66]),c_0_67]),c_0_32]),
    [final]).

fof(c_0_73,plain,(
    ! [X24,X25] :
      ( ( ~ m1_subset_1(X24,k1_zfmisc_1(X25))
        | r1_tarski(X24,X25) )
      & ( ~ r1_tarski(X24,X25)
        | m1_subset_1(X24,k1_zfmisc_1(X25)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_74,plain,
    ( k5_xboole_0(X1,k7_subset_1(X2,X3,X1)) = k5_xboole_0(X1,k7_subset_1(X4,X3,X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_35]),
    [final]).

cnf(c_0_75,negated_conjecture,
    ( k7_subset_1(X1,esk2_0,k5_xboole_0(X2,k7_subset_1(esk2_0,esk2_0,X2))) = k1_xboole_0
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_46])]),
    [final]).

cnf(c_0_76,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)),k7_subset_1(u1_struct_0(esk1_0),esk2_0,k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)))) = k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_46])).

cnf(c_0_77,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(X1,k7_subset_1(X2,esk2_0,X1)),k7_subset_1(X1,X1,k5_xboole_0(X1,k7_subset_1(X2,esk2_0,X1)))) = k5_xboole_0(X1,k7_subset_1(X2,esk2_0,X1))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_42])).

cnf(c_0_78,plain,
    ( k5_xboole_0(X1,k7_subset_1(k5_xboole_0(X2,k7_subset_1(X3,X1,X2)),k5_xboole_0(X2,k7_subset_1(X3,X1,X2)),X1)) = k5_xboole_0(X2,k7_subset_1(X3,X1,X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_53])).

cnf(c_0_79,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))) = X1
    | ~ r1_tarski(k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_27]),c_0_32]),
    [final]).

cnf(c_0_80,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_66]),c_0_67]),c_0_32]),
    [final]).

cnf(c_0_81,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_73]),
    [final]).

cnf(c_0_82,plain,
    ( k7_subset_1(X1,X2,X2) = k5_xboole_0(X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_57])).

cnf(c_0_83,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1)),k7_subset_1(X2,esk2_0,k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1)))) = k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_32])).

cnf(c_0_84,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)),k7_subset_1(u1_struct_0(esk1_0),esk2_0,k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)))) = k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_53])).

cnf(c_0_85,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)),k7_subset_1(X1,X1,k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)))) = k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_46])).

cnf(c_0_86,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k7_subset_1(X2,X3,X1)),k7_subset_1(X3,X3,k5_xboole_0(X1,k7_subset_1(X2,X3,X1)))) = k5_xboole_0(X1,k7_subset_1(X2,X3,X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_53]),
    [final]).

cnf(c_0_87,plain,
    ( k5_xboole_0(X1,k7_subset_1(k5_xboole_0(X2,k7_subset_1(X3,X1,X2)),k5_xboole_0(X2,k7_subset_1(X3,X1,X2)),X1)) = k5_xboole_0(X2,k7_subset_1(X3,X1,X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_78,c_0_53]),
    [final]).

cnf(c_0_88,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1)),k7_subset_1(X1,X1,k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1)))) = k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_53])).

cnf(c_0_89,plain,
    ( k7_subset_1(X1,X2,X3) = k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_66]),c_0_67]),
    [final]).

cnf(c_0_90,plain,
    ( k5_xboole_0(X1,k7_subset_1(X2,X3,X1)) = X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_tarski(k5_xboole_0(X1,k7_subset_1(X2,X3,X1)),X3) ),
    inference(spm,[status(thm)],[c_0_79,c_0_35]),
    [final]).

cnf(c_0_91,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X2,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))))))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_27,c_0_30]),
    [final]).

cnf(c_0_92,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))),k1_setfam_1(k2_tarski(k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))),X1)))) = k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_27]),c_0_32]),
    [final]).

cnf(c_0_93,plain,
    ( X1 = X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81]),
    [final]).

cnf(c_0_94,plain,
    ( k7_subset_1(X1,X2,X2) = k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_82,c_0_67]),
    [final]).

cnf(c_0_95,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1)),k7_subset_1(esk2_0,esk2_0,k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1)))) = k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_83,c_0_53])).

cnf(c_0_96,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk2_0,k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1))) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_84]),c_0_46])]),
    [final]).

cnf(c_0_97,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)),k7_subset_1(X1,X1,k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)))) = k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_85,c_0_53]),
    [final]).

cnf(c_0_98,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k7_subset_1(X2,X3,X1)),k7_subset_1(X1,X1,k5_xboole_0(X1,k7_subset_1(X2,X3,X1)))) = k5_xboole_0(X1,k7_subset_1(X2,X3,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_37]),c_0_32]),c_0_32]),c_0_32])).

cnf(c_0_99,plain,
    ( k5_xboole_0(X1,k7_subset_1(k5_xboole_0(X1,k7_subset_1(X2,X3,X1)),k5_xboole_0(X1,k7_subset_1(X2,X3,X1)),X1)) = k5_xboole_0(X1,k7_subset_1(X2,X3,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_37]),c_0_32]),c_0_32]),c_0_32])).

cnf(c_0_100,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1)),k7_subset_1(X1,X1,k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1)))) = k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_88,c_0_53]),
    [final]).

cnf(c_0_101,plain,
    ( k5_xboole_0(X1,k7_subset_1(X2,X2,X1)) = X1
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ r1_tarski(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_89]),c_0_32]),c_0_32]),c_0_32])).

cnf(c_0_102,plain,
    ( k5_xboole_0(X1,k7_subset_1(X2,X3,X1)) = X3
    | ~ m1_subset_1(k5_xboole_0(X1,k7_subset_1(X2,X3,X1)),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_90,c_0_81]),
    [final]).

cnf(c_0_103,negated_conjecture,
    ( esk2_0 = k2_struct_0(esk1_0)
    | k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_38]),
    [final]).

cnf(c_0_104,plain,
    ( k5_xboole_0(X1,k7_subset_1(X2,X2,X1)) = X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_89]),c_0_32]),c_0_32]),c_0_32])).

cnf(c_0_105,plain,
    ( k5_xboole_0(X1,k7_subset_1(X2,X3,X1)) = k5_xboole_0(X1,k5_xboole_0(X3,k1_setfam_1(k2_tarski(X3,X1))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_35]),
    [final]).

cnf(c_0_106,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X2,k7_subset_1(X3,X1,X2))))) = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_91,c_0_28]),
    [final]).

cnf(c_0_107,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))),k1_setfam_1(k2_tarski(k5_xboole_0(X2,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))),X1)))) = k5_xboole_0(X2,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_91]),c_0_32]),
    [final]).

cnf(c_0_108,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,k7_subset_1(X3,X1,X2)),k1_setfam_1(k2_tarski(k5_xboole_0(X2,k7_subset_1(X3,X1,X2)),X1)))) = k5_xboole_0(X2,k7_subset_1(X3,X1,X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_92,c_0_35]),
    [final]).

cnf(c_0_109,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))) = X2
    | ~ r1_tarski(k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_91]),c_0_32]),
    [final]).

cnf(c_0_110,plain,
    ( k5_xboole_0(X1,k7_subset_1(X2,X3,X1)) = X1
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_tarski(k5_xboole_0(X1,k7_subset_1(X2,X3,X1)),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_31]),c_0_32]),
    [final]).

cnf(c_0_111,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))) = X1
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_72]),
    [final]).

cnf(c_0_112,plain,
    ( k5_xboole_0(X1,k7_subset_1(X2,X3,X1)) = X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_72,c_0_28]),
    [final]).

cnf(c_0_113,plain,
    ( X1 = X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_93,c_0_81]),
    [final]).

cnf(c_0_114,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0) != k1_xboole_0
    | esk2_0 != k2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38]),
    [final]).

cnf(c_0_115,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_89])).

cnf(c_0_116,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))),k7_subset_1(X1,X1,k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))))) = k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_33]),c_0_32]),c_0_32]),c_0_32])).

cnf(c_0_117,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))),k7_subset_1(X2,X2,k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))))) = k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_86,c_0_28])).

cnf(c_0_118,plain,
    ( k5_xboole_0(X1,k7_subset_1(k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))),k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))),X1)) = k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_33]),c_0_32]),c_0_32]),c_0_32])).

cnf(c_0_119,plain,
    ( k5_xboole_0(X1,k7_subset_1(k5_xboole_0(X2,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))),k5_xboole_0(X2,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))),X1)) = k5_xboole_0(X2,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_87,c_0_28])).

cnf(c_0_120,plain,
    ( k5_xboole_0(X1,k7_subset_1(X1,X1,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_94]),c_0_32]),c_0_32]),c_0_32])).

cnf(c_0_121,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1)),k7_subset_1(esk2_0,esk2_0,k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1)))) = k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_95,c_0_53]),
    [final]).

cnf(c_0_122,negated_conjecture,
    ( k7_subset_1(X1,esk2_0,k5_xboole_0(X2,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X2))) = k1_xboole_0
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_96]),c_0_46])]),
    [final]).

cnf(c_0_123,negated_conjecture,
    ( k5_xboole_0(esk2_0,k7_subset_1(k5_xboole_0(X1,k7_subset_1(X2,esk2_0,X1)),k5_xboole_0(X1,k7_subset_1(X2,esk2_0,X1)),esk2_0)) = k5_xboole_0(X1,k7_subset_1(X2,esk2_0,X1))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_78,c_0_46])).

cnf(c_0_124,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)),k7_subset_1(X2,X1,k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)))) = k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_97]),c_0_53])]),
    [final]).

cnf(c_0_125,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k7_subset_1(X2,X3,X1)),k7_subset_1(X1,X1,k5_xboole_0(X1,k7_subset_1(X2,X3,X1)))) = k5_xboole_0(X1,k7_subset_1(X2,X3,X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_98,c_0_53]),
    [final]).

cnf(c_0_126,plain,
    ( k5_xboole_0(X1,k7_subset_1(k5_xboole_0(X1,k7_subset_1(X2,X3,X1)),k5_xboole_0(X1,k7_subset_1(X2,X3,X1)),X1)) = k5_xboole_0(X1,k7_subset_1(X2,X3,X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_99,c_0_53]),
    [final]).

cnf(c_0_127,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1)),k7_subset_1(X2,X1,k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1)))) = k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_100]),c_0_53])]),
    [final]).

cnf(c_0_128,plain,
    ( k5_xboole_0(X1,k7_subset_1(X2,X2,X1)) = X1
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_101,c_0_53]),
    [final]).

cnf(c_0_129,negated_conjecture,
    ( k5_xboole_0(X1,k7_subset_1(X2,k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)),X1)) = k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1))
    | ~ m1_subset_1(k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)),k1_zfmisc_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_97]),c_0_53])]),
    [final]).

cnf(c_0_130,negated_conjecture,
    ( k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)) = X1
    | ~ m1_subset_1(k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)),k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_97]),c_0_53])]),
    [final]).

cnf(c_0_131,negated_conjecture,
    ( k7_subset_1(X1,X2,k5_xboole_0(X2,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X2))) = k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_97]),c_0_53])]),
    [final]).

cnf(c_0_132,negated_conjecture,
    ( k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)) = X1
    | ~ r1_tarski(k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_97]),c_0_53])]),
    [final]).

cnf(c_0_133,negated_conjecture,
    ( k5_xboole_0(X1,k7_subset_1(X2,k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1)),X1)) = k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1))
    | ~ m1_subset_1(k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1)),k1_zfmisc_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_100]),c_0_53])]),
    [final]).

cnf(c_0_134,negated_conjecture,
    ( k7_subset_1(X1,X2,k5_xboole_0(X2,k7_subset_1(esk2_0,esk2_0,X2))) = k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_100]),c_0_53])]),
    [final]).

cnf(c_0_135,negated_conjecture,
    ( k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1)) = X1
    | ~ r1_tarski(k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_100]),c_0_53])]),
    [final]).

cnf(c_0_136,negated_conjecture,
    ( k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1)) = X1
    | ~ m1_subset_1(k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1)),k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_100]),c_0_53])]),
    [final]).

cnf(c_0_137,negated_conjecture,
    ( k5_xboole_0(esk2_0,k7_subset_1(k2_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)) = esk2_0
    | k2_struct_0(esk1_0) = esk2_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_103]),c_0_32]),c_0_32]),c_0_32]),
    [final]).

cnf(c_0_138,plain,
    ( k5_xboole_0(X1,k7_subset_1(X2,X2,X1)) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_104,c_0_53]),
    [final]).

cnf(c_0_139,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k7_subset_1(esk2_0,esk2_0,k2_struct_0(esk1_0))) = esk2_0
    | k2_struct_0(esk1_0) = esk2_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_103]),c_0_32]),c_0_32]),c_0_32]),
    [final]).

cnf(c_0_140,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)),k7_subset_1(X2,esk2_0,k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)))) = k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_96]),c_0_32]),c_0_46])]),
    [final]).

cnf(c_0_141,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1)),k7_subset_1(X2,esk2_0,k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1)))) = k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_69]),c_0_32]),c_0_46])]),
    [final]).

cnf(c_0_142,negated_conjecture,
    ( k5_xboole_0(esk2_0,k7_subset_1(X1,k5_xboole_0(X2,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X2)),esk2_0)) = k5_xboole_0(X2,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X2))
    | ~ m1_subset_1(k5_xboole_0(X2,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X2)),k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_96]),c_0_32]),c_0_46])]),
    [final]).

cnf(c_0_143,negated_conjecture,
    ( k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)) = esk2_0
    | ~ r1_tarski(k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_96]),c_0_32]),c_0_46]),c_0_32])]),
    [final]).

cnf(c_0_144,negated_conjecture,
    ( k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)) = esk2_0
    | ~ m1_subset_1(k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)),k1_zfmisc_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_96]),c_0_32]),c_0_32]),c_0_46])]),
    [final]).

cnf(c_0_145,negated_conjecture,
    ( k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)) = X1
    | ~ r1_tarski(esk2_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_89]),c_0_32]),c_0_32]),c_0_32]),c_0_46])]),
    [final]).

cnf(c_0_146,negated_conjecture,
    ( k5_xboole_0(esk2_0,k7_subset_1(X1,k5_xboole_0(X2,k7_subset_1(esk2_0,esk2_0,X2)),esk2_0)) = k5_xboole_0(X2,k7_subset_1(esk2_0,esk2_0,X2))
    | ~ m1_subset_1(k5_xboole_0(X2,k7_subset_1(esk2_0,esk2_0,X2)),k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_69]),c_0_32]),c_0_46])]),
    [final]).

cnf(c_0_147,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k7_subset_1(X2,X3,X1)),k7_subset_1(X4,X3,k5_xboole_0(X1,k7_subset_1(X2,X3,X1)))) = k5_xboole_0(X1,k7_subset_1(X2,X3,X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_106]),c_0_32]),
    [final]).

cnf(c_0_148,plain,
    ( k5_xboole_0(X1,k7_subset_1(X2,k5_xboole_0(X3,k7_subset_1(X4,X1,X3)),X1)) = k5_xboole_0(X3,k7_subset_1(X4,X1,X3))
    | ~ m1_subset_1(k5_xboole_0(X3,k7_subset_1(X4,X1,X3)),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X4)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_106]),c_0_32]),
    [final]).

cnf(c_0_149,negated_conjecture,
    ( k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1)) = esk2_0
    | ~ m1_subset_1(k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1)),k1_zfmisc_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_69]),c_0_32]),c_0_32]),c_0_46])]),
    [final]).

cnf(c_0_150,negated_conjecture,
    ( k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1)) = esk2_0
    | ~ r1_tarski(k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1)),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_69]),c_0_32]),c_0_46]),c_0_32])]),
    [final]).

cnf(c_0_151,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))),k7_subset_1(X3,X2,k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))))) = k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_107]),
    [final]).

cnf(c_0_152,negated_conjecture,
    ( k5_xboole_0(esk2_0,k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(k2_struct_0(esk1_0),esk2_0)))) = esk2_0
    | k2_struct_0(esk1_0) = esk2_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_103]),c_0_32]),c_0_32]),c_0_32]),c_0_30]),
    [final]).

cnf(c_0_153,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))),k7_subset_1(X3,X1,k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))))) = k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_92]),
    [final]).

cnf(c_0_154,plain,
    ( k5_xboole_0(X1,k7_subset_1(X2,k5_xboole_0(X1,k7_subset_1(X3,X4,X1)),X1)) = k5_xboole_0(X1,k7_subset_1(X3,X4,X1))
    | ~ m1_subset_1(k5_xboole_0(X1,k7_subset_1(X3,X4,X1)),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_31]),c_0_32]),
    [final]).

cnf(c_0_155,plain,
    ( k5_xboole_0(X1,k7_subset_1(X2,k5_xboole_0(X3,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))),X1)) = k5_xboole_0(X3,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3))))
    | ~ m1_subset_1(k5_xboole_0(X3,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))),k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_91]),c_0_32]),
    [final]).

cnf(c_0_156,plain,
    ( k5_xboole_0(X1,k7_subset_1(X2,k5_xboole_0(X1,k5_xboole_0(X3,k1_setfam_1(k2_tarski(X3,X1)))),X1)) = k5_xboole_0(X1,k5_xboole_0(X3,k1_setfam_1(k2_tarski(X3,X1))))
    | ~ m1_subset_1(k5_xboole_0(X1,k5_xboole_0(X3,k1_setfam_1(k2_tarski(X3,X1)))),k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_27]),c_0_32]),
    [final]).

cnf(c_0_157,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k7_subset_1(X1,esk2_0,k2_struct_0(esk1_0))) = esk2_0
    | k2_struct_0(esk1_0) = esk2_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_103]),c_0_32]),
    [final]).

cnf(c_0_158,negated_conjecture,
    ( k5_xboole_0(esk2_0,k7_subset_1(X1,k2_struct_0(esk1_0),esk2_0)) = esk2_0
    | k2_struct_0(esk1_0) = esk2_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_103]),c_0_32]),
    [final]).

cnf(c_0_159,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))) = X2
    | ~ m1_subset_1(k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_109,c_0_81]),
    [final]).

cnf(c_0_160,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(k2_struct_0(esk1_0),esk2_0))) = k1_xboole_0
    | k2_struct_0(esk1_0) = esk2_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_103]),c_0_32]),
    [final]).

cnf(c_0_161,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))) = X1
    | ~ m1_subset_1(k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_81]),
    [final]).

cnf(c_0_162,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk2_0,k5_xboole_0(esk2_0,k7_subset_1(X1,X2,esk2_0))) = k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_31]),c_0_32]),
    [final]).

cnf(c_0_163,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1) = k1_xboole_0
    | ~ r1_tarski(esk2_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_66]),c_0_67]),c_0_32]),
    [final]).

cnf(c_0_164,plain,
    ( k7_subset_1(X1,X2,k5_xboole_0(X3,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3))))) = k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_30]),
    [final]).

cnf(c_0_165,negated_conjecture,
    ( k2_struct_0(esk1_0) = esk2_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(k2_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_103]),c_0_32]),c_0_32])]),
    [final]).

cnf(c_0_166,plain,
    ( k5_xboole_0(X1,k7_subset_1(X2,X1,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_57]),c_0_67]),c_0_32]),
    [final]).

cnf(c_0_167,plain,
    ( k5_xboole_0(X1,k7_subset_1(X2,X3,X1)) = X1
    | ~ m1_subset_1(k5_xboole_0(X1,k7_subset_1(X2,X3,X1)),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_110,c_0_81]),
    [final]).

cnf(c_0_168,plain,
    ( k5_xboole_0(X1,k7_subset_1(X2,X3,X1)) = X1
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_tarski(X3,X1) ),
    inference(spm,[status(thm)],[c_0_111,c_0_28]),
    [final]).

cnf(c_0_169,negated_conjecture,
    ( k2_struct_0(esk1_0) = esk2_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(esk2_0,k2_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_103]),c_0_32])]),
    [final]).

cnf(c_0_170,negated_conjecture,
    ( u1_struct_0(esk1_0) = esk2_0
    | ~ m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_113,c_0_46]),
    [final]).

cnf(c_0_171,negated_conjecture,
    ( k7_subset_1(X1,k2_struct_0(esk1_0),esk2_0) = k1_xboole_0
    | k2_struct_0(esk1_0) = esk2_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_103,c_0_68]),
    [final]).

cnf(c_0_172,negated_conjecture,
    ( k7_subset_1(X1,k2_struct_0(esk1_0),esk2_0) != k1_xboole_0
    | k2_struct_0(esk1_0) != esk2_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_114,c_0_68]),
    [final]).

cnf(c_0_173,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_115,c_0_53]),
    [final]).

cnf(c_0_174,negated_conjecture,
    ( k2_struct_0(esk1_0) != esk2_0
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(k2_struct_0(esk1_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_114,c_0_89]),
    [final]).

cnf(c_0_175,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_73]),
    [final]).

cnf(c_0_176,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))),k7_subset_1(X1,X1,k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))))) = k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))) ),
    inference(spm,[status(thm)],[c_0_116,c_0_53]),
    [final]).

cnf(c_0_177,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))),k7_subset_1(X2,X2,k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))))) = k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))) ),
    inference(spm,[status(thm)],[c_0_117,c_0_53]),
    [final]).

cnf(c_0_178,plain,
    ( k5_xboole_0(X1,k7_subset_1(k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))),k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))),X1)) = k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))) ),
    inference(spm,[status(thm)],[c_0_118,c_0_53]),
    [final]).

cnf(c_0_179,plain,
    ( k5_xboole_0(X1,k7_subset_1(k5_xboole_0(X2,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))),k5_xboole_0(X2,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))),X1)) = k5_xboole_0(X2,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_119,c_0_53]),
    [final]).

cnf(c_0_180,negated_conjecture,
    ( k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)),k1_setfam_1(k2_tarski(k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)),X1)))) = k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_97]),c_0_53])]),
    [final]).

cnf(c_0_181,negated_conjecture,
    ( k5_xboole_0(esk2_0,k5_xboole_0(k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)),k1_setfam_1(k2_tarski(k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)),esk2_0)))) = k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_96]),c_0_32]),c_0_32]),c_0_32]),c_0_46])]),
    [final]).

cnf(c_0_182,negated_conjecture,
    ( k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1)),k1_setfam_1(k2_tarski(k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1)),X1)))) = k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_100]),c_0_53])]),
    [final]).

cnf(c_0_183,negated_conjecture,
    ( k5_xboole_0(X1,k7_subset_1(k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)),k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)),X1)) = k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_97]),c_0_53])]),
    [final]).

cnf(c_0_184,negated_conjecture,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1))))) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_97]),c_0_53])]),
    [final]).

cnf(c_0_185,negated_conjecture,
    ( k5_xboole_0(X1,k7_subset_1(k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1)),k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1)),X1)) = k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_100]),c_0_53])]),
    [final]).

cnf(c_0_186,negated_conjecture,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1))))) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_100]),c_0_53])]),
    [final]).

cnf(c_0_187,plain,
    ( k5_xboole_0(X1,k7_subset_1(X1,X1,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_120,c_0_53]),
    [final]).

cnf(c_0_188,negated_conjecture,
    ( k5_xboole_0(esk2_0,k5_xboole_0(k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1)),k1_setfam_1(k2_tarski(k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1)),esk2_0)))) = k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_69]),c_0_32]),c_0_32]),c_0_32]),c_0_46])]),
    [final]).

cnf(c_0_189,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)),k7_subset_1(esk2_0,esk2_0,k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)))) = k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_122]),c_0_32]),c_0_32]),c_0_32]),c_0_53])]),
    [final]).

cnf(c_0_190,negated_conjecture,
    ( k5_xboole_0(esk2_0,k7_subset_1(k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)),k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)),esk2_0)) = k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_96]),c_0_32]),c_0_32]),c_0_32]),c_0_46])]),
    [final]).

cnf(c_0_191,negated_conjecture,
    ( k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1))))) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_96]),c_0_32]),c_0_46])]),
    [final]).

cnf(c_0_192,negated_conjecture,
    ( k5_xboole_0(esk2_0,k7_subset_1(k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1)),k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1)),esk2_0)) = k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_69]),c_0_32]),c_0_32]),c_0_32]),c_0_46])]),
    [final]).

cnf(c_0_193,negated_conjecture,
    ( k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1))))) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_69]),c_0_32]),c_0_46])]),
    [final]).

cnf(c_0_194,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk2_0,k5_xboole_0(esk2_0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,esk2_0))))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_27]),c_0_32]),
    [final]).

cnf(c_0_195,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk2_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_46]),c_0_57]),c_0_67]),c_0_32]),
    [final]).

cnf(c_0_196,negated_conjecture,
    ( l1_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:08:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.51  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.51  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.51  #
% 0.20/0.51  # Preprocessing time       : 0.026 s
% 0.20/0.51  # Presaturation interreduction done
% 0.20/0.51  
% 0.20/0.51  # No proof found!
% 0.20/0.51  # SZS status CounterSatisfiable
% 0.20/0.51  # SZS output start Saturation
% 0.20/0.51  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.20/0.51  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.20/0.51  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 0.20/0.51  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.20/0.51  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 0.20/0.51  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.20/0.51  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 0.20/0.51  fof(t23_pre_topc, conjecture, ![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(~((X2!=k2_struct_0(X1)&k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)=k1_xboole_0))&~((k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)!=k1_xboole_0&X2=k2_struct_0(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_pre_topc)).
% 0.20/0.51  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.20/0.51  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 0.20/0.51  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 0.20/0.51  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.20/0.51  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.20/0.51  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.51  fof(c_0_14, plain, ![X8, X9]:k4_xboole_0(X8,X9)=k5_xboole_0(X8,k3_xboole_0(X8,X9)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.20/0.51  fof(c_0_15, plain, ![X22, X23]:k1_setfam_1(k2_tarski(X22,X23))=k3_xboole_0(X22,X23), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.20/0.51  fof(c_0_16, plain, ![X12, X13]:k4_xboole_0(X12,k2_xboole_0(X12,X13))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 0.20/0.51  fof(c_0_17, plain, ![X15, X16]:k2_xboole_0(X15,X16)=k5_xboole_0(X15,k4_xboole_0(X16,X15)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.20/0.51  cnf(c_0_18, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.51  cnf(c_0_19, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.51  fof(c_0_20, plain, ![X19, X20, X21]:(~m1_subset_1(X20,k1_zfmisc_1(X19))|k7_subset_1(X19,X20,X21)=k4_xboole_0(X20,X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 0.20/0.51  fof(c_0_21, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.20/0.51  cnf(c_0_22, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.51  cnf(c_0_23, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.51  cnf(c_0_24, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 0.20/0.51  cnf(c_0_25, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.51  cnf(c_0_26, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.51  cnf(c_0_27, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))))))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_23]), c_0_24]), c_0_24]), ['final']).
% 0.20/0.51  cnf(c_0_28, plain, (k7_subset_1(X2,X1,X3)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_25, c_0_24]), ['final']).
% 0.20/0.51  fof(c_0_29, plain, ![X14]:k5_xboole_0(X14,k1_xboole_0)=X14, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.20/0.51  cnf(c_0_30, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1))))=k5_xboole_0(X2,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_23]), c_0_23]), c_0_24]), c_0_24]), ['final']).
% 0.20/0.51  cnf(c_0_31, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k7_subset_1(X2,X3,X1)))))=k1_xboole_0|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_27, c_0_28]), ['final']).
% 0.20/0.51  cnf(c_0_32, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_29]), ['final']).
% 0.20/0.51  cnf(c_0_33, plain, (k7_subset_1(X1,X2,k5_xboole_0(X2,k5_xboole_0(X3,k1_setfam_1(k2_tarski(X3,X2)))))=k1_xboole_0|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_28, c_0_27]), ['final']).
% 0.20/0.51  fof(c_0_34, negated_conjecture, ~(![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(~((X2!=k2_struct_0(X1)&k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)=k1_xboole_0))&~((k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2)!=k1_xboole_0&X2=k2_struct_0(X1))))))), inference(assume_negation,[status(cth)],[t23_pre_topc])).
% 0.20/0.51  cnf(c_0_35, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1))))=k5_xboole_0(X2,k7_subset_1(X3,X1,X2))|~m1_subset_1(X1,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_30, c_0_28]), ['final']).
% 0.20/0.51  cnf(c_0_36, plain, (k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,k7_subset_1(X2,X3,X1)),k1_setfam_1(k2_tarski(k5_xboole_0(X1,k7_subset_1(X2,X3,X1)),X1))))=k5_xboole_0(X1,k7_subset_1(X2,X3,X1))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32]), ['final']).
% 0.20/0.51  cnf(c_0_37, plain, (k7_subset_1(X1,X2,k5_xboole_0(X2,k7_subset_1(X3,X4,X2)))=k1_xboole_0|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_33, c_0_28]), ['final']).
% 0.20/0.51  fof(c_0_38, negated_conjecture, (l1_struct_0(esk1_0)&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(((k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)!=k1_xboole_0|esk2_0!=k2_struct_0(esk1_0))&(esk2_0=k2_struct_0(esk1_0)|esk2_0!=k2_struct_0(esk1_0)))&((k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)!=k1_xboole_0|k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)=k1_xboole_0)&(esk2_0=k2_struct_0(esk1_0)|k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)=k1_xboole_0))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_34])])])])).
% 0.20/0.51  fof(c_0_39, plain, ![X18]:m1_subset_1(k2_subset_1(X18),k1_zfmisc_1(X18)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.20/0.51  fof(c_0_40, plain, ![X17]:k2_subset_1(X17)=X17, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.20/0.51  cnf(c_0_41, plain, (k5_xboole_0(k5_xboole_0(X1,k7_subset_1(X2,X3,X1)),k7_subset_1(X4,X1,k5_xboole_0(X1,k7_subset_1(X2,X3,X1))))=k5_xboole_0(X1,k7_subset_1(X2,X3,X1))|~m1_subset_1(X1,k1_zfmisc_1(X4))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_35, c_0_36]), ['final']).
% 0.20/0.51  cnf(c_0_42, plain, (k5_xboole_0(X1,k7_subset_1(X2,X3,X1))=k5_xboole_0(X3,k7_subset_1(X4,X1,X3))|~m1_subset_1(X1,k1_zfmisc_1(X4))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_35, c_0_28]), ['final']).
% 0.20/0.51  fof(c_0_43, plain, ![X6]:k2_xboole_0(X6,X6)=X6, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 0.20/0.51  fof(c_0_44, plain, ![X7]:k3_xboole_0(X7,X7)=X7, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.20/0.51  cnf(c_0_45, plain, (k7_subset_1(X1,X2,k5_xboole_0(X3,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3)))))=k1_xboole_0|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X4))), inference(spm,[status(thm)],[c_0_37, c_0_35])).
% 0.20/0.51  cnf(c_0_46, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_38]), ['final']).
% 0.20/0.51  cnf(c_0_47, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.51  cnf(c_0_48, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.51  cnf(c_0_49, plain, (k5_xboole_0(k5_xboole_0(X1,k7_subset_1(X2,X3,X1)),k7_subset_1(X4,X3,k5_xboole_0(X1,k7_subset_1(X2,X3,X1))))=k5_xboole_0(X1,k7_subset_1(X2,X3,X1))|~m1_subset_1(X3,k1_zfmisc_1(X4))|~m1_subset_1(X1,k1_zfmisc_1(X5))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.20/0.51  cnf(c_0_50, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.51  cnf(c_0_51, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.51  cnf(c_0_52, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk2_0,k5_xboole_0(X1,k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1)))))=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.20/0.51  cnf(c_0_53, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_47, c_0_48]), ['final']).
% 0.20/0.51  cnf(c_0_54, negated_conjecture, (k5_xboole_0(k5_xboole_0(X1,k7_subset_1(X2,esk2_0,X1)),k7_subset_1(u1_struct_0(esk1_0),esk2_0,k5_xboole_0(X1,k7_subset_1(X2,esk2_0,X1))))=k5_xboole_0(X1,k7_subset_1(X2,esk2_0,X1))|~m1_subset_1(esk2_0,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_49, c_0_46]), ['final']).
% 0.20/0.51  fof(c_0_55, plain, ![X10, X11]:(~r1_tarski(X10,X11)|k3_xboole_0(X10,X11)=X10), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.20/0.51  cnf(c_0_56, plain, (k5_xboole_0(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X1))))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_23]), c_0_24])).
% 0.20/0.51  cnf(c_0_57, plain, (k1_setfam_1(k2_tarski(X1,X1))=X1), inference(rw,[status(thm)],[c_0_51, c_0_19]), ['final']).
% 0.20/0.51  cnf(c_0_58, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk2_0,k5_xboole_0(X1,k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1)))))=k1_xboole_0), inference(spm,[status(thm)],[c_0_52, c_0_53]), ['final']).
% 0.20/0.51  cnf(c_0_59, negated_conjecture, (k5_xboole_0(k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1)),k7_subset_1(u1_struct_0(esk1_0),esk2_0,k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1))))=k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_54, c_0_53])).
% 0.20/0.51  cnf(c_0_60, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.20/0.51  cnf(c_0_61, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X1))=X1), inference(rw,[status(thm)],[c_0_56, c_0_57])).
% 0.20/0.51  cnf(c_0_62, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk2_0,k5_xboole_0(X1,k7_subset_1(X2,esk2_0,X1)))=k1_xboole_0|~m1_subset_1(esk2_0,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_58, c_0_28]), ['final']).
% 0.20/0.51  cnf(c_0_63, negated_conjecture, (k5_xboole_0(k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1)),k7_subset_1(u1_struct_0(esk1_0),esk2_0,k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1))))=k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1))), inference(spm,[status(thm)],[c_0_59, c_0_53])).
% 0.20/0.51  cnf(c_0_64, plain, (k5_xboole_0(k5_xboole_0(X1,k7_subset_1(X2,X3,X1)),k7_subset_1(X3,X3,k5_xboole_0(X1,k7_subset_1(X2,X3,X1))))=k5_xboole_0(X1,k7_subset_1(X2,X3,X1))|~m1_subset_1(X1,k1_zfmisc_1(X4))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_49, c_0_53])).
% 0.20/0.51  cnf(c_0_65, plain, (k7_subset_1(X1,X2,k5_xboole_0(X3,k7_subset_1(X4,X2,X3)))=k1_xboole_0|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X4))), inference(spm,[status(thm)],[c_0_33, c_0_35]), ['final']).
% 0.20/0.51  cnf(c_0_66, plain, (k1_setfam_1(k2_tarski(X1,X2))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_60, c_0_19]), ['final']).
% 0.20/0.51  cnf(c_0_67, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_57]), c_0_61]), c_0_57]), ['final']).
% 0.20/0.51  cnf(c_0_68, plain, (k7_subset_1(X1,X2,X3)=k7_subset_1(X4,X2,X3)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X4))), inference(spm,[status(thm)],[c_0_28, c_0_28]), ['final']).
% 0.20/0.51  cnf(c_0_69, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk2_0,k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1)))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_46])]), ['final']).
% 0.20/0.51  cnf(c_0_70, negated_conjecture, (k5_xboole_0(k5_xboole_0(esk2_0,k7_subset_1(X1,X2,esk2_0)),k7_subset_1(X2,X2,k5_xboole_0(esk2_0,k7_subset_1(X1,X2,esk2_0))))=k5_xboole_0(esk2_0,k7_subset_1(X1,X2,esk2_0))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_64, c_0_46])).
% 0.20/0.51  cnf(c_0_71, plain, (k5_xboole_0(X1,k7_subset_1(X2,k5_xboole_0(X3,k7_subset_1(X4,X1,X3)),X1))=k5_xboole_0(X3,k7_subset_1(X4,X1,X3))|~m1_subset_1(k5_xboole_0(X3,k7_subset_1(X4,X1,X3)),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X5))|~m1_subset_1(X1,k1_zfmisc_1(X4))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_65]), c_0_32])).
% 0.20/0.51  cnf(c_0_72, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1))))=X2|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_66]), c_0_67]), c_0_32]), ['final']).
% 0.20/0.51  fof(c_0_73, plain, ![X24, X25]:((~m1_subset_1(X24,k1_zfmisc_1(X25))|r1_tarski(X24,X25))&(~r1_tarski(X24,X25)|m1_subset_1(X24,k1_zfmisc_1(X25)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.51  cnf(c_0_74, plain, (k5_xboole_0(X1,k7_subset_1(X2,X3,X1))=k5_xboole_0(X1,k7_subset_1(X4,X3,X1))|~m1_subset_1(X3,k1_zfmisc_1(X4))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_35, c_0_35]), ['final']).
% 0.20/0.51  cnf(c_0_75, negated_conjecture, (k7_subset_1(X1,esk2_0,k5_xboole_0(X2,k7_subset_1(esk2_0,esk2_0,X2)))=k1_xboole_0|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_46])]), ['final']).
% 0.20/0.51  cnf(c_0_76, negated_conjecture, (k5_xboole_0(k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)),k7_subset_1(u1_struct_0(esk1_0),esk2_0,k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1))))=k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_54, c_0_46])).
% 0.20/0.51  cnf(c_0_77, negated_conjecture, (k5_xboole_0(k5_xboole_0(X1,k7_subset_1(X2,esk2_0,X1)),k7_subset_1(X1,X1,k5_xboole_0(X1,k7_subset_1(X2,esk2_0,X1))))=k5_xboole_0(X1,k7_subset_1(X2,esk2_0,X1))|~m1_subset_1(esk2_0,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_70, c_0_42])).
% 0.20/0.51  cnf(c_0_78, plain, (k5_xboole_0(X1,k7_subset_1(k5_xboole_0(X2,k7_subset_1(X3,X1,X2)),k5_xboole_0(X2,k7_subset_1(X3,X1,X2)),X1))=k5_xboole_0(X2,k7_subset_1(X3,X1,X2))|~m1_subset_1(X1,k1_zfmisc_1(X4))|~m1_subset_1(X1,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_71, c_0_53])).
% 0.20/0.51  cnf(c_0_79, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1))))=X1|~r1_tarski(k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_27]), c_0_32]), ['final']).
% 0.20/0.51  cnf(c_0_80, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_66]), c_0_67]), c_0_32]), ['final']).
% 0.20/0.51  cnf(c_0_81, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_73]), ['final']).
% 0.20/0.51  cnf(c_0_82, plain, (k7_subset_1(X1,X2,X2)=k5_xboole_0(X2,X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_28, c_0_57])).
% 0.20/0.51  cnf(c_0_83, negated_conjecture, (k5_xboole_0(k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1)),k7_subset_1(X2,esk2_0,k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1))))=k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1))|~m1_subset_1(esk2_0,k1_zfmisc_1(X2))|~m1_subset_1(esk2_0,k1_zfmisc_1(X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_32])).
% 0.20/0.51  cnf(c_0_84, negated_conjecture, (k5_xboole_0(k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)),k7_subset_1(u1_struct_0(esk1_0),esk2_0,k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1))))=k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1))), inference(spm,[status(thm)],[c_0_76, c_0_53])).
% 0.20/0.51  cnf(c_0_85, negated_conjecture, (k5_xboole_0(k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)),k7_subset_1(X1,X1,k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1))))=k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_77, c_0_46])).
% 0.20/0.51  cnf(c_0_86, plain, (k5_xboole_0(k5_xboole_0(X1,k7_subset_1(X2,X3,X1)),k7_subset_1(X3,X3,k5_xboole_0(X1,k7_subset_1(X2,X3,X1))))=k5_xboole_0(X1,k7_subset_1(X2,X3,X1))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_64, c_0_53]), ['final']).
% 0.20/0.51  cnf(c_0_87, plain, (k5_xboole_0(X1,k7_subset_1(k5_xboole_0(X2,k7_subset_1(X3,X1,X2)),k5_xboole_0(X2,k7_subset_1(X3,X1,X2)),X1))=k5_xboole_0(X2,k7_subset_1(X3,X1,X2))|~m1_subset_1(X1,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_78, c_0_53]), ['final']).
% 0.20/0.51  cnf(c_0_88, negated_conjecture, (k5_xboole_0(k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1)),k7_subset_1(X1,X1,k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1))))=k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_77, c_0_53])).
% 0.20/0.51  cnf(c_0_89, plain, (k7_subset_1(X1,X2,X3)=k1_xboole_0|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X2,X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_66]), c_0_67]), ['final']).
% 0.20/0.51  cnf(c_0_90, plain, (k5_xboole_0(X1,k7_subset_1(X2,X3,X1))=X3|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_tarski(k5_xboole_0(X1,k7_subset_1(X2,X3,X1)),X3)), inference(spm,[status(thm)],[c_0_79, c_0_35]), ['final']).
% 0.20/0.51  cnf(c_0_91, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X2,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))))))=k1_xboole_0), inference(spm,[status(thm)],[c_0_27, c_0_30]), ['final']).
% 0.20/0.51  cnf(c_0_92, plain, (k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))),k1_setfam_1(k2_tarski(k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))),X1))))=k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_27]), c_0_32]), ['final']).
% 0.20/0.51  cnf(c_0_93, plain, (X1=X2|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_80, c_0_81]), ['final']).
% 0.20/0.51  cnf(c_0_94, plain, (k7_subset_1(X1,X2,X2)=k1_xboole_0|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_82, c_0_67]), ['final']).
% 0.20/0.51  cnf(c_0_95, negated_conjecture, (k5_xboole_0(k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1)),k7_subset_1(esk2_0,esk2_0,k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1))))=k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1))|~m1_subset_1(esk2_0,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_83, c_0_53])).
% 0.20/0.51  cnf(c_0_96, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk2_0,k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_84]), c_0_46])]), ['final']).
% 0.20/0.51  cnf(c_0_97, negated_conjecture, (k5_xboole_0(k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)),k7_subset_1(X1,X1,k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1))))=k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1))), inference(spm,[status(thm)],[c_0_85, c_0_53]), ['final']).
% 0.20/0.51  cnf(c_0_98, plain, (k5_xboole_0(k5_xboole_0(X1,k7_subset_1(X2,X3,X1)),k7_subset_1(X1,X1,k5_xboole_0(X1,k7_subset_1(X2,X3,X1))))=k5_xboole_0(X1,k7_subset_1(X2,X3,X1))|~m1_subset_1(X1,k1_zfmisc_1(X4))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_37]), c_0_32]), c_0_32]), c_0_32])).
% 0.20/0.51  cnf(c_0_99, plain, (k5_xboole_0(X1,k7_subset_1(k5_xboole_0(X1,k7_subset_1(X2,X3,X1)),k5_xboole_0(X1,k7_subset_1(X2,X3,X1)),X1))=k5_xboole_0(X1,k7_subset_1(X2,X3,X1))|~m1_subset_1(X1,k1_zfmisc_1(X4))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_37]), c_0_32]), c_0_32]), c_0_32])).
% 0.20/0.51  cnf(c_0_100, negated_conjecture, (k5_xboole_0(k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1)),k7_subset_1(X1,X1,k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1))))=k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1))), inference(spm,[status(thm)],[c_0_88, c_0_53]), ['final']).
% 0.20/0.51  cnf(c_0_101, plain, (k5_xboole_0(X1,k7_subset_1(X2,X2,X1))=X1|~m1_subset_1(X2,k1_zfmisc_1(X3))|~r1_tarski(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_89]), c_0_32]), c_0_32]), c_0_32])).
% 0.20/0.51  cnf(c_0_102, plain, (k5_xboole_0(X1,k7_subset_1(X2,X3,X1))=X3|~m1_subset_1(k5_xboole_0(X1,k7_subset_1(X2,X3,X1)),k1_zfmisc_1(X3))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_90, c_0_81]), ['final']).
% 0.20/0.51  cnf(c_0_103, negated_conjecture, (esk2_0=k2_struct_0(esk1_0)|k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_38]), ['final']).
% 0.20/0.51  cnf(c_0_104, plain, (k5_xboole_0(X1,k7_subset_1(X2,X2,X1))=X2|~m1_subset_1(X1,k1_zfmisc_1(X3))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_89]), c_0_32]), c_0_32]), c_0_32])).
% 0.20/0.51  cnf(c_0_105, plain, (k5_xboole_0(X1,k7_subset_1(X2,X3,X1))=k5_xboole_0(X1,k5_xboole_0(X3,k1_setfam_1(k2_tarski(X3,X1))))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_30, c_0_35]), ['final']).
% 0.20/0.51  cnf(c_0_106, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X2,k7_subset_1(X3,X1,X2)))))=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_91, c_0_28]), ['final']).
% 0.20/0.51  cnf(c_0_107, plain, (k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))),k1_setfam_1(k2_tarski(k5_xboole_0(X2,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))),X1))))=k5_xboole_0(X2,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_91]), c_0_32]), ['final']).
% 0.20/0.51  cnf(c_0_108, plain, (k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,k7_subset_1(X3,X1,X2)),k1_setfam_1(k2_tarski(k5_xboole_0(X2,k7_subset_1(X3,X1,X2)),X1))))=k5_xboole_0(X2,k7_subset_1(X3,X1,X2))|~m1_subset_1(X1,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_92, c_0_35]), ['final']).
% 0.20/0.51  cnf(c_0_109, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1))))=X2|~r1_tarski(k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_91]), c_0_32]), ['final']).
% 0.20/0.51  cnf(c_0_110, plain, (k5_xboole_0(X1,k7_subset_1(X2,X3,X1))=X1|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_tarski(k5_xboole_0(X1,k7_subset_1(X2,X3,X1)),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_31]), c_0_32]), ['final']).
% 0.20/0.51  cnf(c_0_111, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1))))=X1|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_30, c_0_72]), ['final']).
% 0.20/0.51  cnf(c_0_112, plain, (k5_xboole_0(X1,k7_subset_1(X2,X3,X1))=X3|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_72, c_0_28]), ['final']).
% 0.20/0.51  cnf(c_0_113, plain, (X1=X2|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_93, c_0_81]), ['final']).
% 0.20/0.51  cnf(c_0_114, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0)!=k1_xboole_0|esk2_0!=k2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_38]), ['final']).
% 0.20/0.51  cnf(c_0_115, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(X3))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_28, c_0_89])).
% 0.20/0.51  cnf(c_0_116, plain, (k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))),k7_subset_1(X1,X1,k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1))))))=k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1))))|~m1_subset_1(X1,k1_zfmisc_1(X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_33]), c_0_32]), c_0_32]), c_0_32])).
% 0.20/0.51  cnf(c_0_117, plain, (k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))),k7_subset_1(X2,X2,k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1))))))=k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1))))|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_86, c_0_28])).
% 0.20/0.51  cnf(c_0_118, plain, (k5_xboole_0(X1,k7_subset_1(k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))),k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))),X1))=k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1))))|~m1_subset_1(X1,k1_zfmisc_1(X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_33]), c_0_32]), c_0_32]), c_0_32])).
% 0.20/0.51  cnf(c_0_119, plain, (k5_xboole_0(X1,k7_subset_1(k5_xboole_0(X2,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))),k5_xboole_0(X2,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))),X1))=k5_xboole_0(X2,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))))|~m1_subset_1(X1,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_87, c_0_28])).
% 0.20/0.51  cnf(c_0_120, plain, (k5_xboole_0(X1,k7_subset_1(X1,X1,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_94]), c_0_32]), c_0_32]), c_0_32])).
% 0.20/0.51  cnf(c_0_121, negated_conjecture, (k5_xboole_0(k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1)),k7_subset_1(esk2_0,esk2_0,k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1))))=k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1))), inference(spm,[status(thm)],[c_0_95, c_0_53]), ['final']).
% 0.20/0.51  cnf(c_0_122, negated_conjecture, (k7_subset_1(X1,esk2_0,k5_xboole_0(X2,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X2)))=k1_xboole_0|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_96]), c_0_46])]), ['final']).
% 0.20/0.51  cnf(c_0_123, negated_conjecture, (k5_xboole_0(esk2_0,k7_subset_1(k5_xboole_0(X1,k7_subset_1(X2,esk2_0,X1)),k5_xboole_0(X1,k7_subset_1(X2,esk2_0,X1)),esk2_0))=k5_xboole_0(X1,k7_subset_1(X2,esk2_0,X1))|~m1_subset_1(esk2_0,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_78, c_0_46])).
% 0.20/0.51  cnf(c_0_124, negated_conjecture, (k5_xboole_0(k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)),k7_subset_1(X2,X1,k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1))))=k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_97]), c_0_53])]), ['final']).
% 0.20/0.51  cnf(c_0_125, plain, (k5_xboole_0(k5_xboole_0(X1,k7_subset_1(X2,X3,X1)),k7_subset_1(X1,X1,k5_xboole_0(X1,k7_subset_1(X2,X3,X1))))=k5_xboole_0(X1,k7_subset_1(X2,X3,X1))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_98, c_0_53]), ['final']).
% 0.20/0.51  cnf(c_0_126, plain, (k5_xboole_0(X1,k7_subset_1(k5_xboole_0(X1,k7_subset_1(X2,X3,X1)),k5_xboole_0(X1,k7_subset_1(X2,X3,X1)),X1))=k5_xboole_0(X1,k7_subset_1(X2,X3,X1))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_99, c_0_53]), ['final']).
% 0.20/0.51  cnf(c_0_127, negated_conjecture, (k5_xboole_0(k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1)),k7_subset_1(X2,X1,k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1))))=k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_100]), c_0_53])]), ['final']).
% 0.20/0.51  cnf(c_0_128, plain, (k5_xboole_0(X1,k7_subset_1(X2,X2,X1))=X1|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_101, c_0_53]), ['final']).
% 0.20/0.51  cnf(c_0_129, negated_conjecture, (k5_xboole_0(X1,k7_subset_1(X2,k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)),X1))=k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1))|~m1_subset_1(k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)),k1_zfmisc_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_97]), c_0_53])]), ['final']).
% 0.20/0.51  cnf(c_0_130, negated_conjecture, (k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1))=X1|~m1_subset_1(k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)),k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_97]), c_0_53])]), ['final']).
% 0.20/0.51  cnf(c_0_131, negated_conjecture, (k7_subset_1(X1,X2,k5_xboole_0(X2,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X2)))=k1_xboole_0|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_97]), c_0_53])]), ['final']).
% 0.20/0.51  cnf(c_0_132, negated_conjecture, (k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1))=X1|~r1_tarski(k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_97]), c_0_53])]), ['final']).
% 0.20/0.51  cnf(c_0_133, negated_conjecture, (k5_xboole_0(X1,k7_subset_1(X2,k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1)),X1))=k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1))|~m1_subset_1(k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1)),k1_zfmisc_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_100]), c_0_53])]), ['final']).
% 0.20/0.51  cnf(c_0_134, negated_conjecture, (k7_subset_1(X1,X2,k5_xboole_0(X2,k7_subset_1(esk2_0,esk2_0,X2)))=k1_xboole_0|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_100]), c_0_53])]), ['final']).
% 0.20/0.51  cnf(c_0_135, negated_conjecture, (k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1))=X1|~r1_tarski(k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_100]), c_0_53])]), ['final']).
% 0.20/0.51  cnf(c_0_136, negated_conjecture, (k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1))=X1|~m1_subset_1(k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1)),k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_100]), c_0_53])]), ['final']).
% 0.20/0.51  cnf(c_0_137, negated_conjecture, (k5_xboole_0(esk2_0,k7_subset_1(k2_struct_0(esk1_0),k2_struct_0(esk1_0),esk2_0))=esk2_0|k2_struct_0(esk1_0)=esk2_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_103]), c_0_32]), c_0_32]), c_0_32]), ['final']).
% 0.20/0.51  cnf(c_0_138, plain, (k5_xboole_0(X1,k7_subset_1(X2,X2,X1))=X2|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_104, c_0_53]), ['final']).
% 0.20/0.51  cnf(c_0_139, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k7_subset_1(esk2_0,esk2_0,k2_struct_0(esk1_0)))=esk2_0|k2_struct_0(esk1_0)=esk2_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_103]), c_0_32]), c_0_32]), c_0_32]), ['final']).
% 0.20/0.51  cnf(c_0_140, negated_conjecture, (k5_xboole_0(k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)),k7_subset_1(X2,esk2_0,k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1))))=k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1))|~m1_subset_1(esk2_0,k1_zfmisc_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_96]), c_0_32]), c_0_46])]), ['final']).
% 0.20/0.51  cnf(c_0_141, negated_conjecture, (k5_xboole_0(k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1)),k7_subset_1(X2,esk2_0,k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1))))=k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1))|~m1_subset_1(esk2_0,k1_zfmisc_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_69]), c_0_32]), c_0_46])]), ['final']).
% 0.20/0.51  cnf(c_0_142, negated_conjecture, (k5_xboole_0(esk2_0,k7_subset_1(X1,k5_xboole_0(X2,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X2)),esk2_0))=k5_xboole_0(X2,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X2))|~m1_subset_1(k5_xboole_0(X2,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X2)),k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_96]), c_0_32]), c_0_46])]), ['final']).
% 0.20/0.51  cnf(c_0_143, negated_conjecture, (k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1))=esk2_0|~r1_tarski(k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_96]), c_0_32]), c_0_46]), c_0_32])]), ['final']).
% 0.20/0.51  cnf(c_0_144, negated_conjecture, (k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1))=esk2_0|~m1_subset_1(k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)),k1_zfmisc_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_96]), c_0_32]), c_0_32]), c_0_46])]), ['final']).
% 0.20/0.51  cnf(c_0_145, negated_conjecture, (k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1))=X1|~r1_tarski(esk2_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_89]), c_0_32]), c_0_32]), c_0_32]), c_0_46])]), ['final']).
% 0.20/0.51  cnf(c_0_146, negated_conjecture, (k5_xboole_0(esk2_0,k7_subset_1(X1,k5_xboole_0(X2,k7_subset_1(esk2_0,esk2_0,X2)),esk2_0))=k5_xboole_0(X2,k7_subset_1(esk2_0,esk2_0,X2))|~m1_subset_1(k5_xboole_0(X2,k7_subset_1(esk2_0,esk2_0,X2)),k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_69]), c_0_32]), c_0_46])]), ['final']).
% 0.20/0.51  cnf(c_0_147, plain, (k5_xboole_0(k5_xboole_0(X1,k7_subset_1(X2,X3,X1)),k7_subset_1(X4,X3,k5_xboole_0(X1,k7_subset_1(X2,X3,X1))))=k5_xboole_0(X1,k7_subset_1(X2,X3,X1))|~m1_subset_1(X3,k1_zfmisc_1(X4))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_106]), c_0_32]), ['final']).
% 0.20/0.51  cnf(c_0_148, plain, (k5_xboole_0(X1,k7_subset_1(X2,k5_xboole_0(X3,k7_subset_1(X4,X1,X3)),X1))=k5_xboole_0(X3,k7_subset_1(X4,X1,X3))|~m1_subset_1(k5_xboole_0(X3,k7_subset_1(X4,X1,X3)),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X4))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_106]), c_0_32]), ['final']).
% 0.20/0.51  cnf(c_0_149, negated_conjecture, (k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1))=esk2_0|~m1_subset_1(k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1)),k1_zfmisc_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_69]), c_0_32]), c_0_32]), c_0_46])]), ['final']).
% 0.20/0.51  cnf(c_0_150, negated_conjecture, (k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1))=esk2_0|~r1_tarski(k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1)),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_69]), c_0_32]), c_0_46]), c_0_32])]), ['final']).
% 0.20/0.51  cnf(c_0_151, plain, (k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))),k7_subset_1(X3,X2,k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1))))))=k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1))))|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_35, c_0_107]), ['final']).
% 0.20/0.51  cnf(c_0_152, negated_conjecture, (k5_xboole_0(esk2_0,k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(k2_struct_0(esk1_0),esk2_0))))=esk2_0|k2_struct_0(esk1_0)=esk2_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_103]), c_0_32]), c_0_32]), c_0_32]), c_0_30]), ['final']).
% 0.20/0.51  cnf(c_0_153, plain, (k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))),k7_subset_1(X3,X1,k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1))))))=k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1))))|~m1_subset_1(X1,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_35, c_0_92]), ['final']).
% 0.20/0.51  cnf(c_0_154, plain, (k5_xboole_0(X1,k7_subset_1(X2,k5_xboole_0(X1,k7_subset_1(X3,X4,X1)),X1))=k5_xboole_0(X1,k7_subset_1(X3,X4,X1))|~m1_subset_1(k5_xboole_0(X1,k7_subset_1(X3,X4,X1)),k1_zfmisc_1(X2))|~m1_subset_1(X4,k1_zfmisc_1(X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_31]), c_0_32]), ['final']).
% 0.20/0.51  cnf(c_0_155, plain, (k5_xboole_0(X1,k7_subset_1(X2,k5_xboole_0(X3,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))),X1))=k5_xboole_0(X3,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3))))|~m1_subset_1(k5_xboole_0(X3,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))),k1_zfmisc_1(X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_91]), c_0_32]), ['final']).
% 0.20/0.51  cnf(c_0_156, plain, (k5_xboole_0(X1,k7_subset_1(X2,k5_xboole_0(X1,k5_xboole_0(X3,k1_setfam_1(k2_tarski(X3,X1)))),X1))=k5_xboole_0(X1,k5_xboole_0(X3,k1_setfam_1(k2_tarski(X3,X1))))|~m1_subset_1(k5_xboole_0(X1,k5_xboole_0(X3,k1_setfam_1(k2_tarski(X3,X1)))),k1_zfmisc_1(X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_27]), c_0_32]), ['final']).
% 0.20/0.51  cnf(c_0_157, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k7_subset_1(X1,esk2_0,k2_struct_0(esk1_0)))=esk2_0|k2_struct_0(esk1_0)=esk2_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_103]), c_0_32]), ['final']).
% 0.20/0.51  cnf(c_0_158, negated_conjecture, (k5_xboole_0(esk2_0,k7_subset_1(X1,k2_struct_0(esk1_0),esk2_0))=esk2_0|k2_struct_0(esk1_0)=esk2_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_103]), c_0_32]), ['final']).
% 0.20/0.51  cnf(c_0_159, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1))))=X2|~m1_subset_1(k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_109, c_0_81]), ['final']).
% 0.20/0.51  cnf(c_0_160, negated_conjecture, (k5_xboole_0(k2_struct_0(esk1_0),k1_setfam_1(k2_tarski(k2_struct_0(esk1_0),esk2_0)))=k1_xboole_0|k2_struct_0(esk1_0)=esk2_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_103]), c_0_32]), ['final']).
% 0.20/0.51  cnf(c_0_161, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1))))=X1|~m1_subset_1(k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_79, c_0_81]), ['final']).
% 0.20/0.51  cnf(c_0_162, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk2_0,k5_xboole_0(esk2_0,k7_subset_1(X1,X2,esk2_0)))=k1_xboole_0|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_31]), c_0_32]), ['final']).
% 0.20/0.51  cnf(c_0_163, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)=k1_xboole_0|~r1_tarski(esk2_0,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_66]), c_0_67]), c_0_32]), ['final']).
% 0.20/0.51  cnf(c_0_164, plain, (k7_subset_1(X1,X2,k5_xboole_0(X3,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3)))))=k1_xboole_0|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_33, c_0_30]), ['final']).
% 0.20/0.51  cnf(c_0_165, negated_conjecture, (k2_struct_0(esk1_0)=esk2_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(esk2_0,k1_zfmisc_1(k2_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_103]), c_0_32]), c_0_32])]), ['final']).
% 0.20/0.51  cnf(c_0_166, plain, (k5_xboole_0(X1,k7_subset_1(X2,X1,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_57]), c_0_67]), c_0_32]), ['final']).
% 0.20/0.51  cnf(c_0_167, plain, (k5_xboole_0(X1,k7_subset_1(X2,X3,X1))=X1|~m1_subset_1(k5_xboole_0(X1,k7_subset_1(X2,X3,X1)),k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_110, c_0_81]), ['final']).
% 0.20/0.51  cnf(c_0_168, plain, (k5_xboole_0(X1,k7_subset_1(X2,X3,X1))=X1|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_tarski(X3,X1)), inference(spm,[status(thm)],[c_0_111, c_0_28]), ['final']).
% 0.20/0.51  cnf(c_0_169, negated_conjecture, (k2_struct_0(esk1_0)=esk2_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(esk2_0,k2_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_103]), c_0_32])]), ['final']).
% 0.20/0.51  cnf(c_0_170, negated_conjecture, (u1_struct_0(esk1_0)=esk2_0|~m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_113, c_0_46]), ['final']).
% 0.20/0.51  cnf(c_0_171, negated_conjecture, (k7_subset_1(X1,k2_struct_0(esk1_0),esk2_0)=k1_xboole_0|k2_struct_0(esk1_0)=esk2_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_103, c_0_68]), ['final']).
% 0.20/0.51  cnf(c_0_172, negated_conjecture, (k7_subset_1(X1,k2_struct_0(esk1_0),esk2_0)!=k1_xboole_0|k2_struct_0(esk1_0)!=esk2_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_114, c_0_68]), ['final']).
% 0.20/0.51  cnf(c_0_173, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k1_xboole_0|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_115, c_0_53]), ['final']).
% 0.20/0.51  cnf(c_0_174, negated_conjecture, (k2_struct_0(esk1_0)!=esk2_0|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(k2_struct_0(esk1_0),esk2_0)), inference(spm,[status(thm)],[c_0_114, c_0_89]), ['final']).
% 0.20/0.51  cnf(c_0_175, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_73]), ['final']).
% 0.20/0.51  cnf(c_0_176, plain, (k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))),k7_subset_1(X1,X1,k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1))))))=k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1))))), inference(spm,[status(thm)],[c_0_116, c_0_53]), ['final']).
% 0.20/0.51  cnf(c_0_177, plain, (k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))),k7_subset_1(X2,X2,k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1))))))=k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1))))), inference(spm,[status(thm)],[c_0_117, c_0_53]), ['final']).
% 0.20/0.51  cnf(c_0_178, plain, (k5_xboole_0(X1,k7_subset_1(k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))),k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))),X1))=k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1))))), inference(spm,[status(thm)],[c_0_118, c_0_53]), ['final']).
% 0.20/0.51  cnf(c_0_179, plain, (k5_xboole_0(X1,k7_subset_1(k5_xboole_0(X2,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))),k5_xboole_0(X2,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))),X1))=k5_xboole_0(X2,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))))), inference(spm,[status(thm)],[c_0_119, c_0_53]), ['final']).
% 0.20/0.51  cnf(c_0_180, negated_conjecture, (k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)),k1_setfam_1(k2_tarski(k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)),X1))))=k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_97]), c_0_53])]), ['final']).
% 0.20/0.51  cnf(c_0_181, negated_conjecture, (k5_xboole_0(esk2_0,k5_xboole_0(k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)),k1_setfam_1(k2_tarski(k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)),esk2_0))))=k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_96]), c_0_32]), c_0_32]), c_0_32]), c_0_46])]), ['final']).
% 0.20/0.51  cnf(c_0_182, negated_conjecture, (k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1)),k1_setfam_1(k2_tarski(k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1)),X1))))=k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_100]), c_0_53])]), ['final']).
% 0.20/0.51  cnf(c_0_183, negated_conjecture, (k5_xboole_0(X1,k7_subset_1(k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)),k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)),X1))=k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_97]), c_0_53])]), ['final']).
% 0.20/0.51  cnf(c_0_184, negated_conjecture, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)))))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_97]), c_0_53])]), ['final']).
% 0.20/0.51  cnf(c_0_185, negated_conjecture, (k5_xboole_0(X1,k7_subset_1(k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1)),k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1)),X1))=k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_100]), c_0_53])]), ['final']).
% 0.20/0.51  cnf(c_0_186, negated_conjecture, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1)))))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_100]), c_0_53])]), ['final']).
% 0.20/0.51  cnf(c_0_187, plain, (k5_xboole_0(X1,k7_subset_1(X1,X1,X1))=X1), inference(spm,[status(thm)],[c_0_120, c_0_53]), ['final']).
% 0.20/0.51  cnf(c_0_188, negated_conjecture, (k5_xboole_0(esk2_0,k5_xboole_0(k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1)),k1_setfam_1(k2_tarski(k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1)),esk2_0))))=k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_69]), c_0_32]), c_0_32]), c_0_32]), c_0_46])]), ['final']).
% 0.20/0.51  cnf(c_0_189, negated_conjecture, (k5_xboole_0(k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)),k7_subset_1(esk2_0,esk2_0,k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1))))=k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121, c_0_122]), c_0_32]), c_0_32]), c_0_32]), c_0_53])]), ['final']).
% 0.20/0.51  cnf(c_0_190, negated_conjecture, (k5_xboole_0(esk2_0,k7_subset_1(k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)),k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)),esk2_0))=k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123, c_0_96]), c_0_32]), c_0_32]), c_0_32]), c_0_46])]), ['final']).
% 0.20/0.51  cnf(c_0_191, negated_conjecture, (k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,k5_xboole_0(X1,k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)))))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_96]), c_0_32]), c_0_46])]), ['final']).
% 0.20/0.51  cnf(c_0_192, negated_conjecture, (k5_xboole_0(esk2_0,k7_subset_1(k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1)),k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1)),esk2_0))=k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123, c_0_69]), c_0_32]), c_0_32]), c_0_32]), c_0_46])]), ['final']).
% 0.20/0.51  cnf(c_0_193, negated_conjecture, (k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,k5_xboole_0(X1,k7_subset_1(esk2_0,esk2_0,X1)))))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_69]), c_0_32]), c_0_46])]), ['final']).
% 0.20/0.51  cnf(c_0_194, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk2_0,k5_xboole_0(esk2_0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,esk2_0)))))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_27]), c_0_32]), ['final']).
% 0.20/0.51  cnf(c_0_195, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk2_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_46]), c_0_57]), c_0_67]), c_0_32]), ['final']).
% 0.20/0.51  cnf(c_0_196, negated_conjecture, (l1_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_38]), ['final']).
% 0.20/0.51  # SZS output end Saturation
% 0.20/0.51  # Proof object total steps             : 197
% 0.20/0.51  # Proof object clause steps            : 168
% 0.20/0.51  # Proof object formula steps           : 29
% 0.20/0.51  # Proof object conjectures             : 77
% 0.20/0.51  # Proof object clause conjectures      : 74
% 0.20/0.51  # Proof object formula conjectures     : 3
% 0.20/0.51  # Proof object initial clauses used    : 18
% 0.20/0.51  # Proof object initial formulas used   : 14
% 0.20/0.51  # Proof object generating inferences   : 140
% 0.20/0.51  # Proof object simplifying inferences  : 188
% 0.20/0.51  # Parsed axioms                        : 14
% 0.20/0.51  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.51  # Initial clauses                      : 20
% 0.20/0.51  # Removed in clause preprocessing      : 6
% 0.20/0.51  # Initial clauses in saturation        : 14
% 0.20/0.51  # Processed clauses                    : 4025
% 0.20/0.51  # ...of these trivial                  : 141
% 0.20/0.51  # ...subsumed                          : 3641
% 0.20/0.51  # ...remaining for further processing  : 243
% 0.20/0.51  # Other redundant clauses eliminated   : 0
% 0.20/0.51  # Clauses deleted for lack of memory   : 0
% 0.20/0.51  # Backward-subsumed                    : 51
% 0.20/0.51  # Backward-rewritten                   : 52
% 0.20/0.51  # Generated clauses                    : 7038
% 0.20/0.51  # ...of the previous two non-trivial   : 4569
% 0.20/0.51  # Contextual simplify-reflections      : 0
% 0.20/0.51  # Paramodulations                      : 7038
% 0.20/0.51  # Factorizations                       : 0
% 0.20/0.51  # Equation resolutions                 : 0
% 0.20/0.51  # Propositional unsat checks           : 0
% 0.20/0.51  #    Propositional check models        : 0
% 0.20/0.51  #    Propositional check unsatisfiable : 0
% 0.20/0.51  #    Propositional clauses             : 0
% 0.20/0.51  #    Propositional clauses after purity: 0
% 0.20/0.51  #    Propositional unsat core size     : 0
% 0.20/0.51  #    Propositional preprocessing time  : 0.000
% 0.20/0.51  #    Propositional encoding time       : 0.000
% 0.20/0.51  #    Propositional solver time         : 0.000
% 0.20/0.51  #    Success case prop preproc time    : 0.000
% 0.20/0.51  #    Success case prop encoding time   : 0.000
% 0.20/0.51  #    Success case prop solver time     : 0.000
% 0.20/0.51  # Current number of processed clauses  : 126
% 0.20/0.51  #    Positive orientable unit clauses  : 36
% 0.20/0.51  #    Positive unorientable unit clauses: 1
% 0.20/0.51  #    Negative unit clauses             : 0
% 0.20/0.51  #    Non-unit-clauses                  : 89
% 0.20/0.51  # Current number of unprocessed clauses: 0
% 0.20/0.51  # ...number of literals in the above   : 0
% 0.20/0.51  # Current number of archived formulas  : 0
% 0.20/0.51  # Current number of archived clauses   : 121
% 0.20/0.51  # Clause-clause subsumption calls (NU) : 40877
% 0.20/0.51  # Rec. Clause-clause subsumption calls : 36822
% 0.20/0.51  # Non-unit clause-clause subsumptions  : 3690
% 0.20/0.51  # Unit Clause-clause subsumption calls : 108
% 0.20/0.51  # Rewrite failures with RHS unbound    : 0
% 0.20/0.51  # BW rewrite match attempts            : 268
% 0.20/0.51  # BW rewrite match successes           : 41
% 0.20/0.51  # Condensation attempts                : 0
% 0.20/0.51  # Condensation successes               : 0
% 0.20/0.51  # Termbank termtop insertions          : 149159
% 0.20/0.51  
% 0.20/0.51  # -------------------------------------------------
% 0.20/0.51  # User time                : 0.156 s
% 0.20/0.51  # System time              : 0.009 s
% 0.20/0.51  # Total time               : 0.165 s
% 0.20/0.51  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------

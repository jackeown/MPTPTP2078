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
% DateTime   : Thu Dec  3 11:11:20 EST 2020

% Result     : Theorem 4.77s
% Output     : CNFRefutation 4.77s
% Verified   : 
% Statistics : Number of formulae       :  193 (3440 expanded)
%              Number of clauses        :  136 (1577 expanded)
%              Number of leaves         :   28 ( 885 expanded)
%              Depth                    :   20
%              Number of atoms          :  345 (5951 expanded)
%              Number of equality atoms :  123 (2800 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t76_tops_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t74_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k1_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t44_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X1,X2),X3)
     => r1_tarski(X1,k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(t48_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(X2,k2_pre_topc(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(l78_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(t56_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( v3_pre_topc(X2,X1)
                  & r1_tarski(X2,X3) )
               => r1_tarski(X2,k1_tops_1(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).

fof(fc9_tops_1,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => v3_pre_topc(k1_tops_1(X1,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(c_0_28,plain,(
    ! [X10,X11] : k4_xboole_0(X10,X11) = k5_xboole_0(X10,k3_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_29,plain,(
    ! [X48,X49] : k1_setfam_1(k2_tarski(X48,X49)) = k3_xboole_0(X48,X49) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_30,plain,(
    ! [X30,X31] : k4_xboole_0(X30,k4_xboole_0(X30,X31)) = k3_xboole_0(X30,X31) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_31,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_32,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_33,plain,(
    ! [X28,X29] : k4_xboole_0(X28,k2_xboole_0(X28,X29)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

fof(c_0_34,plain,(
    ! [X22] : k4_xboole_0(X22,k1_xboole_0) = X22 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_35,plain,(
    ! [X20,X21] : r1_tarski(k4_xboole_0(X20,X21),X20) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_36,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v3_pre_topc(X2,X1)
            <=> k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t76_tops_1])).

fof(c_0_37,plain,(
    ! [X18,X19] :
      ( ~ r1_tarski(X18,X19)
      | k3_xboole_0(X18,X19) = X18 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_38,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k3_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_39,plain,(
    ! [X23,X24] : k4_xboole_0(k2_xboole_0(X23,X24),X24) = k4_xboole_0(X23,X24) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

cnf(c_0_40,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_41,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_42,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_43,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_44,plain,(
    ! [X14] : k2_xboole_0(X14,k1_xboole_0) = X14 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_45,plain,(
    ! [X12,X13] :
      ( ~ r1_tarski(X12,X13)
      | k2_xboole_0(X12,X13) = X13 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_46,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_47,plain,(
    ! [X32,X33] :
      ( ~ m1_subset_1(X33,k1_zfmisc_1(X32))
      | k3_subset_1(X32,X33) = k4_xboole_0(X32,X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_48,plain,(
    ! [X41,X42,X43] :
      ( ~ m1_subset_1(X42,k1_zfmisc_1(X41))
      | k7_subset_1(X41,X42,X43) = k4_xboole_0(X42,X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

fof(c_0_49,plain,(
    ! [X50,X51] :
      ( ( ~ m1_subset_1(X50,k1_zfmisc_1(X51))
        | r1_tarski(X50,X51) )
      & ( ~ r1_tarski(X50,X51)
        | m1_subset_1(X50,k1_zfmisc_1(X51)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_50,negated_conjecture,
    ( v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & ( ~ v3_pre_topc(esk2_0,esk1_0)
      | k2_tops_1(esk1_0,esk2_0) != k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0) )
    & ( v3_pre_topc(esk2_0,esk1_0)
      | k2_tops_1(esk1_0,esk2_0) = k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_36])])])).

cnf(c_0_51,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_52,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_53,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_54,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))))) = k1_setfam_1(k2_tarski(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_32]),c_0_41]),c_0_41])).

cnf(c_0_55,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k2_xboole_0(X1,X2)))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_42,c_0_41])).

cnf(c_0_56,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_xboole_0))) = X1 ),
    inference(rw,[status(thm)],[c_0_43,c_0_41])).

fof(c_0_57,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_58,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_59,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_60,plain,
    ( r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X1) ),
    inference(rw,[status(thm)],[c_0_46,c_0_41])).

cnf(c_0_61,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

fof(c_0_62,plain,(
    ! [X68,X69] :
      ( ~ l1_pre_topc(X68)
      | ~ m1_subset_1(X69,k1_zfmisc_1(u1_struct_0(X68)))
      | k1_tops_1(X68,X69) = k7_subset_1(u1_struct_0(X68),X69,k2_tops_1(X68,X69)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_tops_1])])])).

cnf(c_0_63,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

fof(c_0_64,plain,(
    ! [X15,X16,X17] :
      ( ~ r1_tarski(X15,X16)
      | ~ r1_tarski(X16,X17)
      | r1_tarski(X15,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_65,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_66,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_67,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_51,c_0_32])).

cnf(c_0_68,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k1_setfam_1(k2_tarski(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_32]),c_0_32])).

cnf(c_0_69,plain,
    ( k5_xboole_0(k2_xboole_0(X1,X2),k1_setfam_1(k2_tarski(k2_xboole_0(X1,X2),X2))) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_41]),c_0_41])).

cnf(c_0_70,plain,
    ( k1_setfam_1(k2_tarski(X1,k2_xboole_0(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56])).

cnf(c_0_71,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_72,plain,
    ( k1_xboole_0 = X1
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_73,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_54])).

fof(c_0_74,plain,(
    ! [X8,X9] :
      ( ( r1_tarski(X8,X9)
        | X8 != X9 )
      & ( r1_tarski(X9,X8)
        | X8 != X9 )
      & ( ~ r1_tarski(X8,X9)
        | ~ r1_tarski(X9,X8)
        | X8 = X9 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_75,plain,(
    ! [X25,X26,X27] :
      ( ~ r1_tarski(k4_xboole_0(X25,X26),X27)
      | r1_tarski(X25,k2_xboole_0(X26,X27)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).

cnf(c_0_76,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_61,c_0_41])).

cnf(c_0_77,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_78,plain,
    ( k1_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_79,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_80,plain,
    ( k7_subset_1(X2,X1,X3) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_63,c_0_41])).

cnf(c_0_81,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_82,negated_conjecture,
    ( r1_tarski(esk2_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_83,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_84,plain,
    ( k5_xboole_0(k2_xboole_0(X1,X2),k1_setfam_1(k2_tarski(X2,k2_xboole_0(X1,X2)))) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_69,c_0_68])).

cnf(c_0_85,plain,
    ( k1_setfam_1(k2_tarski(X1,k2_xboole_0(X2,X1))) = X1 ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_86,plain,
    ( k1_setfam_1(k2_tarski(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_87,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_88,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_89,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k3_subset_1(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_90,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk2_0,k2_tops_1(esk1_0,esk2_0)) = k1_tops_1(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_66]),c_0_79])])).

cnf(c_0_91,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1) = k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1))) ),
    inference(spm,[status(thm)],[c_0_80,c_0_66])).

cnf(c_0_92,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_93,plain,
    ( r1_tarski(k5_xboole_0(X1,X2),X1)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_83])).

cnf(c_0_94,plain,
    ( k5_xboole_0(k2_xboole_0(X1,X2),X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_95,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X1))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_55,c_0_58])).

cnf(c_0_96,plain,
    ( k1_setfam_1(k2_tarski(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_68,c_0_86])).

cnf(c_0_97,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_86]),c_0_58]),c_0_56])).

cnf(c_0_98,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_87])).

cnf(c_0_99,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X3) ),
    inference(rw,[status(thm)],[c_0_88,c_0_41])).

fof(c_0_100,plain,(
    ! [X57,X58] :
      ( ~ l1_pre_topc(X57)
      | ~ m1_subset_1(X58,k1_zfmisc_1(u1_struct_0(X57)))
      | r1_tarski(X58,k2_pre_topc(X57,X58)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_pre_topc])])])).

cnf(c_0_101,plain,
    ( k5_xboole_0(X1,X2) = k3_subset_1(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_89,c_0_83])).

cnf(c_0_102,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_setfam_1(k2_tarski(X1,X2))))) = k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))))) ),
    inference(spm,[status(thm)],[c_0_54,c_0_54])).

cnf(c_0_103,negated_conjecture,
    ( k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,k2_tops_1(esk1_0,esk2_0)))) = k1_tops_1(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_104,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X2,esk2_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_81,c_0_92])).

cnf(c_0_105,plain,
    ( r1_tarski(k5_xboole_0(k2_xboole_0(X1,X2),X2),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_73])])).

fof(c_0_106,plain,(
    ! [X39,X40] :
      ( ~ m1_subset_1(X40,k1_zfmisc_1(X39))
      | k3_subset_1(X39,k3_subset_1(X39,X40)) = X40 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

cnf(c_0_107,plain,
    ( k1_setfam_1(k2_tarski(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_95]),c_0_96]),c_0_97])).

cnf(c_0_108,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_67]),c_0_98])])).

cnf(c_0_109,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_99,c_0_60])).

fof(c_0_110,plain,(
    ! [X47] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X47)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_111,plain,
    ( r1_tarski(X2,k2_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_100])).

cnf(c_0_112,plain,
    ( k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))))) = k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,k1_setfam_1(k2_tarski(X1,X2))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_102]),c_0_73])])).

cnf(c_0_113,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))) = k1_setfam_1(k2_tarski(X1,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_83]),c_0_60])])).

cnf(c_0_114,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_103])).

cnf(c_0_115,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,k5_xboole_0(k2_xboole_0(esk2_0,X2),X2)) ),
    inference(spm,[status(thm)],[c_0_104,c_0_105])).

cnf(c_0_116,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_106])).

cnf(c_0_117,plain,
    ( k5_xboole_0(k2_xboole_0(X1,X1),X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_70]),c_0_107]),c_0_108])).

cnf(c_0_118,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_109,c_0_71])).

cnf(c_0_119,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_110])).

cnf(c_0_120,negated_conjecture,
    ( r1_tarski(esk2_0,k2_pre_topc(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_66]),c_0_79])])).

cnf(c_0_121,plain,
    ( k5_xboole_0(X1,k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,k1_setfam_1(k2_tarski(X1,X2)))))) = k1_setfam_1(k2_tarski(X1,X2)) ),
    inference(rw,[status(thm)],[c_0_54,c_0_112])).

cnf(c_0_122,plain,
    ( k5_xboole_0(X1,k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,X2)))) = k1_setfam_1(k2_tarski(X1,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_101]),c_0_73])])).

cnf(c_0_123,negated_conjecture,
    ( r1_tarski(X1,esk2_0)
    | ~ r1_tarski(X1,k1_tops_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_81,c_0_114])).

cnf(c_0_124,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k5_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_99,c_0_83])).

cnf(c_0_125,negated_conjecture,
    ( r1_tarski(k5_xboole_0(k2_xboole_0(esk2_0,X1),X1),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_115,c_0_98])).

cnf(c_0_126,plain,
    ( k3_subset_1(X1,k3_subset_1(X1,X2)) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_116,c_0_77])).

cnf(c_0_127,plain,
    ( k3_subset_1(k2_xboole_0(X1,X1),X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_101]),c_0_118])])).

cnf(c_0_128,plain,
    ( k3_subset_1(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_119]),c_0_56])).

fof(c_0_129,plain,(
    ! [X55,X56] :
      ( ~ l1_pre_topc(X55)
      | ~ m1_subset_1(X56,k1_zfmisc_1(u1_struct_0(X55)))
      | m1_subset_1(k2_pre_topc(X55,X56),k1_zfmisc_1(u1_struct_0(X55))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

cnf(c_0_130,negated_conjecture,
    ( r1_tarski(X1,k2_pre_topc(esk1_0,esk2_0))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_81,c_0_120])).

fof(c_0_131,plain,(
    ! [X34,X35] :
      ( ~ m1_subset_1(X35,k1_zfmisc_1(X34))
      | m1_subset_1(k3_subset_1(X34,X35),k1_zfmisc_1(X34)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

cnf(c_0_132,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1)))))) = k1_setfam_1(k2_tarski(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_68])).

cnf(c_0_133,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_setfam_1(k2_tarski(X1,X2))))) = k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,k1_setfam_1(k2_tarski(X1,X2))))) ),
    inference(rw,[status(thm)],[c_0_102,c_0_112])).

cnf(c_0_134,plain,
    ( k1_setfam_1(k2_tarski(X1,k1_setfam_1(k2_tarski(X1,X2)))) = k1_setfam_1(k2_tarski(X1,X2)) ),
    inference(rw,[status(thm)],[c_0_121,c_0_122])).

cnf(c_0_135,negated_conjecture,
    ( r1_tarski(k5_xboole_0(k2_xboole_0(k1_tops_1(esk1_0,esk2_0),X1),X1),esk2_0) ),
    inference(spm,[status(thm)],[c_0_123,c_0_105])).

cnf(c_0_136,negated_conjecture,
    ( r1_tarski(k2_xboole_0(esk2_0,X1),k2_xboole_0(X1,u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_125]),c_0_109])])).

cnf(c_0_137,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_127]),c_0_128]),c_0_118])])).

cnf(c_0_138,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_129])).

fof(c_0_139,plain,(
    ! [X61,X62] :
      ( ~ l1_pre_topc(X61)
      | ~ m1_subset_1(X62,k1_zfmisc_1(u1_struct_0(X61)))
      | k2_tops_1(X61,X62) = k7_subset_1(u1_struct_0(X61),k2_pre_topc(X61,X62),k1_tops_1(X61,X62)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l78_tops_1])])])).

cnf(c_0_140,plain,
    ( k7_subset_1(X1,X2,X3) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3)))
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_80,c_0_77])).

cnf(c_0_141,negated_conjecture,
    ( r1_tarski(X1,k2_xboole_0(X2,k2_pre_topc(esk1_0,esk2_0)))
    | ~ r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),esk2_0) ),
    inference(spm,[status(thm)],[c_0_99,c_0_130])).

cnf(c_0_142,negated_conjecture,
    ( r1_tarski(k5_xboole_0(k1_tops_1(esk1_0,esk2_0),k1_setfam_1(k2_tarski(k1_tops_1(esk1_0,esk2_0),X1))),esk2_0) ),
    inference(spm,[status(thm)],[c_0_123,c_0_60])).

cnf(c_0_143,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_131])).

cnf(c_0_144,plain,
    ( k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,X2))) = k3_subset_1(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_101]),c_0_73])])).

cnf(c_0_145,plain,
    ( k5_xboole_0(k2_xboole_0(X1,X2),k1_setfam_1(k2_tarski(k2_xboole_0(X1,X2),k5_xboole_0(k2_xboole_0(X1,X2),X1)))) = X1 ),
    inference(spm,[status(thm)],[c_0_132,c_0_70])).

cnf(c_0_146,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_133,c_0_134]),c_0_134])).

cnf(c_0_147,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))) = k3_subset_1(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_89,c_0_68])).

cnf(c_0_148,negated_conjecture,
    ( r1_tarski(k2_xboole_0(k1_tops_1(esk1_0,esk2_0),X1),k2_xboole_0(X1,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_135]),c_0_109])])).

cnf(c_0_149,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_150,negated_conjecture,
    ( r1_tarski(k2_xboole_0(esk2_0,u1_struct_0(esk1_0)),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_136,c_0_137])).

cnf(c_0_151,plain,
    ( r1_tarski(k2_pre_topc(X1,X2),u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_65,c_0_138])).

cnf(c_0_152,plain,
    ( k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_139])).

cnf(c_0_153,plain,
    ( k7_subset_1(X1,X2,X3) = k3_subset_1(X2,X3)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_89,c_0_140])).

cnf(c_0_154,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk2_0),k2_xboole_0(X1,k2_pre_topc(esk1_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_141,c_0_142])).

cnf(c_0_155,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_58,c_0_71])).

cnf(c_0_156,plain,
    ( m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_setfam_1(k2_tarski(X1,X2)),k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_143,c_0_144])).

cnf(c_0_157,plain,
    ( k3_subset_1(k2_xboole_0(X1,X2),k1_setfam_1(k2_tarski(k2_xboole_0(X1,X2),k5_xboole_0(k2_xboole_0(X1,X2),X1)))) = X1 ),
    inference(rw,[status(thm)],[c_0_145,c_0_146])).

cnf(c_0_158,plain,
    ( k5_xboole_0(k2_xboole_0(X1,X2),X1) = k3_subset_1(k2_xboole_0(X1,X2),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_147,c_0_70]),c_0_118])])).

cnf(c_0_159,negated_conjecture,
    ( r1_tarski(k2_xboole_0(k1_tops_1(esk1_0,esk2_0),X1),k2_xboole_0(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_148,c_0_71])).

cnf(c_0_160,negated_conjecture,
    ( k2_xboole_0(esk2_0,u1_struct_0(esk1_0)) = u1_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_149,c_0_150]),c_0_109])])).

fof(c_0_161,plain,(
    ! [X63,X64,X65] :
      ( ~ l1_pre_topc(X63)
      | ~ m1_subset_1(X64,k1_zfmisc_1(u1_struct_0(X63)))
      | ~ m1_subset_1(X65,k1_zfmisc_1(u1_struct_0(X63)))
      | ~ v3_pre_topc(X64,X63)
      | ~ r1_tarski(X64,X65)
      | r1_tarski(X64,k1_tops_1(X63,X65)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_tops_1])])])).

cnf(c_0_162,negated_conjecture,
    ( v3_pre_topc(esk2_0,esk1_0)
    | k2_tops_1(esk1_0,esk2_0) = k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_163,negated_conjecture,
    ( r1_tarski(k2_pre_topc(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_151,c_0_66]),c_0_79])])).

cnf(c_0_164,plain,
    ( k3_subset_1(k2_pre_topc(X1,X2),k1_tops_1(X1,X2)) = k2_tops_1(X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k1_tops_1(X1,X2),k2_pre_topc(X1,X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_152,c_0_153]),c_0_151])).

cnf(c_0_165,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk2_0),k2_pre_topc(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_154,c_0_155])).

cnf(c_0_166,plain,
    ( m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_156,c_0_77]),c_0_73])])).

cnf(c_0_167,plain,
    ( k3_subset_1(k2_xboole_0(X1,X2),k1_setfam_1(k2_tarski(k2_xboole_0(X1,X2),k3_subset_1(k2_xboole_0(X1,X2),X1)))) = X1 ),
    inference(rw,[status(thm)],[c_0_157,c_0_158])).

cnf(c_0_168,negated_conjecture,
    ( r1_tarski(k2_xboole_0(k1_tops_1(esk1_0,esk2_0),u1_struct_0(esk1_0)),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_159,c_0_160])).

cnf(c_0_169,plain,
    ( r1_tarski(X2,k1_tops_1(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X2,X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_161])).

cnf(c_0_170,negated_conjecture,
    ( k3_subset_1(k2_pre_topc(esk1_0,esk2_0),esk2_0) = k2_tops_1(esk1_0,esk2_0)
    | v3_pre_topc(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_162,c_0_153]),c_0_120]),c_0_163])])).

cnf(c_0_171,negated_conjecture,
    ( k3_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_tops_1(esk1_0,esk2_0)) = k2_tops_1(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_164,c_0_66]),c_0_79]),c_0_165])])).

fof(c_0_172,plain,(
    ! [X59,X60] :
      ( ~ v2_pre_topc(X59)
      | ~ l1_pre_topc(X59)
      | ~ m1_subset_1(X60,k1_zfmisc_1(u1_struct_0(X59)))
      | v3_pre_topc(k1_tops_1(X59,X60),X59) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).

cnf(c_0_173,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_xboole_0(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_166,c_0_167]),c_0_73])])).

cnf(c_0_174,negated_conjecture,
    ( k2_xboole_0(k1_tops_1(esk1_0,esk2_0),u1_struct_0(esk1_0)) = u1_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_149,c_0_168]),c_0_109])])).

cnf(c_0_175,negated_conjecture,
    ( r1_tarski(X1,k1_tops_1(esk1_0,esk2_0))
    | ~ v3_pre_topc(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_169,c_0_66]),c_0_79])])).

cnf(c_0_176,negated_conjecture,
    ( k3_subset_1(k2_pre_topc(esk1_0,esk2_0),k2_tops_1(esk1_0,esk2_0)) = esk2_0
    | v3_pre_topc(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_170]),c_0_120])])).

cnf(c_0_177,negated_conjecture,
    ( k3_subset_1(k2_pre_topc(esk1_0,esk2_0),k2_tops_1(esk1_0,esk2_0)) = k1_tops_1(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_171]),c_0_165])])).

cnf(c_0_178,negated_conjecture,
    ( ~ v3_pre_topc(esk2_0,esk1_0)
    | k2_tops_1(esk1_0,esk2_0) != k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_179,plain,
    ( k7_subset_1(X1,X2,X3) = k3_subset_1(X2,k1_setfam_1(k2_tarski(X2,X3)))
    | ~ r1_tarski(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_140]),c_0_73])])).

cnf(c_0_180,plain,
    ( v3_pre_topc(k1_tops_1(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_172])).

cnf(c_0_181,negated_conjecture,
    ( m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_173,c_0_174])).

cnf(c_0_182,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_183,negated_conjecture,
    ( r1_tarski(X1,k1_tops_1(esk1_0,esk2_0))
    | ~ v3_pre_topc(X1,esk1_0)
    | ~ r1_tarski(X1,esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_175,c_0_77]),c_0_92])).

cnf(c_0_184,negated_conjecture,
    ( k1_tops_1(esk1_0,esk2_0) = esk2_0
    | v3_pre_topc(esk2_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_176,c_0_177])).

cnf(c_0_185,negated_conjecture,
    ( k1_tops_1(esk1_0,esk2_0) = esk2_0
    | ~ r1_tarski(esk2_0,k1_tops_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_149,c_0_114])).

cnf(c_0_186,negated_conjecture,
    ( k3_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_setfam_1(k2_tarski(esk2_0,k2_pre_topc(esk1_0,esk2_0)))) != k2_tops_1(esk1_0,esk2_0)
    | ~ v3_pre_topc(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_178,c_0_179]),c_0_68]),c_0_163])])).

cnf(c_0_187,negated_conjecture,
    ( v3_pre_topc(k1_tops_1(esk1_0,k1_tops_1(esk1_0,esk2_0)),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_180,c_0_181]),c_0_182]),c_0_79])])).

cnf(c_0_188,negated_conjecture,
    ( k1_tops_1(esk1_0,esk2_0) = esk2_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_183,c_0_184]),c_0_98])]),c_0_185])).

cnf(c_0_189,negated_conjecture,
    ( k3_subset_1(k2_pre_topc(esk1_0,esk2_0),esk2_0) != k2_tops_1(esk1_0,esk2_0)
    | ~ v3_pre_topc(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_186,c_0_67]),c_0_120])])).

cnf(c_0_190,negated_conjecture,
    ( v3_pre_topc(esk2_0,esk1_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_187,c_0_188]),c_0_188])).

cnf(c_0_191,negated_conjecture,
    ( k3_subset_1(k2_pre_topc(esk1_0,esk2_0),esk2_0) != k2_tops_1(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_189,c_0_190])])).

cnf(c_0_192,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_171,c_0_188]),c_0_191]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 14:41:07 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 4.77/5.00  # AutoSched0-Mode selected heuristic G_E___107_C36_F1_PI_AE_Q4_CS_SP_PS_S0Y
% 4.77/5.00  # and selection function SelectMaxLComplexAvoidPosPred.
% 4.77/5.00  #
% 4.77/5.00  # Preprocessing time       : 0.029 s
% 4.77/5.00  # Presaturation interreduction done
% 4.77/5.00  
% 4.77/5.00  # Proof found!
% 4.77/5.00  # SZS status Theorem
% 4.77/5.00  # SZS output start CNFRefutation
% 4.77/5.00  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.77/5.00  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 4.77/5.00  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.77/5.00  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 4.77/5.00  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 4.77/5.00  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.77/5.00  fof(t76_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_tops_1)).
% 4.77/5.00  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.77/5.00  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.77/5.00  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 4.77/5.00  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 4.77/5.00  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.77/5.00  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 4.77/5.00  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 4.77/5.00  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.77/5.00  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.77/5.00  fof(t74_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k1_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tops_1)).
% 4.77/5.00  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.77/5.00  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.77/5.00  fof(t44_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k4_xboole_0(X1,X2),X3)=>r1_tarski(X1,k2_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 4.77/5.00  fof(t48_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(X2,k2_pre_topc(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_pre_topc)).
% 4.77/5.00  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 4.77/5.00  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 4.77/5.00  fof(dt_k2_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 4.77/5.00  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 4.77/5.00  fof(l78_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 4.77/5.00  fof(t56_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v3_pre_topc(X2,X1)&r1_tarski(X2,X3))=>r1_tarski(X2,k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tops_1)).
% 4.77/5.00  fof(fc9_tops_1, axiom, ![X1, X2]:(((v2_pre_topc(X1)&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v3_pre_topc(k1_tops_1(X1,X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 4.77/5.00  fof(c_0_28, plain, ![X10, X11]:k4_xboole_0(X10,X11)=k5_xboole_0(X10,k3_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 4.77/5.00  fof(c_0_29, plain, ![X48, X49]:k1_setfam_1(k2_tarski(X48,X49))=k3_xboole_0(X48,X49), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 4.77/5.00  fof(c_0_30, plain, ![X30, X31]:k4_xboole_0(X30,k4_xboole_0(X30,X31))=k3_xboole_0(X30,X31), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 4.77/5.00  cnf(c_0_31, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 4.77/5.00  cnf(c_0_32, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 4.77/5.00  fof(c_0_33, plain, ![X28, X29]:k4_xboole_0(X28,k2_xboole_0(X28,X29))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 4.77/5.00  fof(c_0_34, plain, ![X22]:k4_xboole_0(X22,k1_xboole_0)=X22, inference(variable_rename,[status(thm)],[t3_boole])).
% 4.77/5.00  fof(c_0_35, plain, ![X20, X21]:r1_tarski(k4_xboole_0(X20,X21),X20), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 4.77/5.00  fof(c_0_36, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2))))), inference(assume_negation,[status(cth)],[t76_tops_1])).
% 4.77/5.00  fof(c_0_37, plain, ![X18, X19]:(~r1_tarski(X18,X19)|k3_xboole_0(X18,X19)=X18), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 4.77/5.00  fof(c_0_38, plain, ![X6, X7]:k3_xboole_0(X6,X7)=k3_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 4.77/5.00  fof(c_0_39, plain, ![X23, X24]:k4_xboole_0(k2_xboole_0(X23,X24),X24)=k4_xboole_0(X23,X24), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 4.77/5.00  cnf(c_0_40, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 4.77/5.00  cnf(c_0_41, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_31, c_0_32])).
% 4.77/5.00  cnf(c_0_42, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_33])).
% 4.77/5.00  cnf(c_0_43, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_34])).
% 4.77/5.00  fof(c_0_44, plain, ![X14]:k2_xboole_0(X14,k1_xboole_0)=X14, inference(variable_rename,[status(thm)],[t1_boole])).
% 4.77/5.00  fof(c_0_45, plain, ![X12, X13]:(~r1_tarski(X12,X13)|k2_xboole_0(X12,X13)=X13), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 4.77/5.00  cnf(c_0_46, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 4.77/5.00  fof(c_0_47, plain, ![X32, X33]:(~m1_subset_1(X33,k1_zfmisc_1(X32))|k3_subset_1(X32,X33)=k4_xboole_0(X32,X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 4.77/5.00  fof(c_0_48, plain, ![X41, X42, X43]:(~m1_subset_1(X42,k1_zfmisc_1(X41))|k7_subset_1(X41,X42,X43)=k4_xboole_0(X42,X43)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 4.77/5.00  fof(c_0_49, plain, ![X50, X51]:((~m1_subset_1(X50,k1_zfmisc_1(X51))|r1_tarski(X50,X51))&(~r1_tarski(X50,X51)|m1_subset_1(X50,k1_zfmisc_1(X51)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 4.77/5.00  fof(c_0_50, negated_conjecture, ((v2_pre_topc(esk1_0)&l1_pre_topc(esk1_0))&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&((~v3_pre_topc(esk2_0,esk1_0)|k2_tops_1(esk1_0,esk2_0)!=k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0))&(v3_pre_topc(esk2_0,esk1_0)|k2_tops_1(esk1_0,esk2_0)=k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_36])])])).
% 4.77/5.00  cnf(c_0_51, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 4.77/5.00  cnf(c_0_52, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 4.77/5.00  cnf(c_0_53, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 4.77/5.00  cnf(c_0_54, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))))))=k1_setfam_1(k2_tarski(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_32]), c_0_41]), c_0_41])).
% 4.77/5.00  cnf(c_0_55, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k2_xboole_0(X1,X2))))=k1_xboole_0), inference(rw,[status(thm)],[c_0_42, c_0_41])).
% 4.77/5.00  cnf(c_0_56, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_xboole_0)))=X1), inference(rw,[status(thm)],[c_0_43, c_0_41])).
% 4.77/5.00  fof(c_0_57, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 4.77/5.00  cnf(c_0_58, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_44])).
% 4.77/5.00  cnf(c_0_59, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 4.77/5.00  cnf(c_0_60, plain, (r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X1)), inference(rw,[status(thm)],[c_0_46, c_0_41])).
% 4.77/5.00  cnf(c_0_61, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 4.77/5.00  fof(c_0_62, plain, ![X68, X69]:(~l1_pre_topc(X68)|(~m1_subset_1(X69,k1_zfmisc_1(u1_struct_0(X68)))|k1_tops_1(X68,X69)=k7_subset_1(u1_struct_0(X68),X69,k2_tops_1(X68,X69)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_tops_1])])])).
% 4.77/5.00  cnf(c_0_63, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 4.77/5.00  fof(c_0_64, plain, ![X15, X16, X17]:(~r1_tarski(X15,X16)|~r1_tarski(X16,X17)|r1_tarski(X15,X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 4.77/5.00  cnf(c_0_65, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 4.77/5.00  cnf(c_0_66, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 4.77/5.00  cnf(c_0_67, plain, (k1_setfam_1(k2_tarski(X1,X2))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_51, c_0_32])).
% 4.77/5.00  cnf(c_0_68, plain, (k1_setfam_1(k2_tarski(X1,X2))=k1_setfam_1(k2_tarski(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_32]), c_0_32])).
% 4.77/5.00  cnf(c_0_69, plain, (k5_xboole_0(k2_xboole_0(X1,X2),k1_setfam_1(k2_tarski(k2_xboole_0(X1,X2),X2)))=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_41]), c_0_41])).
% 4.77/5.00  cnf(c_0_70, plain, (k1_setfam_1(k2_tarski(X1,k2_xboole_0(X1,X2)))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56])).
% 4.77/5.00  cnf(c_0_71, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 4.77/5.00  cnf(c_0_72, plain, (k1_xboole_0=X1|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 4.77/5.00  cnf(c_0_73, plain, (r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X1)), inference(spm,[status(thm)],[c_0_60, c_0_54])).
% 4.77/5.00  fof(c_0_74, plain, ![X8, X9]:(((r1_tarski(X8,X9)|X8!=X9)&(r1_tarski(X9,X8)|X8!=X9))&(~r1_tarski(X8,X9)|~r1_tarski(X9,X8)|X8=X9)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 4.77/5.00  fof(c_0_75, plain, ![X25, X26, X27]:(~r1_tarski(k4_xboole_0(X25,X26),X27)|r1_tarski(X25,k2_xboole_0(X26,X27))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).
% 4.77/5.00  cnf(c_0_76, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_61, c_0_41])).
% 4.77/5.00  cnf(c_0_77, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 4.77/5.00  cnf(c_0_78, plain, (k1_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_62])).
% 4.77/5.00  cnf(c_0_79, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 4.77/5.00  cnf(c_0_80, plain, (k7_subset_1(X2,X1,X3)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_63, c_0_41])).
% 4.77/5.00  cnf(c_0_81, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 4.77/5.00  cnf(c_0_82, negated_conjecture, (r1_tarski(esk2_0,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 4.77/5.00  cnf(c_0_83, plain, (k1_setfam_1(k2_tarski(X1,X2))=X2|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 4.77/5.00  cnf(c_0_84, plain, (k5_xboole_0(k2_xboole_0(X1,X2),k1_setfam_1(k2_tarski(X2,k2_xboole_0(X1,X2))))=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_69, c_0_68])).
% 4.77/5.00  cnf(c_0_85, plain, (k1_setfam_1(k2_tarski(X1,k2_xboole_0(X2,X1)))=X1), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 4.77/5.00  cnf(c_0_86, plain, (k1_setfam_1(k2_tarski(k1_xboole_0,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 4.77/5.00  cnf(c_0_87, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_74])).
% 4.77/5.00  cnf(c_0_88, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 4.77/5.00  cnf(c_0_89, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k3_subset_1(X1,X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 4.77/5.00  cnf(c_0_90, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk2_0,k2_tops_1(esk1_0,esk2_0))=k1_tops_1(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_66]), c_0_79])])).
% 4.77/5.00  cnf(c_0_91, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)=k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1)))), inference(spm,[status(thm)],[c_0_80, c_0_66])).
% 4.77/5.00  cnf(c_0_92, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 4.77/5.00  cnf(c_0_93, plain, (r1_tarski(k5_xboole_0(X1,X2),X1)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_60, c_0_83])).
% 4.77/5.00  cnf(c_0_94, plain, (k5_xboole_0(k2_xboole_0(X1,X2),X2)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_84, c_0_85])).
% 4.77/5.00  cnf(c_0_95, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X1)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_55, c_0_58])).
% 4.77/5.00  cnf(c_0_96, plain, (k1_setfam_1(k2_tarski(X1,k1_xboole_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_68, c_0_86])).
% 4.77/5.00  cnf(c_0_97, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_86]), c_0_58]), c_0_56])).
% 4.77/5.00  cnf(c_0_98, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_87])).
% 4.77/5.00  cnf(c_0_99, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X3)), inference(rw,[status(thm)],[c_0_88, c_0_41])).
% 4.77/5.00  fof(c_0_100, plain, ![X57, X58]:(~l1_pre_topc(X57)|(~m1_subset_1(X58,k1_zfmisc_1(u1_struct_0(X57)))|r1_tarski(X58,k2_pre_topc(X57,X58)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_pre_topc])])])).
% 4.77/5.00  cnf(c_0_101, plain, (k5_xboole_0(X1,X2)=k3_subset_1(X1,X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_89, c_0_83])).
% 4.77/5.00  cnf(c_0_102, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_setfam_1(k2_tarski(X1,X2)))))=k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))))), inference(spm,[status(thm)],[c_0_54, c_0_54])).
% 4.77/5.00  cnf(c_0_103, negated_conjecture, (k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,k2_tops_1(esk1_0,esk2_0))))=k1_tops_1(esk1_0,esk2_0)), inference(rw,[status(thm)],[c_0_90, c_0_91])).
% 4.77/5.00  cnf(c_0_104, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X2,esk2_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_81, c_0_92])).
% 4.77/5.00  cnf(c_0_105, plain, (r1_tarski(k5_xboole_0(k2_xboole_0(X1,X2),X2),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_73])])).
% 4.77/5.00  fof(c_0_106, plain, ![X39, X40]:(~m1_subset_1(X40,k1_zfmisc_1(X39))|k3_subset_1(X39,k3_subset_1(X39,X40))=X40), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 4.77/5.00  cnf(c_0_107, plain, (k1_setfam_1(k2_tarski(X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_95]), c_0_96]), c_0_97])).
% 4.77/5.00  cnf(c_0_108, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_67]), c_0_98])])).
% 4.77/5.00  cnf(c_0_109, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_99, c_0_60])).
% 4.77/5.00  fof(c_0_110, plain, ![X47]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X47)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 4.77/5.00  cnf(c_0_111, plain, (r1_tarski(X2,k2_pre_topc(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_100])).
% 4.77/5.00  cnf(c_0_112, plain, (k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))))=k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,k1_setfam_1(k2_tarski(X1,X2)))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_102]), c_0_73])])).
% 4.77/5.00  cnf(c_0_113, plain, (k5_xboole_0(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))))=k1_setfam_1(k2_tarski(X1,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_83]), c_0_60])])).
% 4.77/5.00  cnf(c_0_114, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,esk2_0),esk2_0)), inference(spm,[status(thm)],[c_0_60, c_0_103])).
% 4.77/5.00  cnf(c_0_115, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X1,k5_xboole_0(k2_xboole_0(esk2_0,X2),X2))), inference(spm,[status(thm)],[c_0_104, c_0_105])).
% 4.77/5.00  cnf(c_0_116, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_106])).
% 4.77/5.00  cnf(c_0_117, plain, (k5_xboole_0(k2_xboole_0(X1,X1),X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_70]), c_0_107]), c_0_108])).
% 4.77/5.00  cnf(c_0_118, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_109, c_0_71])).
% 4.77/5.00  cnf(c_0_119, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_110])).
% 4.77/5.00  cnf(c_0_120, negated_conjecture, (r1_tarski(esk2_0,k2_pre_topc(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_66]), c_0_79])])).
% 4.77/5.00  cnf(c_0_121, plain, (k5_xboole_0(X1,k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,k1_setfam_1(k2_tarski(X1,X2))))))=k1_setfam_1(k2_tarski(X1,X2))), inference(rw,[status(thm)],[c_0_54, c_0_112])).
% 4.77/5.00  cnf(c_0_122, plain, (k5_xboole_0(X1,k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,X2))))=k1_setfam_1(k2_tarski(X1,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_101]), c_0_73])])).
% 4.77/5.00  cnf(c_0_123, negated_conjecture, (r1_tarski(X1,esk2_0)|~r1_tarski(X1,k1_tops_1(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_81, c_0_114])).
% 4.77/5.00  cnf(c_0_124, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k5_xboole_0(X1,X2),X3)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_99, c_0_83])).
% 4.77/5.00  cnf(c_0_125, negated_conjecture, (r1_tarski(k5_xboole_0(k2_xboole_0(esk2_0,X1),X1),u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_115, c_0_98])).
% 4.77/5.00  cnf(c_0_126, plain, (k3_subset_1(X1,k3_subset_1(X1,X2))=X2|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_116, c_0_77])).
% 4.77/5.00  cnf(c_0_127, plain, (k3_subset_1(k2_xboole_0(X1,X1),X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_101]), c_0_118])])).
% 4.77/5.00  cnf(c_0_128, plain, (k3_subset_1(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_119]), c_0_56])).
% 4.77/5.00  fof(c_0_129, plain, ![X55, X56]:(~l1_pre_topc(X55)|~m1_subset_1(X56,k1_zfmisc_1(u1_struct_0(X55)))|m1_subset_1(k2_pre_topc(X55,X56),k1_zfmisc_1(u1_struct_0(X55)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).
% 4.77/5.00  cnf(c_0_130, negated_conjecture, (r1_tarski(X1,k2_pre_topc(esk1_0,esk2_0))|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_81, c_0_120])).
% 4.77/5.00  fof(c_0_131, plain, ![X34, X35]:(~m1_subset_1(X35,k1_zfmisc_1(X34))|m1_subset_1(k3_subset_1(X34,X35),k1_zfmisc_1(X34))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 4.77/5.00  cnf(c_0_132, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))))))=k1_setfam_1(k2_tarski(X2,X1))), inference(spm,[status(thm)],[c_0_54, c_0_68])).
% 4.77/5.00  cnf(c_0_133, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_setfam_1(k2_tarski(X1,X2)))))=k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,k1_setfam_1(k2_tarski(X1,X2)))))), inference(rw,[status(thm)],[c_0_102, c_0_112])).
% 4.77/5.00  cnf(c_0_134, plain, (k1_setfam_1(k2_tarski(X1,k1_setfam_1(k2_tarski(X1,X2))))=k1_setfam_1(k2_tarski(X1,X2))), inference(rw,[status(thm)],[c_0_121, c_0_122])).
% 4.77/5.00  cnf(c_0_135, negated_conjecture, (r1_tarski(k5_xboole_0(k2_xboole_0(k1_tops_1(esk1_0,esk2_0),X1),X1),esk2_0)), inference(spm,[status(thm)],[c_0_123, c_0_105])).
% 4.77/5.00  cnf(c_0_136, negated_conjecture, (r1_tarski(k2_xboole_0(esk2_0,X1),k2_xboole_0(X1,u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124, c_0_125]), c_0_109])])).
% 4.77/5.00  cnf(c_0_137, plain, (k2_xboole_0(X1,X1)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126, c_0_127]), c_0_128]), c_0_118])])).
% 4.77/5.00  cnf(c_0_138, plain, (m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_129])).
% 4.77/5.00  fof(c_0_139, plain, ![X61, X62]:(~l1_pre_topc(X61)|(~m1_subset_1(X62,k1_zfmisc_1(u1_struct_0(X61)))|k2_tops_1(X61,X62)=k7_subset_1(u1_struct_0(X61),k2_pre_topc(X61,X62),k1_tops_1(X61,X62)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l78_tops_1])])])).
% 4.77/5.00  cnf(c_0_140, plain, (k7_subset_1(X1,X2,X3)=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3)))|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_80, c_0_77])).
% 4.77/5.00  cnf(c_0_141, negated_conjecture, (r1_tarski(X1,k2_xboole_0(X2,k2_pre_topc(esk1_0,esk2_0)))|~r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),esk2_0)), inference(spm,[status(thm)],[c_0_99, c_0_130])).
% 4.77/5.00  cnf(c_0_142, negated_conjecture, (r1_tarski(k5_xboole_0(k1_tops_1(esk1_0,esk2_0),k1_setfam_1(k2_tarski(k1_tops_1(esk1_0,esk2_0),X1))),esk2_0)), inference(spm,[status(thm)],[c_0_123, c_0_60])).
% 4.77/5.00  cnf(c_0_143, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_131])).
% 4.77/5.00  cnf(c_0_144, plain, (k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,X2)))=k3_subset_1(X1,X2)|~r1_tarski(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_101]), c_0_73])])).
% 4.77/5.00  cnf(c_0_145, plain, (k5_xboole_0(k2_xboole_0(X1,X2),k1_setfam_1(k2_tarski(k2_xboole_0(X1,X2),k5_xboole_0(k2_xboole_0(X1,X2),X1))))=X1), inference(spm,[status(thm)],[c_0_132, c_0_70])).
% 4.77/5.00  cnf(c_0_146, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_133, c_0_134]), c_0_134])).
% 4.77/5.00  cnf(c_0_147, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1)))=k3_subset_1(X1,X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_89, c_0_68])).
% 4.77/5.00  cnf(c_0_148, negated_conjecture, (r1_tarski(k2_xboole_0(k1_tops_1(esk1_0,esk2_0),X1),k2_xboole_0(X1,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124, c_0_135]), c_0_109])])).
% 4.77/5.00  cnf(c_0_149, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_74])).
% 4.77/5.00  cnf(c_0_150, negated_conjecture, (r1_tarski(k2_xboole_0(esk2_0,u1_struct_0(esk1_0)),u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_136, c_0_137])).
% 4.77/5.00  cnf(c_0_151, plain, (r1_tarski(k2_pre_topc(X1,X2),u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_65, c_0_138])).
% 4.77/5.00  cnf(c_0_152, plain, (k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_139])).
% 4.77/5.00  cnf(c_0_153, plain, (k7_subset_1(X1,X2,X3)=k3_subset_1(X2,X3)|~r1_tarski(X3,X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_89, c_0_140])).
% 4.77/5.00  cnf(c_0_154, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,esk2_0),k2_xboole_0(X1,k2_pre_topc(esk1_0,esk2_0)))), inference(spm,[status(thm)],[c_0_141, c_0_142])).
% 4.77/5.00  cnf(c_0_155, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_58, c_0_71])).
% 4.77/5.00  cnf(c_0_156, plain, (m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))|~m1_subset_1(k1_setfam_1(k2_tarski(X1,X2)),k1_zfmisc_1(X1))|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_143, c_0_144])).
% 4.77/5.00  cnf(c_0_157, plain, (k3_subset_1(k2_xboole_0(X1,X2),k1_setfam_1(k2_tarski(k2_xboole_0(X1,X2),k5_xboole_0(k2_xboole_0(X1,X2),X1))))=X1), inference(rw,[status(thm)],[c_0_145, c_0_146])).
% 4.77/5.00  cnf(c_0_158, plain, (k5_xboole_0(k2_xboole_0(X1,X2),X1)=k3_subset_1(k2_xboole_0(X1,X2),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_147, c_0_70]), c_0_118])])).
% 4.77/5.00  cnf(c_0_159, negated_conjecture, (r1_tarski(k2_xboole_0(k1_tops_1(esk1_0,esk2_0),X1),k2_xboole_0(esk2_0,X1))), inference(spm,[status(thm)],[c_0_148, c_0_71])).
% 4.77/5.00  cnf(c_0_160, negated_conjecture, (k2_xboole_0(esk2_0,u1_struct_0(esk1_0))=u1_struct_0(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_149, c_0_150]), c_0_109])])).
% 4.77/5.00  fof(c_0_161, plain, ![X63, X64, X65]:(~l1_pre_topc(X63)|(~m1_subset_1(X64,k1_zfmisc_1(u1_struct_0(X63)))|(~m1_subset_1(X65,k1_zfmisc_1(u1_struct_0(X63)))|(~v3_pre_topc(X64,X63)|~r1_tarski(X64,X65)|r1_tarski(X64,k1_tops_1(X63,X65)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_tops_1])])])).
% 4.77/5.00  cnf(c_0_162, negated_conjecture, (v3_pre_topc(esk2_0,esk1_0)|k2_tops_1(esk1_0,esk2_0)=k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 4.77/5.00  cnf(c_0_163, negated_conjecture, (r1_tarski(k2_pre_topc(esk1_0,esk2_0),u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_151, c_0_66]), c_0_79])])).
% 4.77/5.00  cnf(c_0_164, plain, (k3_subset_1(k2_pre_topc(X1,X2),k1_tops_1(X1,X2))=k2_tops_1(X1,X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k1_tops_1(X1,X2),k2_pre_topc(X1,X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_152, c_0_153]), c_0_151])).
% 4.77/5.00  cnf(c_0_165, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,esk2_0),k2_pre_topc(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_154, c_0_155])).
% 4.77/5.00  cnf(c_0_166, plain, (m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))|~r1_tarski(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_156, c_0_77]), c_0_73])])).
% 4.77/5.00  cnf(c_0_167, plain, (k3_subset_1(k2_xboole_0(X1,X2),k1_setfam_1(k2_tarski(k2_xboole_0(X1,X2),k3_subset_1(k2_xboole_0(X1,X2),X1))))=X1), inference(rw,[status(thm)],[c_0_157, c_0_158])).
% 4.77/5.00  cnf(c_0_168, negated_conjecture, (r1_tarski(k2_xboole_0(k1_tops_1(esk1_0,esk2_0),u1_struct_0(esk1_0)),u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_159, c_0_160])).
% 4.77/5.00  cnf(c_0_169, plain, (r1_tarski(X2,k1_tops_1(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v3_pre_topc(X2,X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_161])).
% 4.77/5.00  cnf(c_0_170, negated_conjecture, (k3_subset_1(k2_pre_topc(esk1_0,esk2_0),esk2_0)=k2_tops_1(esk1_0,esk2_0)|v3_pre_topc(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_162, c_0_153]), c_0_120]), c_0_163])])).
% 4.77/5.00  cnf(c_0_171, negated_conjecture, (k3_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_tops_1(esk1_0,esk2_0))=k2_tops_1(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_164, c_0_66]), c_0_79]), c_0_165])])).
% 4.77/5.00  fof(c_0_172, plain, ![X59, X60]:(~v2_pre_topc(X59)|~l1_pre_topc(X59)|~m1_subset_1(X60,k1_zfmisc_1(u1_struct_0(X59)))|v3_pre_topc(k1_tops_1(X59,X60),X59)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).
% 4.77/5.00  cnf(c_0_173, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_xboole_0(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_166, c_0_167]), c_0_73])])).
% 4.77/5.00  cnf(c_0_174, negated_conjecture, (k2_xboole_0(k1_tops_1(esk1_0,esk2_0),u1_struct_0(esk1_0))=u1_struct_0(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_149, c_0_168]), c_0_109])])).
% 4.77/5.00  cnf(c_0_175, negated_conjecture, (r1_tarski(X1,k1_tops_1(esk1_0,esk2_0))|~v3_pre_topc(X1,esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_169, c_0_66]), c_0_79])])).
% 4.77/5.00  cnf(c_0_176, negated_conjecture, (k3_subset_1(k2_pre_topc(esk1_0,esk2_0),k2_tops_1(esk1_0,esk2_0))=esk2_0|v3_pre_topc(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126, c_0_170]), c_0_120])])).
% 4.77/5.00  cnf(c_0_177, negated_conjecture, (k3_subset_1(k2_pre_topc(esk1_0,esk2_0),k2_tops_1(esk1_0,esk2_0))=k1_tops_1(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126, c_0_171]), c_0_165])])).
% 4.77/5.00  cnf(c_0_178, negated_conjecture, (~v3_pre_topc(esk2_0,esk1_0)|k2_tops_1(esk1_0,esk2_0)!=k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 4.77/5.00  cnf(c_0_179, plain, (k7_subset_1(X1,X2,X3)=k3_subset_1(X2,k1_setfam_1(k2_tarski(X2,X3)))|~r1_tarski(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_140]), c_0_73])])).
% 4.77/5.00  cnf(c_0_180, plain, (v3_pre_topc(k1_tops_1(X1,X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_172])).
% 4.77/5.00  cnf(c_0_181, negated_conjecture, (m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_173, c_0_174])).
% 4.77/5.00  cnf(c_0_182, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 4.77/5.00  cnf(c_0_183, negated_conjecture, (r1_tarski(X1,k1_tops_1(esk1_0,esk2_0))|~v3_pre_topc(X1,esk1_0)|~r1_tarski(X1,esk2_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_175, c_0_77]), c_0_92])).
% 4.77/5.00  cnf(c_0_184, negated_conjecture, (k1_tops_1(esk1_0,esk2_0)=esk2_0|v3_pre_topc(esk2_0,esk1_0)), inference(spm,[status(thm)],[c_0_176, c_0_177])).
% 4.77/5.00  cnf(c_0_185, negated_conjecture, (k1_tops_1(esk1_0,esk2_0)=esk2_0|~r1_tarski(esk2_0,k1_tops_1(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_149, c_0_114])).
% 4.77/5.00  cnf(c_0_186, negated_conjecture, (k3_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_setfam_1(k2_tarski(esk2_0,k2_pre_topc(esk1_0,esk2_0))))!=k2_tops_1(esk1_0,esk2_0)|~v3_pre_topc(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_178, c_0_179]), c_0_68]), c_0_163])])).
% 4.77/5.00  cnf(c_0_187, negated_conjecture, (v3_pre_topc(k1_tops_1(esk1_0,k1_tops_1(esk1_0,esk2_0)),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_180, c_0_181]), c_0_182]), c_0_79])])).
% 4.77/5.00  cnf(c_0_188, negated_conjecture, (k1_tops_1(esk1_0,esk2_0)=esk2_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_183, c_0_184]), c_0_98])]), c_0_185])).
% 4.77/5.00  cnf(c_0_189, negated_conjecture, (k3_subset_1(k2_pre_topc(esk1_0,esk2_0),esk2_0)!=k2_tops_1(esk1_0,esk2_0)|~v3_pre_topc(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_186, c_0_67]), c_0_120])])).
% 4.77/5.00  cnf(c_0_190, negated_conjecture, (v3_pre_topc(esk2_0,esk1_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_187, c_0_188]), c_0_188])).
% 4.77/5.00  cnf(c_0_191, negated_conjecture, (k3_subset_1(k2_pre_topc(esk1_0,esk2_0),esk2_0)!=k2_tops_1(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_189, c_0_190])])).
% 4.77/5.00  cnf(c_0_192, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_171, c_0_188]), c_0_191]), ['proof']).
% 4.77/5.00  # SZS output end CNFRefutation
% 4.77/5.00  # Proof object total steps             : 193
% 4.77/5.00  # Proof object clause steps            : 136
% 4.77/5.00  # Proof object formula steps           : 57
% 4.77/5.00  # Proof object conjectures             : 49
% 4.77/5.00  # Proof object clause conjectures      : 46
% 4.77/5.00  # Proof object formula conjectures     : 3
% 4.77/5.00  # Proof object initial clauses used    : 34
% 4.77/5.00  # Proof object initial formulas used   : 28
% 4.77/5.00  # Proof object generating inferences   : 78
% 4.77/5.00  # Proof object simplifying inferences  : 104
% 4.77/5.00  # Training examples: 0 positive, 0 negative
% 4.77/5.00  # Parsed axioms                        : 32
% 4.77/5.00  # Removed by relevancy pruning/SinE    : 0
% 4.77/5.00  # Initial clauses                      : 39
% 4.77/5.00  # Removed in clause preprocessing      : 2
% 4.77/5.00  # Initial clauses in saturation        : 37
% 4.77/5.00  # Processed clauses                    : 48339
% 4.77/5.00  # ...of these trivial                  : 910
% 4.77/5.00  # ...subsumed                          : 40986
% 4.77/5.00  # ...remaining for further processing  : 6442
% 4.77/5.00  # Other redundant clauses eliminated   : 2
% 4.77/5.00  # Clauses deleted for lack of memory   : 0
% 4.77/5.00  # Backward-subsumed                    : 697
% 4.77/5.00  # Backward-rewritten                   : 1460
% 4.77/5.00  # Generated clauses                    : 610204
% 4.77/5.00  # ...of the previous two non-trivial   : 521219
% 4.77/5.00  # Contextual simplify-reflections      : 187
% 4.77/5.00  # Paramodulations                      : 610202
% 4.77/5.00  # Factorizations                       : 0
% 4.77/5.00  # Equation resolutions                 : 2
% 4.77/5.00  # Propositional unsat checks           : 0
% 4.77/5.00  #    Propositional check models        : 0
% 4.77/5.00  #    Propositional check unsatisfiable : 0
% 4.77/5.00  #    Propositional clauses             : 0
% 4.77/5.00  #    Propositional clauses after purity: 0
% 4.77/5.00  #    Propositional unsat core size     : 0
% 4.77/5.00  #    Propositional preprocessing time  : 0.000
% 4.77/5.00  #    Propositional encoding time       : 0.000
% 4.77/5.00  #    Propositional solver time         : 0.000
% 4.77/5.00  #    Success case prop preproc time    : 0.000
% 4.77/5.00  #    Success case prop encoding time   : 0.000
% 4.77/5.00  #    Success case prop solver time     : 0.000
% 4.77/5.00  # Current number of processed clauses  : 4247
% 4.77/5.00  #    Positive orientable unit clauses  : 689
% 4.77/5.00  #    Positive unorientable unit clauses: 5
% 4.77/5.00  #    Negative unit clauses             : 145
% 4.77/5.00  #    Non-unit-clauses                  : 3408
% 4.77/5.00  # Current number of unprocessed clauses: 463706
% 4.77/5.00  # ...number of literals in the above   : 1238999
% 4.77/5.00  # Current number of archived formulas  : 0
% 4.77/5.00  # Current number of archived clauses   : 2195
% 4.77/5.00  # Clause-clause subsumption calls (NU) : 2473142
% 4.77/5.00  # Rec. Clause-clause subsumption calls : 1866816
% 4.77/5.00  # Non-unit clause-clause subsumptions  : 20633
% 4.77/5.00  # Unit Clause-clause subsumption calls : 58138
% 4.77/5.00  # Rewrite failures with RHS unbound    : 0
% 4.77/5.00  # BW rewrite match attempts            : 19611
% 4.77/5.00  # BW rewrite match successes           : 680
% 4.77/5.00  # Condensation attempts                : 0
% 4.77/5.00  # Condensation successes               : 0
% 4.77/5.00  # Termbank termtop insertions          : 10370703
% 4.77/5.02  
% 4.77/5.02  # -------------------------------------------------
% 4.77/5.02  # User time                : 4.495 s
% 4.77/5.02  # System time              : 0.178 s
% 4.77/5.02  # Total time               : 4.673 s
% 4.77/5.02  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:11:47 EST 2020

% Result     : Theorem 0.39s
% Output     : CNFRefutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   95 (1160 expanded)
%              Number of clauses        :   60 ( 538 expanded)
%              Number of leaves         :   17 ( 298 expanded)
%              Depth                    :   18
%              Number of atoms          :  193 (2097 expanded)
%              Number of equality atoms :   74 ( 889 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    9 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t44_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X1,X2),X3)
     => r1_tarski(X1,k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t77_tops_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v4_pre_topc(X2,X1)
          <=> k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k1_tops_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t52_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ( v4_pre_topc(X2,X1)
             => k2_pre_topc(X1,X2) = X2 )
            & ( ( v2_pre_topc(X1)
                & k2_pre_topc(X1,X2) = X2 )
             => v4_pre_topc(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(dt_k2_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(t65_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_pre_topc(X1,X2) = k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

fof(fc1_tops_1,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => v4_pre_topc(k2_pre_topc(X1,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).

fof(l78_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(c_0_17,plain,(
    ! [X18,X19,X20] :
      ( ~ r1_tarski(k4_xboole_0(X18,X19),X20)
      | r1_tarski(X18,k2_xboole_0(X19,X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).

fof(c_0_18,plain,(
    ! [X13,X14] : r1_tarski(k4_xboole_0(X13,X14),X13) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_20,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_21,plain,(
    ! [X10] : k2_xboole_0(X10,k1_xboole_0) = X10 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_22,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | X6 != X7 )
      & ( r1_tarski(X7,X6)
        | X6 != X7 )
      & ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,X6)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_24,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_25,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_26,plain,(
    ! [X21,X22] : k4_xboole_0(X21,k4_xboole_0(X21,X22)) = k3_xboole_0(X21,X22) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_27,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

fof(c_0_33,plain,(
    ! [X11,X12] :
      ( ~ r1_tarski(X11,X12)
      | k3_xboole_0(X11,X12) = X11 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_35,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_31]),c_0_31])).

cnf(c_0_36,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_32,c_0_20])).

cnf(c_0_37,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_34])).

cnf(c_0_39,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

fof(c_0_40,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v4_pre_topc(X2,X1)
            <=> k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k1_tops_1(X1,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t77_tops_1])).

fof(c_0_41,plain,(
    ! [X15,X16,X17] : k4_xboole_0(k4_xboole_0(X15,X16),X17) = k4_xboole_0(X15,k2_xboole_0(X16,X17)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

fof(c_0_42,plain,(
    ! [X8,X9] :
      ( ~ r1_tarski(X8,X9)
      | k2_xboole_0(X8,X9) = X9 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_43,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_37,c_0_31])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,k4_xboole_0(X1,k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_24])).

fof(c_0_45,plain,(
    ! [X31,X32] :
      ( ( ~ v4_pre_topc(X32,X31)
        | k2_pre_topc(X31,X32) = X32
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
        | ~ l1_pre_topc(X31) )
      & ( ~ v2_pre_topc(X31)
        | k2_pre_topc(X31,X32) != X32
        | v4_pre_topc(X32,X31)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
        | ~ l1_pre_topc(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).

fof(c_0_46,negated_conjecture,
    ( v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & ( ~ v4_pre_topc(esk2_0,esk1_0)
      | k2_tops_1(esk1_0,esk2_0) != k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0)) )
    & ( v4_pre_topc(esk2_0,esk1_0)
      | k2_tops_1(esk1_0,esk2_0) = k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_40])])])).

cnf(c_0_47,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_48,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_49,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_39])).

cnf(c_0_50,plain,
    ( k2_pre_topc(X2,X1) = X1
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

fof(c_0_53,plain,(
    ! [X26,X27,X28] :
      ( ~ m1_subset_1(X27,k1_zfmisc_1(X26))
      | k7_subset_1(X26,X27,X28) = k4_xboole_0(X27,X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

cnf(c_0_54,plain,
    ( r1_tarski(k4_xboole_0(k4_xboole_0(X1,X2),X3),X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_47])).

cnf(c_0_55,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),X1) = X1 ),
    inference(spm,[status(thm)],[c_0_48,c_0_20])).

cnf(c_0_56,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_39,c_0_49])).

fof(c_0_57,plain,(
    ! [X33,X34] :
      ( ~ l1_pre_topc(X33)
      | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))
      | m1_subset_1(k2_tops_1(X33,X34),k1_zfmisc_1(u1_struct_0(X33))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_1])])).

cnf(c_0_58,negated_conjecture,
    ( k2_pre_topc(esk1_0,esk2_0) = esk2_0
    | ~ v4_pre_topc(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])])).

cnf(c_0_59,negated_conjecture,
    ( v4_pre_topc(esk2_0,esk1_0)
    | k2_tops_1(esk1_0,esk2_0) = k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_60,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_61,plain,
    ( r1_tarski(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4))
    | ~ r1_tarski(k4_xboole_0(k4_xboole_0(X1,X2),X3),X4) ),
    inference(spm,[status(thm)],[c_0_19,c_0_47])).

cnf(c_0_62,plain,
    ( r1_tarski(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3),X2) ),
    inference(spm,[status(thm)],[c_0_54,c_0_35])).

cnf(c_0_63,plain,
    ( k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X2) = X2 ),
    inference(spm,[status(thm)],[c_0_55,c_0_35])).

cnf(c_0_64,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),X1),X2) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_47,c_0_56])).

fof(c_0_65,plain,(
    ! [X23,X24,X25] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(X23))
      | ~ m1_subset_1(X25,k1_zfmisc_1(X23))
      | k4_subset_1(X23,X24,X25) = k2_xboole_0(X24,X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_66,plain,
    ( m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

fof(c_0_67,plain,(
    ! [X39,X40] :
      ( ~ l1_pre_topc(X39)
      | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))
      | k2_pre_topc(X39,X40) = k4_subset_1(u1_struct_0(X39),X40,k2_tops_1(X39,X40)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_tops_1])])])).

cnf(c_0_68,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0)) = k2_tops_1(esk1_0,esk2_0)
    | k2_pre_topc(esk1_0,esk2_0) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_69,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1) = k4_xboole_0(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_51])).

cnf(c_0_70,plain,
    ( r1_tarski(X1,k2_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X3),X2)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_71,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),X1),X2) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_49])).

cnf(c_0_72,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_73,negated_conjecture,
    ( m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_51]),c_0_52])])).

cnf(c_0_74,plain,
    ( k2_pre_topc(X1,X2) = k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

fof(c_0_75,plain,(
    ! [X35,X36] :
      ( ~ v2_pre_topc(X35)
      | ~ l1_pre_topc(X35)
      | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))
      | v4_pre_topc(k2_pre_topc(X35,X36),X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_tops_1])])).

cnf(c_0_76,negated_conjecture,
    ( k4_xboole_0(esk2_0,k1_tops_1(esk1_0,esk2_0)) = k2_tops_1(esk1_0,esk2_0)
    | k2_pre_topc(esk1_0,esk2_0) = esk2_0 ),
    inference(rw,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_77,plain,
    ( r1_tarski(k2_xboole_0(X1,X2),k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_78,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),X1,k2_tops_1(esk1_0,esk2_0)) = k2_xboole_0(X1,k2_tops_1(esk1_0,esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_79,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),esk2_0,k2_tops_1(esk1_0,esk2_0)) = k2_pre_topc(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_51]),c_0_52])])).

cnf(c_0_80,plain,
    ( v4_pre_topc(k2_pre_topc(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_81,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_82,negated_conjecture,
    ( k2_xboole_0(k2_tops_1(esk1_0,esk2_0),esk2_0) = esk2_0
    | k2_pre_topc(esk1_0,esk2_0) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_55,c_0_76])).

cnf(c_0_83,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_77]),c_0_77])])).

cnf(c_0_84,negated_conjecture,
    ( k2_xboole_0(esk2_0,k2_tops_1(esk1_0,esk2_0)) = k2_pre_topc(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_51]),c_0_79])).

fof(c_0_85,plain,(
    ! [X37,X38] :
      ( ~ l1_pre_topc(X37)
      | ~ m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X37)))
      | k2_tops_1(X37,X38) = k7_subset_1(u1_struct_0(X37),k2_pre_topc(X37,X38),k1_tops_1(X37,X38)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l78_tops_1])])])).

cnf(c_0_86,negated_conjecture,
    ( ~ v4_pre_topc(esk2_0,esk1_0)
    | k2_tops_1(esk1_0,esk2_0) != k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_87,negated_conjecture,
    ( v4_pre_topc(k2_pre_topc(esk1_0,esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_51]),c_0_81]),c_0_52])])).

cnf(c_0_88,negated_conjecture,
    ( k2_pre_topc(esk1_0,esk2_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_83]),c_0_84])])).

cnf(c_0_89,plain,
    ( k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_90,negated_conjecture,
    ( k4_xboole_0(esk2_0,k1_tops_1(esk1_0,esk2_0)) != k2_tops_1(esk1_0,esk2_0)
    | ~ v4_pre_topc(esk2_0,esk1_0) ),
    inference(rw,[status(thm)],[c_0_86,c_0_69])).

cnf(c_0_91,negated_conjecture,
    ( v4_pre_topc(esk2_0,esk1_0) ),
    inference(rw,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_92,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),k1_tops_1(esk1_0,esk2_0)) = k2_tops_1(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_51]),c_0_52])])).

cnf(c_0_93,negated_conjecture,
    ( k4_xboole_0(esk2_0,k1_tops_1(esk1_0,esk2_0)) != k2_tops_1(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_90,c_0_91])])).

cnf(c_0_94,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_92,c_0_88]),c_0_69]),c_0_93]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:06:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.39/0.54  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S2mI
% 0.39/0.54  # and selection function SelectCQArNTNpEqFirst.
% 0.39/0.54  #
% 0.39/0.54  # Preprocessing time       : 0.028 s
% 0.39/0.54  # Presaturation interreduction done
% 0.39/0.54  
% 0.39/0.54  # Proof found!
% 0.39/0.54  # SZS status Theorem
% 0.39/0.54  # SZS output start CNFRefutation
% 0.39/0.54  fof(t44_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k4_xboole_0(X1,X2),X3)=>r1_tarski(X1,k2_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 0.39/0.54  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.39/0.54  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 0.39/0.54  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.39/0.54  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.39/0.54  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.39/0.54  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.39/0.54  fof(t77_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)<=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k1_tops_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tops_1)).
% 0.39/0.54  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.39/0.54  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.39/0.54  fof(t52_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v4_pre_topc(X2,X1)=>k2_pre_topc(X1,X2)=X2)&((v2_pre_topc(X1)&k2_pre_topc(X1,X2)=X2)=>v4_pre_topc(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 0.39/0.54  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 0.39/0.54  fof(dt_k2_tops_1, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 0.39/0.54  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 0.39/0.54  fof(t65_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_pre_topc(X1,X2)=k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 0.39/0.54  fof(fc1_tops_1, axiom, ![X1, X2]:(((v2_pre_topc(X1)&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v4_pre_topc(k2_pre_topc(X1,X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_tops_1)).
% 0.39/0.54  fof(l78_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 0.39/0.54  fof(c_0_17, plain, ![X18, X19, X20]:(~r1_tarski(k4_xboole_0(X18,X19),X20)|r1_tarski(X18,k2_xboole_0(X19,X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).
% 0.39/0.54  fof(c_0_18, plain, ![X13, X14]:r1_tarski(k4_xboole_0(X13,X14),X13), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.39/0.54  cnf(c_0_19, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.39/0.54  cnf(c_0_20, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.39/0.54  fof(c_0_21, plain, ![X10]:k2_xboole_0(X10,k1_xboole_0)=X10, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.39/0.54  fof(c_0_22, plain, ![X6, X7]:(((r1_tarski(X6,X7)|X6!=X7)&(r1_tarski(X7,X6)|X6!=X7))&(~r1_tarski(X6,X7)|~r1_tarski(X7,X6)|X6=X7)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.39/0.54  cnf(c_0_23, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.39/0.54  cnf(c_0_24, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.39/0.54  fof(c_0_25, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.39/0.54  fof(c_0_26, plain, ![X21, X22]:k4_xboole_0(X21,k4_xboole_0(X21,X22))=k3_xboole_0(X21,X22), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.39/0.54  cnf(c_0_27, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.39/0.54  cnf(c_0_28, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.39/0.54  cnf(c_0_29, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.39/0.54  cnf(c_0_30, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.39/0.54  cnf(c_0_31, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.39/0.54  cnf(c_0_32, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.39/0.54  fof(c_0_33, plain, ![X11, X12]:(~r1_tarski(X11,X12)|k3_xboole_0(X11,X12)=X11), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.39/0.54  cnf(c_0_34, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_29])).
% 0.39/0.54  cnf(c_0_35, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_31]), c_0_31])).
% 0.39/0.54  cnf(c_0_36, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_32, c_0_20])).
% 0.39/0.54  cnf(c_0_37, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.39/0.54  cnf(c_0_38, plain, (r1_tarski(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_19, c_0_34])).
% 0.39/0.54  cnf(c_0_39, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.39/0.54  fof(c_0_40, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)<=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k1_tops_1(X1,X2)))))), inference(assume_negation,[status(cth)],[t77_tops_1])).
% 0.39/0.54  fof(c_0_41, plain, ![X15, X16, X17]:k4_xboole_0(k4_xboole_0(X15,X16),X17)=k4_xboole_0(X15,k2_xboole_0(X16,X17)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.39/0.54  fof(c_0_42, plain, ![X8, X9]:(~r1_tarski(X8,X9)|k2_xboole_0(X8,X9)=X9), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.39/0.54  cnf(c_0_43, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_37, c_0_31])).
% 0.39/0.54  cnf(c_0_44, plain, (r1_tarski(X1,k4_xboole_0(X1,k1_xboole_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_24])).
% 0.39/0.54  fof(c_0_45, plain, ![X31, X32]:((~v4_pre_topc(X32,X31)|k2_pre_topc(X31,X32)=X32|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))|~l1_pre_topc(X31))&(~v2_pre_topc(X31)|k2_pre_topc(X31,X32)!=X32|v4_pre_topc(X32,X31)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))|~l1_pre_topc(X31))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).
% 0.39/0.54  fof(c_0_46, negated_conjecture, ((v2_pre_topc(esk1_0)&l1_pre_topc(esk1_0))&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&((~v4_pre_topc(esk2_0,esk1_0)|k2_tops_1(esk1_0,esk2_0)!=k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0)))&(v4_pre_topc(esk2_0,esk1_0)|k2_tops_1(esk1_0,esk2_0)=k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_40])])])).
% 0.39/0.54  cnf(c_0_47, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.39/0.54  cnf(c_0_48, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.39/0.54  cnf(c_0_49, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_39])).
% 0.39/0.54  cnf(c_0_50, plain, (k2_pre_topc(X2,X1)=X1|~v4_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.39/0.54  cnf(c_0_51, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.39/0.54  cnf(c_0_52, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.39/0.54  fof(c_0_53, plain, ![X26, X27, X28]:(~m1_subset_1(X27,k1_zfmisc_1(X26))|k7_subset_1(X26,X27,X28)=k4_xboole_0(X27,X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 0.39/0.54  cnf(c_0_54, plain, (r1_tarski(k4_xboole_0(k4_xboole_0(X1,X2),X3),X1)), inference(spm,[status(thm)],[c_0_20, c_0_47])).
% 0.39/0.54  cnf(c_0_55, plain, (k2_xboole_0(k4_xboole_0(X1,X2),X1)=X1), inference(spm,[status(thm)],[c_0_48, c_0_20])).
% 0.39/0.54  cnf(c_0_56, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_39, c_0_49])).
% 0.39/0.54  fof(c_0_57, plain, ![X33, X34]:(~l1_pre_topc(X33)|~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))|m1_subset_1(k2_tops_1(X33,X34),k1_zfmisc_1(u1_struct_0(X33)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_1])])).
% 0.39/0.54  cnf(c_0_58, negated_conjecture, (k2_pre_topc(esk1_0,esk2_0)=esk2_0|~v4_pre_topc(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52])])).
% 0.39/0.54  cnf(c_0_59, negated_conjecture, (v4_pre_topc(esk2_0,esk1_0)|k2_tops_1(esk1_0,esk2_0)=k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.39/0.54  cnf(c_0_60, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.39/0.54  cnf(c_0_61, plain, (r1_tarski(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4))|~r1_tarski(k4_xboole_0(k4_xboole_0(X1,X2),X3),X4)), inference(spm,[status(thm)],[c_0_19, c_0_47])).
% 0.39/0.54  cnf(c_0_62, plain, (r1_tarski(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3),X2)), inference(spm,[status(thm)],[c_0_54, c_0_35])).
% 0.39/0.54  cnf(c_0_63, plain, (k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X2)=X2), inference(spm,[status(thm)],[c_0_55, c_0_35])).
% 0.39/0.54  cnf(c_0_64, plain, (k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),X1),X2)=k1_xboole_0), inference(spm,[status(thm)],[c_0_47, c_0_56])).
% 0.39/0.54  fof(c_0_65, plain, ![X23, X24, X25]:(~m1_subset_1(X24,k1_zfmisc_1(X23))|~m1_subset_1(X25,k1_zfmisc_1(X23))|k4_subset_1(X23,X24,X25)=k2_xboole_0(X24,X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 0.39/0.54  cnf(c_0_66, plain, (m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.39/0.54  fof(c_0_67, plain, ![X39, X40]:(~l1_pre_topc(X39)|(~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))|k2_pre_topc(X39,X40)=k4_subset_1(u1_struct_0(X39),X40,k2_tops_1(X39,X40)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_tops_1])])])).
% 0.39/0.54  cnf(c_0_68, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0))=k2_tops_1(esk1_0,esk2_0)|k2_pre_topc(esk1_0,esk2_0)=esk2_0), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.39/0.54  cnf(c_0_69, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)=k4_xboole_0(esk2_0,X1)), inference(spm,[status(thm)],[c_0_60, c_0_51])).
% 0.39/0.54  cnf(c_0_70, plain, (r1_tarski(X1,k2_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X3),X2))), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.39/0.54  cnf(c_0_71, plain, (k2_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),X1),X2)=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_49])).
% 0.39/0.54  cnf(c_0_72, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.39/0.54  cnf(c_0_73, negated_conjecture, (m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_51]), c_0_52])])).
% 0.39/0.54  cnf(c_0_74, plain, (k2_pre_topc(X1,X2)=k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.39/0.54  fof(c_0_75, plain, ![X35, X36]:(~v2_pre_topc(X35)|~l1_pre_topc(X35)|~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))|v4_pre_topc(k2_pre_topc(X35,X36),X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_tops_1])])).
% 0.39/0.54  cnf(c_0_76, negated_conjecture, (k4_xboole_0(esk2_0,k1_tops_1(esk1_0,esk2_0))=k2_tops_1(esk1_0,esk2_0)|k2_pre_topc(esk1_0,esk2_0)=esk2_0), inference(rw,[status(thm)],[c_0_68, c_0_69])).
% 0.39/0.54  cnf(c_0_77, plain, (r1_tarski(k2_xboole_0(X1,X2),k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.39/0.54  cnf(c_0_78, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),X1,k2_tops_1(esk1_0,esk2_0))=k2_xboole_0(X1,k2_tops_1(esk1_0,esk2_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.39/0.54  cnf(c_0_79, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),esk2_0,k2_tops_1(esk1_0,esk2_0))=k2_pre_topc(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_51]), c_0_52])])).
% 0.39/0.54  cnf(c_0_80, plain, (v4_pre_topc(k2_pre_topc(X1,X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.39/0.54  cnf(c_0_81, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.39/0.54  cnf(c_0_82, negated_conjecture, (k2_xboole_0(k2_tops_1(esk1_0,esk2_0),esk2_0)=esk2_0|k2_pre_topc(esk1_0,esk2_0)=esk2_0), inference(spm,[status(thm)],[c_0_55, c_0_76])).
% 0.39/0.54  cnf(c_0_83, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_77]), c_0_77])])).
% 0.39/0.54  cnf(c_0_84, negated_conjecture, (k2_xboole_0(esk2_0,k2_tops_1(esk1_0,esk2_0))=k2_pre_topc(esk1_0,esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_51]), c_0_79])).
% 0.39/0.54  fof(c_0_85, plain, ![X37, X38]:(~l1_pre_topc(X37)|(~m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X37)))|k2_tops_1(X37,X38)=k7_subset_1(u1_struct_0(X37),k2_pre_topc(X37,X38),k1_tops_1(X37,X38)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l78_tops_1])])])).
% 0.39/0.54  cnf(c_0_86, negated_conjecture, (~v4_pre_topc(esk2_0,esk1_0)|k2_tops_1(esk1_0,esk2_0)!=k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.39/0.54  cnf(c_0_87, negated_conjecture, (v4_pre_topc(k2_pre_topc(esk1_0,esk2_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_51]), c_0_81]), c_0_52])])).
% 0.39/0.54  cnf(c_0_88, negated_conjecture, (k2_pre_topc(esk1_0,esk2_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82, c_0_83]), c_0_84])])).
% 0.39/0.54  cnf(c_0_89, plain, (k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_85])).
% 0.39/0.54  cnf(c_0_90, negated_conjecture, (k4_xboole_0(esk2_0,k1_tops_1(esk1_0,esk2_0))!=k2_tops_1(esk1_0,esk2_0)|~v4_pre_topc(esk2_0,esk1_0)), inference(rw,[status(thm)],[c_0_86, c_0_69])).
% 0.39/0.54  cnf(c_0_91, negated_conjecture, (v4_pre_topc(esk2_0,esk1_0)), inference(rw,[status(thm)],[c_0_87, c_0_88])).
% 0.39/0.54  cnf(c_0_92, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),k1_tops_1(esk1_0,esk2_0))=k2_tops_1(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_51]), c_0_52])])).
% 0.39/0.54  cnf(c_0_93, negated_conjecture, (k4_xboole_0(esk2_0,k1_tops_1(esk1_0,esk2_0))!=k2_tops_1(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_90, c_0_91])])).
% 0.39/0.54  cnf(c_0_94, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_92, c_0_88]), c_0_69]), c_0_93]), ['proof']).
% 0.39/0.54  # SZS output end CNFRefutation
% 0.39/0.54  # Proof object total steps             : 95
% 0.39/0.54  # Proof object clause steps            : 60
% 0.39/0.54  # Proof object formula steps           : 35
% 0.39/0.54  # Proof object conjectures             : 24
% 0.39/0.54  # Proof object clause conjectures      : 21
% 0.39/0.54  # Proof object formula conjectures     : 3
% 0.39/0.54  # Proof object initial clauses used    : 22
% 0.39/0.54  # Proof object initial formulas used   : 17
% 0.39/0.54  # Proof object generating inferences   : 28
% 0.39/0.54  # Proof object simplifying inferences  : 33
% 0.39/0.54  # Training examples: 0 positive, 0 negative
% 0.39/0.54  # Parsed axioms                        : 18
% 0.39/0.54  # Removed by relevancy pruning/SinE    : 0
% 0.39/0.54  # Initial clauses                      : 26
% 0.39/0.54  # Removed in clause preprocessing      : 1
% 0.39/0.54  # Initial clauses in saturation        : 25
% 0.39/0.54  # Processed clauses                    : 1919
% 0.39/0.54  # ...of these trivial                  : 251
% 0.39/0.54  # ...subsumed                          : 749
% 0.39/0.54  # ...remaining for further processing  : 918
% 0.39/0.54  # Other redundant clauses eliminated   : 2
% 0.39/0.54  # Clauses deleted for lack of memory   : 0
% 0.39/0.54  # Backward-subsumed                    : 1
% 0.39/0.54  # Backward-rewritten                   : 269
% 0.39/0.54  # Generated clauses                    : 19855
% 0.39/0.54  # ...of the previous two non-trivial   : 10747
% 0.39/0.54  # Contextual simplify-reflections      : 0
% 0.39/0.54  # Paramodulations                      : 19853
% 0.39/0.54  # Factorizations                       : 0
% 0.39/0.54  # Equation resolutions                 : 2
% 0.39/0.54  # Propositional unsat checks           : 0
% 0.39/0.54  #    Propositional check models        : 0
% 0.39/0.54  #    Propositional check unsatisfiable : 0
% 0.39/0.54  #    Propositional clauses             : 0
% 0.39/0.54  #    Propositional clauses after purity: 0
% 0.39/0.54  #    Propositional unsat core size     : 0
% 0.39/0.54  #    Propositional preprocessing time  : 0.000
% 0.39/0.54  #    Propositional encoding time       : 0.000
% 0.39/0.54  #    Propositional solver time         : 0.000
% 0.39/0.54  #    Success case prop preproc time    : 0.000
% 0.39/0.54  #    Success case prop encoding time   : 0.000
% 0.39/0.54  #    Success case prop solver time     : 0.000
% 0.39/0.54  # Current number of processed clauses  : 622
% 0.39/0.54  #    Positive orientable unit clauses  : 489
% 0.39/0.54  #    Positive unorientable unit clauses: 3
% 0.39/0.54  #    Negative unit clauses             : 1
% 0.39/0.54  #    Non-unit-clauses                  : 129
% 0.39/0.54  # Current number of unprocessed clauses: 8813
% 0.39/0.54  # ...number of literals in the above   : 10494
% 0.39/0.54  # Current number of archived formulas  : 0
% 0.39/0.54  # Current number of archived clauses   : 295
% 0.39/0.54  # Clause-clause subsumption calls (NU) : 3650
% 0.39/0.54  # Rec. Clause-clause subsumption calls : 3563
% 0.39/0.54  # Non-unit clause-clause subsumptions  : 747
% 0.39/0.54  # Unit Clause-clause subsumption calls : 1123
% 0.39/0.54  # Rewrite failures with RHS unbound    : 0
% 0.39/0.54  # BW rewrite match attempts            : 6319
% 0.39/0.54  # BW rewrite match successes           : 382
% 0.39/0.54  # Condensation attempts                : 0
% 0.39/0.54  # Condensation successes               : 0
% 0.39/0.54  # Termbank termtop insertions          : 304962
% 0.39/0.55  
% 0.39/0.55  # -------------------------------------------------
% 0.39/0.55  # User time                : 0.186 s
% 0.39/0.55  # System time              : 0.017 s
% 0.39/0.55  # Total time               : 0.203 s
% 0.39/0.55  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------

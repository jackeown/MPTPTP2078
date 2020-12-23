%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:11:32 EST 2020

% Result     : Theorem 2.80s
% Output     : CNFRefutation 2.80s
% Verified   : 
% Statistics : Number of formulae       :  167 (6771 expanded)
%              Number of clauses        :  110 (3149 expanded)
%              Number of leaves         :   28 (1784 expanded)
%              Depth                    :   24
%              Number of atoms          :  318 (8473 expanded)
%              Number of equality atoms :  112 (6124 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    9 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(t25_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k4_subset_1(X1,X2,k3_subset_1(X1,X2)) = k2_subset_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(t77_tops_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v4_pre_topc(X2,X1)
          <=> k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k1_tops_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t62_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_tops_1(X1,X2) = k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_1)).

fof(t38_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k4_xboole_0(X2,X1))
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(dt_k2_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(t43_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_xboole_0(X2,X3))
     => r1_tarski(k4_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t65_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_pre_topc(X1,X2) = k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(t6_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_1)).

fof(t44_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X1,X2),X3)
     => r1_tarski(X1,k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(t74_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k1_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

fof(fc1_tops_1,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => v4_pre_topc(k2_pre_topc(X1,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

fof(c_0_28,plain,(
    ! [X4,X5] : k4_xboole_0(X4,X5) = k5_xboole_0(X4,k3_xboole_0(X4,X5)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_29,plain,(
    ! [X44,X45] : k1_setfam_1(k2_tarski(X44,X45)) = k3_xboole_0(X44,X45) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_30,plain,(
    ! [X14] : k4_xboole_0(X14,k1_xboole_0) = X14 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_31,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_32,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_33,plain,(
    ! [X9] : k3_xboole_0(X9,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_34,plain,(
    ! [X21,X22] : k4_xboole_0(X21,k4_xboole_0(X21,X22)) = k3_xboole_0(X21,X22) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_35,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_37,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_38,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_39,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_xboole_0))) = X1 ),
    inference(rw,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_40,plain,
    ( k1_setfam_1(k2_tarski(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_37,c_0_32])).

fof(c_0_41,plain,(
    ! [X30,X31] :
      ( ~ m1_subset_1(X31,k1_zfmisc_1(X30))
      | k3_subset_1(X30,X31) = k4_xboole_0(X30,X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_42,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))))) = k1_setfam_1(k2_tarski(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_32]),c_0_36]),c_0_36])).

cnf(c_0_43,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_39,c_0_40])).

fof(c_0_44,plain,(
    ! [X10,X11] : r1_tarski(k4_xboole_0(X10,X11),X10) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_45,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_46,plain,(
    ! [X46,X47] :
      ( ( ~ m1_subset_1(X46,k1_zfmisc_1(X47))
        | r1_tarski(X46,X47) )
      & ( ~ r1_tarski(X46,X47)
        | m1_subset_1(X46,k1_zfmisc_1(X47)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_47,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X1))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_40]),c_0_43])).

cnf(c_0_48,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_49,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_45,c_0_36])).

cnf(c_0_50,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_51,plain,
    ( k1_setfam_1(k2_tarski(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_47]),c_0_40]),c_0_43])).

cnf(c_0_52,plain,
    ( r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X1) ),
    inference(rw,[status(thm)],[c_0_48,c_0_36])).

fof(c_0_53,plain,(
    ! [X32,X33] :
      ( ~ m1_subset_1(X33,k1_zfmisc_1(X32))
      | m1_subset_1(k3_subset_1(X32,X33),k1_zfmisc_1(X32)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

cnf(c_0_54,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k3_subset_1(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_55,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_47,c_0_51])).

cnf(c_0_56,plain,
    ( r1_tarski(X1,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_40]),c_0_43])).

cnf(c_0_57,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_42])).

cnf(c_0_58,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_59,plain,
    ( k3_subset_1(X1,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_51]),c_0_55]),c_0_56])])).

fof(c_0_60,plain,(
    ! [X42,X43] :
      ( ~ m1_subset_1(X43,k1_zfmisc_1(X42))
      | k4_subset_1(X42,X43,k3_subset_1(X42,X43)) = k2_subset_1(X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_subset_1])])).

fof(c_0_61,plain,(
    ! [X29] : k2_subset_1(X29) = X29 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_62,plain,(
    ! [X39,X40,X41] :
      ( ~ m1_subset_1(X40,k1_zfmisc_1(X39))
      | k7_subset_1(X39,X40,X41) = k4_xboole_0(X40,X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

fof(c_0_63,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v4_pre_topc(X2,X1)
            <=> k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k1_tops_1(X1,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t77_tops_1])).

fof(c_0_64,plain,(
    ! [X36,X37,X38] :
      ( ~ m1_subset_1(X37,k1_zfmisc_1(X36))
      | ~ m1_subset_1(X38,k1_zfmisc_1(X36))
      | k4_subset_1(X36,X37,X38) = k2_xboole_0(X37,X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

fof(c_0_65,plain,(
    ! [X27,X28] : k3_tarski(k2_tarski(X27,X28)) = k2_xboole_0(X27,X28) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

cnf(c_0_66,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_40])).

cnf(c_0_67,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_68,plain,
    ( k4_subset_1(X2,X1,k3_subset_1(X2,X1)) = k2_subset_1(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_69,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_70,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

fof(c_0_71,negated_conjecture,
    ( v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & ( ~ v4_pre_topc(esk2_0,esk1_0)
      | k2_tops_1(esk1_0,esk2_0) != k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0)) )
    & ( v4_pre_topc(esk2_0,esk1_0)
      | k2_tops_1(esk1_0,esk2_0) = k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_63])])])).

fof(c_0_72,plain,(
    ! [X54,X55] :
      ( ~ l1_pre_topc(X54)
      | ~ m1_subset_1(X55,k1_zfmisc_1(u1_struct_0(X54)))
      | k2_tops_1(X54,X55) = k2_tops_1(X54,k3_subset_1(u1_struct_0(X54),X55)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_tops_1])])])).

fof(c_0_73,plain,(
    ! [X12,X13] :
      ( ~ r1_tarski(X12,k4_xboole_0(X13,X12))
      | X12 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_xboole_1])])).

fof(c_0_74,plain,(
    ! [X25,X26] : k2_tarski(X25,X26) = k2_tarski(X26,X25) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_75,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_76,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_77,plain,
    ( k3_subset_1(X1,k1_xboole_0) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_40]),c_0_43]),c_0_66])])).

cnf(c_0_78,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_50]),c_0_56])])).

cnf(c_0_79,plain,
    ( k4_subset_1(X2,X1,k3_subset_1(X2,X1)) = X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_80,plain,
    ( k7_subset_1(X2,X1,X3) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_70,c_0_36])).

cnf(c_0_81,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

fof(c_0_82,plain,(
    ! [X50,X51] :
      ( ~ l1_pre_topc(X50)
      | ~ m1_subset_1(X51,k1_zfmisc_1(u1_struct_0(X50)))
      | m1_subset_1(k2_tops_1(X50,X51),k1_zfmisc_1(u1_struct_0(X50))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_1])])).

cnf(c_0_83,plain,
    ( k2_tops_1(X1,X2) = k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_84,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_85,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_86,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_87,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

fof(c_0_88,plain,(
    ! [X15,X16,X17] :
      ( ~ r1_tarski(X15,k2_xboole_0(X16,X17))
      | r1_tarski(k4_xboole_0(X15,X16),X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).

cnf(c_0_89,plain,
    ( k4_subset_1(X2,X1,X3) = k3_tarski(k2_tarski(X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_90,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_77]),c_0_78])])).

cnf(c_0_91,plain,
    ( k4_subset_1(X1,X2,k3_subset_1(X1,X2)) = X1
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_79,c_0_50])).

cnf(c_0_92,negated_conjecture,
    ( v4_pre_topc(esk2_0,esk1_0)
    | k2_tops_1(esk1_0,esk2_0) = k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_93,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1) = k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1))) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_94,plain,
    ( m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_95,negated_conjecture,
    ( k2_tops_1(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)) = k2_tops_1(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_81]),c_0_84])])).

cnf(c_0_96,plain,
    ( r1_tarski(k3_subset_1(X1,X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_85,c_0_58])).

cnf(c_0_97,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))) ),
    inference(rw,[status(thm)],[c_0_86,c_0_36])).

cnf(c_0_98,plain,
    ( k1_setfam_1(k2_tarski(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_40,c_0_87])).

cnf(c_0_99,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

cnf(c_0_100,plain,
    ( k4_subset_1(X1,X2,X1) = k3_tarski(k2_tarski(X2,X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_101,plain,
    ( k4_subset_1(X1,k1_xboole_0,X1) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_77]),c_0_66])])).

fof(c_0_102,plain,(
    ! [X6,X7,X8] :
      ( ~ r1_tarski(X6,X7)
      | ~ r1_tarski(X7,X8)
      | r1_tarski(X6,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_103,negated_conjecture,
    ( k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,k1_tops_1(esk1_0,esk2_0)))) = k2_tops_1(esk1_0,esk2_0)
    | v4_pre_topc(esk2_0,esk1_0) ),
    inference(rw,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_104,negated_conjecture,
    ( m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_84])])).

cnf(c_0_105,negated_conjecture,
    ( r1_tarski(k3_subset_1(u1_struct_0(esk1_0),esk2_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_96,c_0_81])).

fof(c_0_106,plain,(
    ! [X56,X57] :
      ( ~ l1_pre_topc(X56)
      | ~ m1_subset_1(X57,k1_zfmisc_1(u1_struct_0(X56)))
      | k2_pre_topc(X56,X57) = k4_subset_1(u1_struct_0(X56),X57,k2_tops_1(X56,X57)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_tops_1])])])).

fof(c_0_107,plain,(
    ! [X23,X24] : k2_xboole_0(X23,k2_xboole_0(X23,X24)) = k2_xboole_0(X23,X24) ),
    inference(variable_rename,[status(thm)],[t6_xboole_1])).

cnf(c_0_108,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_43])).

cnf(c_0_109,plain,
    ( r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X3)
    | ~ r1_tarski(X1,k3_tarski(k2_tarski(X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_99,c_0_76]),c_0_36])).

cnf(c_0_110,plain,
    ( k3_tarski(k2_tarski(k1_xboole_0,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_78]),c_0_101])).

fof(c_0_111,plain,(
    ! [X18,X19,X20] :
      ( ~ r1_tarski(k4_xboole_0(X18,X19),X20)
      | r1_tarski(X18,k2_xboole_0(X19,X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).

cnf(c_0_112,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_102])).

cnf(c_0_113,negated_conjecture,
    ( v4_pre_topc(esk2_0,esk1_0)
    | r1_tarski(k2_tops_1(esk1_0,esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_103])).

cnf(c_0_114,negated_conjecture,
    ( m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_50]),c_0_105])])).

cnf(c_0_115,plain,
    ( k2_pre_topc(X1,X2) = k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_106])).

cnf(c_0_116,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_107])).

cnf(c_0_117,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k1_xboole_0
    | ~ r1_tarski(X1,k3_tarski(k2_tarski(X2,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_108,c_0_109])).

cnf(c_0_118,plain,
    ( k3_tarski(k2_tarski(X1,k1_xboole_0)) = X1 ),
    inference(spm,[status(thm)],[c_0_110,c_0_87])).

cnf(c_0_119,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_111])).

fof(c_0_120,plain,(
    ! [X58,X59] :
      ( ~ l1_pre_topc(X58)
      | ~ m1_subset_1(X59,k1_zfmisc_1(u1_struct_0(X58)))
      | k1_tops_1(X58,X59) = k7_subset_1(u1_struct_0(X58),X59,k2_tops_1(X58,X59)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_tops_1])])])).

cnf(c_0_121,negated_conjecture,
    ( v4_pre_topc(esk2_0,esk1_0)
    | r1_tarski(X1,esk2_0)
    | ~ r1_tarski(X1,k2_tops_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_112,c_0_113])).

cnf(c_0_122,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),X1,k2_tops_1(esk1_0,esk2_0)) = k3_tarski(k2_tarski(X1,k2_tops_1(esk1_0,esk2_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_89,c_0_114])).

cnf(c_0_123,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),esk2_0,k2_tops_1(esk1_0,esk2_0)) = k2_pre_topc(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_81]),c_0_84])])).

cnf(c_0_124,plain,
    ( k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(X1,X2)))) = k3_tarski(k2_tarski(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_116,c_0_76]),c_0_76]),c_0_76])).

cnf(c_0_125,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_117,c_0_118])).

cnf(c_0_126,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))
    | ~ r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_119,c_0_76]),c_0_36])).

cnf(c_0_127,plain,
    ( k1_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_120])).

cnf(c_0_128,negated_conjecture,
    ( v4_pre_topc(esk2_0,esk1_0)
    | r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),esk2_0)
    | ~ r1_tarski(X1,k3_tarski(k2_tarski(X2,k2_tops_1(esk1_0,esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_121,c_0_109])).

cnf(c_0_129,negated_conjecture,
    ( k3_tarski(k2_tarski(esk2_0,k2_tops_1(esk1_0,esk2_0))) = k2_pre_topc(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_81]),c_0_123])).

cnf(c_0_130,plain,
    ( k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(X2,X1)))) = k3_tarski(k2_tarski(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_124,c_0_87])).

cnf(c_0_131,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_125]),c_0_40]),c_0_43])).

cnf(c_0_132,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_126,c_0_52])).

cnf(c_0_133,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk2_0,k2_tops_1(esk1_0,esk2_0)) = k1_tops_1(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_81]),c_0_84])])).

fof(c_0_134,plain,(
    ! [X34,X35] :
      ( ~ m1_subset_1(X35,k1_zfmisc_1(X34))
      | k3_subset_1(X34,k3_subset_1(X34,X35)) = X35 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

fof(c_0_135,plain,(
    ! [X48,X49] :
      ( ( ~ v4_pre_topc(X49,X48)
        | k2_pre_topc(X48,X49) = X49
        | ~ m1_subset_1(X49,k1_zfmisc_1(u1_struct_0(X48)))
        | ~ l1_pre_topc(X48) )
      & ( ~ v2_pre_topc(X48)
        | k2_pre_topc(X48,X49) != X49
        | v4_pre_topc(X49,X48)
        | ~ m1_subset_1(X49,k1_zfmisc_1(u1_struct_0(X48)))
        | ~ l1_pre_topc(X48) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).

cnf(c_0_136,negated_conjecture,
    ( v4_pre_topc(esk2_0,esk1_0)
    | r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,esk2_0))),esk2_0)
    | ~ r1_tarski(X1,k2_pre_topc(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_128,c_0_129])).

cnf(c_0_137,plain,
    ( k3_tarski(k2_tarski(X1,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_130,c_0_110])).

cnf(c_0_138,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_131,c_0_87])).

cnf(c_0_139,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_132,c_0_87])).

cnf(c_0_140,negated_conjecture,
    ( ~ v4_pre_topc(esk2_0,esk1_0)
    | k2_tops_1(esk1_0,esk2_0) != k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_141,negated_conjecture,
    ( k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,k2_tops_1(esk1_0,esk2_0)))) = k1_tops_1(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_133,c_0_93])).

cnf(c_0_142,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_134])).

fof(c_0_143,plain,(
    ! [X52,X53] :
      ( ~ v2_pre_topc(X52)
      | ~ l1_pre_topc(X52)
      | ~ m1_subset_1(X53,k1_zfmisc_1(u1_struct_0(X52)))
      | v4_pre_topc(k2_pre_topc(X52,X53),X52) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_tops_1])])).

cnf(c_0_144,plain,
    ( k2_pre_topc(X2,X1) = X1
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_135])).

cnf(c_0_145,negated_conjecture,
    ( v4_pre_topc(esk2_0,esk1_0)
    | r1_tarski(X1,esk2_0)
    | ~ r1_tarski(X1,k2_pre_topc(esk1_0,esk2_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_136]),c_0_137])).

cnf(c_0_146,plain,
    ( X1 = X2
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_131,c_0_138])).

cnf(c_0_147,negated_conjecture,
    ( r1_tarski(esk2_0,k2_pre_topc(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_139,c_0_129])).

cnf(c_0_148,negated_conjecture,
    ( k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,k1_tops_1(esk1_0,esk2_0)))) != k2_tops_1(esk1_0,esk2_0)
    | ~ v4_pre_topc(esk2_0,esk1_0) ),
    inference(rw,[status(thm)],[c_0_140,c_0_93])).

cnf(c_0_149,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_141])).

cnf(c_0_150,plain,
    ( k3_subset_1(X1,k3_subset_1(X1,X2)) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_142,c_0_50])).

cnf(c_0_151,negated_conjecture,
    ( k3_subset_1(esk2_0,k2_tops_1(esk1_0,esk2_0)) = k1_tops_1(esk1_0,esk2_0)
    | ~ r1_tarski(k2_tops_1(esk1_0,esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_141,c_0_54])).

cnf(c_0_152,plain,
    ( v4_pre_topc(k2_pre_topc(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_143])).

cnf(c_0_153,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_154,plain,
    ( k2_pre_topc(X1,X2) = X2
    | ~ v4_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_144,c_0_50])).

cnf(c_0_155,negated_conjecture,
    ( v4_pre_topc(esk2_0,esk1_0)
    | r1_tarski(k2_pre_topc(esk1_0,esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_145,c_0_56])).

cnf(c_0_156,negated_conjecture,
    ( r1_tarski(esk2_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_85,c_0_81])).

cnf(c_0_157,negated_conjecture,
    ( k2_pre_topc(esk1_0,esk2_0) = esk2_0
    | ~ r1_tarski(k2_pre_topc(esk1_0,esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_146,c_0_147])).

cnf(c_0_158,negated_conjecture,
    ( k3_subset_1(esk2_0,k1_tops_1(esk1_0,esk2_0)) != k2_tops_1(esk1_0,esk2_0)
    | ~ v4_pre_topc(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148,c_0_54]),c_0_149])])).

cnf(c_0_159,negated_conjecture,
    ( k3_subset_1(esk2_0,k1_tops_1(esk1_0,esk2_0)) = k2_tops_1(esk1_0,esk2_0)
    | ~ r1_tarski(k2_tops_1(esk1_0,esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_150,c_0_151])).

cnf(c_0_160,negated_conjecture,
    ( v4_pre_topc(k2_pre_topc(esk1_0,esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_152,c_0_81]),c_0_153]),c_0_84])])).

cnf(c_0_161,negated_conjecture,
    ( k2_pre_topc(esk1_0,esk2_0) = esk2_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_154,c_0_155]),c_0_84]),c_0_156])]),c_0_157])).

cnf(c_0_162,negated_conjecture,
    ( ~ v4_pre_topc(esk2_0,esk1_0)
    | ~ r1_tarski(k2_tops_1(esk1_0,esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_158,c_0_159])).

cnf(c_0_163,negated_conjecture,
    ( v4_pre_topc(esk2_0,esk1_0) ),
    inference(rw,[status(thm)],[c_0_160,c_0_161])).

cnf(c_0_164,negated_conjecture,
    ( r1_tarski(k2_tops_1(esk1_0,esk2_0),k2_pre_topc(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_132,c_0_129])).

cnf(c_0_165,negated_conjecture,
    ( ~ r1_tarski(k2_tops_1(esk1_0,esk2_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_162,c_0_163])])).

cnf(c_0_166,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_164,c_0_161]),c_0_165]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.15  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.16/0.36  % Computer   : n024.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.36  % CPULimit   : 60
% 0.16/0.36  % WCLimit    : 600
% 0.16/0.36  % DateTime   : Tue Dec  1 14:02:36 EST 2020
% 0.16/0.36  % CPUTime    : 
% 0.16/0.36  # Version: 2.5pre002
% 0.16/0.37  # No SInE strategy applied
% 0.16/0.37  # Trying AutoSched0 for 299 seconds
% 2.80/3.00  # AutoSched0-Mode selected heuristic G_E___107_C36_F1_PI_AE_Q4_CS_SP_PS_S0Y
% 2.80/3.00  # and selection function SelectMaxLComplexAvoidPosPred.
% 2.80/3.00  #
% 2.80/3.00  # Preprocessing time       : 0.042 s
% 2.80/3.00  # Presaturation interreduction done
% 2.80/3.00  
% 2.80/3.00  # Proof found!
% 2.80/3.00  # SZS status Theorem
% 2.80/3.00  # SZS output start CNFRefutation
% 2.80/3.00  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.80/3.00  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.80/3.00  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.80/3.00  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.80/3.00  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.80/3.00  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.80/3.00  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.80/3.00  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.80/3.00  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.80/3.00  fof(t25_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k4_subset_1(X1,X2,k3_subset_1(X1,X2))=k2_subset_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_subset_1)).
% 2.80/3.00  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.80/3.00  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 2.80/3.00  fof(t77_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)<=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k1_tops_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 2.80/3.00  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 2.80/3.00  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.80/3.00  fof(t62_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_tops_1(X1,X2)=k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tops_1)).
% 2.80/3.00  fof(t38_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,k4_xboole_0(X2,X1))=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_xboole_1)).
% 2.80/3.00  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.80/3.00  fof(dt_k2_tops_1, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 2.80/3.00  fof(t43_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_xboole_0(X2,X3))=>r1_tarski(k4_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 2.80/3.00  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.80/3.00  fof(t65_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_pre_topc(X1,X2)=k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 2.80/3.00  fof(t6_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k2_xboole_0(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_1)).
% 2.80/3.00  fof(t44_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k4_xboole_0(X1,X2),X3)=>r1_tarski(X1,k2_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 2.80/3.00  fof(t74_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k1_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 2.80/3.00  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.80/3.00  fof(t52_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v4_pre_topc(X2,X1)=>k2_pre_topc(X1,X2)=X2)&((v2_pre_topc(X1)&k2_pre_topc(X1,X2)=X2)=>v4_pre_topc(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 2.80/3.00  fof(fc1_tops_1, axiom, ![X1, X2]:(((v2_pre_topc(X1)&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v4_pre_topc(k2_pre_topc(X1,X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_tops_1)).
% 2.80/3.00  fof(c_0_28, plain, ![X4, X5]:k4_xboole_0(X4,X5)=k5_xboole_0(X4,k3_xboole_0(X4,X5)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 2.80/3.00  fof(c_0_29, plain, ![X44, X45]:k1_setfam_1(k2_tarski(X44,X45))=k3_xboole_0(X44,X45), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 2.80/3.00  fof(c_0_30, plain, ![X14]:k4_xboole_0(X14,k1_xboole_0)=X14, inference(variable_rename,[status(thm)],[t3_boole])).
% 2.80/3.00  cnf(c_0_31, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 2.80/3.00  cnf(c_0_32, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 2.80/3.00  fof(c_0_33, plain, ![X9]:k3_xboole_0(X9,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 2.80/3.00  fof(c_0_34, plain, ![X21, X22]:k4_xboole_0(X21,k4_xboole_0(X21,X22))=k3_xboole_0(X21,X22), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 2.80/3.00  cnf(c_0_35, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_30])).
% 2.80/3.00  cnf(c_0_36, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_31, c_0_32])).
% 2.80/3.00  cnf(c_0_37, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_33])).
% 2.80/3.00  cnf(c_0_38, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 2.80/3.00  cnf(c_0_39, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_xboole_0)))=X1), inference(rw,[status(thm)],[c_0_35, c_0_36])).
% 2.80/3.00  cnf(c_0_40, plain, (k1_setfam_1(k2_tarski(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_37, c_0_32])).
% 2.80/3.00  fof(c_0_41, plain, ![X30, X31]:(~m1_subset_1(X31,k1_zfmisc_1(X30))|k3_subset_1(X30,X31)=k4_xboole_0(X30,X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 2.80/3.00  cnf(c_0_42, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))))))=k1_setfam_1(k2_tarski(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_32]), c_0_36]), c_0_36])).
% 2.80/3.00  cnf(c_0_43, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_39, c_0_40])).
% 2.80/3.00  fof(c_0_44, plain, ![X10, X11]:r1_tarski(k4_xboole_0(X10,X11),X10), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 2.80/3.00  cnf(c_0_45, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 2.80/3.00  fof(c_0_46, plain, ![X46, X47]:((~m1_subset_1(X46,k1_zfmisc_1(X47))|r1_tarski(X46,X47))&(~r1_tarski(X46,X47)|m1_subset_1(X46,k1_zfmisc_1(X47)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 2.80/3.00  cnf(c_0_47, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X1)))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_40]), c_0_43])).
% 2.80/3.00  cnf(c_0_48, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 2.80/3.00  cnf(c_0_49, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_45, c_0_36])).
% 2.80/3.00  cnf(c_0_50, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 2.80/3.00  cnf(c_0_51, plain, (k1_setfam_1(k2_tarski(X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_47]), c_0_40]), c_0_43])).
% 2.80/3.00  cnf(c_0_52, plain, (r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X1)), inference(rw,[status(thm)],[c_0_48, c_0_36])).
% 2.80/3.00  fof(c_0_53, plain, ![X32, X33]:(~m1_subset_1(X33,k1_zfmisc_1(X32))|m1_subset_1(k3_subset_1(X32,X33),k1_zfmisc_1(X32))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 2.80/3.00  cnf(c_0_54, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k3_subset_1(X1,X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 2.80/3.00  cnf(c_0_55, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_47, c_0_51])).
% 2.80/3.00  cnf(c_0_56, plain, (r1_tarski(X1,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_40]), c_0_43])).
% 2.80/3.00  cnf(c_0_57, plain, (r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X1)), inference(spm,[status(thm)],[c_0_52, c_0_42])).
% 2.80/3.00  cnf(c_0_58, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 2.80/3.00  cnf(c_0_59, plain, (k3_subset_1(X1,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_51]), c_0_55]), c_0_56])])).
% 2.80/3.00  fof(c_0_60, plain, ![X42, X43]:(~m1_subset_1(X43,k1_zfmisc_1(X42))|k4_subset_1(X42,X43,k3_subset_1(X42,X43))=k2_subset_1(X42)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_subset_1])])).
% 2.80/3.00  fof(c_0_61, plain, ![X29]:k2_subset_1(X29)=X29, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 2.80/3.00  fof(c_0_62, plain, ![X39, X40, X41]:(~m1_subset_1(X40,k1_zfmisc_1(X39))|k7_subset_1(X39,X40,X41)=k4_xboole_0(X40,X41)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 2.80/3.00  fof(c_0_63, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)<=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k1_tops_1(X1,X2)))))), inference(assume_negation,[status(cth)],[t77_tops_1])).
% 2.80/3.00  fof(c_0_64, plain, ![X36, X37, X38]:(~m1_subset_1(X37,k1_zfmisc_1(X36))|~m1_subset_1(X38,k1_zfmisc_1(X36))|k4_subset_1(X36,X37,X38)=k2_xboole_0(X37,X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 2.80/3.00  fof(c_0_65, plain, ![X27, X28]:k3_tarski(k2_tarski(X27,X28))=k2_xboole_0(X27,X28), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 2.80/3.00  cnf(c_0_66, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_57, c_0_40])).
% 2.80/3.00  cnf(c_0_67, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 2.80/3.00  cnf(c_0_68, plain, (k4_subset_1(X2,X1,k3_subset_1(X2,X1))=k2_subset_1(X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 2.80/3.00  cnf(c_0_69, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_61])).
% 2.80/3.00  cnf(c_0_70, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_62])).
% 2.80/3.00  fof(c_0_71, negated_conjecture, ((v2_pre_topc(esk1_0)&l1_pre_topc(esk1_0))&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&((~v4_pre_topc(esk2_0,esk1_0)|k2_tops_1(esk1_0,esk2_0)!=k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0)))&(v4_pre_topc(esk2_0,esk1_0)|k2_tops_1(esk1_0,esk2_0)=k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_63])])])).
% 2.80/3.00  fof(c_0_72, plain, ![X54, X55]:(~l1_pre_topc(X54)|(~m1_subset_1(X55,k1_zfmisc_1(u1_struct_0(X54)))|k2_tops_1(X54,X55)=k2_tops_1(X54,k3_subset_1(u1_struct_0(X54),X55)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_tops_1])])])).
% 2.80/3.00  fof(c_0_73, plain, ![X12, X13]:(~r1_tarski(X12,k4_xboole_0(X13,X12))|X12=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_xboole_1])])).
% 2.80/3.00  fof(c_0_74, plain, ![X25, X26]:k2_tarski(X25,X26)=k2_tarski(X26,X25), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 2.80/3.00  cnf(c_0_75, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_64])).
% 2.80/3.00  cnf(c_0_76, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 2.80/3.00  cnf(c_0_77, plain, (k3_subset_1(X1,k1_xboole_0)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_40]), c_0_43]), c_0_66])])).
% 2.80/3.00  cnf(c_0_78, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_50]), c_0_56])])).
% 2.80/3.00  cnf(c_0_79, plain, (k4_subset_1(X2,X1,k3_subset_1(X2,X1))=X2|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_68, c_0_69])).
% 2.80/3.00  cnf(c_0_80, plain, (k7_subset_1(X2,X1,X3)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_70, c_0_36])).
% 2.80/3.00  cnf(c_0_81, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_71])).
% 2.80/3.00  fof(c_0_82, plain, ![X50, X51]:(~l1_pre_topc(X50)|~m1_subset_1(X51,k1_zfmisc_1(u1_struct_0(X50)))|m1_subset_1(k2_tops_1(X50,X51),k1_zfmisc_1(u1_struct_0(X50)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_1])])).
% 2.80/3.00  cnf(c_0_83, plain, (k2_tops_1(X1,X2)=k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_72])).
% 2.80/3.00  cnf(c_0_84, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 2.80/3.00  cnf(c_0_85, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 2.80/3.00  cnf(c_0_86, plain, (X1=k1_xboole_0|~r1_tarski(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_73])).
% 2.80/3.00  cnf(c_0_87, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_74])).
% 2.80/3.00  fof(c_0_88, plain, ![X15, X16, X17]:(~r1_tarski(X15,k2_xboole_0(X16,X17))|r1_tarski(k4_xboole_0(X15,X16),X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).
% 2.80/3.00  cnf(c_0_89, plain, (k4_subset_1(X2,X1,X3)=k3_tarski(k2_tarski(X1,X3))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_75, c_0_76])).
% 2.80/3.00  cnf(c_0_90, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_77]), c_0_78])])).
% 2.80/3.00  cnf(c_0_91, plain, (k4_subset_1(X1,X2,k3_subset_1(X1,X2))=X1|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_79, c_0_50])).
% 2.80/3.00  cnf(c_0_92, negated_conjecture, (v4_pre_topc(esk2_0,esk1_0)|k2_tops_1(esk1_0,esk2_0)=k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_71])).
% 2.80/3.00  cnf(c_0_93, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)=k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1)))), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 2.80/3.00  cnf(c_0_94, plain, (m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_82])).
% 2.80/3.00  cnf(c_0_95, negated_conjecture, (k2_tops_1(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0))=k2_tops_1(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_81]), c_0_84])])).
% 2.80/3.00  cnf(c_0_96, plain, (r1_tarski(k3_subset_1(X1,X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_85, c_0_58])).
% 2.80/3.00  cnf(c_0_97, plain, (X1=k1_xboole_0|~r1_tarski(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1))))), inference(rw,[status(thm)],[c_0_86, c_0_36])).
% 2.80/3.00  cnf(c_0_98, plain, (k1_setfam_1(k2_tarski(k1_xboole_0,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_40, c_0_87])).
% 2.80/3.00  cnf(c_0_99, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_88])).
% 2.80/3.00  cnf(c_0_100, plain, (k4_subset_1(X1,X2,X1)=k3_tarski(k2_tarski(X2,X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_89, c_0_90])).
% 2.80/3.00  cnf(c_0_101, plain, (k4_subset_1(X1,k1_xboole_0,X1)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_77]), c_0_66])])).
% 2.80/3.00  fof(c_0_102, plain, ![X6, X7, X8]:(~r1_tarski(X6,X7)|~r1_tarski(X7,X8)|r1_tarski(X6,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 2.80/3.00  cnf(c_0_103, negated_conjecture, (k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,k1_tops_1(esk1_0,esk2_0))))=k2_tops_1(esk1_0,esk2_0)|v4_pre_topc(esk2_0,esk1_0)), inference(rw,[status(thm)],[c_0_92, c_0_93])).
% 2.80/3.00  cnf(c_0_104, negated_conjecture, (m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_84])])).
% 2.80/3.00  cnf(c_0_105, negated_conjecture, (r1_tarski(k3_subset_1(u1_struct_0(esk1_0),esk2_0),u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_96, c_0_81])).
% 2.80/3.00  fof(c_0_106, plain, ![X56, X57]:(~l1_pre_topc(X56)|(~m1_subset_1(X57,k1_zfmisc_1(u1_struct_0(X56)))|k2_pre_topc(X56,X57)=k4_subset_1(u1_struct_0(X56),X57,k2_tops_1(X56,X57)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_tops_1])])])).
% 2.80/3.00  fof(c_0_107, plain, ![X23, X24]:k2_xboole_0(X23,k2_xboole_0(X23,X24))=k2_xboole_0(X23,X24), inference(variable_rename,[status(thm)],[t6_xboole_1])).
% 2.80/3.00  cnf(c_0_108, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_98]), c_0_43])).
% 2.80/3.00  cnf(c_0_109, plain, (r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X3)|~r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_99, c_0_76]), c_0_36])).
% 2.80/3.00  cnf(c_0_110, plain, (k3_tarski(k2_tarski(k1_xboole_0,X1))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_78]), c_0_101])).
% 2.80/3.00  fof(c_0_111, plain, ![X18, X19, X20]:(~r1_tarski(k4_xboole_0(X18,X19),X20)|r1_tarski(X18,k2_xboole_0(X19,X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).
% 2.80/3.00  cnf(c_0_112, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_102])).
% 2.80/3.00  cnf(c_0_113, negated_conjecture, (v4_pre_topc(esk2_0,esk1_0)|r1_tarski(k2_tops_1(esk1_0,esk2_0),esk2_0)), inference(spm,[status(thm)],[c_0_52, c_0_103])).
% 2.80/3.00  cnf(c_0_114, negated_conjecture, (m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_50]), c_0_105])])).
% 2.80/3.00  cnf(c_0_115, plain, (k2_pre_topc(X1,X2)=k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_106])).
% 2.80/3.00  cnf(c_0_116, plain, (k2_xboole_0(X1,k2_xboole_0(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_107])).
% 2.80/3.00  cnf(c_0_117, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k1_xboole_0|~r1_tarski(X1,k3_tarski(k2_tarski(X2,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_108, c_0_109])).
% 2.80/3.00  cnf(c_0_118, plain, (k3_tarski(k2_tarski(X1,k1_xboole_0))=X1), inference(spm,[status(thm)],[c_0_110, c_0_87])).
% 2.80/3.00  cnf(c_0_119, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_111])).
% 2.80/3.00  fof(c_0_120, plain, ![X58, X59]:(~l1_pre_topc(X58)|(~m1_subset_1(X59,k1_zfmisc_1(u1_struct_0(X58)))|k1_tops_1(X58,X59)=k7_subset_1(u1_struct_0(X58),X59,k2_tops_1(X58,X59)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_tops_1])])])).
% 2.80/3.00  cnf(c_0_121, negated_conjecture, (v4_pre_topc(esk2_0,esk1_0)|r1_tarski(X1,esk2_0)|~r1_tarski(X1,k2_tops_1(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_112, c_0_113])).
% 2.80/3.00  cnf(c_0_122, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),X1,k2_tops_1(esk1_0,esk2_0))=k3_tarski(k2_tarski(X1,k2_tops_1(esk1_0,esk2_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_89, c_0_114])).
% 2.80/3.00  cnf(c_0_123, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),esk2_0,k2_tops_1(esk1_0,esk2_0))=k2_pre_topc(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_81]), c_0_84])])).
% 2.80/3.00  cnf(c_0_124, plain, (k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(X1,X2))))=k3_tarski(k2_tarski(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_116, c_0_76]), c_0_76]), c_0_76])).
% 2.80/3.00  cnf(c_0_125, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k1_xboole_0|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_117, c_0_118])).
% 2.80/3.00  cnf(c_0_126, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))|~r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_119, c_0_76]), c_0_36])).
% 2.80/3.00  cnf(c_0_127, plain, (k1_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_120])).
% 2.80/3.00  cnf(c_0_128, negated_conjecture, (v4_pre_topc(esk2_0,esk1_0)|r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),esk2_0)|~r1_tarski(X1,k3_tarski(k2_tarski(X2,k2_tops_1(esk1_0,esk2_0))))), inference(spm,[status(thm)],[c_0_121, c_0_109])).
% 2.80/3.00  cnf(c_0_129, negated_conjecture, (k3_tarski(k2_tarski(esk2_0,k2_tops_1(esk1_0,esk2_0)))=k2_pre_topc(esk1_0,esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122, c_0_81]), c_0_123])).
% 2.80/3.00  cnf(c_0_130, plain, (k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(X2,X1))))=k3_tarski(k2_tarski(X2,X1))), inference(spm,[status(thm)],[c_0_124, c_0_87])).
% 2.80/3.00  cnf(c_0_131, plain, (k1_setfam_1(k2_tarski(X1,X2))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_125]), c_0_40]), c_0_43])).
% 2.80/3.00  cnf(c_0_132, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X2,X1)))), inference(spm,[status(thm)],[c_0_126, c_0_52])).
% 2.80/3.00  cnf(c_0_133, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk2_0,k2_tops_1(esk1_0,esk2_0))=k1_tops_1(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127, c_0_81]), c_0_84])])).
% 2.80/3.00  fof(c_0_134, plain, ![X34, X35]:(~m1_subset_1(X35,k1_zfmisc_1(X34))|k3_subset_1(X34,k3_subset_1(X34,X35))=X35), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 2.80/3.00  fof(c_0_135, plain, ![X48, X49]:((~v4_pre_topc(X49,X48)|k2_pre_topc(X48,X49)=X49|~m1_subset_1(X49,k1_zfmisc_1(u1_struct_0(X48)))|~l1_pre_topc(X48))&(~v2_pre_topc(X48)|k2_pre_topc(X48,X49)!=X49|v4_pre_topc(X49,X48)|~m1_subset_1(X49,k1_zfmisc_1(u1_struct_0(X48)))|~l1_pre_topc(X48))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).
% 2.80/3.00  cnf(c_0_136, negated_conjecture, (v4_pre_topc(esk2_0,esk1_0)|r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,esk2_0))),esk2_0)|~r1_tarski(X1,k2_pre_topc(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_128, c_0_129])).
% 2.80/3.00  cnf(c_0_137, plain, (k3_tarski(k2_tarski(X1,X1))=X1), inference(spm,[status(thm)],[c_0_130, c_0_110])).
% 2.80/3.00  cnf(c_0_138, plain, (k1_setfam_1(k2_tarski(X1,X2))=X2|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_131, c_0_87])).
% 2.80/3.00  cnf(c_0_139, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X1,X2)))), inference(spm,[status(thm)],[c_0_132, c_0_87])).
% 2.80/3.00  cnf(c_0_140, negated_conjecture, (~v4_pre_topc(esk2_0,esk1_0)|k2_tops_1(esk1_0,esk2_0)!=k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_71])).
% 2.80/3.00  cnf(c_0_141, negated_conjecture, (k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,k2_tops_1(esk1_0,esk2_0))))=k1_tops_1(esk1_0,esk2_0)), inference(rw,[status(thm)],[c_0_133, c_0_93])).
% 2.80/3.00  cnf(c_0_142, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_134])).
% 2.80/3.00  fof(c_0_143, plain, ![X52, X53]:(~v2_pre_topc(X52)|~l1_pre_topc(X52)|~m1_subset_1(X53,k1_zfmisc_1(u1_struct_0(X52)))|v4_pre_topc(k2_pre_topc(X52,X53),X52)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_tops_1])])).
% 2.80/3.00  cnf(c_0_144, plain, (k2_pre_topc(X2,X1)=X1|~v4_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_135])).
% 2.80/3.00  cnf(c_0_145, negated_conjecture, (v4_pre_topc(esk2_0,esk1_0)|r1_tarski(X1,esk2_0)|~r1_tarski(X1,k2_pre_topc(esk1_0,esk2_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126, c_0_136]), c_0_137])).
% 2.80/3.00  cnf(c_0_146, plain, (X1=X2|~r1_tarski(X2,X1)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_131, c_0_138])).
% 2.80/3.00  cnf(c_0_147, negated_conjecture, (r1_tarski(esk2_0,k2_pre_topc(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_139, c_0_129])).
% 2.80/3.00  cnf(c_0_148, negated_conjecture, (k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,k1_tops_1(esk1_0,esk2_0))))!=k2_tops_1(esk1_0,esk2_0)|~v4_pre_topc(esk2_0,esk1_0)), inference(rw,[status(thm)],[c_0_140, c_0_93])).
% 2.80/3.00  cnf(c_0_149, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,esk2_0),esk2_0)), inference(spm,[status(thm)],[c_0_52, c_0_141])).
% 2.80/3.00  cnf(c_0_150, plain, (k3_subset_1(X1,k3_subset_1(X1,X2))=X2|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_142, c_0_50])).
% 2.80/3.00  cnf(c_0_151, negated_conjecture, (k3_subset_1(esk2_0,k2_tops_1(esk1_0,esk2_0))=k1_tops_1(esk1_0,esk2_0)|~r1_tarski(k2_tops_1(esk1_0,esk2_0),esk2_0)), inference(spm,[status(thm)],[c_0_141, c_0_54])).
% 2.80/3.00  cnf(c_0_152, plain, (v4_pre_topc(k2_pre_topc(X1,X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_143])).
% 2.80/3.00  cnf(c_0_153, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 2.80/3.00  cnf(c_0_154, plain, (k2_pre_topc(X1,X2)=X2|~v4_pre_topc(X2,X1)|~l1_pre_topc(X1)|~r1_tarski(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_144, c_0_50])).
% 2.80/3.00  cnf(c_0_155, negated_conjecture, (v4_pre_topc(esk2_0,esk1_0)|r1_tarski(k2_pre_topc(esk1_0,esk2_0),esk2_0)), inference(spm,[status(thm)],[c_0_145, c_0_56])).
% 2.80/3.00  cnf(c_0_156, negated_conjecture, (r1_tarski(esk2_0,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_85, c_0_81])).
% 2.80/3.00  cnf(c_0_157, negated_conjecture, (k2_pre_topc(esk1_0,esk2_0)=esk2_0|~r1_tarski(k2_pre_topc(esk1_0,esk2_0),esk2_0)), inference(spm,[status(thm)],[c_0_146, c_0_147])).
% 2.80/3.00  cnf(c_0_158, negated_conjecture, (k3_subset_1(esk2_0,k1_tops_1(esk1_0,esk2_0))!=k2_tops_1(esk1_0,esk2_0)|~v4_pre_topc(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148, c_0_54]), c_0_149])])).
% 2.80/3.00  cnf(c_0_159, negated_conjecture, (k3_subset_1(esk2_0,k1_tops_1(esk1_0,esk2_0))=k2_tops_1(esk1_0,esk2_0)|~r1_tarski(k2_tops_1(esk1_0,esk2_0),esk2_0)), inference(spm,[status(thm)],[c_0_150, c_0_151])).
% 2.80/3.00  cnf(c_0_160, negated_conjecture, (v4_pre_topc(k2_pre_topc(esk1_0,esk2_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_152, c_0_81]), c_0_153]), c_0_84])])).
% 2.80/3.00  cnf(c_0_161, negated_conjecture, (k2_pre_topc(esk1_0,esk2_0)=esk2_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_154, c_0_155]), c_0_84]), c_0_156])]), c_0_157])).
% 2.80/3.00  cnf(c_0_162, negated_conjecture, (~v4_pre_topc(esk2_0,esk1_0)|~r1_tarski(k2_tops_1(esk1_0,esk2_0),esk2_0)), inference(spm,[status(thm)],[c_0_158, c_0_159])).
% 2.80/3.00  cnf(c_0_163, negated_conjecture, (v4_pre_topc(esk2_0,esk1_0)), inference(rw,[status(thm)],[c_0_160, c_0_161])).
% 2.80/3.00  cnf(c_0_164, negated_conjecture, (r1_tarski(k2_tops_1(esk1_0,esk2_0),k2_pre_topc(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_132, c_0_129])).
% 2.80/3.00  cnf(c_0_165, negated_conjecture, (~r1_tarski(k2_tops_1(esk1_0,esk2_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_162, c_0_163])])).
% 2.80/3.00  cnf(c_0_166, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_164, c_0_161]), c_0_165]), ['proof']).
% 2.80/3.00  # SZS output end CNFRefutation
% 2.80/3.00  # Proof object total steps             : 167
% 2.80/3.00  # Proof object clause steps            : 110
% 2.80/3.00  # Proof object formula steps           : 57
% 2.80/3.00  # Proof object conjectures             : 40
% 2.80/3.00  # Proof object clause conjectures      : 37
% 2.80/3.00  # Proof object formula conjectures     : 3
% 2.80/3.00  # Proof object initial clauses used    : 33
% 2.80/3.00  # Proof object initial formulas used   : 28
% 2.80/3.00  # Proof object generating inferences   : 55
% 2.80/3.00  # Proof object simplifying inferences  : 71
% 2.80/3.00  # Training examples: 0 positive, 0 negative
% 2.80/3.00  # Parsed axioms                        : 28
% 2.80/3.00  # Removed by relevancy pruning/SinE    : 0
% 2.80/3.00  # Initial clauses                      : 34
% 2.80/3.00  # Removed in clause preprocessing      : 4
% 2.80/3.00  # Initial clauses in saturation        : 30
% 2.80/3.00  # Processed clauses                    : 22273
% 2.80/3.00  # ...of these trivial                  : 367
% 2.80/3.00  # ...subsumed                          : 17892
% 2.80/3.00  # ...remaining for further processing  : 4013
% 2.80/3.00  # Other redundant clauses eliminated   : 0
% 2.80/3.00  # Clauses deleted for lack of memory   : 0
% 2.80/3.00  # Backward-subsumed                    : 165
% 2.80/3.00  # Backward-rewritten                   : 576
% 2.80/3.00  # Generated clauses                    : 309603
% 2.80/3.00  # ...of the previous two non-trivial   : 257599
% 2.80/3.00  # Contextual simplify-reflections      : 150
% 2.80/3.00  # Paramodulations                      : 309600
% 2.80/3.00  # Factorizations                       : 0
% 2.80/3.00  # Equation resolutions                 : 0
% 2.80/3.00  # Propositional unsat checks           : 0
% 2.80/3.00  #    Propositional check models        : 0
% 2.80/3.00  #    Propositional check unsatisfiable : 0
% 2.80/3.00  #    Propositional clauses             : 0
% 2.80/3.00  #    Propositional clauses after purity: 0
% 2.80/3.00  #    Propositional unsat core size     : 0
% 2.80/3.00  #    Propositional preprocessing time  : 0.000
% 2.80/3.00  #    Propositional encoding time       : 0.000
% 2.80/3.00  #    Propositional solver time         : 0.000
% 2.80/3.00  #    Success case prop preproc time    : 0.000
% 2.80/3.00  #    Success case prop encoding time   : 0.000
% 2.80/3.00  #    Success case prop solver time     : 0.000
% 2.80/3.00  # Current number of processed clauses  : 3241
% 2.80/3.00  #    Positive orientable unit clauses  : 688
% 2.80/3.00  #    Positive unorientable unit clauses: 1
% 2.80/3.00  #    Negative unit clauses             : 12
% 2.80/3.00  #    Non-unit-clauses                  : 2540
% 2.80/3.00  # Current number of unprocessed clauses: 233826
% 2.80/3.00  # ...number of literals in the above   : 610241
% 2.80/3.00  # Current number of archived formulas  : 0
% 2.80/3.00  # Current number of archived clauses   : 775
% 2.80/3.00  # Clause-clause subsumption calls (NU) : 1006340
% 2.80/3.00  # Rec. Clause-clause subsumption calls : 849673
% 2.80/3.00  # Non-unit clause-clause subsumptions  : 13075
% 2.80/3.00  # Unit Clause-clause subsumption calls : 9816
% 2.80/3.00  # Rewrite failures with RHS unbound    : 0
% 2.80/3.00  # BW rewrite match attempts            : 19310
% 2.80/3.00  # BW rewrite match successes           : 80
% 2.80/3.00  # Condensation attempts                : 0
% 2.80/3.00  # Condensation successes               : 0
% 2.80/3.00  # Termbank termtop insertions          : 7372019
% 2.85/3.01  
% 2.85/3.01  # -------------------------------------------------
% 2.85/3.01  # User time                : 2.553 s
% 2.85/3.01  # System time              : 0.096 s
% 2.85/3.01  # Total time               : 2.649 s
% 2.85/3.01  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------

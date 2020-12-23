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
% DateTime   : Thu Dec  3 11:11:20 EST 2020

% Result     : Theorem 14.71s
% Output     : CNFRefutation 14.71s
% Verified   : 
% Statistics : Number of formulae       :  236 (2639 expanded)
%              Number of clauses        :  165 (1243 expanded)
%              Number of leaves         :   35 ( 680 expanded)
%              Depth                    :   21
%              Number of atoms          :  494 (4628 expanded)
%              Number of equality atoms :  146 (2147 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t76_tops_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(idempotence_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(t44_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X1,X2),X3)
     => r1_tarski(X1,k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t52_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(dt_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(t32_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => k7_subset_1(X1,X2,X3) = k9_subset_1(X1,X2,k3_subset_1(X1,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(dt_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(t65_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_pre_topc(X1,X2) = k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(dt_k2_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(t74_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k1_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(t62_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_tops_1(X1,X2) = k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

fof(fc9_tops_1,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => v3_pre_topc(k1_tops_1(X1,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(l78_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(c_0_35,plain,(
    ! [X12,X13] : k4_xboole_0(X12,X13) = k5_xboole_0(X12,k3_xboole_0(X12,X13)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_36,plain,(
    ! [X61,X62] : k1_setfam_1(k2_tarski(X61,X62)) = k3_xboole_0(X61,X62) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_37,plain,(
    ! [X17,X18,X19] :
      ( ~ r1_tarski(X17,X18)
      | ~ r1_tarski(X18,X19)
      | r1_tarski(X17,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_38,plain,(
    ! [X63,X64] :
      ( ( ~ m1_subset_1(X63,k1_zfmisc_1(X64))
        | r1_tarski(X63,X64) )
      & ( ~ r1_tarski(X63,X64)
        | m1_subset_1(X63,k1_zfmisc_1(X64)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_39,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v3_pre_topc(X2,X1)
            <=> k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t76_tops_1])).

fof(c_0_40,plain,(
    ! [X22,X23] : r1_tarski(k4_xboole_0(X22,X23),X22) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_41,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_42,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_43,plain,(
    ! [X10,X11] :
      ( ( k4_xboole_0(X10,X11) != k1_xboole_0
        | r1_tarski(X10,X11) )
      & ( ~ r1_tarski(X10,X11)
        | k4_xboole_0(X10,X11) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_44,plain,(
    ! [X20,X21] :
      ( ~ r1_tarski(X20,X21)
      | k3_xboole_0(X20,X21) = X20 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_45,plain,(
    ! [X16] : k2_xboole_0(X16,k1_xboole_0) = X16 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_46,plain,(
    ! [X14,X15] :
      ( ~ r1_tarski(X14,X15)
      | k2_xboole_0(X14,X15) = X15 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_49,negated_conjecture,
    ( v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & ( ~ v3_pre_topc(esk2_0,esk1_0)
      | k2_tops_1(esk1_0,esk2_0) != k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0) )
    & ( v3_pre_topc(esk2_0,esk1_0)
      | k2_tops_1(esk1_0,esk2_0) = k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_39])])])).

fof(c_0_50,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k3_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_51,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_52,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_53,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_54,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_55,plain,(
    ! [X8,X9] :
      ( ( r1_tarski(X8,X9)
        | X8 != X9 )
      & ( r1_tarski(X9,X8)
        | X8 != X9 )
      & ( ~ r1_tarski(X8,X9)
        | ~ r1_tarski(X9,X8)
        | X8 = X9 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_56,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_57,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_58,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_59,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_60,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

fof(c_0_61,plain,(
    ! [X43,X44,X45] :
      ( ~ m1_subset_1(X45,k1_zfmisc_1(X43))
      | k9_subset_1(X43,X44,X44) = X44 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[idempotence_k9_subset_1])])).

cnf(c_0_62,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_63,plain,
    ( r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X1) ),
    inference(rw,[status(thm)],[c_0_51,c_0_52])).

fof(c_0_64,plain,(
    ! [X54,X55,X56] :
      ( ~ m1_subset_1(X56,k1_zfmisc_1(X54))
      | k9_subset_1(X54,X55,X56) = k3_xboole_0(X55,X56) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

fof(c_0_65,plain,(
    ! [X25,X26,X27] :
      ( ~ r1_tarski(k4_xboole_0(X25,X26),X27)
      | r1_tarski(X25,k2_xboole_0(X26,X27)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).

cnf(c_0_66,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_53,c_0_52])).

cnf(c_0_67,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_54,c_0_42])).

cnf(c_0_68,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_69,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_70,plain,
    ( k1_xboole_0 = X1
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_71,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_72,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k1_setfam_1(k2_tarski(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_42]),c_0_42])).

cnf(c_0_73,plain,
    ( k9_subset_1(X2,X3,X3) = X3
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_74,plain,
    ( m1_subset_1(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_75,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

fof(c_0_76,plain,(
    ! [X24] : k4_xboole_0(X24,k1_xboole_0) = X24 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_77,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_78,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_79,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_68])).

cnf(c_0_80,plain,
    ( r1_tarski(X1,X2)
    | k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_69,c_0_52])).

cnf(c_0_81,plain,
    ( k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,X1))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_70,c_0_63])).

cnf(c_0_82,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X2,esk2_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_47,c_0_71])).

fof(c_0_83,plain,(
    ! [X28,X29] : k4_xboole_0(X28,k4_xboole_0(X28,X29)) = k3_xboole_0(X28,X29) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_84,plain,
    ( r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))),X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_72])).

cnf(c_0_85,plain,
    ( k9_subset_1(X1,X2,X2) = X2 ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_86,plain,
    ( k9_subset_1(X2,X3,X1) = k1_setfam_1(k2_tarski(X3,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_75,c_0_42])).

cnf(c_0_87,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

fof(c_0_88,plain,(
    ! [X51,X52,X53] :
      ( ~ m1_subset_1(X52,k1_zfmisc_1(X51))
      | k7_subset_1(X51,X52,X53) = k4_xboole_0(X52,X53) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

cnf(c_0_89,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X3) ),
    inference(rw,[status(thm)],[c_0_77,c_0_52])).

cnf(c_0_90,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_91,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_92,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X2)))) ),
    inference(spm,[status(thm)],[c_0_82,c_0_63])).

fof(c_0_93,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_94,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

fof(c_0_95,plain,(
    ! [X30,X31,X32] : k4_xboole_0(X30,k4_xboole_0(X31,X32)) = k2_xboole_0(k4_xboole_0(X30,X31),k3_xboole_0(X30,X32)) ),
    inference(variable_rename,[status(thm)],[t52_xboole_1])).

cnf(c_0_96,plain,
    ( k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(X1,k1_xboole_0))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_70,c_0_84])).

cnf(c_0_97,plain,
    ( k1_setfam_1(k2_tarski(X1,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_98,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_79])).

cnf(c_0_99,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_xboole_0))) = X1 ),
    inference(rw,[status(thm)],[c_0_87,c_0_52])).

cnf(c_0_100,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

cnf(c_0_101,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_67]),c_0_90]),c_0_91])])).

cnf(c_0_102,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1))),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_92,c_0_79])).

cnf(c_0_103,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

fof(c_0_104,plain,(
    ! [X33,X34] :
      ( ~ m1_subset_1(X34,k1_zfmisc_1(X33))
      | k3_subset_1(X33,X34) = k4_xboole_0(X33,X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_105,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))))) = k1_setfam_1(k2_tarski(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94,c_0_42]),c_0_52]),c_0_52])).

cnf(c_0_106,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_95])).

cnf(c_0_107,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_96,c_0_67])).

cnf(c_0_108,plain,
    ( k1_setfam_1(k2_tarski(X1,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_109,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(k1_xboole_0,X1))) = X1 ),
    inference(spm,[status(thm)],[c_0_99,c_0_72])).

cnf(c_0_110,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_91])).

fof(c_0_111,plain,(
    ! [X40,X41,X42] :
      ( ~ m1_subset_1(X42,k1_zfmisc_1(X40))
      | m1_subset_1(k9_subset_1(X40,X41,X42),k1_zfmisc_1(X40)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).

fof(c_0_112,plain,(
    ! [X57,X58,X59] :
      ( ~ m1_subset_1(X58,k1_zfmisc_1(X57))
      | ~ m1_subset_1(X59,k1_zfmisc_1(X57))
      | k7_subset_1(X57,X58,X59) = k9_subset_1(X57,X58,k3_subset_1(X57,X59)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_subset_1])])])).

fof(c_0_113,plain,(
    ! [X35,X36] :
      ( ~ m1_subset_1(X36,k1_zfmisc_1(X35))
      | m1_subset_1(k3_subset_1(X35,X36),k1_zfmisc_1(X35)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

cnf(c_0_114,plain,
    ( k7_subset_1(X2,X1,X3) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_100,c_0_52])).

cnf(c_0_115,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_xboole_0(X2,X3)))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_62,c_0_101])).

fof(c_0_116,plain,(
    ! [X37,X38,X39] :
      ( ~ m1_subset_1(X38,k1_zfmisc_1(X37))
      | ~ m1_subset_1(X39,k1_zfmisc_1(X37))
      | m1_subset_1(k4_subset_1(X37,X38,X39),k1_zfmisc_1(X37)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_subset_1])])).

fof(c_0_117,plain,(
    ! [X79,X80] :
      ( ~ l1_pre_topc(X79)
      | ~ m1_subset_1(X80,k1_zfmisc_1(u1_struct_0(X79)))
      | k2_pre_topc(X79,X80) = k4_subset_1(u1_struct_0(X79),X80,k2_tops_1(X79,X80)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_tops_1])])])).

fof(c_0_118,plain,(
    ! [X68,X69] :
      ( ~ l1_pre_topc(X68)
      | ~ m1_subset_1(X69,k1_zfmisc_1(u1_struct_0(X68)))
      | m1_subset_1(k2_tops_1(X68,X69),k1_zfmisc_1(u1_struct_0(X68))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_1])])).

cnf(c_0_119,negated_conjecture,
    ( r1_tarski(esk2_0,k2_xboole_0(X1,u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_89,c_0_102])).

cnf(c_0_120,plain,
    ( k2_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_103,c_0_57])).

cnf(c_0_121,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))))) ),
    inference(spm,[status(thm)],[c_0_89,c_0_79])).

cnf(c_0_122,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_104])).

cnf(c_0_123,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_105])).

cnf(c_0_124,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3)))))) = k2_xboole_0(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_setfam_1(k2_tarski(X1,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_106,c_0_42]),c_0_52]),c_0_52]),c_0_52])).

cnf(c_0_125,plain,
    ( k1_setfam_1(k2_tarski(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_105]),c_0_81]),c_0_108]),c_0_79])])).

cnf(c_0_126,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_67]),c_0_91])])).

cnf(c_0_127,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_128,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_110,c_0_48])).

cnf(c_0_129,plain,
    ( m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_111])).

cnf(c_0_130,plain,
    ( k7_subset_1(X2,X1,X3) = k9_subset_1(X2,X1,k3_subset_1(X2,X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_112])).

cnf(c_0_131,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_113])).

cnf(c_0_132,negated_conjecture,
    ( v3_pre_topc(esk2_0,esk1_0)
    | k2_tops_1(esk1_0,esk2_0) = k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_133,plain,
    ( k7_subset_1(X1,X2,X3) = k7_subset_1(X4,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_114,c_0_114])).

cnf(c_0_134,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_115,c_0_57])).

cnf(c_0_135,plain,
    ( m1_subset_1(k4_subset_1(X2,X1,X3),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_116])).

cnf(c_0_136,plain,
    ( k2_pre_topc(X1,X2) = k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_117])).

cnf(c_0_137,plain,
    ( m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_118])).

cnf(c_0_138,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_89,c_0_63])).

cnf(c_0_139,negated_conjecture,
    ( r1_tarski(esk2_0,X1)
    | ~ r1_tarski(u1_struct_0(esk1_0),X1) ),
    inference(spm,[status(thm)],[c_0_119,c_0_120])).

cnf(c_0_140,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))))) ),
    inference(spm,[status(thm)],[c_0_121,c_0_72])).

cnf(c_0_141,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_122,c_0_52])).

cnf(c_0_142,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_72,c_0_67])).

cnf(c_0_143,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_123,c_0_72])).

cnf(c_0_144,plain,
    ( k2_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_125]),c_0_126]),c_0_99]),c_0_99])).

cnf(c_0_145,plain,
    ( X1 = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_127,c_0_128])).

cnf(c_0_146,plain,
    ( m1_subset_1(k7_subset_1(X1,X2,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_129,c_0_130]),c_0_131])).

cnf(c_0_147,negated_conjecture,
    ( k7_subset_1(X1,k2_pre_topc(esk1_0,esk2_0),esk2_0) = k2_tops_1(esk1_0,esk2_0)
    | v3_pre_topc(esk2_0,esk1_0)
    | ~ m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_132,c_0_133])).

cnf(c_0_148,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_134,c_0_48])).

cnf(c_0_149,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_136]),c_0_137])).

cnf(c_0_150,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X3,k1_setfam_1(k2_tarski(X3,X2))))))) ),
    inference(spm,[status(thm)],[c_0_138,c_0_124])).

fof(c_0_151,plain,(
    ! [X60] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X60)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_152,negated_conjecture,
    ( r1_tarski(esk2_0,k2_xboole_0(X1,k5_xboole_0(u1_struct_0(esk1_0),k1_setfam_1(k2_tarski(X1,u1_struct_0(esk1_0)))))) ),
    inference(spm,[status(thm)],[c_0_139,c_0_140])).

cnf(c_0_153,plain,
    ( k5_xboole_0(X1,X2) = k3_subset_1(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_141,c_0_142]),c_0_48])).

cnf(c_0_154,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(X1,X2)),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_143])).

cnf(c_0_155,plain,
    ( k2_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))) = X1 ),
    inference(spm,[status(thm)],[c_0_144,c_0_72])).

cnf(c_0_156,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_145,c_0_123])).

fof(c_0_157,plain,(
    ! [X46,X47] :
      ( ~ m1_subset_1(X47,k1_zfmisc_1(X46))
      | k3_subset_1(X46,k3_subset_1(X46,X47)) = X47 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

cnf(c_0_158,plain,
    ( k7_subset_1(X1,X2,X3) = k3_subset_1(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_141,c_0_114])).

cnf(c_0_159,negated_conjecture,
    ( v3_pre_topc(esk2_0,esk1_0)
    | m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_146,c_0_147])).

cnf(c_0_160,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(u1_struct_0(X1),X3) ),
    inference(spm,[status(thm)],[c_0_148,c_0_149])).

cnf(c_0_161,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_162,plain,
    ( X1 = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_127,c_0_48])).

cnf(c_0_163,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1))))),k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_150,c_0_108]),c_0_90]),c_0_72])).

cnf(c_0_164,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_151])).

cnf(c_0_165,plain,
    ( k9_subset_1(X1,X2,X3) = X2
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_67,c_0_86])).

cnf(c_0_166,negated_conjecture,
    ( r1_tarski(esk2_0,k2_xboole_0(X1,k3_subset_1(u1_struct_0(esk1_0),k1_setfam_1(k2_tarski(X1,u1_struct_0(esk1_0)))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_152,c_0_153]),c_0_154])])).

cnf(c_0_167,plain,
    ( k2_xboole_0(X1,X2) = X1
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_155,c_0_156])).

cnf(c_0_168,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_157])).

cnf(c_0_169,negated_conjecture,
    ( k3_subset_1(k2_pre_topc(esk1_0,esk2_0),esk2_0) = k2_tops_1(esk1_0,esk2_0)
    | v3_pre_topc(esk2_0,esk1_0)
    | ~ m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(k2_pre_topc(esk1_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_132,c_0_158])).

cnf(c_0_170,negated_conjecture,
    ( v3_pre_topc(esk2_0,esk1_0)
    | m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_159,c_0_160]),c_0_161]),c_0_59]),c_0_79])])).

cnf(c_0_171,plain,
    ( k2_xboole_0(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_setfam_1(k2_tarski(X1,X3))) = k3_subset_1(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3))))
    | ~ m1_subset_1(k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3))),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_141,c_0_124])).

cnf(c_0_172,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_56,c_0_103])).

cnf(c_0_173,plain,
    ( k1_setfam_1(k2_tarski(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1))))) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_162,c_0_163]),c_0_164])])).

cnf(c_0_174,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(X1,X2)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_123])).

cnf(c_0_175,plain,
    ( k3_subset_1(X1,k1_xboole_0) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_141]),c_0_164])])).

cnf(c_0_176,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_129,c_0_165])).

cnf(c_0_177,negated_conjecture,
    ( r1_tarski(esk2_0,k2_xboole_0(X1,k3_subset_1(u1_struct_0(esk1_0),X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_166,c_0_156])).

cnf(c_0_178,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_103,c_0_167])).

cnf(c_0_179,plain,
    ( k7_subset_1(X1,k3_subset_1(X1,X2),X2) = k3_subset_1(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_130]),c_0_131])).

cnf(c_0_180,negated_conjecture,
    ( k3_subset_1(k2_pre_topc(esk1_0,esk2_0),k2_tops_1(esk1_0,esk2_0)) = esk2_0
    | v3_pre_topc(esk2_0,esk1_0)
    | ~ m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(k2_pre_topc(esk1_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_168,c_0_169])).

cnf(c_0_181,negated_conjecture,
    ( v3_pre_topc(esk2_0,esk1_0)
    | m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(k2_pre_topc(esk1_0,esk2_0)))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(k2_pre_topc(esk1_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_170,c_0_98])).

cnf(c_0_182,plain,
    ( k3_subset_1(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))) = k1_setfam_1(k2_tarski(X1,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_171,c_0_108]),c_0_90]),c_0_172]),c_0_74])])).

cnf(c_0_183,plain,
    ( k1_setfam_1(k2_tarski(X1,k3_subset_1(X2,k1_setfam_1(k2_tarski(X2,X1))))) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_173,c_0_153]),c_0_174])])).

cnf(c_0_184,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk2_0,X1),u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_102,c_0_142])).

cnf(c_0_185,plain,
    ( r1_tarski(k5_xboole_0(X1,k9_subset_1(X2,X3,X1)),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_84,c_0_86])).

cnf(c_0_186,plain,
    ( k9_subset_1(X1,X2,X1) = k7_subset_1(X1,X2,k1_xboole_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130,c_0_175]),c_0_164])])).

cnf(c_0_187,plain,
    ( k7_subset_1(X1,X2,X3) = X2
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,k3_subset_1(X1,X3)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_130,c_0_165]),c_0_176]),c_0_131])).

cnf(c_0_188,negated_conjecture,
    ( r1_tarski(esk2_0,k3_subset_1(u1_struct_0(esk1_0),X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_177,c_0_178])).

cnf(c_0_189,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_128])).

fof(c_0_190,plain,(
    ! [X81,X82] :
      ( ~ l1_pre_topc(X81)
      | ~ m1_subset_1(X82,k1_zfmisc_1(u1_struct_0(X81)))
      | k1_tops_1(X81,X82) = k7_subset_1(u1_struct_0(X81),X82,k2_tops_1(X81,X82)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_tops_1])])])).

cnf(c_0_191,negated_conjecture,
    ( k7_subset_1(k2_pre_topc(esk1_0,esk2_0),esk2_0,k2_tops_1(esk1_0,esk2_0)) = esk2_0
    | v3_pre_topc(esk2_0,esk1_0)
    | ~ m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(k2_pre_topc(esk1_0,esk2_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_179,c_0_180]),c_0_181])).

fof(c_0_192,plain,(
    ! [X48,X49,X50] :
      ( ~ m1_subset_1(X49,k1_zfmisc_1(X48))
      | ~ m1_subset_1(X50,k1_zfmisc_1(X48))
      | k4_subset_1(X48,X49,X50) = k2_xboole_0(X49,X50) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

fof(c_0_193,plain,(
    ! [X77,X78] :
      ( ~ l1_pre_topc(X77)
      | ~ m1_subset_1(X78,k1_zfmisc_1(u1_struct_0(X77)))
      | k2_tops_1(X77,X78) = k2_tops_1(X77,k3_subset_1(u1_struct_0(X77),X78)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_tops_1])])])).

cnf(c_0_194,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_168,c_0_182]),c_0_74])])).

cnf(c_0_195,plain,
    ( k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,X2))) = k1_xboole_0
    | ~ r1_tarski(k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,X2))),X2) ),
    inference(spm,[status(thm)],[c_0_142,c_0_183])).

cnf(c_0_196,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk2_0,X1),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_184,c_0_141]),c_0_123])])).

cnf(c_0_197,plain,
    ( r1_tarski(k5_xboole_0(X1,k7_subset_1(X1,X2,k1_xboole_0)),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_185,c_0_186]),c_0_98])])).

cnf(c_0_198,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1) = esk2_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_187,c_0_188]),c_0_189])).

cnf(c_0_199,plain,
    ( k1_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_190])).

cnf(c_0_200,negated_conjecture,
    ( k7_subset_1(X1,esk2_0,k2_tops_1(esk1_0,esk2_0)) = esk2_0
    | v3_pre_topc(esk2_0,esk1_0)
    | ~ m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(k2_pre_topc(esk1_0,esk2_0)))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_133,c_0_191])).

cnf(c_0_201,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_108]),c_0_90]),c_0_91])])).

cnf(c_0_202,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_192])).

cnf(c_0_203,plain,
    ( r1_tarski(k5_xboole_0(X1,X2),X1)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_84,c_0_67])).

cnf(c_0_204,plain,
    ( k2_tops_1(X1,X2) = k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_193])).

cnf(c_0_205,plain,
    ( k3_subset_1(X1,k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,X2)))) = k1_setfam_1(k2_tarski(X1,X2)) ),
    inference(rw,[status(thm)],[c_0_182,c_0_194])).

cnf(c_0_206,negated_conjecture,
    ( k3_subset_1(esk2_0,k1_setfam_1(k2_tarski(esk2_0,u1_struct_0(esk1_0)))) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_195,c_0_196]),c_0_174])])).

cnf(c_0_207,negated_conjecture,
    ( r1_tarski(k5_xboole_0(u1_struct_0(esk1_0),esk2_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_197,c_0_198]),c_0_59]),c_0_164])])).

cnf(c_0_208,negated_conjecture,
    ( k1_tops_1(esk1_0,esk2_0) = esk2_0
    | v3_pre_topc(esk2_0,esk1_0)
    | ~ m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(k2_pre_topc(esk1_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_199,c_0_200]),c_0_161]),c_0_59])])).

cnf(c_0_209,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_62,c_0_201])).

cnf(c_0_210,plain,
    ( k2_xboole_0(X1,k2_tops_1(X2,X1)) = k2_pre_topc(X2,X1)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_202,c_0_136]),c_0_137])).

fof(c_0_211,plain,(
    ! [X74,X75,X76] :
      ( ~ l1_pre_topc(X74)
      | ~ m1_subset_1(X75,k1_zfmisc_1(u1_struct_0(X74)))
      | ~ m1_subset_1(X76,k1_zfmisc_1(u1_struct_0(X74)))
      | ~ v3_pre_topc(X75,X74)
      | ~ r1_tarski(X75,X76)
      | r1_tarski(X75,k1_tops_1(X74,X76)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_tops_1])])])).

cnf(c_0_212,plain,
    ( r1_tarski(k7_subset_1(X1,X2,X3),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_203,c_0_114]),c_0_123])])).

cnf(c_0_213,plain,
    ( k7_subset_1(u1_struct_0(X1),k3_subset_1(u1_struct_0(X1),X2),k2_tops_1(X1,X2)) = k1_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_199,c_0_204]),c_0_131])).

cnf(c_0_214,plain,
    ( k3_subset_1(X1,k3_subset_1(X1,k1_setfam_1(k2_tarski(X2,X1)))) = k1_setfam_1(k2_tarski(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_205,c_0_72])).

cnf(c_0_215,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk2_0,u1_struct_0(esk1_0))) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_168,c_0_206]),c_0_175]),c_0_174])])).

cnf(c_0_216,negated_conjecture,
    ( r1_tarski(k3_subset_1(u1_struct_0(esk1_0),esk2_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_207,c_0_153]),c_0_59])])).

fof(c_0_217,plain,(
    ! [X70,X71] :
      ( ~ v2_pre_topc(X70)
      | ~ l1_pre_topc(X70)
      | ~ m1_subset_1(X71,k1_zfmisc_1(u1_struct_0(X70)))
      | v3_pre_topc(k1_tops_1(X70,X71),X70) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).

cnf(c_0_218,negated_conjecture,
    ( k1_tops_1(esk1_0,esk2_0) = esk2_0
    | v3_pre_topc(esk2_0,esk1_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(k2_pre_topc(esk1_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_208,c_0_160]),c_0_161]),c_0_59]),c_0_79])])).

cnf(c_0_219,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_pre_topc(X2,X1)))
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(spm,[status(thm)],[c_0_209,c_0_210])).

cnf(c_0_220,plain,
    ( r1_tarski(X2,k1_tops_1(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X2,X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_211])).

cnf(c_0_221,plain,
    ( r1_tarski(k1_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2)),k3_subset_1(u1_struct_0(X1),X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_212,c_0_213]),c_0_131])).

cnf(c_0_222,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_214,c_0_215])).

cnf(c_0_223,negated_conjecture,
    ( m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_62,c_0_216])).

cnf(c_0_224,plain,
    ( v3_pre_topc(k1_tops_1(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_217])).

cnf(c_0_225,negated_conjecture,
    ( k1_tops_1(esk1_0,esk2_0) = esk2_0
    | v3_pre_topc(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_218,c_0_219]),c_0_161]),c_0_59])])).

cnf(c_0_226,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_227,plain,(
    ! [X72,X73] :
      ( ~ l1_pre_topc(X72)
      | ~ m1_subset_1(X73,k1_zfmisc_1(u1_struct_0(X72)))
      | k2_tops_1(X72,X73) = k7_subset_1(u1_struct_0(X72),k2_pre_topc(X72,X73),k1_tops_1(X72,X73)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l78_tops_1])])])).

cnf(c_0_228,plain,
    ( k1_tops_1(X1,X2) = X3
    | ~ v3_pre_topc(X3,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k1_tops_1(X1,X2),X3)
    | ~ r1_tarski(X3,X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_220]),c_0_176])).

cnf(c_0_229,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk2_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_221,c_0_222]),c_0_161]),c_0_223])])).

cnf(c_0_230,negated_conjecture,
    ( v3_pre_topc(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_224,c_0_225]),c_0_226]),c_0_161]),c_0_59])])).

cnf(c_0_231,negated_conjecture,
    ( ~ v3_pre_topc(esk2_0,esk1_0)
    | k2_tops_1(esk1_0,esk2_0) != k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_232,plain,
    ( k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_227])).

cnf(c_0_233,negated_conjecture,
    ( k1_tops_1(esk1_0,esk2_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_228,c_0_229]),c_0_230]),c_0_161]),c_0_59]),c_0_79])])).

cnf(c_0_234,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0) != k2_tops_1(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_231,c_0_230])])).

cnf(c_0_235,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_232,c_0_233]),c_0_161]),c_0_59])]),c_0_234]),
    [proof]).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 13:37:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 14.71/14.94  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 14.71/14.94  # and selection function SelectMaxLComplexAvoidPosPred.
% 14.71/14.94  #
% 14.71/14.94  # Preprocessing time       : 0.029 s
% 14.71/14.94  
% 14.71/14.94  # Proof found!
% 14.71/14.94  # SZS status Theorem
% 14.71/14.94  # SZS output start CNFRefutation
% 14.71/14.94  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 14.71/14.94  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 14.71/14.94  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 14.71/14.94  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 14.71/14.94  fof(t76_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_tops_1)).
% 14.71/14.94  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 14.71/14.94  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 14.71/14.94  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 14.71/14.94  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 14.71/14.94  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 14.71/14.94  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 14.71/14.94  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 14.71/14.94  fof(idempotence_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k9_subset_1)).
% 14.71/14.94  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 14.71/14.94  fof(t44_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k4_xboole_0(X1,X2),X3)=>r1_tarski(X1,k2_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 14.71/14.94  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 14.71/14.94  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 14.71/14.94  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 14.71/14.94  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 14.71/14.94  fof(t52_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 14.71/14.94  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 14.71/14.94  fof(dt_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 14.71/14.94  fof(t32_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k9_subset_1(X1,X2,k3_subset_1(X1,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_subset_1)).
% 14.71/14.94  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 14.71/14.94  fof(dt_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 14.71/14.94  fof(t65_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_pre_topc(X1,X2)=k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 14.71/14.94  fof(dt_k2_tops_1, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 14.71/14.94  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 14.71/14.94  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 14.71/14.94  fof(t74_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k1_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 14.71/14.94  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 14.71/14.94  fof(t62_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_tops_1(X1,X2)=k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tops_1)).
% 14.71/14.94  fof(t56_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v3_pre_topc(X2,X1)&r1_tarski(X2,X3))=>r1_tarski(X2,k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tops_1)).
% 14.71/14.94  fof(fc9_tops_1, axiom, ![X1, X2]:(((v2_pre_topc(X1)&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v3_pre_topc(k1_tops_1(X1,X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 14.71/14.94  fof(l78_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 14.71/14.94  fof(c_0_35, plain, ![X12, X13]:k4_xboole_0(X12,X13)=k5_xboole_0(X12,k3_xboole_0(X12,X13)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 14.71/14.94  fof(c_0_36, plain, ![X61, X62]:k1_setfam_1(k2_tarski(X61,X62))=k3_xboole_0(X61,X62), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 14.71/14.94  fof(c_0_37, plain, ![X17, X18, X19]:(~r1_tarski(X17,X18)|~r1_tarski(X18,X19)|r1_tarski(X17,X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 14.71/14.94  fof(c_0_38, plain, ![X63, X64]:((~m1_subset_1(X63,k1_zfmisc_1(X64))|r1_tarski(X63,X64))&(~r1_tarski(X63,X64)|m1_subset_1(X63,k1_zfmisc_1(X64)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 14.71/14.94  fof(c_0_39, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2))))), inference(assume_negation,[status(cth)],[t76_tops_1])).
% 14.71/14.94  fof(c_0_40, plain, ![X22, X23]:r1_tarski(k4_xboole_0(X22,X23),X22), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 14.71/14.94  cnf(c_0_41, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 14.71/14.94  cnf(c_0_42, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 14.71/14.94  fof(c_0_43, plain, ![X10, X11]:((k4_xboole_0(X10,X11)!=k1_xboole_0|r1_tarski(X10,X11))&(~r1_tarski(X10,X11)|k4_xboole_0(X10,X11)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 14.71/14.94  fof(c_0_44, plain, ![X20, X21]:(~r1_tarski(X20,X21)|k3_xboole_0(X20,X21)=X20), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 14.71/14.94  fof(c_0_45, plain, ![X16]:k2_xboole_0(X16,k1_xboole_0)=X16, inference(variable_rename,[status(thm)],[t1_boole])).
% 14.71/14.94  fof(c_0_46, plain, ![X14, X15]:(~r1_tarski(X14,X15)|k2_xboole_0(X14,X15)=X15), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 14.71/14.94  cnf(c_0_47, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 14.71/14.94  cnf(c_0_48, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 14.71/14.94  fof(c_0_49, negated_conjecture, ((v2_pre_topc(esk1_0)&l1_pre_topc(esk1_0))&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&((~v3_pre_topc(esk2_0,esk1_0)|k2_tops_1(esk1_0,esk2_0)!=k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0))&(v3_pre_topc(esk2_0,esk1_0)|k2_tops_1(esk1_0,esk2_0)=k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_39])])])).
% 14.71/14.94  fof(c_0_50, plain, ![X6, X7]:k3_xboole_0(X6,X7)=k3_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 14.71/14.94  cnf(c_0_51, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 14.71/14.94  cnf(c_0_52, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_41, c_0_42])).
% 14.71/14.94  cnf(c_0_53, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 14.71/14.94  cnf(c_0_54, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 14.71/14.94  fof(c_0_55, plain, ![X8, X9]:(((r1_tarski(X8,X9)|X8!=X9)&(r1_tarski(X9,X8)|X8!=X9))&(~r1_tarski(X8,X9)|~r1_tarski(X9,X8)|X8=X9)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 14.71/14.94  cnf(c_0_56, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_45])).
% 14.71/14.94  cnf(c_0_57, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 14.71/14.94  cnf(c_0_58, plain, (r1_tarski(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 14.71/14.94  cnf(c_0_59, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 14.71/14.94  cnf(c_0_60, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 14.71/14.94  fof(c_0_61, plain, ![X43, X44, X45]:(~m1_subset_1(X45,k1_zfmisc_1(X43))|k9_subset_1(X43,X44,X44)=X44), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[idempotence_k9_subset_1])])).
% 14.71/14.94  cnf(c_0_62, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 14.71/14.94  cnf(c_0_63, plain, (r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X1)), inference(rw,[status(thm)],[c_0_51, c_0_52])).
% 14.71/14.94  fof(c_0_64, plain, ![X54, X55, X56]:(~m1_subset_1(X56,k1_zfmisc_1(X54))|k9_subset_1(X54,X55,X56)=k3_xboole_0(X55,X56)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 14.71/14.94  fof(c_0_65, plain, ![X25, X26, X27]:(~r1_tarski(k4_xboole_0(X25,X26),X27)|r1_tarski(X25,k2_xboole_0(X26,X27))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).
% 14.71/14.94  cnf(c_0_66, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k1_xboole_0|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_53, c_0_52])).
% 14.71/14.94  cnf(c_0_67, plain, (k1_setfam_1(k2_tarski(X1,X2))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_54, c_0_42])).
% 14.71/14.94  cnf(c_0_68, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_55])).
% 14.71/14.94  cnf(c_0_69, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_43])).
% 14.71/14.94  cnf(c_0_70, plain, (k1_xboole_0=X1|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 14.71/14.94  cnf(c_0_71, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 14.71/14.94  cnf(c_0_72, plain, (k1_setfam_1(k2_tarski(X1,X2))=k1_setfam_1(k2_tarski(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_42]), c_0_42])).
% 14.71/14.94  cnf(c_0_73, plain, (k9_subset_1(X2,X3,X3)=X3|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 14.71/14.94  cnf(c_0_74, plain, (m1_subset_1(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 14.71/14.94  cnf(c_0_75, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_64])).
% 14.71/14.94  fof(c_0_76, plain, ![X24]:k4_xboole_0(X24,k1_xboole_0)=X24, inference(variable_rename,[status(thm)],[t3_boole])).
% 14.71/14.94  cnf(c_0_77, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 14.71/14.94  cnf(c_0_78, plain, (k5_xboole_0(X1,X1)=k1_xboole_0|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 14.71/14.94  cnf(c_0_79, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_68])).
% 14.71/14.94  cnf(c_0_80, plain, (r1_tarski(X1,X2)|k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_69, c_0_52])).
% 14.71/14.94  cnf(c_0_81, plain, (k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,X1)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_70, c_0_63])).
% 14.71/14.94  cnf(c_0_82, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X2,esk2_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_47, c_0_71])).
% 14.71/14.94  fof(c_0_83, plain, ![X28, X29]:k4_xboole_0(X28,k4_xboole_0(X28,X29))=k3_xboole_0(X28,X29), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 14.71/14.94  cnf(c_0_84, plain, (r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))),X1)), inference(spm,[status(thm)],[c_0_63, c_0_72])).
% 14.71/14.94  cnf(c_0_85, plain, (k9_subset_1(X1,X2,X2)=X2), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 14.71/14.94  cnf(c_0_86, plain, (k9_subset_1(X2,X3,X1)=k1_setfam_1(k2_tarski(X3,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_75, c_0_42])).
% 14.71/14.94  cnf(c_0_87, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_76])).
% 14.71/14.94  fof(c_0_88, plain, ![X51, X52, X53]:(~m1_subset_1(X52,k1_zfmisc_1(X51))|k7_subset_1(X51,X52,X53)=k4_xboole_0(X52,X53)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 14.71/14.94  cnf(c_0_89, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X3)), inference(rw,[status(thm)],[c_0_77, c_0_52])).
% 14.71/14.94  cnf(c_0_90, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 14.71/14.94  cnf(c_0_91, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 14.71/14.94  cnf(c_0_92, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X1,k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X2))))), inference(spm,[status(thm)],[c_0_82, c_0_63])).
% 14.71/14.94  fof(c_0_93, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 14.71/14.94  cnf(c_0_94, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_83])).
% 14.71/14.94  fof(c_0_95, plain, ![X30, X31, X32]:k4_xboole_0(X30,k4_xboole_0(X31,X32))=k2_xboole_0(k4_xboole_0(X30,X31),k3_xboole_0(X30,X32)), inference(variable_rename,[status(thm)],[t52_xboole_1])).
% 14.71/14.94  cnf(c_0_96, plain, (k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(X1,k1_xboole_0)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_70, c_0_84])).
% 14.71/14.94  cnf(c_0_97, plain, (k1_setfam_1(k2_tarski(X1,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 14.71/14.94  cnf(c_0_98, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_62, c_0_79])).
% 14.71/14.94  cnf(c_0_99, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_xboole_0)))=X1), inference(rw,[status(thm)],[c_0_87, c_0_52])).
% 14.71/14.94  cnf(c_0_100, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_88])).
% 14.71/14.94  cnf(c_0_101, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_67]), c_0_90]), c_0_91])])).
% 14.71/14.94  cnf(c_0_102, negated_conjecture, (r1_tarski(k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1))),u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_92, c_0_79])).
% 14.71/14.94  cnf(c_0_103, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_93])).
% 14.71/14.94  fof(c_0_104, plain, ![X33, X34]:(~m1_subset_1(X34,k1_zfmisc_1(X33))|k3_subset_1(X33,X34)=k4_xboole_0(X33,X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 14.71/14.94  cnf(c_0_105, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))))))=k1_setfam_1(k2_tarski(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94, c_0_42]), c_0_52]), c_0_52])).
% 14.71/14.94  cnf(c_0_106, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_95])).
% 14.71/14.94  cnf(c_0_107, plain, (k5_xboole_0(k1_xboole_0,X1)=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_96, c_0_67])).
% 14.71/14.94  cnf(c_0_108, plain, (k1_setfam_1(k2_tarski(X1,X1))=X1), inference(spm,[status(thm)],[c_0_97, c_0_98])).
% 14.71/14.94  cnf(c_0_109, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(k1_xboole_0,X1)))=X1), inference(spm,[status(thm)],[c_0_99, c_0_72])).
% 14.71/14.94  cnf(c_0_110, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_47, c_0_91])).
% 14.71/14.94  fof(c_0_111, plain, ![X40, X41, X42]:(~m1_subset_1(X42,k1_zfmisc_1(X40))|m1_subset_1(k9_subset_1(X40,X41,X42),k1_zfmisc_1(X40))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).
% 14.71/14.94  fof(c_0_112, plain, ![X57, X58, X59]:(~m1_subset_1(X58,k1_zfmisc_1(X57))|(~m1_subset_1(X59,k1_zfmisc_1(X57))|k7_subset_1(X57,X58,X59)=k9_subset_1(X57,X58,k3_subset_1(X57,X59)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_subset_1])])])).
% 14.71/14.94  fof(c_0_113, plain, ![X35, X36]:(~m1_subset_1(X36,k1_zfmisc_1(X35))|m1_subset_1(k3_subset_1(X35,X36),k1_zfmisc_1(X35))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 14.71/14.94  cnf(c_0_114, plain, (k7_subset_1(X2,X1,X3)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_100, c_0_52])).
% 14.71/14.94  cnf(c_0_115, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_xboole_0(X2,X3)))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_62, c_0_101])).
% 14.71/14.94  fof(c_0_116, plain, ![X37, X38, X39]:(~m1_subset_1(X38,k1_zfmisc_1(X37))|~m1_subset_1(X39,k1_zfmisc_1(X37))|m1_subset_1(k4_subset_1(X37,X38,X39),k1_zfmisc_1(X37))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_subset_1])])).
% 14.71/14.94  fof(c_0_117, plain, ![X79, X80]:(~l1_pre_topc(X79)|(~m1_subset_1(X80,k1_zfmisc_1(u1_struct_0(X79)))|k2_pre_topc(X79,X80)=k4_subset_1(u1_struct_0(X79),X80,k2_tops_1(X79,X80)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_tops_1])])])).
% 14.71/14.94  fof(c_0_118, plain, ![X68, X69]:(~l1_pre_topc(X68)|~m1_subset_1(X69,k1_zfmisc_1(u1_struct_0(X68)))|m1_subset_1(k2_tops_1(X68,X69),k1_zfmisc_1(u1_struct_0(X68)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_1])])).
% 14.71/14.94  cnf(c_0_119, negated_conjecture, (r1_tarski(esk2_0,k2_xboole_0(X1,u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_89, c_0_102])).
% 14.71/14.94  cnf(c_0_120, plain, (k2_xboole_0(X1,X2)=X1|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_103, c_0_57])).
% 14.71/14.94  cnf(c_0_121, plain, (r1_tarski(X1,k2_xboole_0(X2,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))))), inference(spm,[status(thm)],[c_0_89, c_0_79])).
% 14.71/14.94  cnf(c_0_122, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_104])).
% 14.71/14.94  cnf(c_0_123, plain, (r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X1)), inference(spm,[status(thm)],[c_0_63, c_0_105])).
% 14.71/14.94  cnf(c_0_124, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3))))))=k2_xboole_0(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_setfam_1(k2_tarski(X1,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_106, c_0_42]), c_0_52]), c_0_52]), c_0_52])).
% 14.71/14.94  cnf(c_0_125, plain, (k1_setfam_1(k2_tarski(k1_xboole_0,X1))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_105]), c_0_81]), c_0_108]), c_0_79])])).
% 14.71/14.94  cnf(c_0_126, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_67]), c_0_91])])).
% 14.71/14.94  cnf(c_0_127, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 14.71/14.94  cnf(c_0_128, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_110, c_0_48])).
% 14.71/14.94  cnf(c_0_129, plain, (m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_111])).
% 14.71/14.94  cnf(c_0_130, plain, (k7_subset_1(X2,X1,X3)=k9_subset_1(X2,X1,k3_subset_1(X2,X3))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_112])).
% 14.71/14.94  cnf(c_0_131, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_113])).
% 14.71/14.94  cnf(c_0_132, negated_conjecture, (v3_pre_topc(esk2_0,esk1_0)|k2_tops_1(esk1_0,esk2_0)=k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 14.71/14.94  cnf(c_0_133, plain, (k7_subset_1(X1,X2,X3)=k7_subset_1(X4,X2,X3)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X4))), inference(spm,[status(thm)],[c_0_114, c_0_114])).
% 14.71/14.94  cnf(c_0_134, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X3)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_115, c_0_57])).
% 14.71/14.94  cnf(c_0_135, plain, (m1_subset_1(k4_subset_1(X2,X1,X3),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_116])).
% 14.71/14.94  cnf(c_0_136, plain, (k2_pre_topc(X1,X2)=k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_117])).
% 14.71/14.94  cnf(c_0_137, plain, (m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_118])).
% 14.71/14.94  cnf(c_0_138, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_89, c_0_63])).
% 14.71/14.94  cnf(c_0_139, negated_conjecture, (r1_tarski(esk2_0,X1)|~r1_tarski(u1_struct_0(esk1_0),X1)), inference(spm,[status(thm)],[c_0_119, c_0_120])).
% 14.71/14.94  cnf(c_0_140, plain, (r1_tarski(X1,k2_xboole_0(X2,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1)))))), inference(spm,[status(thm)],[c_0_121, c_0_72])).
% 14.71/14.94  cnf(c_0_141, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_122, c_0_52])).
% 14.71/14.94  cnf(c_0_142, plain, (k1_setfam_1(k2_tarski(X1,X2))=X2|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_72, c_0_67])).
% 14.71/14.94  cnf(c_0_143, plain, (r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_123, c_0_72])).
% 14.71/14.94  cnf(c_0_144, plain, (k2_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124, c_0_125]), c_0_126]), c_0_99]), c_0_99])).
% 14.71/14.94  cnf(c_0_145, plain, (X1=X2|~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_127, c_0_128])).
% 14.71/14.94  cnf(c_0_146, plain, (m1_subset_1(k7_subset_1(X1,X2,X3),k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_129, c_0_130]), c_0_131])).
% 14.71/14.94  cnf(c_0_147, negated_conjecture, (k7_subset_1(X1,k2_pre_topc(esk1_0,esk2_0),esk2_0)=k2_tops_1(esk1_0,esk2_0)|v3_pre_topc(esk2_0,esk1_0)|~m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_132, c_0_133])).
% 14.71/14.94  cnf(c_0_148, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X3))|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_134, c_0_48])).
% 14.71/14.94  cnf(c_0_149, plain, (m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_135, c_0_136]), c_0_137])).
% 14.71/14.94  cnf(c_0_150, plain, (r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X3,k1_setfam_1(k2_tarski(X3,X2)))))))), inference(spm,[status(thm)],[c_0_138, c_0_124])).
% 14.71/14.94  fof(c_0_151, plain, ![X60]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X60)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 14.71/14.94  cnf(c_0_152, negated_conjecture, (r1_tarski(esk2_0,k2_xboole_0(X1,k5_xboole_0(u1_struct_0(esk1_0),k1_setfam_1(k2_tarski(X1,u1_struct_0(esk1_0))))))), inference(spm,[status(thm)],[c_0_139, c_0_140])).
% 14.71/14.94  cnf(c_0_153, plain, (k5_xboole_0(X1,X2)=k3_subset_1(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_141, c_0_142]), c_0_48])).
% 14.71/14.94  cnf(c_0_154, plain, (m1_subset_1(k1_setfam_1(k2_tarski(X1,X2)),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_62, c_0_143])).
% 14.71/14.94  cnf(c_0_155, plain, (k2_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1)))=X1), inference(spm,[status(thm)],[c_0_144, c_0_72])).
% 14.71/14.94  cnf(c_0_156, plain, (k1_setfam_1(k2_tarski(X1,X2))=X1|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_145, c_0_123])).
% 14.71/14.94  fof(c_0_157, plain, ![X46, X47]:(~m1_subset_1(X47,k1_zfmisc_1(X46))|k3_subset_1(X46,k3_subset_1(X46,X47))=X47), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 14.71/14.94  cnf(c_0_158, plain, (k7_subset_1(X1,X2,X3)=k3_subset_1(X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_141, c_0_114])).
% 14.71/14.94  cnf(c_0_159, negated_conjecture, (v3_pre_topc(esk2_0,esk1_0)|m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(X1))|~m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(X1))|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_146, c_0_147])).
% 14.71/14.94  cnf(c_0_160, plain, (m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(u1_struct_0(X1),X3)), inference(spm,[status(thm)],[c_0_148, c_0_149])).
% 14.71/14.94  cnf(c_0_161, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 14.71/14.94  cnf(c_0_162, plain, (X1=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_127, c_0_48])).
% 14.71/14.94  cnf(c_0_163, plain, (r1_tarski(k1_setfam_1(k2_tarski(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1))))),k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_150, c_0_108]), c_0_90]), c_0_72])).
% 14.71/14.94  cnf(c_0_164, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_151])).
% 14.71/14.94  cnf(c_0_165, plain, (k9_subset_1(X1,X2,X3)=X2|~m1_subset_1(X3,k1_zfmisc_1(X1))|~r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_67, c_0_86])).
% 14.71/14.94  cnf(c_0_166, negated_conjecture, (r1_tarski(esk2_0,k2_xboole_0(X1,k3_subset_1(u1_struct_0(esk1_0),k1_setfam_1(k2_tarski(X1,u1_struct_0(esk1_0))))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_152, c_0_153]), c_0_154])])).
% 14.71/14.94  cnf(c_0_167, plain, (k2_xboole_0(X1,X2)=X1|~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_155, c_0_156])).
% 14.71/14.94  cnf(c_0_168, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_157])).
% 14.71/14.94  cnf(c_0_169, negated_conjecture, (k3_subset_1(k2_pre_topc(esk1_0,esk2_0),esk2_0)=k2_tops_1(esk1_0,esk2_0)|v3_pre_topc(esk2_0,esk1_0)|~m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(esk2_0,k1_zfmisc_1(k2_pre_topc(esk1_0,esk2_0)))), inference(spm,[status(thm)],[c_0_132, c_0_158])).
% 14.71/14.94  cnf(c_0_170, negated_conjecture, (v3_pre_topc(esk2_0,esk1_0)|m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(X1))|~m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(X1))|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_159, c_0_160]), c_0_161]), c_0_59]), c_0_79])])).
% 14.71/14.94  cnf(c_0_171, plain, (k2_xboole_0(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_setfam_1(k2_tarski(X1,X3)))=k3_subset_1(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3))))|~m1_subset_1(k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3))),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_141, c_0_124])).
% 14.71/14.94  cnf(c_0_172, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_56, c_0_103])).
% 14.71/14.94  cnf(c_0_173, plain, (k1_setfam_1(k2_tarski(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_162, c_0_163]), c_0_164])])).
% 14.71/14.94  cnf(c_0_174, plain, (m1_subset_1(k1_setfam_1(k2_tarski(X1,X2)),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_62, c_0_123])).
% 14.71/14.94  cnf(c_0_175, plain, (k3_subset_1(X1,k1_xboole_0)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_141]), c_0_164])])).
% 14.71/14.94  cnf(c_0_176, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_129, c_0_165])).
% 14.71/14.94  cnf(c_0_177, negated_conjecture, (r1_tarski(esk2_0,k2_xboole_0(X1,k3_subset_1(u1_struct_0(esk1_0),X1)))|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_166, c_0_156])).
% 14.71/14.94  cnf(c_0_178, plain, (k2_xboole_0(X1,X2)=X2|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_103, c_0_167])).
% 14.71/14.94  cnf(c_0_179, plain, (k7_subset_1(X1,k3_subset_1(X1,X2),X2)=k3_subset_1(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_130]), c_0_131])).
% 14.71/14.94  cnf(c_0_180, negated_conjecture, (k3_subset_1(k2_pre_topc(esk1_0,esk2_0),k2_tops_1(esk1_0,esk2_0))=esk2_0|v3_pre_topc(esk2_0,esk1_0)|~m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(esk2_0,k1_zfmisc_1(k2_pre_topc(esk1_0,esk2_0)))), inference(spm,[status(thm)],[c_0_168, c_0_169])).
% 14.71/14.94  cnf(c_0_181, negated_conjecture, (v3_pre_topc(esk2_0,esk1_0)|m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(k2_pre_topc(esk1_0,esk2_0)))|~m1_subset_1(esk2_0,k1_zfmisc_1(k2_pre_topc(esk1_0,esk2_0)))), inference(spm,[status(thm)],[c_0_170, c_0_98])).
% 14.71/14.94  cnf(c_0_182, plain, (k3_subset_1(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))))=k1_setfam_1(k2_tarski(X1,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_171, c_0_108]), c_0_90]), c_0_172]), c_0_74])])).
% 14.71/14.94  cnf(c_0_183, plain, (k1_setfam_1(k2_tarski(X1,k3_subset_1(X2,k1_setfam_1(k2_tarski(X2,X1)))))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_173, c_0_153]), c_0_174])])).
% 14.71/14.94  cnf(c_0_184, negated_conjecture, (r1_tarski(k5_xboole_0(esk2_0,X1),u1_struct_0(esk1_0))|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_102, c_0_142])).
% 14.71/14.94  cnf(c_0_185, plain, (r1_tarski(k5_xboole_0(X1,k9_subset_1(X2,X3,X1)),X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_84, c_0_86])).
% 14.71/14.94  cnf(c_0_186, plain, (k9_subset_1(X1,X2,X1)=k7_subset_1(X1,X2,k1_xboole_0)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130, c_0_175]), c_0_164])])).
% 14.71/14.94  cnf(c_0_187, plain, (k7_subset_1(X1,X2,X3)=X2|~m1_subset_1(X3,k1_zfmisc_1(X1))|~r1_tarski(X2,k3_subset_1(X1,X3))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_130, c_0_165]), c_0_176]), c_0_131])).
% 14.71/14.94  cnf(c_0_188, negated_conjecture, (r1_tarski(esk2_0,k3_subset_1(u1_struct_0(esk1_0),X1))|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_177, c_0_178])).
% 14.71/14.94  cnf(c_0_189, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_62, c_0_128])).
% 14.71/14.94  fof(c_0_190, plain, ![X81, X82]:(~l1_pre_topc(X81)|(~m1_subset_1(X82,k1_zfmisc_1(u1_struct_0(X81)))|k1_tops_1(X81,X82)=k7_subset_1(u1_struct_0(X81),X82,k2_tops_1(X81,X82)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_tops_1])])])).
% 14.71/14.94  cnf(c_0_191, negated_conjecture, (k7_subset_1(k2_pre_topc(esk1_0,esk2_0),esk2_0,k2_tops_1(esk1_0,esk2_0))=esk2_0|v3_pre_topc(esk2_0,esk1_0)|~m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(esk2_0,k1_zfmisc_1(k2_pre_topc(esk1_0,esk2_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_179, c_0_180]), c_0_181])).
% 14.71/14.94  fof(c_0_192, plain, ![X48, X49, X50]:(~m1_subset_1(X49,k1_zfmisc_1(X48))|~m1_subset_1(X50,k1_zfmisc_1(X48))|k4_subset_1(X48,X49,X50)=k2_xboole_0(X49,X50)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 14.71/14.94  fof(c_0_193, plain, ![X77, X78]:(~l1_pre_topc(X77)|(~m1_subset_1(X78,k1_zfmisc_1(u1_struct_0(X77)))|k2_tops_1(X77,X78)=k2_tops_1(X77,k3_subset_1(u1_struct_0(X77),X78)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_tops_1])])])).
% 14.71/14.94  cnf(c_0_194, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_168, c_0_182]), c_0_74])])).
% 14.71/14.94  cnf(c_0_195, plain, (k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,X2)))=k1_xboole_0|~r1_tarski(k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,X2))),X2)), inference(spm,[status(thm)],[c_0_142, c_0_183])).
% 14.71/14.94  cnf(c_0_196, negated_conjecture, (r1_tarski(k3_subset_1(esk2_0,X1),u1_struct_0(esk1_0))|~m1_subset_1(X1,k1_zfmisc_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_184, c_0_141]), c_0_123])])).
% 14.71/14.94  cnf(c_0_197, plain, (r1_tarski(k5_xboole_0(X1,k7_subset_1(X1,X2,k1_xboole_0)),X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_185, c_0_186]), c_0_98])])).
% 14.71/14.94  cnf(c_0_198, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)=esk2_0|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_187, c_0_188]), c_0_189])).
% 14.71/14.94  cnf(c_0_199, plain, (k1_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_190])).
% 14.71/14.94  cnf(c_0_200, negated_conjecture, (k7_subset_1(X1,esk2_0,k2_tops_1(esk1_0,esk2_0))=esk2_0|v3_pre_topc(esk2_0,esk1_0)|~m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(esk2_0,k1_zfmisc_1(k2_pre_topc(esk1_0,esk2_0)))|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_133, c_0_191])).
% 14.71/14.94  cnf(c_0_201, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_108]), c_0_90]), c_0_91])])).
% 14.71/14.94  cnf(c_0_202, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_192])).
% 14.71/14.94  cnf(c_0_203, plain, (r1_tarski(k5_xboole_0(X1,X2),X1)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_84, c_0_67])).
% 14.71/14.94  cnf(c_0_204, plain, (k2_tops_1(X1,X2)=k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_193])).
% 14.71/14.94  cnf(c_0_205, plain, (k3_subset_1(X1,k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,X2))))=k1_setfam_1(k2_tarski(X1,X2))), inference(rw,[status(thm)],[c_0_182, c_0_194])).
% 14.71/14.94  cnf(c_0_206, negated_conjecture, (k3_subset_1(esk2_0,k1_setfam_1(k2_tarski(esk2_0,u1_struct_0(esk1_0))))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_195, c_0_196]), c_0_174])])).
% 14.71/14.94  cnf(c_0_207, negated_conjecture, (r1_tarski(k5_xboole_0(u1_struct_0(esk1_0),esk2_0),u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_197, c_0_198]), c_0_59]), c_0_164])])).
% 14.71/14.94  cnf(c_0_208, negated_conjecture, (k1_tops_1(esk1_0,esk2_0)=esk2_0|v3_pre_topc(esk2_0,esk1_0)|~m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(esk2_0,k1_zfmisc_1(k2_pre_topc(esk1_0,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_199, c_0_200]), c_0_161]), c_0_59])])).
% 14.71/14.94  cnf(c_0_209, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_62, c_0_201])).
% 14.71/14.94  cnf(c_0_210, plain, (k2_xboole_0(X1,k2_tops_1(X2,X1))=k2_pre_topc(X2,X1)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_202, c_0_136]), c_0_137])).
% 14.71/14.94  fof(c_0_211, plain, ![X74, X75, X76]:(~l1_pre_topc(X74)|(~m1_subset_1(X75,k1_zfmisc_1(u1_struct_0(X74)))|(~m1_subset_1(X76,k1_zfmisc_1(u1_struct_0(X74)))|(~v3_pre_topc(X75,X74)|~r1_tarski(X75,X76)|r1_tarski(X75,k1_tops_1(X74,X76)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_tops_1])])])).
% 14.71/14.94  cnf(c_0_212, plain, (r1_tarski(k7_subset_1(X1,X2,X3),X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_203, c_0_114]), c_0_123])])).
% 14.71/14.94  cnf(c_0_213, plain, (k7_subset_1(u1_struct_0(X1),k3_subset_1(u1_struct_0(X1),X2),k2_tops_1(X1,X2))=k1_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_199, c_0_204]), c_0_131])).
% 14.71/14.94  cnf(c_0_214, plain, (k3_subset_1(X1,k3_subset_1(X1,k1_setfam_1(k2_tarski(X2,X1))))=k1_setfam_1(k2_tarski(X2,X1))), inference(spm,[status(thm)],[c_0_205, c_0_72])).
% 14.71/14.94  cnf(c_0_215, negated_conjecture, (k1_setfam_1(k2_tarski(esk2_0,u1_struct_0(esk1_0)))=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_168, c_0_206]), c_0_175]), c_0_174])])).
% 14.71/14.94  cnf(c_0_216, negated_conjecture, (r1_tarski(k3_subset_1(u1_struct_0(esk1_0),esk2_0),u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_207, c_0_153]), c_0_59])])).
% 14.71/14.94  fof(c_0_217, plain, ![X70, X71]:(~v2_pre_topc(X70)|~l1_pre_topc(X70)|~m1_subset_1(X71,k1_zfmisc_1(u1_struct_0(X70)))|v3_pre_topc(k1_tops_1(X70,X71),X70)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).
% 14.71/14.94  cnf(c_0_218, negated_conjecture, (k1_tops_1(esk1_0,esk2_0)=esk2_0|v3_pre_topc(esk2_0,esk1_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(k2_pre_topc(esk1_0,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_208, c_0_160]), c_0_161]), c_0_59]), c_0_79])])).
% 14.71/14.94  cnf(c_0_219, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_pre_topc(X2,X1)))|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(spm,[status(thm)],[c_0_209, c_0_210])).
% 14.71/14.94  cnf(c_0_220, plain, (r1_tarski(X2,k1_tops_1(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v3_pre_topc(X2,X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_211])).
% 14.71/14.94  cnf(c_0_221, plain, (r1_tarski(k1_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2)),k3_subset_1(u1_struct_0(X1),X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_212, c_0_213]), c_0_131])).
% 14.71/14.94  cnf(c_0_222, negated_conjecture, (k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))=esk2_0), inference(spm,[status(thm)],[c_0_214, c_0_215])).
% 14.71/14.94  cnf(c_0_223, negated_conjecture, (m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_62, c_0_216])).
% 14.71/14.94  cnf(c_0_224, plain, (v3_pre_topc(k1_tops_1(X1,X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_217])).
% 14.71/14.94  cnf(c_0_225, negated_conjecture, (k1_tops_1(esk1_0,esk2_0)=esk2_0|v3_pre_topc(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_218, c_0_219]), c_0_161]), c_0_59])])).
% 14.71/14.94  cnf(c_0_226, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 14.71/14.94  fof(c_0_227, plain, ![X72, X73]:(~l1_pre_topc(X72)|(~m1_subset_1(X73,k1_zfmisc_1(u1_struct_0(X72)))|k2_tops_1(X72,X73)=k7_subset_1(u1_struct_0(X72),k2_pre_topc(X72,X73),k1_tops_1(X72,X73)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l78_tops_1])])])).
% 14.71/14.94  cnf(c_0_228, plain, (k1_tops_1(X1,X2)=X3|~v3_pre_topc(X3,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k1_tops_1(X1,X2),X3)|~r1_tarski(X3,X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_127, c_0_220]), c_0_176])).
% 14.71/14.94  cnf(c_0_229, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,esk2_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_221, c_0_222]), c_0_161]), c_0_223])])).
% 14.71/14.94  cnf(c_0_230, negated_conjecture, (v3_pre_topc(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_224, c_0_225]), c_0_226]), c_0_161]), c_0_59])])).
% 14.71/14.94  cnf(c_0_231, negated_conjecture, (~v3_pre_topc(esk2_0,esk1_0)|k2_tops_1(esk1_0,esk2_0)!=k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 14.71/14.94  cnf(c_0_232, plain, (k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_227])).
% 14.71/14.94  cnf(c_0_233, negated_conjecture, (k1_tops_1(esk1_0,esk2_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_228, c_0_229]), c_0_230]), c_0_161]), c_0_59]), c_0_79])])).
% 14.71/14.94  cnf(c_0_234, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0)!=k2_tops_1(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_231, c_0_230])])).
% 14.71/14.94  cnf(c_0_235, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_232, c_0_233]), c_0_161]), c_0_59])]), c_0_234]), ['proof']).
% 14.71/14.94  # SZS output end CNFRefutation
% 14.71/14.94  # Proof object total steps             : 236
% 14.71/14.94  # Proof object clause steps            : 165
% 14.71/14.94  # Proof object formula steps           : 71
% 14.71/14.94  # Proof object conjectures             : 43
% 14.71/14.94  # Proof object clause conjectures      : 40
% 14.71/14.94  # Proof object formula conjectures     : 3
% 14.71/14.94  # Proof object initial clauses used    : 42
% 14.71/14.94  # Proof object initial formulas used   : 35
% 14.71/14.94  # Proof object generating inferences   : 107
% 14.71/14.94  # Proof object simplifying inferences  : 114
% 14.71/14.94  # Training examples: 0 positive, 0 negative
% 14.71/14.94  # Parsed axioms                        : 36
% 14.71/14.94  # Removed by relevancy pruning/SinE    : 0
% 14.71/14.94  # Initial clauses                      : 44
% 14.71/14.94  # Removed in clause preprocessing      : 2
% 14.71/14.94  # Initial clauses in saturation        : 42
% 14.71/14.94  # Processed clauses                    : 94300
% 14.71/14.94  # ...of these trivial                  : 9061
% 14.71/14.94  # ...subsumed                          : 77583
% 14.71/14.94  # ...remaining for further processing  : 7656
% 14.71/14.94  # Other redundant clauses eliminated   : 703
% 14.71/14.94  # Clauses deleted for lack of memory   : 0
% 14.71/14.94  # Backward-subsumed                    : 553
% 14.71/14.94  # Backward-rewritten                   : 892
% 14.71/14.94  # Generated clauses                    : 1909815
% 14.71/14.94  # ...of the previous two non-trivial   : 1511234
% 14.71/14.94  # Contextual simplify-reflections      : 281
% 14.71/14.94  # Paramodulations                      : 1909112
% 14.71/14.94  # Factorizations                       : 0
% 14.71/14.94  # Equation resolutions                 : 703
% 14.71/14.94  # Propositional unsat checks           : 0
% 14.71/14.94  #    Propositional check models        : 0
% 14.71/14.94  #    Propositional check unsatisfiable : 0
% 14.71/14.94  #    Propositional clauses             : 0
% 14.71/14.94  #    Propositional clauses after purity: 0
% 14.71/14.94  #    Propositional unsat core size     : 0
% 14.71/14.94  #    Propositional preprocessing time  : 0.000
% 14.71/14.94  #    Propositional encoding time       : 0.000
% 14.71/14.94  #    Propositional solver time         : 0.000
% 14.71/14.94  #    Success case prop preproc time    : 0.000
% 14.71/14.94  #    Success case prop encoding time   : 0.000
% 14.71/14.94  #    Success case prop solver time     : 0.000
% 14.71/14.94  # Current number of processed clauses  : 6209
% 14.71/14.94  #    Positive orientable unit clauses  : 1753
% 14.71/14.94  #    Positive unorientable unit clauses: 10
% 14.71/14.94  #    Negative unit clauses             : 44
% 14.71/14.94  #    Non-unit-clauses                  : 4402
% 14.71/14.94  # Current number of unprocessed clauses: 1399819
% 14.71/14.94  # ...number of literals in the above   : 4272647
% 14.71/14.94  # Current number of archived formulas  : 0
% 14.71/14.94  # Current number of archived clauses   : 1447
% 14.71/14.94  # Clause-clause subsumption calls (NU) : 4709771
% 14.71/14.94  # Rec. Clause-clause subsumption calls : 2770120
% 14.71/14.94  # Non-unit clause-clause subsumptions  : 59199
% 14.71/14.94  # Unit Clause-clause subsumption calls : 34335
% 14.71/14.94  # Rewrite failures with RHS unbound    : 0
% 14.71/14.94  # BW rewrite match attempts            : 124060
% 14.71/14.94  # BW rewrite match successes           : 236
% 14.71/14.94  # Condensation attempts                : 0
% 14.71/14.94  # Condensation successes               : 0
% 14.71/14.94  # Termbank termtop insertions          : 29576133
% 14.81/14.99  
% 14.81/14.99  # -------------------------------------------------
% 14.81/14.99  # User time                : 14.072 s
% 14.81/14.99  # System time              : 0.573 s
% 14.81/14.99  # Total time               : 14.645 s
% 14.81/14.99  # Maximum resident set size: 1604 pages
%------------------------------------------------------------------------------

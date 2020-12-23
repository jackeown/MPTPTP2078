%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:11:15 EST 2020

% Result     : Theorem 5.47s
% Output     : CNFRefutation 5.47s
% Verified   : 
% Statistics : Number of formulae       :  189 (5989 expanded)
%              Number of clauses        :  130 (2642 expanded)
%              Number of leaves         :   29 (1519 expanded)
%              Depth                    :   23
%              Number of atoms          :  361 (13216 expanded)
%              Number of equality atoms :  114 (4529 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t51_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(dt_k6_subset_1,axiom,(
    ! [X1,X2] : m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t76_tops_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).

fof(t62_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_tops_1(X1,X2) = k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(t43_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_xboole_0(X2,X3))
     => r1_tarski(k4_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(t65_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_pre_topc(X1,X2) = k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

fof(dt_k2_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(dt_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t74_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k1_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

fof(l78_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(t38_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k4_xboole_0(X2,X1))
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

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

fof(c_0_29,plain,(
    ! [X8,X9] : k4_xboole_0(X8,X9) = k5_xboole_0(X8,k3_xboole_0(X8,X9)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_30,plain,(
    ! [X54,X55] : k1_setfam_1(k2_tarski(X54,X55)) = k3_xboole_0(X54,X55) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_31,plain,(
    ! [X10] : k2_xboole_0(X10,k1_xboole_0) = X10 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_32,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_33,plain,(
    ! [X21,X22] : k2_xboole_0(k3_xboole_0(X21,X22),k4_xboole_0(X21,X22)) = X21 ),
    inference(variable_rename,[status(thm)],[t51_xboole_1])).

cnf(c_0_34,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_36,plain,(
    ! [X23,X24] : r1_tarski(X23,k2_xboole_0(X23,X24)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_37,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_40,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_34,c_0_35])).

fof(c_0_41,plain,(
    ! [X34,X35] : m1_subset_1(k6_subset_1(X34,X35),k1_zfmisc_1(X34)) ),
    inference(variable_rename,[status(thm)],[dt_k6_subset_1])).

fof(c_0_42,plain,(
    ! [X46,X47] : k6_subset_1(X46,X47) = k4_xboole_0(X46,X47) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

fof(c_0_43,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | X6 != X7 )
      & ( r1_tarski(X7,X6)
        | X6 != X7 )
      & ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,X6)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_45,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_46,plain,
    ( k2_xboole_0(k1_setfam_1(k2_tarski(X1,X2)),k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_35]),c_0_40])).

fof(c_0_47,plain,(
    ! [X25,X26] : k2_tarski(X25,X26) = k2_tarski(X26,X25) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

fof(c_0_48,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v3_pre_topc(X2,X1)
            <=> k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t76_tops_1])).

cnf(c_0_49,plain,
    ( m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_50,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_51,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_52,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_53,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_46])).

cnf(c_0_54,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

fof(c_0_55,plain,(
    ! [X67,X68] :
      ( ~ l1_pre_topc(X67)
      | ~ m1_subset_1(X68,k1_zfmisc_1(u1_struct_0(X67)))
      | k2_tops_1(X67,X68) = k2_tops_1(X67,k3_subset_1(u1_struct_0(X67),X68)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_tops_1])])])).

fof(c_0_56,negated_conjecture,
    ( v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & ( ~ v3_pre_topc(esk3_0,esk2_0)
      | k2_tops_1(esk2_0,esk3_0) != k7_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),esk3_0) )
    & ( v3_pre_topc(esk3_0,esk2_0)
      | k2_tops_1(esk2_0,esk3_0) = k7_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_48])])])).

fof(c_0_57,plain,(
    ! [X56,X57] :
      ( ( ~ m1_subset_1(X56,k1_zfmisc_1(X57))
        | r1_tarski(X56,X57) )
      & ( ~ r1_tarski(X56,X57)
        | m1_subset_1(X56,k1_zfmisc_1(X57)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_58,plain,(
    ! [X29,X30] :
      ( ~ m1_subset_1(X30,k1_zfmisc_1(X29))
      | m1_subset_1(k3_subset_1(X29,X30),k1_zfmisc_1(X29)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

cnf(c_0_59,plain,
    ( m1_subset_1(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_50]),c_0_40])).

cnf(c_0_60,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_61,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

fof(c_0_62,plain,(
    ! [X18,X19,X20] :
      ( ~ r1_tarski(X18,k2_xboole_0(X19,X20))
      | r1_tarski(k4_xboole_0(X18,X19),X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).

fof(c_0_63,plain,(
    ! [X69,X70] :
      ( ~ l1_pre_topc(X69)
      | ~ m1_subset_1(X70,k1_zfmisc_1(u1_struct_0(X69)))
      | k2_pre_topc(X69,X70) = k4_subset_1(u1_struct_0(X69),X70,k2_tops_1(X69,X70)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_tops_1])])])).

fof(c_0_64,plain,(
    ! [X58,X59] :
      ( ~ l1_pre_topc(X58)
      | ~ m1_subset_1(X59,k1_zfmisc_1(u1_struct_0(X58)))
      | m1_subset_1(k2_tops_1(X58,X59),k1_zfmisc_1(u1_struct_0(X58))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_1])])).

cnf(c_0_65,plain,
    ( k2_tops_1(X1,X2) = k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_66,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_67,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_68,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_69,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_70,plain,
    ( m1_subset_1(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_54])).

cnf(c_0_71,plain,
    ( k1_setfam_1(k2_tarski(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_60,c_0_53])).

cnf(c_0_72,plain,
    ( k1_setfam_1(k2_tarski(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_73,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

fof(c_0_74,plain,(
    ! [X31,X32,X33] :
      ( ~ m1_subset_1(X32,k1_zfmisc_1(X31))
      | ~ m1_subset_1(X33,k1_zfmisc_1(X31))
      | m1_subset_1(k4_subset_1(X31,X32,X33),k1_zfmisc_1(X31)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_subset_1])])).

cnf(c_0_75,plain,
    ( k2_pre_topc(X1,X2) = k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_76,plain,
    ( m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_77,negated_conjecture,
    ( k2_tops_1(esk2_0,k3_subset_1(u1_struct_0(esk2_0),esk3_0)) = k2_tops_1(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67])])).

cnf(c_0_78,plain,
    ( r1_tarski(k3_subset_1(X1,X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

fof(c_0_79,plain,(
    ! [X43,X44,X45] :
      ( ~ m1_subset_1(X44,k1_zfmisc_1(X43))
      | ~ m1_subset_1(X45,k1_zfmisc_1(X43))
      | k4_subset_1(X43,X44,X45) = k2_xboole_0(X44,X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_80,plain,
    ( m1_subset_1(k5_xboole_0(X1,k1_xboole_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_81,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_72]),c_0_45])).

cnf(c_0_82,plain,
    ( r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[c_0_73,c_0_40])).

fof(c_0_83,plain,(
    ! [X48,X49,X50] :
      ( ~ m1_subset_1(X49,k1_zfmisc_1(X48))
      | k7_subset_1(X48,X49,X50) = k4_xboole_0(X49,X50) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

cnf(c_0_84,plain,
    ( m1_subset_1(k4_subset_1(X2,X1,X3),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_85,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk2_0),esk3_0,k2_tops_1(esk2_0,esk3_0)) = k2_pre_topc(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_66]),c_0_67])])).

cnf(c_0_86,negated_conjecture,
    ( m1_subset_1(k2_tops_1(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(esk2_0),esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_67])])).

cnf(c_0_87,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_88,negated_conjecture,
    ( r1_tarski(k3_subset_1(u1_struct_0(esk2_0),esk3_0),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_78,c_0_66])).

cnf(c_0_89,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_90,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_91,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_82]),c_0_37])).

cnf(c_0_92,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_93,negated_conjecture,
    ( m1_subset_1(k2_pre_topc(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(k2_tops_1(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_66])])).

cnf(c_0_94,negated_conjecture,
    ( m1_subset_1(k2_tops_1(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_88])])).

cnf(c_0_95,plain,
    ( k4_subset_1(X1,X2,X1) = k2_xboole_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_96,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_91]),c_0_37])).

cnf(c_0_97,plain,
    ( k7_subset_1(X2,X1,X3) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_92,c_0_40])).

cnf(c_0_98,negated_conjecture,
    ( m1_subset_1(k2_pre_topc(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_93,c_0_94])])).

fof(c_0_99,plain,(
    ! [X11,X12,X13] :
      ( ~ r1_tarski(X11,X12)
      | ~ r1_tarski(X12,X13)
      | r1_tarski(X11,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_100,plain,(
    ! [X71,X72] :
      ( ~ l1_pre_topc(X71)
      | ~ m1_subset_1(X72,k1_zfmisc_1(u1_struct_0(X71)))
      | k1_tops_1(X71,X72) = k7_subset_1(u1_struct_0(X71),X72,k2_tops_1(X71,X72)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_tops_1])])])).

cnf(c_0_101,plain,
    ( k4_subset_1(X1,X2,X1) = k2_xboole_0(X2,X1)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_95,c_0_87])).

cnf(c_0_102,plain,
    ( m1_subset_1(k5_xboole_0(X1,X2),k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_70,c_0_96])).

cnf(c_0_103,negated_conjecture,
    ( k5_xboole_0(k2_pre_topc(esk2_0,esk3_0),k1_setfam_1(k2_tarski(k2_pre_topc(esk2_0,esk3_0),X1))) = k7_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),X1) ),
    inference(spm,[status(thm)],[c_0_97,c_0_98])).

fof(c_0_104,plain,(
    ! [X62,X63] :
      ( ~ l1_pre_topc(X62)
      | ~ m1_subset_1(X63,k1_zfmisc_1(u1_struct_0(X62)))
      | k2_tops_1(X62,X63) = k7_subset_1(u1_struct_0(X62),k2_pre_topc(X62,X63),k1_tops_1(X62,X63)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l78_tops_1])])])).

fof(c_0_105,plain,(
    ! [X16,X17] :
      ( ~ r1_tarski(X16,k4_xboole_0(X17,X16))
      | X16 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_xboole_1])])).

cnf(c_0_106,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_99])).

cnf(c_0_107,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk2_0),X1,k2_tops_1(esk2_0,esk3_0)) = k2_xboole_0(X1,k2_tops_1(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_89,c_0_94])).

fof(c_0_108,plain,(
    ! [X27,X28] :
      ( ~ m1_subset_1(X28,k1_zfmisc_1(X27))
      | k3_subset_1(X27,X28) = k4_xboole_0(X27,X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_109,plain,
    ( k1_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_100])).

cnf(c_0_110,plain,
    ( m1_subset_1(k2_xboole_0(X1,X2),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_101]),c_0_90])]),c_0_68])).

cnf(c_0_111,negated_conjecture,
    ( m1_subset_1(k7_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),X1),k1_zfmisc_1(k2_pre_topc(esk2_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_103]),c_0_53])])).

cnf(c_0_112,plain,
    ( k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_104])).

cnf(c_0_113,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_105])).

cnf(c_0_114,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_106,c_0_44])).

cnf(c_0_115,negated_conjecture,
    ( k2_xboole_0(esk3_0,k2_tops_1(esk2_0,esk3_0)) = k2_pre_topc(esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_66]),c_0_85])).

cnf(c_0_116,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_108])).

cnf(c_0_117,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk2_0),esk3_0,k2_tops_1(esk2_0,esk3_0)) = k1_tops_1(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_66]),c_0_67])])).

cnf(c_0_118,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk2_0),esk3_0,X1) = k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X1))) ),
    inference(spm,[status(thm)],[c_0_97,c_0_66])).

cnf(c_0_119,plain,
    ( r1_tarski(k2_xboole_0(X1,X2),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_110])).

cnf(c_0_120,negated_conjecture,
    ( m1_subset_1(k2_tops_1(esk2_0,esk3_0),k1_zfmisc_1(k2_pre_topc(esk2_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_112]),c_0_67]),c_0_66])])).

cnf(c_0_121,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))) ),
    inference(rw,[status(thm)],[c_0_113,c_0_40])).

cnf(c_0_122,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X4)
    | ~ r1_tarski(X4,X2) ),
    inference(spm,[status(thm)],[c_0_106,c_0_114])).

cnf(c_0_123,negated_conjecture,
    ( r1_tarski(esk3_0,k2_pre_topc(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_115])).

cnf(c_0_124,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_125,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_116,c_0_40])).

cnf(c_0_126,negated_conjecture,
    ( k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,k2_tops_1(esk2_0,esk3_0)))) = k1_tops_1(esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_117,c_0_118])).

cnf(c_0_127,negated_conjecture,
    ( r1_tarski(k2_xboole_0(k2_tops_1(esk2_0,esk3_0),k2_pre_topc(esk2_0,esk3_0)),k2_pre_topc(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_119,c_0_120])).

cnf(c_0_128,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_38])).

cnf(c_0_129,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k1_xboole_0
    | ~ r1_tarski(X1,k2_xboole_0(X2,k5_xboole_0(X3,k1_setfam_1(k2_tarski(X3,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))))))) ),
    inference(spm,[status(thm)],[c_0_121,c_0_82])).

cnf(c_0_130,plain,
    ( k7_subset_1(X1,X2,X3) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3)))
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_97,c_0_87])).

cnf(c_0_131,negated_conjecture,
    ( r1_tarski(esk3_0,k2_xboole_0(X1,X2))
    | ~ r1_tarski(k2_pre_topc(esk2_0,esk3_0),X1) ),
    inference(spm,[status(thm)],[c_0_122,c_0_123])).

cnf(c_0_132,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_124])).

fof(c_0_133,plain,(
    ! [X41,X42] :
      ( ~ m1_subset_1(X42,k1_zfmisc_1(X41))
      | k3_subset_1(X41,k3_subset_1(X41,X42)) = X42 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

cnf(c_0_134,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k3_subset_1(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_125,c_0_87])).

cnf(c_0_135,negated_conjecture,
    ( r1_tarski(k2_pre_topc(esk2_0,esk3_0),u1_struct_0(esk2_0))
    | ~ m1_subset_1(k2_tops_1(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_68,c_0_93])).

cnf(c_0_136,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk2_0,esk3_0),X1)
    | ~ r1_tarski(esk3_0,k2_xboole_0(k2_tops_1(esk2_0,esk3_0),X1)) ),
    inference(spm,[status(thm)],[c_0_82,c_0_126])).

cnf(c_0_137,negated_conjecture,
    ( k2_xboole_0(k2_tops_1(esk2_0,esk3_0),k2_pre_topc(esk2_0,esk3_0)) = k2_pre_topc(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_127]),c_0_128])])).

fof(c_0_138,plain,(
    ! [X14,X15] : r1_tarski(k4_xboole_0(X14,X15),X14) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_139,plain,
    ( k7_subset_1(X1,X2,X3) = k1_xboole_0
    | ~ r1_tarski(X2,k2_xboole_0(X3,k5_xboole_0(X4,k1_setfam_1(k2_tarski(X4,k7_subset_1(X1,X2,X3))))))
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_129,c_0_130])).

cnf(c_0_140,negated_conjecture,
    ( r1_tarski(esk3_0,k2_xboole_0(k2_pre_topc(esk2_0,esk3_0),X1)) ),
    inference(spm,[status(thm)],[c_0_131,c_0_132])).

fof(c_0_141,plain,(
    ! [X64,X65,X66] :
      ( ~ l1_pre_topc(X64)
      | ~ m1_subset_1(X65,k1_zfmisc_1(u1_struct_0(X64)))
      | ~ m1_subset_1(X66,k1_zfmisc_1(u1_struct_0(X64)))
      | ~ v3_pre_topc(X65,X64)
      | ~ r1_tarski(X65,X66)
      | r1_tarski(X65,k1_tops_1(X64,X66)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_tops_1])])])).

cnf(c_0_142,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_133])).

cnf(c_0_143,negated_conjecture,
    ( v3_pre_topc(esk3_0,esk2_0)
    | k2_tops_1(esk2_0,esk3_0) = k7_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_144,plain,
    ( k7_subset_1(X1,X2,X3) = k3_subset_1(X2,X3)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_134,c_0_130])).

cnf(c_0_145,negated_conjecture,
    ( r1_tarski(k2_pre_topc(esk2_0,esk3_0),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_76]),c_0_67]),c_0_66])])).

cnf(c_0_146,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),X1) = k3_subset_1(k2_pre_topc(esk2_0,esk3_0),X1)
    | ~ r1_tarski(X1,k2_pre_topc(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_134,c_0_103])).

cnf(c_0_147,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk2_0,esk3_0),k2_pre_topc(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136,c_0_137]),c_0_123])])).

cnf(c_0_148,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_138])).

cnf(c_0_149,plain,
    ( k2_xboole_0(k1_setfam_1(k2_tarski(X1,X2)),k7_subset_1(X3,X1,X2)) = X1
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_46,c_0_130])).

cnf(c_0_150,negated_conjecture,
    ( k7_subset_1(X1,esk3_0,k2_pre_topc(esk2_0,esk3_0)) = k1_xboole_0
    | ~ r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_139,c_0_140])).

cnf(c_0_151,plain,
    ( r1_tarski(X2,k1_tops_1(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X2,X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_141])).

cnf(c_0_152,negated_conjecture,
    ( r1_tarski(esk3_0,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_66])).

cnf(c_0_153,plain,
    ( k3_subset_1(X1,k3_subset_1(X1,X2)) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_142,c_0_87])).

cnf(c_0_154,negated_conjecture,
    ( k3_subset_1(k2_pre_topc(esk2_0,esk3_0),esk3_0) = k2_tops_1(esk2_0,esk3_0)
    | v3_pre_topc(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_144]),c_0_123]),c_0_145])])).

cnf(c_0_155,negated_conjecture,
    ( k3_subset_1(k2_pre_topc(esk2_0,esk3_0),k1_tops_1(esk2_0,esk3_0)) = k2_tops_1(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_146]),c_0_67]),c_0_66]),c_0_147])])).

cnf(c_0_156,plain,
    ( r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X1) ),
    inference(rw,[status(thm)],[c_0_148,c_0_40])).

cnf(c_0_157,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk3_0,k2_pre_topc(esk2_0,esk3_0))) = esk3_0
    | ~ r1_tarski(esk3_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_149,c_0_150]),c_0_37])).

cnf(c_0_158,negated_conjecture,
    ( r1_tarski(X1,k2_pre_topc(esk2_0,esk3_0))
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_114,c_0_115])).

fof(c_0_159,plain,(
    ! [X60,X61] :
      ( ~ v2_pre_topc(X60)
      | ~ l1_pre_topc(X60)
      | ~ m1_subset_1(X61,k1_zfmisc_1(u1_struct_0(X60)))
      | v3_pre_topc(k1_tops_1(X60,X61),X60) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).

cnf(c_0_160,negated_conjecture,
    ( r1_tarski(X1,k1_tops_1(esk2_0,esk3_0))
    | ~ v3_pre_topc(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_tarski(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_151,c_0_66]),c_0_67])])).

cnf(c_0_161,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk2_0))
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_106,c_0_152])).

cnf(c_0_162,negated_conjecture,
    ( k3_subset_1(k2_pre_topc(esk2_0,esk3_0),k2_tops_1(esk2_0,esk3_0)) = esk3_0
    | v3_pre_topc(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_153,c_0_154]),c_0_123])])).

cnf(c_0_163,negated_conjecture,
    ( k3_subset_1(k2_pre_topc(esk2_0,esk3_0),k2_tops_1(esk2_0,esk3_0)) = k1_tops_1(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_153,c_0_155]),c_0_147])])).

cnf(c_0_164,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk2_0,esk3_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_156,c_0_126])).

cnf(c_0_165,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))) = k3_subset_1(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_134,c_0_54])).

cnf(c_0_166,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk3_0,k2_pre_topc(esk2_0,esk3_0))) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_157,c_0_158]),c_0_132])])).

cnf(c_0_167,plain,
    ( v3_pre_topc(k1_tops_1(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_159])).

cnf(c_0_168,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_169,negated_conjecture,
    ( r1_tarski(X1,k1_tops_1(esk2_0,esk3_0))
    | ~ v3_pre_topc(X1,esk2_0)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_160,c_0_87]),c_0_161])).

cnf(c_0_170,negated_conjecture,
    ( k1_tops_1(esk2_0,esk3_0) = esk3_0
    | v3_pre_topc(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_162,c_0_163])).

cnf(c_0_171,negated_conjecture,
    ( k1_tops_1(esk2_0,esk3_0) = esk3_0
    | ~ r1_tarski(esk3_0,k1_tops_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_164])).

cnf(c_0_172,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))))) = k3_subset_1(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_125,c_0_59])).

cnf(c_0_173,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),k2_tops_1(esk2_0,esk3_0)) = k3_subset_1(k2_pre_topc(esk2_0,esk3_0),k2_tops_1(esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_120]),c_0_103])).

cnf(c_0_174,plain,
    ( k7_subset_1(X1,X2,X3) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X3,X2)))
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_130,c_0_54])).

cnf(c_0_175,negated_conjecture,
    ( k5_xboole_0(k2_pre_topc(esk2_0,esk3_0),esk3_0) = k3_subset_1(k2_pre_topc(esk2_0,esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_165,c_0_166]),c_0_123])])).

cnf(c_0_176,negated_conjecture,
    ( ~ v3_pre_topc(esk3_0,esk2_0)
    | k2_tops_1(esk2_0,esk3_0) != k7_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_177,negated_conjecture,
    ( v3_pre_topc(k1_tops_1(esk2_0,esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_167,c_0_66]),c_0_168]),c_0_67])])).

cnf(c_0_178,negated_conjecture,
    ( k1_tops_1(esk2_0,esk3_0) = esk3_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_169,c_0_170]),c_0_132])]),c_0_171])).

cnf(c_0_179,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),k7_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),X1)) = k3_subset_1(k2_pre_topc(esk2_0,esk3_0),k7_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_172,c_0_103]),c_0_103])).

cnf(c_0_180,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),k2_tops_1(esk2_0,esk3_0)) = k1_tops_1(esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_173,c_0_163])).

cnf(c_0_181,plain,
    ( k7_subset_1(X1,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_97,c_0_90])).

cnf(c_0_182,negated_conjecture,
    ( k7_subset_1(X1,k2_pre_topc(esk2_0,esk3_0),esk3_0) = k3_subset_1(k2_pre_topc(esk2_0,esk3_0),esk3_0)
    | ~ r1_tarski(k2_pre_topc(esk2_0,esk3_0),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_174,c_0_166]),c_0_175])).

cnf(c_0_183,negated_conjecture,
    ( k3_subset_1(k2_pre_topc(esk2_0,esk3_0),esk3_0) != k2_tops_1(esk2_0,esk3_0)
    | ~ v3_pre_topc(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_176,c_0_144]),c_0_123]),c_0_145])])).

cnf(c_0_184,negated_conjecture,
    ( v3_pre_topc(esk3_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_177,c_0_178])).

cnf(c_0_185,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),k1_tops_1(esk2_0,esk3_0)) = k2_tops_1(esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_179,c_0_180]),c_0_155])).

cnf(c_0_186,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),esk3_0) = k3_subset_1(k2_pre_topc(esk2_0,esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_181,c_0_182]),c_0_103]),c_0_132])])).

cnf(c_0_187,negated_conjecture,
    ( k3_subset_1(k2_pre_topc(esk2_0,esk3_0),esk3_0) != k2_tops_1(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_183,c_0_184])])).

cnf(c_0_188,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_185,c_0_178]),c_0_186]),c_0_187]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:38:00 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 5.47/5.70  # AutoSched0-Mode selected heuristic G_E___107_C36_F1_PI_AE_Q4_CS_SP_PS_S0Y
% 5.47/5.70  # and selection function SelectMaxLComplexAvoidPosPred.
% 5.47/5.70  #
% 5.47/5.70  # Preprocessing time       : 0.029 s
% 5.47/5.70  # Presaturation interreduction done
% 5.47/5.70  
% 5.47/5.70  # Proof found!
% 5.47/5.70  # SZS status Theorem
% 5.47/5.70  # SZS output start CNFRefutation
% 5.47/5.70  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.47/5.70  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 5.47/5.70  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 5.47/5.70  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 5.47/5.70  fof(t51_xboole_1, axiom, ![X1, X2]:k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 5.47/5.70  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 5.47/5.70  fof(dt_k6_subset_1, axiom, ![X1, X2]:m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 5.47/5.70  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 5.47/5.70  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.47/5.70  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 5.47/5.70  fof(t76_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_tops_1)).
% 5.47/5.70  fof(t62_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_tops_1(X1,X2)=k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_tops_1)).
% 5.47/5.70  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.47/5.70  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 5.47/5.70  fof(t43_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_xboole_0(X2,X3))=>r1_tarski(k4_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 5.47/5.70  fof(t65_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_pre_topc(X1,X2)=k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 5.47/5.70  fof(dt_k2_tops_1, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 5.47/5.70  fof(dt_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 5.47/5.70  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 5.47/5.70  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 5.47/5.70  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 5.47/5.70  fof(t74_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k1_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tops_1)).
% 5.47/5.70  fof(l78_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 5.47/5.70  fof(t38_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,k4_xboole_0(X2,X1))=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_xboole_1)).
% 5.47/5.70  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 5.47/5.70  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 5.47/5.70  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.47/5.70  fof(t56_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v3_pre_topc(X2,X1)&r1_tarski(X2,X3))=>r1_tarski(X2,k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tops_1)).
% 5.47/5.70  fof(fc9_tops_1, axiom, ![X1, X2]:(((v2_pre_topc(X1)&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v3_pre_topc(k1_tops_1(X1,X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 5.47/5.70  fof(c_0_29, plain, ![X8, X9]:k4_xboole_0(X8,X9)=k5_xboole_0(X8,k3_xboole_0(X8,X9)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 5.47/5.70  fof(c_0_30, plain, ![X54, X55]:k1_setfam_1(k2_tarski(X54,X55))=k3_xboole_0(X54,X55), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 5.47/5.70  fof(c_0_31, plain, ![X10]:k2_xboole_0(X10,k1_xboole_0)=X10, inference(variable_rename,[status(thm)],[t1_boole])).
% 5.47/5.70  fof(c_0_32, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 5.47/5.70  fof(c_0_33, plain, ![X21, X22]:k2_xboole_0(k3_xboole_0(X21,X22),k4_xboole_0(X21,X22))=X21, inference(variable_rename,[status(thm)],[t51_xboole_1])).
% 5.47/5.70  cnf(c_0_34, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 5.47/5.70  cnf(c_0_35, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 5.47/5.70  fof(c_0_36, plain, ![X23, X24]:r1_tarski(X23,k2_xboole_0(X23,X24)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 5.47/5.70  cnf(c_0_37, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_31])).
% 5.47/5.70  cnf(c_0_38, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 5.47/5.70  cnf(c_0_39, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_33])).
% 5.47/5.70  cnf(c_0_40, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_34, c_0_35])).
% 5.47/5.70  fof(c_0_41, plain, ![X34, X35]:m1_subset_1(k6_subset_1(X34,X35),k1_zfmisc_1(X34)), inference(variable_rename,[status(thm)],[dt_k6_subset_1])).
% 5.47/5.70  fof(c_0_42, plain, ![X46, X47]:k6_subset_1(X46,X47)=k4_xboole_0(X46,X47), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 5.47/5.70  fof(c_0_43, plain, ![X6, X7]:(((r1_tarski(X6,X7)|X6!=X7)&(r1_tarski(X7,X6)|X6!=X7))&(~r1_tarski(X6,X7)|~r1_tarski(X7,X6)|X6=X7)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 5.47/5.70  cnf(c_0_44, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 5.47/5.70  cnf(c_0_45, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 5.47/5.70  cnf(c_0_46, plain, (k2_xboole_0(k1_setfam_1(k2_tarski(X1,X2)),k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_35]), c_0_40])).
% 5.47/5.70  fof(c_0_47, plain, ![X25, X26]:k2_tarski(X25,X26)=k2_tarski(X26,X25), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 5.47/5.70  fof(c_0_48, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2))))), inference(assume_negation,[status(cth)],[t76_tops_1])).
% 5.47/5.70  cnf(c_0_49, plain, (m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 5.47/5.70  cnf(c_0_50, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 5.47/5.70  cnf(c_0_51, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 5.47/5.70  cnf(c_0_52, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 5.47/5.70  cnf(c_0_53, plain, (r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X1)), inference(spm,[status(thm)],[c_0_44, c_0_46])).
% 5.47/5.70  cnf(c_0_54, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 5.47/5.70  fof(c_0_55, plain, ![X67, X68]:(~l1_pre_topc(X67)|(~m1_subset_1(X68,k1_zfmisc_1(u1_struct_0(X67)))|k2_tops_1(X67,X68)=k2_tops_1(X67,k3_subset_1(u1_struct_0(X67),X68)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_tops_1])])])).
% 5.47/5.70  fof(c_0_56, negated_conjecture, ((v2_pre_topc(esk2_0)&l1_pre_topc(esk2_0))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&((~v3_pre_topc(esk3_0,esk2_0)|k2_tops_1(esk2_0,esk3_0)!=k7_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),esk3_0))&(v3_pre_topc(esk3_0,esk2_0)|k2_tops_1(esk2_0,esk3_0)=k7_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_48])])])).
% 5.47/5.70  fof(c_0_57, plain, ![X56, X57]:((~m1_subset_1(X56,k1_zfmisc_1(X57))|r1_tarski(X56,X57))&(~r1_tarski(X56,X57)|m1_subset_1(X56,k1_zfmisc_1(X57)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 5.47/5.70  fof(c_0_58, plain, ![X29, X30]:(~m1_subset_1(X30,k1_zfmisc_1(X29))|m1_subset_1(k3_subset_1(X29,X30),k1_zfmisc_1(X29))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 5.47/5.70  cnf(c_0_59, plain, (m1_subset_1(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_zfmisc_1(X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_50]), c_0_40])).
% 5.47/5.70  cnf(c_0_60, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 5.47/5.70  cnf(c_0_61, plain, (r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 5.47/5.70  fof(c_0_62, plain, ![X18, X19, X20]:(~r1_tarski(X18,k2_xboole_0(X19,X20))|r1_tarski(k4_xboole_0(X18,X19),X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).
% 5.47/5.70  fof(c_0_63, plain, ![X69, X70]:(~l1_pre_topc(X69)|(~m1_subset_1(X70,k1_zfmisc_1(u1_struct_0(X69)))|k2_pre_topc(X69,X70)=k4_subset_1(u1_struct_0(X69),X70,k2_tops_1(X69,X70)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_tops_1])])])).
% 5.47/5.70  fof(c_0_64, plain, ![X58, X59]:(~l1_pre_topc(X58)|~m1_subset_1(X59,k1_zfmisc_1(u1_struct_0(X58)))|m1_subset_1(k2_tops_1(X58,X59),k1_zfmisc_1(u1_struct_0(X58)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_1])])).
% 5.47/5.70  cnf(c_0_65, plain, (k2_tops_1(X1,X2)=k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 5.47/5.70  cnf(c_0_66, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 5.47/5.70  cnf(c_0_67, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 5.47/5.70  cnf(c_0_68, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 5.47/5.70  cnf(c_0_69, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 5.47/5.70  cnf(c_0_70, plain, (m1_subset_1(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_59, c_0_54])).
% 5.47/5.70  cnf(c_0_71, plain, (k1_setfam_1(k2_tarski(k1_xboole_0,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_60, c_0_53])).
% 5.47/5.70  cnf(c_0_72, plain, (k1_setfam_1(k2_tarski(X1,k1_xboole_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 5.47/5.70  cnf(c_0_73, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_62])).
% 5.47/5.70  fof(c_0_74, plain, ![X31, X32, X33]:(~m1_subset_1(X32,k1_zfmisc_1(X31))|~m1_subset_1(X33,k1_zfmisc_1(X31))|m1_subset_1(k4_subset_1(X31,X32,X33),k1_zfmisc_1(X31))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_subset_1])])).
% 5.47/5.70  cnf(c_0_75, plain, (k2_pre_topc(X1,X2)=k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_63])).
% 5.47/5.70  cnf(c_0_76, plain, (m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_64])).
% 5.47/5.70  cnf(c_0_77, negated_conjecture, (k2_tops_1(esk2_0,k3_subset_1(u1_struct_0(esk2_0),esk3_0))=k2_tops_1(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67])])).
% 5.47/5.70  cnf(c_0_78, plain, (r1_tarski(k3_subset_1(X1,X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 5.47/5.70  fof(c_0_79, plain, ![X43, X44, X45]:(~m1_subset_1(X44,k1_zfmisc_1(X43))|~m1_subset_1(X45,k1_zfmisc_1(X43))|k4_subset_1(X43,X44,X45)=k2_xboole_0(X44,X45)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 5.47/5.70  cnf(c_0_80, plain, (m1_subset_1(k5_xboole_0(X1,k1_xboole_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 5.47/5.70  cnf(c_0_81, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_72]), c_0_45])).
% 5.47/5.70  cnf(c_0_82, plain, (r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X3)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(rw,[status(thm)],[c_0_73, c_0_40])).
% 5.47/5.70  fof(c_0_83, plain, ![X48, X49, X50]:(~m1_subset_1(X49,k1_zfmisc_1(X48))|k7_subset_1(X48,X49,X50)=k4_xboole_0(X49,X50)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 5.47/5.70  cnf(c_0_84, plain, (m1_subset_1(k4_subset_1(X2,X1,X3),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_74])).
% 5.47/5.70  cnf(c_0_85, negated_conjecture, (k4_subset_1(u1_struct_0(esk2_0),esk3_0,k2_tops_1(esk2_0,esk3_0))=k2_pre_topc(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_66]), c_0_67])])).
% 5.47/5.70  cnf(c_0_86, negated_conjecture, (m1_subset_1(k2_tops_1(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(k3_subset_1(u1_struct_0(esk2_0),esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_67])])).
% 5.47/5.70  cnf(c_0_87, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 5.47/5.70  cnf(c_0_88, negated_conjecture, (r1_tarski(k3_subset_1(u1_struct_0(esk2_0),esk3_0),u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_78, c_0_66])).
% 5.47/5.70  cnf(c_0_89, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_79])).
% 5.47/5.70  cnf(c_0_90, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_80, c_0_81])).
% 5.47/5.70  cnf(c_0_91, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k1_xboole_0|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_82]), c_0_37])).
% 5.47/5.70  cnf(c_0_92, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_83])).
% 5.47/5.70  cnf(c_0_93, negated_conjecture, (m1_subset_1(k2_pre_topc(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(k2_tops_1(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_66])])).
% 5.47/5.70  cnf(c_0_94, negated_conjecture, (m1_subset_1(k2_tops_1(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_88])])).
% 5.47/5.70  cnf(c_0_95, plain, (k4_subset_1(X1,X2,X1)=k2_xboole_0(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_89, c_0_90])).
% 5.47/5.70  cnf(c_0_96, plain, (k1_setfam_1(k2_tarski(X1,X2))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_91]), c_0_37])).
% 5.47/5.70  cnf(c_0_97, plain, (k7_subset_1(X2,X1,X3)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_92, c_0_40])).
% 5.47/5.70  cnf(c_0_98, negated_conjecture, (m1_subset_1(k2_pre_topc(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_93, c_0_94])])).
% 5.47/5.70  fof(c_0_99, plain, ![X11, X12, X13]:(~r1_tarski(X11,X12)|~r1_tarski(X12,X13)|r1_tarski(X11,X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 5.47/5.70  fof(c_0_100, plain, ![X71, X72]:(~l1_pre_topc(X71)|(~m1_subset_1(X72,k1_zfmisc_1(u1_struct_0(X71)))|k1_tops_1(X71,X72)=k7_subset_1(u1_struct_0(X71),X72,k2_tops_1(X71,X72)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_tops_1])])])).
% 5.47/5.70  cnf(c_0_101, plain, (k4_subset_1(X1,X2,X1)=k2_xboole_0(X2,X1)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_95, c_0_87])).
% 5.47/5.70  cnf(c_0_102, plain, (m1_subset_1(k5_xboole_0(X1,X2),k1_zfmisc_1(X1))|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_70, c_0_96])).
% 5.47/5.70  cnf(c_0_103, negated_conjecture, (k5_xboole_0(k2_pre_topc(esk2_0,esk3_0),k1_setfam_1(k2_tarski(k2_pre_topc(esk2_0,esk3_0),X1)))=k7_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),X1)), inference(spm,[status(thm)],[c_0_97, c_0_98])).
% 5.47/5.70  fof(c_0_104, plain, ![X62, X63]:(~l1_pre_topc(X62)|(~m1_subset_1(X63,k1_zfmisc_1(u1_struct_0(X62)))|k2_tops_1(X62,X63)=k7_subset_1(u1_struct_0(X62),k2_pre_topc(X62,X63),k1_tops_1(X62,X63)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l78_tops_1])])])).
% 5.47/5.70  fof(c_0_105, plain, ![X16, X17]:(~r1_tarski(X16,k4_xboole_0(X17,X16))|X16=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_xboole_1])])).
% 5.47/5.70  cnf(c_0_106, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_99])).
% 5.47/5.70  cnf(c_0_107, negated_conjecture, (k4_subset_1(u1_struct_0(esk2_0),X1,k2_tops_1(esk2_0,esk3_0))=k2_xboole_0(X1,k2_tops_1(esk2_0,esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_89, c_0_94])).
% 5.47/5.70  fof(c_0_108, plain, ![X27, X28]:(~m1_subset_1(X28,k1_zfmisc_1(X27))|k3_subset_1(X27,X28)=k4_xboole_0(X27,X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 5.47/5.70  cnf(c_0_109, plain, (k1_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_100])).
% 5.47/5.70  cnf(c_0_110, plain, (m1_subset_1(k2_xboole_0(X1,X2),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_101]), c_0_90])]), c_0_68])).
% 5.47/5.70  cnf(c_0_111, negated_conjecture, (m1_subset_1(k7_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),X1),k1_zfmisc_1(k2_pre_topc(esk2_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_103]), c_0_53])])).
% 5.47/5.70  cnf(c_0_112, plain, (k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_104])).
% 5.47/5.70  cnf(c_0_113, plain, (X1=k1_xboole_0|~r1_tarski(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_105])).
% 5.47/5.70  cnf(c_0_114, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_106, c_0_44])).
% 5.47/5.70  cnf(c_0_115, negated_conjecture, (k2_xboole_0(esk3_0,k2_tops_1(esk2_0,esk3_0))=k2_pre_topc(esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_66]), c_0_85])).
% 5.47/5.70  cnf(c_0_116, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_108])).
% 5.47/5.70  cnf(c_0_117, negated_conjecture, (k7_subset_1(u1_struct_0(esk2_0),esk3_0,k2_tops_1(esk2_0,esk3_0))=k1_tops_1(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_66]), c_0_67])])).
% 5.47/5.70  cnf(c_0_118, negated_conjecture, (k7_subset_1(u1_struct_0(esk2_0),esk3_0,X1)=k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X1)))), inference(spm,[status(thm)],[c_0_97, c_0_66])).
% 5.47/5.70  cnf(c_0_119, plain, (r1_tarski(k2_xboole_0(X1,X2),X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_68, c_0_110])).
% 5.47/5.70  cnf(c_0_120, negated_conjecture, (m1_subset_1(k2_tops_1(esk2_0,esk3_0),k1_zfmisc_1(k2_pre_topc(esk2_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_112]), c_0_67]), c_0_66])])).
% 5.47/5.70  cnf(c_0_121, plain, (X1=k1_xboole_0|~r1_tarski(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1))))), inference(rw,[status(thm)],[c_0_113, c_0_40])).
% 5.47/5.70  cnf(c_0_122, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(X1,X4)|~r1_tarski(X4,X2)), inference(spm,[status(thm)],[c_0_106, c_0_114])).
% 5.47/5.70  cnf(c_0_123, negated_conjecture, (r1_tarski(esk3_0,k2_pre_topc(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_44, c_0_115])).
% 5.47/5.70  cnf(c_0_124, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_43])).
% 5.47/5.70  cnf(c_0_125, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_116, c_0_40])).
% 5.47/5.70  cnf(c_0_126, negated_conjecture, (k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,k2_tops_1(esk2_0,esk3_0))))=k1_tops_1(esk2_0,esk3_0)), inference(rw,[status(thm)],[c_0_117, c_0_118])).
% 5.47/5.70  cnf(c_0_127, negated_conjecture, (r1_tarski(k2_xboole_0(k2_tops_1(esk2_0,esk3_0),k2_pre_topc(esk2_0,esk3_0)),k2_pre_topc(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_119, c_0_120])).
% 5.47/5.70  cnf(c_0_128, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_44, c_0_38])).
% 5.47/5.70  cnf(c_0_129, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k1_xboole_0|~r1_tarski(X1,k2_xboole_0(X2,k5_xboole_0(X3,k1_setfam_1(k2_tarski(X3,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))))))))), inference(spm,[status(thm)],[c_0_121, c_0_82])).
% 5.47/5.70  cnf(c_0_130, plain, (k7_subset_1(X1,X2,X3)=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3)))|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_97, c_0_87])).
% 5.47/5.70  cnf(c_0_131, negated_conjecture, (r1_tarski(esk3_0,k2_xboole_0(X1,X2))|~r1_tarski(k2_pre_topc(esk2_0,esk3_0),X1)), inference(spm,[status(thm)],[c_0_122, c_0_123])).
% 5.47/5.70  cnf(c_0_132, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_124])).
% 5.47/5.70  fof(c_0_133, plain, ![X41, X42]:(~m1_subset_1(X42,k1_zfmisc_1(X41))|k3_subset_1(X41,k3_subset_1(X41,X42))=X42), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 5.47/5.70  cnf(c_0_134, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k3_subset_1(X1,X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_125, c_0_87])).
% 5.47/5.70  cnf(c_0_135, negated_conjecture, (r1_tarski(k2_pre_topc(esk2_0,esk3_0),u1_struct_0(esk2_0))|~m1_subset_1(k2_tops_1(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_68, c_0_93])).
% 5.47/5.70  cnf(c_0_136, negated_conjecture, (r1_tarski(k1_tops_1(esk2_0,esk3_0),X1)|~r1_tarski(esk3_0,k2_xboole_0(k2_tops_1(esk2_0,esk3_0),X1))), inference(spm,[status(thm)],[c_0_82, c_0_126])).
% 5.47/5.70  cnf(c_0_137, negated_conjecture, (k2_xboole_0(k2_tops_1(esk2_0,esk3_0),k2_pre_topc(esk2_0,esk3_0))=k2_pre_topc(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_127]), c_0_128])])).
% 5.47/5.70  fof(c_0_138, plain, ![X14, X15]:r1_tarski(k4_xboole_0(X14,X15),X14), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 5.47/5.70  cnf(c_0_139, plain, (k7_subset_1(X1,X2,X3)=k1_xboole_0|~r1_tarski(X2,k2_xboole_0(X3,k5_xboole_0(X4,k1_setfam_1(k2_tarski(X4,k7_subset_1(X1,X2,X3))))))|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_129, c_0_130])).
% 5.47/5.70  cnf(c_0_140, negated_conjecture, (r1_tarski(esk3_0,k2_xboole_0(k2_pre_topc(esk2_0,esk3_0),X1))), inference(spm,[status(thm)],[c_0_131, c_0_132])).
% 5.47/5.70  fof(c_0_141, plain, ![X64, X65, X66]:(~l1_pre_topc(X64)|(~m1_subset_1(X65,k1_zfmisc_1(u1_struct_0(X64)))|(~m1_subset_1(X66,k1_zfmisc_1(u1_struct_0(X64)))|(~v3_pre_topc(X65,X64)|~r1_tarski(X65,X66)|r1_tarski(X65,k1_tops_1(X64,X66)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_tops_1])])])).
% 5.47/5.70  cnf(c_0_142, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_133])).
% 5.47/5.70  cnf(c_0_143, negated_conjecture, (v3_pre_topc(esk3_0,esk2_0)|k2_tops_1(esk2_0,esk3_0)=k7_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 5.47/5.70  cnf(c_0_144, plain, (k7_subset_1(X1,X2,X3)=k3_subset_1(X2,X3)|~r1_tarski(X3,X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_134, c_0_130])).
% 5.47/5.70  cnf(c_0_145, negated_conjecture, (r1_tarski(k2_pre_topc(esk2_0,esk3_0),u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135, c_0_76]), c_0_67]), c_0_66])])).
% 5.47/5.70  cnf(c_0_146, negated_conjecture, (k7_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),X1)=k3_subset_1(k2_pre_topc(esk2_0,esk3_0),X1)|~r1_tarski(X1,k2_pre_topc(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_134, c_0_103])).
% 5.47/5.70  cnf(c_0_147, negated_conjecture, (r1_tarski(k1_tops_1(esk2_0,esk3_0),k2_pre_topc(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136, c_0_137]), c_0_123])])).
% 5.47/5.70  cnf(c_0_148, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_138])).
% 5.47/5.70  cnf(c_0_149, plain, (k2_xboole_0(k1_setfam_1(k2_tarski(X1,X2)),k7_subset_1(X3,X1,X2))=X1|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_46, c_0_130])).
% 5.47/5.70  cnf(c_0_150, negated_conjecture, (k7_subset_1(X1,esk3_0,k2_pre_topc(esk2_0,esk3_0))=k1_xboole_0|~r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_139, c_0_140])).
% 5.47/5.70  cnf(c_0_151, plain, (r1_tarski(X2,k1_tops_1(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v3_pre_topc(X2,X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_141])).
% 5.47/5.70  cnf(c_0_152, negated_conjecture, (r1_tarski(esk3_0,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_68, c_0_66])).
% 5.47/5.70  cnf(c_0_153, plain, (k3_subset_1(X1,k3_subset_1(X1,X2))=X2|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_142, c_0_87])).
% 5.47/5.70  cnf(c_0_154, negated_conjecture, (k3_subset_1(k2_pre_topc(esk2_0,esk3_0),esk3_0)=k2_tops_1(esk2_0,esk3_0)|v3_pre_topc(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143, c_0_144]), c_0_123]), c_0_145])])).
% 5.47/5.70  cnf(c_0_155, negated_conjecture, (k3_subset_1(k2_pre_topc(esk2_0,esk3_0),k1_tops_1(esk2_0,esk3_0))=k2_tops_1(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_146]), c_0_67]), c_0_66]), c_0_147])])).
% 5.47/5.70  cnf(c_0_156, plain, (r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X1)), inference(rw,[status(thm)],[c_0_148, c_0_40])).
% 5.47/5.70  cnf(c_0_157, negated_conjecture, (k1_setfam_1(k2_tarski(esk3_0,k2_pre_topc(esk2_0,esk3_0)))=esk3_0|~r1_tarski(esk3_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_149, c_0_150]), c_0_37])).
% 5.47/5.70  cnf(c_0_158, negated_conjecture, (r1_tarski(X1,k2_pre_topc(esk2_0,esk3_0))|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_114, c_0_115])).
% 5.47/5.70  fof(c_0_159, plain, ![X60, X61]:(~v2_pre_topc(X60)|~l1_pre_topc(X60)|~m1_subset_1(X61,k1_zfmisc_1(u1_struct_0(X60)))|v3_pre_topc(k1_tops_1(X60,X61),X60)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).
% 5.47/5.70  cnf(c_0_160, negated_conjecture, (r1_tarski(X1,k1_tops_1(esk2_0,esk3_0))|~v3_pre_topc(X1,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r1_tarski(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_151, c_0_66]), c_0_67])])).
% 5.47/5.70  cnf(c_0_161, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk2_0))|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_106, c_0_152])).
% 5.47/5.70  cnf(c_0_162, negated_conjecture, (k3_subset_1(k2_pre_topc(esk2_0,esk3_0),k2_tops_1(esk2_0,esk3_0))=esk3_0|v3_pre_topc(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_153, c_0_154]), c_0_123])])).
% 5.47/5.70  cnf(c_0_163, negated_conjecture, (k3_subset_1(k2_pre_topc(esk2_0,esk3_0),k2_tops_1(esk2_0,esk3_0))=k1_tops_1(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_153, c_0_155]), c_0_147])])).
% 5.47/5.70  cnf(c_0_164, negated_conjecture, (r1_tarski(k1_tops_1(esk2_0,esk3_0),esk3_0)), inference(spm,[status(thm)],[c_0_156, c_0_126])).
% 5.47/5.70  cnf(c_0_165, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1)))=k3_subset_1(X1,X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_134, c_0_54])).
% 5.47/5.70  cnf(c_0_166, negated_conjecture, (k1_setfam_1(k2_tarski(esk3_0,k2_pre_topc(esk2_0,esk3_0)))=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_157, c_0_158]), c_0_132])])).
% 5.47/5.70  cnf(c_0_167, plain, (v3_pre_topc(k1_tops_1(X1,X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_159])).
% 5.47/5.70  cnf(c_0_168, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 5.47/5.70  cnf(c_0_169, negated_conjecture, (r1_tarski(X1,k1_tops_1(esk2_0,esk3_0))|~v3_pre_topc(X1,esk2_0)|~r1_tarski(X1,esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_160, c_0_87]), c_0_161])).
% 5.47/5.70  cnf(c_0_170, negated_conjecture, (k1_tops_1(esk2_0,esk3_0)=esk3_0|v3_pre_topc(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_162, c_0_163])).
% 5.47/5.70  cnf(c_0_171, negated_conjecture, (k1_tops_1(esk2_0,esk3_0)=esk3_0|~r1_tarski(esk3_0,k1_tops_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_51, c_0_164])).
% 5.47/5.70  cnf(c_0_172, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))))))=k3_subset_1(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))))), inference(spm,[status(thm)],[c_0_125, c_0_59])).
% 5.47/5.70  cnf(c_0_173, negated_conjecture, (k7_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),k2_tops_1(esk2_0,esk3_0))=k3_subset_1(k2_pre_topc(esk2_0,esk3_0),k2_tops_1(esk2_0,esk3_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125, c_0_120]), c_0_103])).
% 5.47/5.70  cnf(c_0_174, plain, (k7_subset_1(X1,X2,X3)=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X3,X2)))|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_130, c_0_54])).
% 5.47/5.70  cnf(c_0_175, negated_conjecture, (k5_xboole_0(k2_pre_topc(esk2_0,esk3_0),esk3_0)=k3_subset_1(k2_pre_topc(esk2_0,esk3_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_165, c_0_166]), c_0_123])])).
% 5.47/5.70  cnf(c_0_176, negated_conjecture, (~v3_pre_topc(esk3_0,esk2_0)|k2_tops_1(esk2_0,esk3_0)!=k7_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 5.47/5.70  cnf(c_0_177, negated_conjecture, (v3_pre_topc(k1_tops_1(esk2_0,esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_167, c_0_66]), c_0_168]), c_0_67])])).
% 5.47/5.70  cnf(c_0_178, negated_conjecture, (k1_tops_1(esk2_0,esk3_0)=esk3_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_169, c_0_170]), c_0_132])]), c_0_171])).
% 5.47/5.70  cnf(c_0_179, negated_conjecture, (k7_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),k7_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),X1))=k3_subset_1(k2_pre_topc(esk2_0,esk3_0),k7_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_172, c_0_103]), c_0_103])).
% 5.47/5.70  cnf(c_0_180, negated_conjecture, (k7_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),k2_tops_1(esk2_0,esk3_0))=k1_tops_1(esk2_0,esk3_0)), inference(rw,[status(thm)],[c_0_173, c_0_163])).
% 5.47/5.70  cnf(c_0_181, plain, (k7_subset_1(X1,X1,X2)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))), inference(spm,[status(thm)],[c_0_97, c_0_90])).
% 5.47/5.70  cnf(c_0_182, negated_conjecture, (k7_subset_1(X1,k2_pre_topc(esk2_0,esk3_0),esk3_0)=k3_subset_1(k2_pre_topc(esk2_0,esk3_0),esk3_0)|~r1_tarski(k2_pre_topc(esk2_0,esk3_0),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_174, c_0_166]), c_0_175])).
% 5.47/5.70  cnf(c_0_183, negated_conjecture, (k3_subset_1(k2_pre_topc(esk2_0,esk3_0),esk3_0)!=k2_tops_1(esk2_0,esk3_0)|~v3_pre_topc(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_176, c_0_144]), c_0_123]), c_0_145])])).
% 5.47/5.70  cnf(c_0_184, negated_conjecture, (v3_pre_topc(esk3_0,esk2_0)), inference(rw,[status(thm)],[c_0_177, c_0_178])).
% 5.47/5.70  cnf(c_0_185, negated_conjecture, (k7_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),k1_tops_1(esk2_0,esk3_0))=k2_tops_1(esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_179, c_0_180]), c_0_155])).
% 5.47/5.70  cnf(c_0_186, negated_conjecture, (k7_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),esk3_0)=k3_subset_1(k2_pre_topc(esk2_0,esk3_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_181, c_0_182]), c_0_103]), c_0_132])])).
% 5.47/5.70  cnf(c_0_187, negated_conjecture, (k3_subset_1(k2_pre_topc(esk2_0,esk3_0),esk3_0)!=k2_tops_1(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_183, c_0_184])])).
% 5.47/5.70  cnf(c_0_188, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_185, c_0_178]), c_0_186]), c_0_187]), ['proof']).
% 5.47/5.70  # SZS output end CNFRefutation
% 5.47/5.70  # Proof object total steps             : 189
% 5.47/5.70  # Proof object clause steps            : 130
% 5.47/5.70  # Proof object formula steps           : 59
% 5.47/5.70  # Proof object conjectures             : 61
% 5.47/5.70  # Proof object clause conjectures      : 58
% 5.47/5.70  # Proof object formula conjectures     : 3
% 5.47/5.70  # Proof object initial clauses used    : 35
% 5.47/5.70  # Proof object initial formulas used   : 29
% 5.47/5.70  # Proof object generating inferences   : 79
% 5.47/5.70  # Proof object simplifying inferences  : 88
% 5.47/5.70  # Training examples: 0 positive, 0 negative
% 5.47/5.70  # Parsed axioms                        : 32
% 5.47/5.70  # Removed by relevancy pruning/SinE    : 0
% 5.47/5.70  # Initial clauses                      : 39
% 5.47/5.70  # Removed in clause preprocessing      : 3
% 5.47/5.70  # Initial clauses in saturation        : 36
% 5.47/5.70  # Processed clauses                    : 37521
% 5.47/5.70  # ...of these trivial                  : 2284
% 5.47/5.70  # ...subsumed                          : 28764
% 5.47/5.70  # ...remaining for further processing  : 6472
% 5.47/5.70  # Other redundant clauses eliminated   : 2
% 5.47/5.70  # Clauses deleted for lack of memory   : 0
% 5.47/5.70  # Backward-subsumed                    : 802
% 5.47/5.70  # Backward-rewritten                   : 1019
% 5.47/5.70  # Generated clauses                    : 583773
% 5.47/5.70  # ...of the previous two non-trivial   : 488742
% 5.47/5.70  # Contextual simplify-reflections      : 132
% 5.47/5.70  # Paramodulations                      : 583771
% 5.47/5.70  # Factorizations                       : 0
% 5.47/5.70  # Equation resolutions                 : 2
% 5.47/5.70  # Propositional unsat checks           : 0
% 5.47/5.70  #    Propositional check models        : 0
% 5.47/5.70  #    Propositional check unsatisfiable : 0
% 5.47/5.70  #    Propositional clauses             : 0
% 5.47/5.70  #    Propositional clauses after purity: 0
% 5.47/5.70  #    Propositional unsat core size     : 0
% 5.47/5.70  #    Propositional preprocessing time  : 0.000
% 5.47/5.70  #    Propositional encoding time       : 0.000
% 5.47/5.70  #    Propositional solver time         : 0.000
% 5.47/5.70  #    Success case prop preproc time    : 0.000
% 5.47/5.70  #    Success case prop encoding time   : 0.000
% 5.47/5.70  #    Success case prop solver time     : 0.000
% 5.47/5.70  # Current number of processed clauses  : 4614
% 5.47/5.70  #    Positive orientable unit clauses  : 1670
% 5.47/5.70  #    Positive unorientable unit clauses: 11
% 5.47/5.70  #    Negative unit clauses             : 23
% 5.47/5.70  #    Non-unit-clauses                  : 2910
% 5.47/5.70  # Current number of unprocessed clauses: 431463
% 5.47/5.70  # ...number of literals in the above   : 1101191
% 5.47/5.70  # Current number of archived formulas  : 0
% 5.47/5.70  # Current number of archived clauses   : 1859
% 5.47/5.70  # Clause-clause subsumption calls (NU) : 1409159
% 5.47/5.70  # Rec. Clause-clause subsumption calls : 989283
% 5.47/5.70  # Non-unit clause-clause subsumptions  : 16705
% 5.47/5.70  # Unit Clause-clause subsumption calls : 52680
% 5.47/5.70  # Rewrite failures with RHS unbound    : 0
% 5.47/5.70  # BW rewrite match attempts            : 26787
% 5.47/5.70  # BW rewrite match successes           : 231
% 5.47/5.70  # Condensation attempts                : 0
% 5.47/5.70  # Condensation successes               : 0
% 5.47/5.70  # Termbank termtop insertions          : 14775593
% 5.56/5.72  
% 5.56/5.72  # -------------------------------------------------
% 5.56/5.72  # User time                : 5.207 s
% 5.56/5.72  # System time              : 0.177 s
% 5.56/5.72  # Total time               : 5.384 s
% 5.56/5.72  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------

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
% DateTime   : Thu Dec  3 11:11:05 EST 2020

% Result     : Theorem 0.53s
% Output     : CNFRefutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :  135 (9439 expanded)
%              Number of clauses        :   80 (4429 expanded)
%              Number of leaves         :   27 (2474 expanded)
%              Depth                    :   20
%              Number of atoms          :  247 (13879 expanded)
%              Number of equality atoms :   88 (7552 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t69_tops_1,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v4_pre_topc(X2,X1)
           => r1_tarski(k2_tops_1(X1,X2),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(dt_k6_subset_1,axiom,(
    ! [X1,X2] : m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(t65_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_pre_topc(X1,X2) = k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(t62_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_tops_1(X1,X2) = k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(dt_k2_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(t31_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( v4_pre_topc(X2,X1)
                  & r1_tarski(X3,X2) )
               => r1_tarski(k2_pre_topc(X1,X3),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tops_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(c_0_27,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v4_pre_topc(X2,X1)
             => r1_tarski(k2_tops_1(X1,X2),X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t69_tops_1])).

fof(c_0_28,plain,(
    ! [X10,X11] : k4_xboole_0(X10,X11) = k5_xboole_0(X10,k3_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_29,plain,(
    ! [X45,X46] : k1_setfam_1(k2_tarski(X45,X46)) = k3_xboole_0(X45,X46) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_30,plain,(
    ! [X47,X48] :
      ( ( ~ m1_subset_1(X47,k1_zfmisc_1(X48))
        | r1_tarski(X47,X48) )
      & ( ~ r1_tarski(X47,X48)
        | m1_subset_1(X47,k1_zfmisc_1(X48)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_31,negated_conjecture,
    ( l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & v4_pre_topc(esk2_0,esk1_0)
    & ~ r1_tarski(k2_tops_1(esk1_0,esk2_0),esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_27])])])).

fof(c_0_32,plain,(
    ! [X38,X39] : m1_subset_1(k6_subset_1(X38,X39),k1_zfmisc_1(X38)) ),
    inference(variable_rename,[status(thm)],[dt_k6_subset_1])).

fof(c_0_33,plain,(
    ! [X43,X44] : k6_subset_1(X43,X44) = k4_xboole_0(X43,X44) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

cnf(c_0_34,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_36,plain,(
    ! [X19,X20] :
      ( ~ r1_tarski(X19,X20)
      | k3_xboole_0(X19,X20) = X19 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_37,plain,(
    ! [X16,X17,X18] :
      ( ~ r1_tarski(X16,X17)
      | ~ r1_tarski(X17,X18)
      | r1_tarski(X16,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_40,plain,
    ( m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_41,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_43,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_44,plain,(
    ! [X32,X33] : k2_tarski(X32,X33) = k2_tarski(X33,X32) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

fof(c_0_45,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | X6 != X7 )
      & ( r1_tarski(X7,X6)
        | X6 != X7 )
      & ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,X6)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_46,plain,(
    ! [X21] : r1_tarski(k1_xboole_0,X21) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_47,plain,(
    ! [X14,X15] : r1_tarski(k3_xboole_0(X14,X15),X14) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(esk2_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_50,plain,
    ( m1_subset_1(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_41]),c_0_42])).

cnf(c_0_51,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_43,c_0_35])).

cnf(c_0_52,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_53,plain,(
    ! [X8,X9] :
      ( ( k4_xboole_0(X8,X9) != k1_xboole_0
        | r1_tarski(X8,X9) )
      & ( ~ r1_tarski(X8,X9)
        | k4_xboole_0(X8,X9) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_54,plain,(
    ! [X24] : k4_xboole_0(X24,k1_xboole_0) = X24 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_55,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_56,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_57,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

fof(c_0_58,plain,(
    ! [X22,X23] : k2_xboole_0(X22,k4_xboole_0(X23,X22)) = k2_xboole_0(X22,X23) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

fof(c_0_59,plain,(
    ! [X12,X13] :
      ( ~ r1_tarski(X12,X13)
      | k2_xboole_0(X12,X13) = X13 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_60,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_62,plain,
    ( r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_50])).

cnf(c_0_63,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

fof(c_0_64,plain,(
    ! [X25,X26,X27] : k4_xboole_0(k4_xboole_0(X25,X26),X27) = k4_xboole_0(X25,k2_xboole_0(X26,X27)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_65,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_66,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_67,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_68,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_57,c_0_35])).

cnf(c_0_69,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_70,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_71,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_72,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X2,esk2_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_48,c_0_61])).

cnf(c_0_73,plain,
    ( r1_tarski(k5_xboole_0(X1,X2),X1)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_74,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

fof(c_0_75,plain,(
    ! [X28,X29] : k4_xboole_0(X28,k4_xboole_0(X28,X29)) = k3_xboole_0(X28,X29) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_76,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_77,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_65,c_0_42])).

cnf(c_0_78,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_xboole_0))) = X1 ),
    inference(rw,[status(thm)],[c_0_66,c_0_42])).

cnf(c_0_79,plain,
    ( k1_setfam_1(k2_tarski(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_80,plain,
    ( k2_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_69,c_0_42])).

cnf(c_0_81,plain,
    ( k2_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_82,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,k5_xboole_0(esk2_0,X2))
    | ~ r1_tarski(X2,esk2_0) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_83,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_74])).

fof(c_0_84,plain,(
    ! [X34,X35] :
      ( ~ m1_subset_1(X35,k1_zfmisc_1(X34))
      | k3_subset_1(X34,X35) = k4_xboole_0(X34,X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_85,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_86,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_setfam_1(k2_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X3))) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k2_xboole_0(X2,X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_42]),c_0_42]),c_0_42])).

cnf(c_0_87,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_77,c_0_52])).

cnf(c_0_88,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_52]),c_0_79])).

cnf(c_0_89,plain,
    ( k2_xboole_0(X1,X2) = X1
    | ~ r1_tarski(k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1))),X1) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_90,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk2_0,X1),u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_91,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_92,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))))) = k1_setfam_1(k2_tarski(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_85,c_0_35]),c_0_42]),c_0_42])).

cnf(c_0_93,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k2_xboole_0(X1,X2)))) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_79]),c_0_88]),c_0_83])])).

cnf(c_0_94,negated_conjecture,
    ( k2_xboole_0(esk2_0,u1_struct_0(esk1_0)) = u1_struct_0(esk1_0) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_68])]),c_0_71])).

cnf(c_0_95,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_91,c_0_42])).

cnf(c_0_96,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,X2)))) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_92,c_0_63])).

cnf(c_0_97,negated_conjecture,
    ( k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,u1_struct_0(esk1_0)))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_93,c_0_94])).

cnf(c_0_98,plain,
    ( k1_setfam_1(k2_tarski(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_79,c_0_52])).

cnf(c_0_99,plain,
    ( k3_subset_1(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))) = k1_setfam_1(k2_tarski(X1,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_92]),c_0_50])])).

cnf(c_0_100,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))) = k3_subset_1(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_95,c_0_52])).

cnf(c_0_101,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk2_0,u1_struct_0(esk1_0))) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_98]),c_0_88]),c_0_68])])).

fof(c_0_102,plain,(
    ! [X56,X57] :
      ( ~ l1_pre_topc(X56)
      | ~ m1_subset_1(X57,k1_zfmisc_1(u1_struct_0(X56)))
      | k2_pre_topc(X56,X57) = k4_subset_1(u1_struct_0(X56),X57,k2_tops_1(X56,X57)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_tops_1])])])).

fof(c_0_103,plain,(
    ! [X54,X55] :
      ( ~ l1_pre_topc(X54)
      | ~ m1_subset_1(X55,k1_zfmisc_1(u1_struct_0(X54)))
      | k2_tops_1(X54,X55) = k2_tops_1(X54,k3_subset_1(u1_struct_0(X54),X55)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_tops_1])])])).

fof(c_0_104,plain,(
    ! [X36,X37] :
      ( ~ m1_subset_1(X37,k1_zfmisc_1(X36))
      | m1_subset_1(k3_subset_1(X36,X37),k1_zfmisc_1(X36)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

cnf(c_0_105,plain,
    ( k3_subset_1(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1)))) = k1_setfam_1(k2_tarski(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_99,c_0_52])).

cnf(c_0_106,negated_conjecture,
    ( k5_xboole_0(u1_struct_0(esk1_0),esk2_0) = k3_subset_1(u1_struct_0(esk1_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_39])])).

cnf(c_0_107,plain,
    ( m1_subset_1(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_52])).

cnf(c_0_108,plain,
    ( k2_pre_topc(X1,X2) = k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_102])).

cnf(c_0_109,plain,
    ( k2_tops_1(X1,X2) = k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_103])).

cnf(c_0_110,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_104])).

cnf(c_0_111,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)) = esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_101]),c_0_106])).

cnf(c_0_112,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_113,negated_conjecture,
    ( m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_101]),c_0_106])).

fof(c_0_114,plain,(
    ! [X49,X50] :
      ( ~ l1_pre_topc(X49)
      | ~ m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X49)))
      | m1_subset_1(k2_tops_1(X49,X50),k1_zfmisc_1(u1_struct_0(X49))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_1])])).

fof(c_0_115,plain,(
    ! [X40,X41,X42] :
      ( ~ m1_subset_1(X41,k1_zfmisc_1(X40))
      | ~ m1_subset_1(X42,k1_zfmisc_1(X40))
      | k4_subset_1(X40,X41,X42) = k2_xboole_0(X41,X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_116,plain,
    ( k4_subset_1(u1_struct_0(X1),k3_subset_1(u1_struct_0(X1),X2),k2_tops_1(X1,X2)) = k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_109]),c_0_110])).

cnf(c_0_117,negated_conjecture,
    ( k2_tops_1(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)) = k2_tops_1(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_111]),c_0_112]),c_0_113])])).

cnf(c_0_118,plain,
    ( m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_114])).

fof(c_0_119,plain,(
    ! [X51,X52,X53] :
      ( ~ l1_pre_topc(X51)
      | ~ m1_subset_1(X52,k1_zfmisc_1(u1_struct_0(X51)))
      | ~ m1_subset_1(X53,k1_zfmisc_1(u1_struct_0(X51)))
      | ~ v4_pre_topc(X52,X51)
      | ~ r1_tarski(X53,X52)
      | r1_tarski(k2_pre_topc(X51,X53),X52) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_tops_1])])])).

fof(c_0_120,plain,(
    ! [X30,X31] : r1_tarski(X30,k2_xboole_0(X30,X31)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_121,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_115])).

cnf(c_0_122,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),esk2_0,k2_tops_1(esk1_0,esk2_0)) = k2_pre_topc(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_117]),c_0_111]),c_0_111]),c_0_112]),c_0_113])])).

cnf(c_0_123,negated_conjecture,
    ( m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_117]),c_0_112]),c_0_113])])).

cnf(c_0_124,plain,
    ( r1_tarski(k2_pre_topc(X1,X3),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X2,X1)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_119])).

cnf(c_0_125,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_120])).

cnf(c_0_126,negated_conjecture,
    ( k2_xboole_0(esk2_0,k2_tops_1(esk1_0,esk2_0)) = k2_pre_topc(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_122]),c_0_123]),c_0_39])])).

cnf(c_0_127,plain,
    ( X1 = k2_pre_topc(X2,X3)
    | ~ v4_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(X1,k2_pre_topc(X2,X3))
    | ~ r1_tarski(X3,X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_124])).

cnf(c_0_128,negated_conjecture,
    ( r1_tarski(esk2_0,k2_pre_topc(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_125,c_0_126])).

cnf(c_0_129,negated_conjecture,
    ( v4_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_130,negated_conjecture,
    ( k2_pre_topc(esk1_0,esk2_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_128]),c_0_129]),c_0_112]),c_0_39]),c_0_83])])).

cnf(c_0_131,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_125,c_0_71])).

cnf(c_0_132,negated_conjecture,
    ( k2_xboole_0(esk2_0,k2_tops_1(esk1_0,esk2_0)) = esk2_0 ),
    inference(rw,[status(thm)],[c_0_126,c_0_130])).

cnf(c_0_133,negated_conjecture,
    ( ~ r1_tarski(k2_tops_1(esk1_0,esk2_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_134,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_132]),c_0_133]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 16:10:45 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.33  # No SInE strategy applied
% 0.13/0.33  # Trying AutoSched0 for 299 seconds
% 0.53/0.69  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.53/0.69  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.53/0.69  #
% 0.53/0.69  # Preprocessing time       : 0.028 s
% 0.53/0.69  # Presaturation interreduction done
% 0.53/0.69  
% 0.53/0.69  # Proof found!
% 0.53/0.69  # SZS status Theorem
% 0.53/0.69  # SZS output start CNFRefutation
% 0.53/0.69  fof(t69_tops_1, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)=>r1_tarski(k2_tops_1(X1,X2),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_tops_1)).
% 0.53/0.69  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.53/0.69  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.53/0.69  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.53/0.69  fof(dt_k6_subset_1, axiom, ![X1, X2]:m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 0.53/0.69  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 0.53/0.69  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.53/0.69  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.53/0.69  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.53/0.69  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.53/0.69  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.53/0.69  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.53/0.69  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.53/0.69  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 0.53/0.69  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.53/0.69  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.53/0.69  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.53/0.69  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.53/0.69  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.53/0.69  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 0.53/0.69  fof(t65_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_pre_topc(X1,X2)=k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 0.53/0.69  fof(t62_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_tops_1(X1,X2)=k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tops_1)).
% 0.53/0.69  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 0.53/0.69  fof(dt_k2_tops_1, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 0.53/0.69  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 0.53/0.69  fof(t31_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v4_pre_topc(X2,X1)&r1_tarski(X3,X2))=>r1_tarski(k2_pre_topc(X1,X3),X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_tops_1)).
% 0.53/0.69  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.53/0.69  fof(c_0_27, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)=>r1_tarski(k2_tops_1(X1,X2),X2))))), inference(assume_negation,[status(cth)],[t69_tops_1])).
% 0.53/0.69  fof(c_0_28, plain, ![X10, X11]:k4_xboole_0(X10,X11)=k5_xboole_0(X10,k3_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.53/0.69  fof(c_0_29, plain, ![X45, X46]:k1_setfam_1(k2_tarski(X45,X46))=k3_xboole_0(X45,X46), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.53/0.69  fof(c_0_30, plain, ![X47, X48]:((~m1_subset_1(X47,k1_zfmisc_1(X48))|r1_tarski(X47,X48))&(~r1_tarski(X47,X48)|m1_subset_1(X47,k1_zfmisc_1(X48)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.53/0.69  fof(c_0_31, negated_conjecture, (l1_pre_topc(esk1_0)&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(v4_pre_topc(esk2_0,esk1_0)&~r1_tarski(k2_tops_1(esk1_0,esk2_0),esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_27])])])).
% 0.53/0.69  fof(c_0_32, plain, ![X38, X39]:m1_subset_1(k6_subset_1(X38,X39),k1_zfmisc_1(X38)), inference(variable_rename,[status(thm)],[dt_k6_subset_1])).
% 0.53/0.69  fof(c_0_33, plain, ![X43, X44]:k6_subset_1(X43,X44)=k4_xboole_0(X43,X44), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 0.53/0.69  cnf(c_0_34, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.53/0.69  cnf(c_0_35, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.53/0.69  fof(c_0_36, plain, ![X19, X20]:(~r1_tarski(X19,X20)|k3_xboole_0(X19,X20)=X19), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.53/0.69  fof(c_0_37, plain, ![X16, X17, X18]:(~r1_tarski(X16,X17)|~r1_tarski(X17,X18)|r1_tarski(X16,X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.53/0.69  cnf(c_0_38, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.53/0.69  cnf(c_0_39, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.53/0.69  cnf(c_0_40, plain, (m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.53/0.69  cnf(c_0_41, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.53/0.69  cnf(c_0_42, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_34, c_0_35])).
% 0.53/0.69  cnf(c_0_43, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.53/0.69  fof(c_0_44, plain, ![X32, X33]:k2_tarski(X32,X33)=k2_tarski(X33,X32), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.53/0.69  fof(c_0_45, plain, ![X6, X7]:(((r1_tarski(X6,X7)|X6!=X7)&(r1_tarski(X7,X6)|X6!=X7))&(~r1_tarski(X6,X7)|~r1_tarski(X7,X6)|X6=X7)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.53/0.69  fof(c_0_46, plain, ![X21]:r1_tarski(k1_xboole_0,X21), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.53/0.69  fof(c_0_47, plain, ![X14, X15]:r1_tarski(k3_xboole_0(X14,X15),X14), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.53/0.69  cnf(c_0_48, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.53/0.69  cnf(c_0_49, negated_conjecture, (r1_tarski(esk2_0,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.53/0.69  cnf(c_0_50, plain, (m1_subset_1(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_zfmisc_1(X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_41]), c_0_42])).
% 0.53/0.69  cnf(c_0_51, plain, (k1_setfam_1(k2_tarski(X1,X2))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_43, c_0_35])).
% 0.53/0.69  cnf(c_0_52, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.53/0.69  fof(c_0_53, plain, ![X8, X9]:((k4_xboole_0(X8,X9)!=k1_xboole_0|r1_tarski(X8,X9))&(~r1_tarski(X8,X9)|k4_xboole_0(X8,X9)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.53/0.69  fof(c_0_54, plain, ![X24]:k4_xboole_0(X24,k1_xboole_0)=X24, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.53/0.69  cnf(c_0_55, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.53/0.69  cnf(c_0_56, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.53/0.69  cnf(c_0_57, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.53/0.69  fof(c_0_58, plain, ![X22, X23]:k2_xboole_0(X22,k4_xboole_0(X23,X22))=k2_xboole_0(X22,X23), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.53/0.69  fof(c_0_59, plain, ![X12, X13]:(~r1_tarski(X12,X13)|k2_xboole_0(X12,X13)=X13), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.53/0.69  fof(c_0_60, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.53/0.69  cnf(c_0_61, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.53/0.69  cnf(c_0_62, plain, (r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X1)), inference(spm,[status(thm)],[c_0_38, c_0_50])).
% 0.53/0.69  cnf(c_0_63, plain, (k1_setfam_1(k2_tarski(X1,X2))=X2|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.53/0.69  fof(c_0_64, plain, ![X25, X26, X27]:k4_xboole_0(k4_xboole_0(X25,X26),X27)=k4_xboole_0(X25,k2_xboole_0(X26,X27)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.53/0.69  cnf(c_0_65, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.53/0.69  cnf(c_0_66, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.53/0.69  cnf(c_0_67, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.53/0.69  cnf(c_0_68, plain, (r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_57, c_0_35])).
% 0.53/0.69  cnf(c_0_69, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.53/0.69  cnf(c_0_70, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.53/0.69  cnf(c_0_71, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.53/0.69  cnf(c_0_72, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X2,esk2_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_48, c_0_61])).
% 0.53/0.69  cnf(c_0_73, plain, (r1_tarski(k5_xboole_0(X1,X2),X1)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.53/0.69  cnf(c_0_74, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.53/0.69  fof(c_0_75, plain, ![X28, X29]:k4_xboole_0(X28,k4_xboole_0(X28,X29))=k3_xboole_0(X28,X29), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.53/0.69  cnf(c_0_76, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.53/0.69  cnf(c_0_77, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k1_xboole_0|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_65, c_0_42])).
% 0.53/0.69  cnf(c_0_78, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_xboole_0)))=X1), inference(rw,[status(thm)],[c_0_66, c_0_42])).
% 0.53/0.69  cnf(c_0_79, plain, (k1_setfam_1(k2_tarski(k1_xboole_0,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.53/0.69  cnf(c_0_80, plain, (k2_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1))))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_69, c_0_42])).
% 0.53/0.69  cnf(c_0_81, plain, (k2_xboole_0(X1,X2)=X1|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.53/0.69  cnf(c_0_82, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X1,k5_xboole_0(esk2_0,X2))|~r1_tarski(X2,esk2_0)), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.53/0.69  cnf(c_0_83, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_74])).
% 0.53/0.69  fof(c_0_84, plain, ![X34, X35]:(~m1_subset_1(X35,k1_zfmisc_1(X34))|k3_subset_1(X34,X35)=k4_xboole_0(X34,X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.53/0.69  cnf(c_0_85, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.53/0.69  cnf(c_0_86, plain, (k5_xboole_0(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_setfam_1(k2_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X3)))=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k2_xboole_0(X2,X3))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_42]), c_0_42]), c_0_42])).
% 0.53/0.69  cnf(c_0_87, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1)))=k1_xboole_0|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_77, c_0_52])).
% 0.53/0.69  cnf(c_0_88, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_52]), c_0_79])).
% 0.53/0.69  cnf(c_0_89, plain, (k2_xboole_0(X1,X2)=X1|~r1_tarski(k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1))),X1)), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 0.53/0.69  cnf(c_0_90, negated_conjecture, (r1_tarski(k5_xboole_0(esk2_0,X1),u1_struct_0(esk1_0))|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 0.53/0.69  cnf(c_0_91, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_84])).
% 0.53/0.69  cnf(c_0_92, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))))))=k1_setfam_1(k2_tarski(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_85, c_0_35]), c_0_42]), c_0_42])).
% 0.53/0.69  cnf(c_0_93, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k2_xboole_0(X1,X2))))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_79]), c_0_88]), c_0_83])])).
% 0.53/0.69  cnf(c_0_94, negated_conjecture, (k2_xboole_0(esk2_0,u1_struct_0(esk1_0))=u1_struct_0(esk1_0)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_68])]), c_0_71])).
% 0.53/0.69  cnf(c_0_95, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_91, c_0_42])).
% 0.53/0.69  cnf(c_0_96, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,X2))))=X2|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_92, c_0_63])).
% 0.53/0.69  cnf(c_0_97, negated_conjecture, (k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,u1_struct_0(esk1_0))))=k1_xboole_0), inference(spm,[status(thm)],[c_0_93, c_0_94])).
% 0.53/0.69  cnf(c_0_98, plain, (k1_setfam_1(k2_tarski(X1,k1_xboole_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_79, c_0_52])).
% 0.53/0.69  cnf(c_0_99, plain, (k3_subset_1(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))))=k1_setfam_1(k2_tarski(X1,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_92]), c_0_50])])).
% 0.53/0.69  cnf(c_0_100, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1)))=k3_subset_1(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_95, c_0_52])).
% 0.53/0.69  cnf(c_0_101, negated_conjecture, (k1_setfam_1(k2_tarski(esk2_0,u1_struct_0(esk1_0)))=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_98]), c_0_88]), c_0_68])])).
% 0.53/0.69  fof(c_0_102, plain, ![X56, X57]:(~l1_pre_topc(X56)|(~m1_subset_1(X57,k1_zfmisc_1(u1_struct_0(X56)))|k2_pre_topc(X56,X57)=k4_subset_1(u1_struct_0(X56),X57,k2_tops_1(X56,X57)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_tops_1])])])).
% 0.53/0.69  fof(c_0_103, plain, ![X54, X55]:(~l1_pre_topc(X54)|(~m1_subset_1(X55,k1_zfmisc_1(u1_struct_0(X54)))|k2_tops_1(X54,X55)=k2_tops_1(X54,k3_subset_1(u1_struct_0(X54),X55)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_tops_1])])])).
% 0.53/0.69  fof(c_0_104, plain, ![X36, X37]:(~m1_subset_1(X37,k1_zfmisc_1(X36))|m1_subset_1(k3_subset_1(X36,X37),k1_zfmisc_1(X36))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 0.53/0.69  cnf(c_0_105, plain, (k3_subset_1(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))))=k1_setfam_1(k2_tarski(X2,X1))), inference(spm,[status(thm)],[c_0_99, c_0_52])).
% 0.53/0.69  cnf(c_0_106, negated_conjecture, (k5_xboole_0(u1_struct_0(esk1_0),esk2_0)=k3_subset_1(u1_struct_0(esk1_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_101]), c_0_39])])).
% 0.53/0.69  cnf(c_0_107, plain, (m1_subset_1(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_50, c_0_52])).
% 0.53/0.69  cnf(c_0_108, plain, (k2_pre_topc(X1,X2)=k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_102])).
% 0.53/0.69  cnf(c_0_109, plain, (k2_tops_1(X1,X2)=k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_103])).
% 0.53/0.69  cnf(c_0_110, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_104])).
% 0.53/0.69  cnf(c_0_111, negated_conjecture, (k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))=esk2_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_101]), c_0_106])).
% 0.53/0.69  cnf(c_0_112, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.53/0.69  cnf(c_0_113, negated_conjecture, (m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_101]), c_0_106])).
% 0.53/0.69  fof(c_0_114, plain, ![X49, X50]:(~l1_pre_topc(X49)|~m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X49)))|m1_subset_1(k2_tops_1(X49,X50),k1_zfmisc_1(u1_struct_0(X49)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_1])])).
% 0.53/0.69  fof(c_0_115, plain, ![X40, X41, X42]:(~m1_subset_1(X41,k1_zfmisc_1(X40))|~m1_subset_1(X42,k1_zfmisc_1(X40))|k4_subset_1(X40,X41,X42)=k2_xboole_0(X41,X42)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 0.53/0.69  cnf(c_0_116, plain, (k4_subset_1(u1_struct_0(X1),k3_subset_1(u1_struct_0(X1),X2),k2_tops_1(X1,X2))=k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_109]), c_0_110])).
% 0.53/0.69  cnf(c_0_117, negated_conjecture, (k2_tops_1(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0))=k2_tops_1(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_111]), c_0_112]), c_0_113])])).
% 0.53/0.69  cnf(c_0_118, plain, (m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_114])).
% 0.53/0.69  fof(c_0_119, plain, ![X51, X52, X53]:(~l1_pre_topc(X51)|(~m1_subset_1(X52,k1_zfmisc_1(u1_struct_0(X51)))|(~m1_subset_1(X53,k1_zfmisc_1(u1_struct_0(X51)))|(~v4_pre_topc(X52,X51)|~r1_tarski(X53,X52)|r1_tarski(k2_pre_topc(X51,X53),X52))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_tops_1])])])).
% 0.53/0.69  fof(c_0_120, plain, ![X30, X31]:r1_tarski(X30,k2_xboole_0(X30,X31)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.53/0.69  cnf(c_0_121, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_115])).
% 0.53/0.69  cnf(c_0_122, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),esk2_0,k2_tops_1(esk1_0,esk2_0))=k2_pre_topc(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_117]), c_0_111]), c_0_111]), c_0_112]), c_0_113])])).
% 0.53/0.69  cnf(c_0_123, negated_conjecture, (m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118, c_0_117]), c_0_112]), c_0_113])])).
% 0.53/0.69  cnf(c_0_124, plain, (r1_tarski(k2_pre_topc(X1,X3),X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v4_pre_topc(X2,X1)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_119])).
% 0.53/0.69  cnf(c_0_125, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_120])).
% 0.53/0.69  cnf(c_0_126, negated_conjecture, (k2_xboole_0(esk2_0,k2_tops_1(esk1_0,esk2_0))=k2_pre_topc(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121, c_0_122]), c_0_123]), c_0_39])])).
% 0.53/0.69  cnf(c_0_127, plain, (X1=k2_pre_topc(X2,X3)|~v4_pre_topc(X1,X2)|~l1_pre_topc(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(X1,k2_pre_topc(X2,X3))|~r1_tarski(X3,X1)), inference(spm,[status(thm)],[c_0_55, c_0_124])).
% 0.53/0.69  cnf(c_0_128, negated_conjecture, (r1_tarski(esk2_0,k2_pre_topc(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_125, c_0_126])).
% 0.53/0.69  cnf(c_0_129, negated_conjecture, (v4_pre_topc(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.53/0.69  cnf(c_0_130, negated_conjecture, (k2_pre_topc(esk1_0,esk2_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127, c_0_128]), c_0_129]), c_0_112]), c_0_39]), c_0_83])])).
% 0.53/0.69  cnf(c_0_131, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_125, c_0_71])).
% 0.53/0.69  cnf(c_0_132, negated_conjecture, (k2_xboole_0(esk2_0,k2_tops_1(esk1_0,esk2_0))=esk2_0), inference(rw,[status(thm)],[c_0_126, c_0_130])).
% 0.53/0.69  cnf(c_0_133, negated_conjecture, (~r1_tarski(k2_tops_1(esk1_0,esk2_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.53/0.69  cnf(c_0_134, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_131, c_0_132]), c_0_133]), ['proof']).
% 0.53/0.69  # SZS output end CNFRefutation
% 0.53/0.69  # Proof object total steps             : 135
% 0.53/0.69  # Proof object clause steps            : 80
% 0.53/0.69  # Proof object formula steps           : 55
% 0.53/0.69  # Proof object conjectures             : 26
% 0.53/0.69  # Proof object clause conjectures      : 23
% 0.53/0.69  # Proof object formula conjectures     : 3
% 0.53/0.69  # Proof object initial clauses used    : 31
% 0.53/0.69  # Proof object initial formulas used   : 27
% 0.53/0.69  # Proof object generating inferences   : 37
% 0.53/0.69  # Proof object simplifying inferences  : 56
% 0.53/0.69  # Training examples: 0 positive, 0 negative
% 0.53/0.69  # Parsed axioms                        : 27
% 0.53/0.69  # Removed by relevancy pruning/SinE    : 0
% 0.53/0.69  # Initial clauses                      : 34
% 0.53/0.69  # Removed in clause preprocessing      : 3
% 0.53/0.69  # Initial clauses in saturation        : 31
% 0.53/0.69  # Processed clauses                    : 4724
% 0.53/0.69  # ...of these trivial                  : 95
% 0.53/0.69  # ...subsumed                          : 3743
% 0.53/0.69  # ...remaining for further processing  : 886
% 0.53/0.69  # Other redundant clauses eliminated   : 148
% 0.53/0.69  # Clauses deleted for lack of memory   : 0
% 0.53/0.69  # Backward-subsumed                    : 97
% 0.53/0.69  # Backward-rewritten                   : 38
% 0.53/0.69  # Generated clauses                    : 29218
% 0.53/0.69  # ...of the previous two non-trivial   : 23854
% 0.53/0.69  # Contextual simplify-reflections      : 31
% 0.53/0.69  # Paramodulations                      : 29070
% 0.53/0.69  # Factorizations                       : 0
% 0.53/0.69  # Equation resolutions                 : 148
% 0.53/0.69  # Propositional unsat checks           : 0
% 0.53/0.69  #    Propositional check models        : 0
% 0.53/0.69  #    Propositional check unsatisfiable : 0
% 0.53/0.69  #    Propositional clauses             : 0
% 0.53/0.69  #    Propositional clauses after purity: 0
% 0.53/0.69  #    Propositional unsat core size     : 0
% 0.53/0.69  #    Propositional preprocessing time  : 0.000
% 0.53/0.69  #    Propositional encoding time       : 0.000
% 0.53/0.69  #    Propositional solver time         : 0.000
% 0.53/0.69  #    Success case prop preproc time    : 0.000
% 0.53/0.69  #    Success case prop encoding time   : 0.000
% 0.53/0.69  #    Success case prop solver time     : 0.000
% 0.53/0.69  # Current number of processed clauses  : 719
% 0.53/0.69  #    Positive orientable unit clauses  : 103
% 0.53/0.69  #    Positive unorientable unit clauses: 4
% 0.53/0.69  #    Negative unit clauses             : 11
% 0.53/0.69  #    Non-unit-clauses                  : 601
% 0.53/0.69  # Current number of unprocessed clauses: 19003
% 0.53/0.69  # ...number of literals in the above   : 51651
% 0.53/0.69  # Current number of archived formulas  : 0
% 0.53/0.69  # Current number of archived clauses   : 168
% 0.53/0.69  # Clause-clause subsumption calls (NU) : 131959
% 0.53/0.69  # Rec. Clause-clause subsumption calls : 94566
% 0.53/0.69  # Non-unit clause-clause subsumptions  : 3324
% 0.53/0.69  # Unit Clause-clause subsumption calls : 2364
% 0.53/0.69  # Rewrite failures with RHS unbound    : 0
% 0.53/0.69  # BW rewrite match attempts            : 478
% 0.53/0.69  # BW rewrite match successes           : 37
% 0.53/0.69  # Condensation attempts                : 0
% 0.53/0.69  # Condensation successes               : 0
% 0.53/0.69  # Termbank termtop insertions          : 387547
% 0.53/0.69  
% 0.53/0.69  # -------------------------------------------------
% 0.53/0.69  # User time                : 0.347 s
% 0.53/0.69  # System time              : 0.016 s
% 0.53/0.69  # Total time               : 0.363 s
% 0.53/0.69  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------

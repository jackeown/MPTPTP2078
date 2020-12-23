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
% DateTime   : Thu Dec  3 11:11:06 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :  125 (2048 expanded)
%              Number of clauses        :   80 ( 971 expanded)
%              Number of leaves         :   22 ( 534 expanded)
%              Depth                    :   22
%              Number of atoms          :  246 (2957 expanded)
%              Number of equality atoms :   62 (1627 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    9 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t38_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k4_xboole_0(X2,X1))
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

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

fof(t69_tops_1,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v4_pre_topc(X2,X1)
           => r1_tarski(k2_tops_1(X1,X2),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

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

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

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

fof(c_0_22,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_23,plain,(
    ! [X13] : r1_tarski(k1_xboole_0,X13) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_24,plain,(
    ! [X8,X9] : r1_tarski(k3_xboole_0(X8,X9),X8) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_25,plain,(
    ! [X49,X50] : k1_setfam_1(k2_tarski(X49,X50)) = k3_xboole_0(X49,X50) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_26,plain,(
    ! [X6,X7] : k4_xboole_0(X6,X7) = k5_xboole_0(X6,k3_xboole_0(X6,X7)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_27,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_31,plain,(
    ! [X18] : k4_xboole_0(X18,k1_xboole_0) = X18 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_29,c_0_30])).

fof(c_0_35,plain,(
    ! [X29,X30] : k2_tarski(X29,X30) = k2_tarski(X30,X29) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

fof(c_0_36,plain,(
    ! [X33,X34] :
      ( ~ m1_subset_1(X34,k1_zfmisc_1(X33))
      | k3_subset_1(X33,X34) = k4_xboole_0(X33,X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_37,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_32,c_0_30])).

cnf(c_0_39,plain,
    ( k1_setfam_1(k2_tarski(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_40,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_41,plain,(
    ! [X25,X26] : k4_xboole_0(X25,k4_xboole_0(X25,X26)) = k3_xboole_0(X25,X26) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_42,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_43,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_xboole_0))) = X1 ),
    inference(rw,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_44,plain,
    ( k1_setfam_1(k2_tarski(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

fof(c_0_45,plain,(
    ! [X16,X17] :
      ( ~ r1_tarski(X16,k4_xboole_0(X17,X16))
      | X16 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_xboole_1])])).

cnf(c_0_46,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_47,plain,(
    ! [X35,X36] :
      ( ~ m1_subset_1(X36,k1_zfmisc_1(X35))
      | m1_subset_1(k3_subset_1(X35,X36),k1_zfmisc_1(X35)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

cnf(c_0_48,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_42,c_0_38])).

cnf(c_0_49,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_50,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_51,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))))) = k1_setfam_1(k2_tarski(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_30]),c_0_38]),c_0_38])).

cnf(c_0_52,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_53,plain,
    ( k3_subset_1(X1,k1_xboole_0) = X1
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_44]),c_0_49])).

fof(c_0_54,plain,(
    ! [X51,X52] :
      ( ( ~ m1_subset_1(X51,k1_zfmisc_1(X52))
        | r1_tarski(X51,X52) )
      & ( ~ r1_tarski(X51,X52)
        | m1_subset_1(X51,k1_zfmisc_1(X52)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_55,plain,(
    ! [X27,X28] : r1_tarski(X27,k2_xboole_0(X27,X28)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_56,plain,(
    ! [X31,X32] : k3_tarski(k2_tarski(X31,X32)) = k2_xboole_0(X31,X32) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

cnf(c_0_57,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))) ),
    inference(rw,[status(thm)],[c_0_50,c_0_38])).

cnf(c_0_58,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_setfam_1(k2_tarski(X1,X2))))) = k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))))) ),
    inference(spm,[status(thm)],[c_0_51,c_0_51])).

cnf(c_0_59,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_60,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

fof(c_0_61,plain,(
    ! [X19,X20,X21] :
      ( ~ r1_tarski(X19,k2_xboole_0(X20,X21))
      | r1_tarski(k4_xboole_0(X19,X20),X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).

fof(c_0_62,plain,(
    ! [X10,X11,X12] :
      ( ~ r1_tarski(X10,X11)
      | ~ r1_tarski(X11,X12)
      | r1_tarski(X10,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_63,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_64,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

fof(c_0_65,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v4_pre_topc(X2,X1)
             => r1_tarski(k2_tops_1(X1,X2),X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t69_tops_1])).

cnf(c_0_66,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_40])).

cnf(c_0_67,plain,
    ( k1_setfam_1(k2_tarski(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_44]),c_0_44]),c_0_49]),c_0_49])).

cnf(c_0_68,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_28])])).

cnf(c_0_69,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_70,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_71,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_63,c_0_64])).

fof(c_0_72,negated_conjecture,
    ( l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & v4_pre_topc(esk2_0,esk1_0)
    & ~ r1_tarski(k2_tops_1(esk1_0,esk2_0),esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_65])])])).

cnf(c_0_73,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k5_xboole_0(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_74,plain,
    ( k5_xboole_0(X1,X1) = k3_subset_1(X1,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_67]),c_0_68])])).

cnf(c_0_75,plain,
    ( r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X3)
    | ~ r1_tarski(X1,k3_tarski(k2_tarski(X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_64]),c_0_38])).

fof(c_0_76,plain,(
    ! [X14,X15] : r1_tarski(k4_xboole_0(X14,X15),X14) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_77,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_78,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_79,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_80,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k3_subset_1(X1,X1)) ),
    inference(rw,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_81,plain,
    ( r1_tarski(k3_subset_1(X1,X1),X2) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_67]),c_0_71])]),c_0_74])).

cnf(c_0_82,plain,
    ( k3_subset_1(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))) = k1_setfam_1(k2_tarski(X1,X2))
    | ~ m1_subset_1(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_48])).

cnf(c_0_83,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_84,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))
    | ~ r1_tarski(X1,X4)
    | ~ r1_tarski(X4,X2) ),
    inference(spm,[status(thm)],[c_0_70,c_0_77])).

cnf(c_0_85,negated_conjecture,
    ( r1_tarski(esk2_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_86,plain,
    ( k3_subset_1(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

fof(c_0_87,plain,(
    ! [X55,X56,X57] :
      ( ~ l1_pre_topc(X55)
      | ~ m1_subset_1(X56,k1_zfmisc_1(u1_struct_0(X55)))
      | ~ m1_subset_1(X57,k1_zfmisc_1(u1_struct_0(X55)))
      | ~ v4_pre_topc(X56,X55)
      | ~ r1_tarski(X57,X56)
      | r1_tarski(k2_pre_topc(X55,X57),X56) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_tops_1])])])).

cnf(c_0_88,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(X1,X2)),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_82])).

cnf(c_0_89,plain,
    ( r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X1) ),
    inference(rw,[status(thm)],[c_0_83,c_0_38])).

cnf(c_0_90,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k1_xboole_0
    | ~ r1_tarski(X1,k3_tarski(k2_tarski(X2,k5_xboole_0(X3,k1_setfam_1(k2_tarski(X3,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))))))))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_75])).

cnf(c_0_91,negated_conjecture,
    ( r1_tarski(esk2_0,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_tarski(u1_struct_0(esk1_0),X1) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_92,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_86]),c_0_68])])).

cnf(c_0_93,plain,
    ( r1_tarski(k2_pre_topc(X1,X3),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X2,X1)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

cnf(c_0_94,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(X1,X2)),k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_60]),c_0_89])])).

cnf(c_0_95,negated_conjecture,
    ( k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1))) = k1_xboole_0
    | ~ r1_tarski(u1_struct_0(esk1_0),X1) ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_96,plain,
    ( k3_subset_1(X1,k1_xboole_0) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_92])])).

cnf(c_0_97,plain,
    ( r1_tarski(X1,X2)
    | ~ v4_pre_topc(X2,X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ r1_tarski(X1,k2_pre_topc(X3,X4))
    | ~ r1_tarski(X4,X2) ),
    inference(spm,[status(thm)],[c_0_70,c_0_93])).

cnf(c_0_98,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_99,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(X1,X2)),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_94,c_0_40])).

cnf(c_0_100,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk2_0,X1)) = esk2_0
    | ~ r1_tarski(u1_struct_0(esk1_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_95]),c_0_96]),c_0_92])])).

cnf(c_0_101,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_102,plain,(
    ! [X40,X41,X42] :
      ( ~ m1_subset_1(X41,k1_zfmisc_1(X40))
      | ~ m1_subset_1(X42,k1_zfmisc_1(X40))
      | k4_subset_1(X40,X41,X42) = k2_xboole_0(X41,X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_103,negated_conjecture,
    ( r1_tarski(X1,X2)
    | ~ v4_pre_topc(X2,esk1_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(X1,k2_pre_topc(esk1_0,esk2_0))
    | ~ r1_tarski(esk2_0,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_79]),c_0_98])])).

cnf(c_0_104,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(X1))
    | ~ r1_tarski(u1_struct_0(esk1_0),X1) ),
    inference(spm,[status(thm)],[c_0_99,c_0_100])).

cnf(c_0_105,negated_conjecture,
    ( v4_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_106,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_101])).

cnf(c_0_107,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_102])).

fof(c_0_108,plain,(
    ! [X60,X61] :
      ( ~ l1_pre_topc(X60)
      | ~ m1_subset_1(X61,k1_zfmisc_1(u1_struct_0(X60)))
      | k2_pre_topc(X60,X61) = k4_subset_1(u1_struct_0(X60),X61,k2_tops_1(X60,X61)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_tops_1])])])).

fof(c_0_109,plain,(
    ! [X53,X54] :
      ( ~ l1_pre_topc(X53)
      | ~ m1_subset_1(X54,k1_zfmisc_1(u1_struct_0(X53)))
      | m1_subset_1(k2_tops_1(X53,X54),k1_zfmisc_1(u1_struct_0(X53))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_1])])).

cnf(c_0_110,negated_conjecture,
    ( r1_tarski(X1,esk2_0)
    | ~ r1_tarski(X1,k2_pre_topc(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_104]),c_0_105]),c_0_106]),c_0_106])])).

cnf(c_0_111,plain,
    ( k4_subset_1(X2,X1,X3) = k3_tarski(k2_tarski(X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_107,c_0_64])).

cnf(c_0_112,plain,
    ( k2_pre_topc(X1,X2) = k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_108])).

cnf(c_0_113,plain,
    ( m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_109])).

cnf(c_0_114,negated_conjecture,
    ( r1_tarski(k2_pre_topc(esk1_0,esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_110,c_0_106])).

cnf(c_0_115,plain,
    ( r1_tarski(X1,k4_subset_1(X2,X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_111])).

cnf(c_0_116,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_77,c_0_40])).

cnf(c_0_117,plain,
    ( k3_tarski(k2_tarski(X1,k2_tops_1(X2,X1))) = k2_pre_topc(X2,X1)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_112]),c_0_113])).

cnf(c_0_118,negated_conjecture,
    ( k2_pre_topc(esk1_0,esk2_0) = esk2_0
    | ~ r1_tarski(esk2_0,k2_pre_topc(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_114])).

cnf(c_0_119,plain,
    ( r1_tarski(X1,k2_pre_topc(X2,X1))
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_112]),c_0_113])).

cnf(c_0_120,plain,
    ( r1_tarski(X1,k2_pre_topc(X2,X3))
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(X1,k2_tops_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_116,c_0_117])).

cnf(c_0_121,negated_conjecture,
    ( k2_pre_topc(esk1_0,esk2_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_119]),c_0_98]),c_0_79])])).

cnf(c_0_122,negated_conjecture,
    ( r1_tarski(X1,esk2_0)
    | ~ r1_tarski(X1,k2_tops_1(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_121]),c_0_98]),c_0_79])])).

cnf(c_0_123,negated_conjecture,
    ( ~ r1_tarski(k2_tops_1(esk1_0,esk2_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_124,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_106]),c_0_123]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:24:59 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 1.81/2.00  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 1.81/2.00  # and selection function SelectComplexExceptUniqMaxHorn.
% 1.81/2.00  #
% 1.81/2.00  # Preprocessing time       : 0.029 s
% 1.81/2.00  # Presaturation interreduction done
% 1.81/2.00  
% 1.81/2.00  # Proof found!
% 1.81/2.00  # SZS status Theorem
% 1.81/2.00  # SZS output start CNFRefutation
% 1.81/2.00  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.81/2.00  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.81/2.00  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.81/2.00  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 1.81/2.00  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.81/2.00  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 1.81/2.00  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 1.81/2.00  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 1.81/2.00  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.81/2.00  fof(t38_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,k4_xboole_0(X2,X1))=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_xboole_1)).
% 1.81/2.00  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 1.81/2.00  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 1.81/2.00  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.81/2.00  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 1.81/2.00  fof(t43_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_xboole_0(X2,X3))=>r1_tarski(k4_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 1.81/2.00  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.81/2.00  fof(t69_tops_1, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)=>r1_tarski(k2_tops_1(X1,X2),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_tops_1)).
% 1.81/2.00  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 1.81/2.00  fof(t31_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v4_pre_topc(X2,X1)&r1_tarski(X3,X2))=>r1_tarski(k2_pre_topc(X1,X3),X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_tops_1)).
% 1.81/2.00  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 1.81/2.00  fof(t65_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_pre_topc(X1,X2)=k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 1.81/2.00  fof(dt_k2_tops_1, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 1.81/2.00  fof(c_0_22, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 1.81/2.00  fof(c_0_23, plain, ![X13]:r1_tarski(k1_xboole_0,X13), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 1.81/2.00  fof(c_0_24, plain, ![X8, X9]:r1_tarski(k3_xboole_0(X8,X9),X8), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 1.81/2.00  fof(c_0_25, plain, ![X49, X50]:k1_setfam_1(k2_tarski(X49,X50))=k3_xboole_0(X49,X50), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 1.81/2.00  fof(c_0_26, plain, ![X6, X7]:k4_xboole_0(X6,X7)=k5_xboole_0(X6,k3_xboole_0(X6,X7)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 1.81/2.00  cnf(c_0_27, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 1.81/2.00  cnf(c_0_28, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.81/2.00  cnf(c_0_29, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.81/2.00  cnf(c_0_30, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 1.81/2.00  fof(c_0_31, plain, ![X18]:k4_xboole_0(X18,k1_xboole_0)=X18, inference(variable_rename,[status(thm)],[t3_boole])).
% 1.81/2.00  cnf(c_0_32, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 1.81/2.00  cnf(c_0_33, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 1.81/2.00  cnf(c_0_34, plain, (r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_29, c_0_30])).
% 1.81/2.00  fof(c_0_35, plain, ![X29, X30]:k2_tarski(X29,X30)=k2_tarski(X30,X29), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 1.81/2.00  fof(c_0_36, plain, ![X33, X34]:(~m1_subset_1(X34,k1_zfmisc_1(X33))|k3_subset_1(X33,X34)=k4_xboole_0(X33,X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 1.81/2.00  cnf(c_0_37, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_31])).
% 1.81/2.00  cnf(c_0_38, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_32, c_0_30])).
% 1.81/2.00  cnf(c_0_39, plain, (k1_setfam_1(k2_tarski(k1_xboole_0,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 1.81/2.00  cnf(c_0_40, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 1.81/2.00  fof(c_0_41, plain, ![X25, X26]:k4_xboole_0(X25,k4_xboole_0(X25,X26))=k3_xboole_0(X25,X26), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 1.81/2.00  cnf(c_0_42, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 1.81/2.00  cnf(c_0_43, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_xboole_0)))=X1), inference(rw,[status(thm)],[c_0_37, c_0_38])).
% 1.81/2.01  cnf(c_0_44, plain, (k1_setfam_1(k2_tarski(X1,k1_xboole_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 1.81/2.01  fof(c_0_45, plain, ![X16, X17]:(~r1_tarski(X16,k4_xboole_0(X17,X16))|X16=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_xboole_1])])).
% 1.81/2.01  cnf(c_0_46, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 1.81/2.01  fof(c_0_47, plain, ![X35, X36]:(~m1_subset_1(X36,k1_zfmisc_1(X35))|m1_subset_1(k3_subset_1(X35,X36),k1_zfmisc_1(X35))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 1.81/2.01  cnf(c_0_48, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_42, c_0_38])).
% 1.81/2.01  cnf(c_0_49, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_43, c_0_44])).
% 1.81/2.01  cnf(c_0_50, plain, (X1=k1_xboole_0|~r1_tarski(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 1.81/2.01  cnf(c_0_51, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))))))=k1_setfam_1(k2_tarski(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_30]), c_0_38]), c_0_38])).
% 1.81/2.01  cnf(c_0_52, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 1.81/2.01  cnf(c_0_53, plain, (k3_subset_1(X1,k1_xboole_0)=X1|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_44]), c_0_49])).
% 1.81/2.01  fof(c_0_54, plain, ![X51, X52]:((~m1_subset_1(X51,k1_zfmisc_1(X52))|r1_tarski(X51,X52))&(~r1_tarski(X51,X52)|m1_subset_1(X51,k1_zfmisc_1(X52)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 1.81/2.01  fof(c_0_55, plain, ![X27, X28]:r1_tarski(X27,k2_xboole_0(X27,X28)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 1.81/2.01  fof(c_0_56, plain, ![X31, X32]:k3_tarski(k2_tarski(X31,X32))=k2_xboole_0(X31,X32), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 1.81/2.01  cnf(c_0_57, plain, (X1=k1_xboole_0|~r1_tarski(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1))))), inference(rw,[status(thm)],[c_0_50, c_0_38])).
% 1.81/2.01  cnf(c_0_58, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_setfam_1(k2_tarski(X1,X2)))))=k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))))), inference(spm,[status(thm)],[c_0_51, c_0_51])).
% 1.81/2.01  cnf(c_0_59, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 1.81/2.01  cnf(c_0_60, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 1.81/2.01  fof(c_0_61, plain, ![X19, X20, X21]:(~r1_tarski(X19,k2_xboole_0(X20,X21))|r1_tarski(k4_xboole_0(X19,X20),X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).
% 1.81/2.01  fof(c_0_62, plain, ![X10, X11, X12]:(~r1_tarski(X10,X11)|~r1_tarski(X11,X12)|r1_tarski(X10,X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 1.81/2.01  cnf(c_0_63, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 1.81/2.01  cnf(c_0_64, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 1.81/2.01  fof(c_0_65, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)=>r1_tarski(k2_tops_1(X1,X2),X2))))), inference(assume_negation,[status(cth)],[t69_tops_1])).
% 1.81/2.01  cnf(c_0_66, plain, (X1=k1_xboole_0|~r1_tarski(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X1,X2))))), inference(spm,[status(thm)],[c_0_57, c_0_40])).
% 1.81/2.01  cnf(c_0_67, plain, (k1_setfam_1(k2_tarski(X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_44]), c_0_44]), c_0_49]), c_0_49])).
% 1.81/2.01  cnf(c_0_68, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_28])])).
% 1.81/2.01  cnf(c_0_69, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 1.81/2.01  cnf(c_0_70, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 1.81/2.01  cnf(c_0_71, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_63, c_0_64])).
% 1.81/2.01  fof(c_0_72, negated_conjecture, (l1_pre_topc(esk1_0)&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(v4_pre_topc(esk2_0,esk1_0)&~r1_tarski(k2_tops_1(esk1_0,esk2_0),esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_65])])])).
% 1.81/2.01  cnf(c_0_73, plain, (X1=k1_xboole_0|~r1_tarski(X1,k5_xboole_0(X1,X1))), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 1.81/2.01  cnf(c_0_74, plain, (k5_xboole_0(X1,X1)=k3_subset_1(X1,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_67]), c_0_68])])).
% 1.81/2.01  cnf(c_0_75, plain, (r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X3)|~r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_64]), c_0_38])).
% 1.81/2.01  fof(c_0_76, plain, ![X14, X15]:r1_tarski(k4_xboole_0(X14,X15),X14), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 1.81/2.01  cnf(c_0_77, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 1.81/2.01  cnf(c_0_78, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 1.81/2.01  cnf(c_0_79, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_72])).
% 1.81/2.01  cnf(c_0_80, plain, (X1=k1_xboole_0|~r1_tarski(X1,k3_subset_1(X1,X1))), inference(rw,[status(thm)],[c_0_73, c_0_74])).
% 1.81/2.01  cnf(c_0_81, plain, (r1_tarski(k3_subset_1(X1,X1),X2)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_67]), c_0_71])]), c_0_74])).
% 1.81/2.01  cnf(c_0_82, plain, (k3_subset_1(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))))=k1_setfam_1(k2_tarski(X1,X2))|~m1_subset_1(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_51, c_0_48])).
% 1.81/2.01  cnf(c_0_83, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_76])).
% 1.81/2.01  cnf(c_0_84, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))|~r1_tarski(X1,X4)|~r1_tarski(X4,X2)), inference(spm,[status(thm)],[c_0_70, c_0_77])).
% 1.81/2.01  cnf(c_0_85, negated_conjecture, (r1_tarski(esk2_0,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 1.81/2.01  cnf(c_0_86, plain, (k3_subset_1(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 1.81/2.01  fof(c_0_87, plain, ![X55, X56, X57]:(~l1_pre_topc(X55)|(~m1_subset_1(X56,k1_zfmisc_1(u1_struct_0(X55)))|(~m1_subset_1(X57,k1_zfmisc_1(u1_struct_0(X55)))|(~v4_pre_topc(X56,X55)|~r1_tarski(X57,X56)|r1_tarski(k2_pre_topc(X55,X57),X56))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_tops_1])])])).
% 1.81/2.01  cnf(c_0_88, plain, (m1_subset_1(k1_setfam_1(k2_tarski(X1,X2)),k1_zfmisc_1(X1))|~m1_subset_1(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_52, c_0_82])).
% 1.81/2.01  cnf(c_0_89, plain, (r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X1)), inference(rw,[status(thm)],[c_0_83, c_0_38])).
% 1.81/2.01  cnf(c_0_90, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k1_xboole_0|~r1_tarski(X1,k3_tarski(k2_tarski(X2,k5_xboole_0(X3,k1_setfam_1(k2_tarski(X3,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))))))))), inference(spm,[status(thm)],[c_0_57, c_0_75])).
% 1.81/2.01  cnf(c_0_91, negated_conjecture, (r1_tarski(esk2_0,k3_tarski(k2_tarski(X1,X2)))|~r1_tarski(u1_struct_0(esk1_0),X1)), inference(spm,[status(thm)],[c_0_84, c_0_85])).
% 1.81/2.01  cnf(c_0_92, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_86]), c_0_68])])).
% 1.81/2.01  cnf(c_0_93, plain, (r1_tarski(k2_pre_topc(X1,X3),X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v4_pre_topc(X2,X1)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_87])).
% 1.81/2.01  cnf(c_0_94, plain, (m1_subset_1(k1_setfam_1(k2_tarski(X1,X2)),k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_60]), c_0_89])])).
% 1.81/2.01  cnf(c_0_95, negated_conjecture, (k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1)))=k1_xboole_0|~r1_tarski(u1_struct_0(esk1_0),X1)), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 1.81/2.01  cnf(c_0_96, plain, (k3_subset_1(X1,k1_xboole_0)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_92])])).
% 1.81/2.01  cnf(c_0_97, plain, (r1_tarski(X1,X2)|~v4_pre_topc(X2,X3)|~l1_pre_topc(X3)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~r1_tarski(X1,k2_pre_topc(X3,X4))|~r1_tarski(X4,X2)), inference(spm,[status(thm)],[c_0_70, c_0_93])).
% 1.81/2.01  cnf(c_0_98, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 1.81/2.01  cnf(c_0_99, plain, (m1_subset_1(k1_setfam_1(k2_tarski(X1,X2)),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_94, c_0_40])).
% 1.81/2.01  cnf(c_0_100, negated_conjecture, (k1_setfam_1(k2_tarski(esk2_0,X1))=esk2_0|~r1_tarski(u1_struct_0(esk1_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_95]), c_0_96]), c_0_92])])).
% 1.81/2.01  cnf(c_0_101, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_22])).
% 1.81/2.01  fof(c_0_102, plain, ![X40, X41, X42]:(~m1_subset_1(X41,k1_zfmisc_1(X40))|~m1_subset_1(X42,k1_zfmisc_1(X40))|k4_subset_1(X40,X41,X42)=k2_xboole_0(X41,X42)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 1.81/2.01  cnf(c_0_103, negated_conjecture, (r1_tarski(X1,X2)|~v4_pre_topc(X2,esk1_0)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(X1,k2_pre_topc(esk1_0,esk2_0))|~r1_tarski(esk2_0,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_79]), c_0_98])])).
% 1.81/2.01  cnf(c_0_104, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(X1))|~r1_tarski(u1_struct_0(esk1_0),X1)), inference(spm,[status(thm)],[c_0_99, c_0_100])).
% 1.81/2.01  cnf(c_0_105, negated_conjecture, (v4_pre_topc(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 1.81/2.01  cnf(c_0_106, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_101])).
% 1.81/2.01  cnf(c_0_107, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_102])).
% 1.81/2.01  fof(c_0_108, plain, ![X60, X61]:(~l1_pre_topc(X60)|(~m1_subset_1(X61,k1_zfmisc_1(u1_struct_0(X60)))|k2_pre_topc(X60,X61)=k4_subset_1(u1_struct_0(X60),X61,k2_tops_1(X60,X61)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_tops_1])])])).
% 1.81/2.01  fof(c_0_109, plain, ![X53, X54]:(~l1_pre_topc(X53)|~m1_subset_1(X54,k1_zfmisc_1(u1_struct_0(X53)))|m1_subset_1(k2_tops_1(X53,X54),k1_zfmisc_1(u1_struct_0(X53)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_1])])).
% 1.81/2.01  cnf(c_0_110, negated_conjecture, (r1_tarski(X1,esk2_0)|~r1_tarski(X1,k2_pre_topc(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_104]), c_0_105]), c_0_106]), c_0_106])])).
% 1.81/2.01  cnf(c_0_111, plain, (k4_subset_1(X2,X1,X3)=k3_tarski(k2_tarski(X1,X3))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_107, c_0_64])).
% 1.81/2.01  cnf(c_0_112, plain, (k2_pre_topc(X1,X2)=k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_108])).
% 1.81/2.01  cnf(c_0_113, plain, (m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_109])).
% 1.81/2.01  cnf(c_0_114, negated_conjecture, (r1_tarski(k2_pre_topc(esk1_0,esk2_0),esk2_0)), inference(spm,[status(thm)],[c_0_110, c_0_106])).
% 1.81/2.01  cnf(c_0_115, plain, (r1_tarski(X1,k4_subset_1(X2,X1,X3))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_71, c_0_111])).
% 1.81/2.01  cnf(c_0_116, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_77, c_0_40])).
% 1.81/2.01  cnf(c_0_117, plain, (k3_tarski(k2_tarski(X1,k2_tops_1(X2,X1)))=k2_pre_topc(X2,X1)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_112]), c_0_113])).
% 1.81/2.01  cnf(c_0_118, negated_conjecture, (k2_pre_topc(esk1_0,esk2_0)=esk2_0|~r1_tarski(esk2_0,k2_pre_topc(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_27, c_0_114])).
% 1.81/2.01  cnf(c_0_119, plain, (r1_tarski(X1,k2_pre_topc(X2,X1))|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_112]), c_0_113])).
% 1.81/2.01  cnf(c_0_120, plain, (r1_tarski(X1,k2_pre_topc(X2,X3))|~l1_pre_topc(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(X1,k2_tops_1(X2,X3))), inference(spm,[status(thm)],[c_0_116, c_0_117])).
% 1.81/2.01  cnf(c_0_121, negated_conjecture, (k2_pre_topc(esk1_0,esk2_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118, c_0_119]), c_0_98]), c_0_79])])).
% 1.81/2.01  cnf(c_0_122, negated_conjecture, (r1_tarski(X1,esk2_0)|~r1_tarski(X1,k2_tops_1(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_121]), c_0_98]), c_0_79])])).
% 1.81/2.01  cnf(c_0_123, negated_conjecture, (~r1_tarski(k2_tops_1(esk1_0,esk2_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 1.81/2.01  cnf(c_0_124, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_122, c_0_106]), c_0_123]), ['proof']).
% 1.81/2.01  # SZS output end CNFRefutation
% 1.81/2.01  # Proof object total steps             : 125
% 1.81/2.01  # Proof object clause steps            : 80
% 1.81/2.01  # Proof object formula steps           : 45
% 1.81/2.01  # Proof object conjectures             : 19
% 1.81/2.01  # Proof object clause conjectures      : 16
% 1.81/2.01  # Proof object formula conjectures     : 3
% 1.81/2.01  # Proof object initial clauses used    : 27
% 1.81/2.01  # Proof object initial formulas used   : 22
% 1.81/2.01  # Proof object generating inferences   : 39
% 1.81/2.01  # Proof object simplifying inferences  : 51
% 1.81/2.01  # Training examples: 0 positive, 0 negative
% 1.81/2.01  # Parsed axioms                        : 27
% 1.81/2.01  # Removed by relevancy pruning/SinE    : 0
% 1.81/2.01  # Initial clauses                      : 33
% 1.81/2.01  # Removed in clause preprocessing      : 3
% 1.81/2.01  # Initial clauses in saturation        : 30
% 1.81/2.01  # Processed clauses                    : 14846
% 1.81/2.01  # ...of these trivial                  : 79
% 1.81/2.01  # ...subsumed                          : 12639
% 1.81/2.01  # ...remaining for further processing  : 2128
% 1.81/2.01  # Other redundant clauses eliminated   : 2
% 1.81/2.01  # Clauses deleted for lack of memory   : 0
% 1.81/2.01  # Backward-subsumed                    : 213
% 1.81/2.01  # Backward-rewritten                   : 76
% 1.81/2.01  # Generated clauses                    : 148999
% 1.81/2.01  # ...of the previous two non-trivial   : 136340
% 1.81/2.01  # Contextual simplify-reflections      : 78
% 1.81/2.01  # Paramodulations                      : 148997
% 1.81/2.01  # Factorizations                       : 0
% 1.81/2.01  # Equation resolutions                 : 2
% 1.81/2.01  # Propositional unsat checks           : 0
% 1.81/2.01  #    Propositional check models        : 0
% 1.81/2.01  #    Propositional check unsatisfiable : 0
% 1.81/2.01  #    Propositional clauses             : 0
% 1.81/2.01  #    Propositional clauses after purity: 0
% 1.81/2.01  #    Propositional unsat core size     : 0
% 1.81/2.01  #    Propositional preprocessing time  : 0.000
% 1.81/2.01  #    Propositional encoding time       : 0.000
% 1.81/2.01  #    Propositional solver time         : 0.000
% 1.81/2.01  #    Success case prop preproc time    : 0.000
% 1.81/2.01  #    Success case prop encoding time   : 0.000
% 1.81/2.01  #    Success case prop solver time     : 0.000
% 1.81/2.01  # Current number of processed clauses  : 1808
% 1.81/2.01  #    Positive orientable unit clauses  : 135
% 1.81/2.01  #    Positive unorientable unit clauses: 1
% 1.81/2.01  #    Negative unit clauses             : 46
% 1.81/2.01  #    Non-unit-clauses                  : 1626
% 1.81/2.01  # Current number of unprocessed clauses: 120861
% 1.81/2.01  # ...number of literals in the above   : 427755
% 1.81/2.01  # Current number of archived formulas  : 0
% 1.81/2.01  # Current number of archived clauses   : 321
% 1.81/2.01  # Clause-clause subsumption calls (NU) : 834642
% 1.81/2.01  # Rec. Clause-clause subsumption calls : 380955
% 1.81/2.01  # Non-unit clause-clause subsumptions  : 8207
% 1.81/2.01  # Unit Clause-clause subsumption calls : 12509
% 1.81/2.01  # Rewrite failures with RHS unbound    : 0
% 1.81/2.01  # BW rewrite match attempts            : 3640
% 1.81/2.01  # BW rewrite match successes           : 43
% 1.81/2.01  # Condensation attempts                : 0
% 1.81/2.01  # Condensation successes               : 0
% 1.81/2.01  # Termbank termtop insertions          : 3231847
% 1.81/2.01  
% 1.81/2.01  # -------------------------------------------------
% 1.81/2.01  # User time                : 1.602 s
% 1.81/2.01  # System time              : 0.064 s
% 1.81/2.01  # Total time               : 1.666 s
% 1.81/2.01  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------

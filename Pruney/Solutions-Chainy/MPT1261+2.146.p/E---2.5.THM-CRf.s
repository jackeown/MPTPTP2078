%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:11:48 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 655 expanded)
%              Number of clauses        :   62 ( 275 expanded)
%              Number of leaves         :   18 ( 164 expanded)
%              Depth                    :   14
%              Number of atoms          :  189 (1660 expanded)
%              Number of equality atoms :   86 ( 622 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    9 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(t77_tops_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v4_pre_topc(X2,X1)
          <=> k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k1_tops_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

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

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(dt_k2_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(t69_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v4_pre_topc(X2,X1)
           => r1_tarski(k2_tops_1(X1,X2),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

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

fof(t74_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k1_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

fof(c_0_18,plain,(
    ! [X14,X15] : r1_tarski(k4_xboole_0(X14,X15),X14) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_19,plain,(
    ! [X7,X8] : k4_xboole_0(X7,X8) = k5_xboole_0(X7,k3_xboole_0(X7,X8)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_20,plain,(
    ! [X19,X20] : k4_xboole_0(X19,k4_xboole_0(X19,X20)) = k3_xboole_0(X19,X20) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_21,plain,(
    ! [X24,X25,X26] :
      ( ~ m1_subset_1(X25,k1_zfmisc_1(X24))
      | k7_subset_1(X24,X25,X26) = k4_xboole_0(X25,X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

fof(c_0_22,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v4_pre_topc(X2,X1)
            <=> k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k1_tops_1(X1,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t77_tops_1])).

cnf(c_0_23,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_27,negated_conjecture,
    ( v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & ( ~ v4_pre_topc(esk2_0,esk1_0)
      | k2_tops_1(esk1_0,esk2_0) != k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0)) )
    & ( v4_pre_topc(esk2_0,esk1_0)
      | k2_tops_1(esk1_0,esk2_0) = k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])).

fof(c_0_28,plain,(
    ! [X27,X28] :
      ( ( ~ v4_pre_topc(X28,X27)
        | k2_pre_topc(X27,X28) = X28
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ l1_pre_topc(X27) )
      & ( ~ v2_pre_topc(X27)
        | k2_pre_topc(X27,X28) != X28
        | v4_pre_topc(X28,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ l1_pre_topc(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).

fof(c_0_29,plain,(
    ! [X9,X10] :
      ( ~ r1_tarski(X9,X10)
      | k2_xboole_0(X9,X10) = X10 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_30,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_31,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_24]),c_0_24])).

cnf(c_0_32,plain,
    ( k7_subset_1(X2,X1,X3) = k5_xboole_0(X1,k3_xboole_0(X1,X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_26,c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,plain,
    ( k2_pre_topc(X2,X1) = X1
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_36,plain,(
    ! [X18] : k4_xboole_0(X18,k1_xboole_0) = X18 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_37,plain,(
    ! [X11] : k2_xboole_0(X11,k1_xboole_0) = X11 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_38,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

fof(c_0_40,plain,(
    ! [X16,X17] : k2_xboole_0(X16,k4_xboole_0(X17,X16)) = k2_xboole_0(X16,X17) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_41,negated_conjecture,
    ( k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,X1)) = k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_42,negated_conjecture,
    ( k2_pre_topc(esk1_0,esk2_0) = esk2_0
    | ~ v4_pre_topc(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_33]),c_0_35])])).

cnf(c_0_43,negated_conjecture,
    ( v4_pre_topc(esk2_0,esk1_0)
    | k2_tops_1(esk1_0,esk2_0) = k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_44,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_45,plain,(
    ! [X6] : k3_xboole_0(X6,X6) = X6 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

fof(c_0_46,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_47,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_48,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),X1) = X1 ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

fof(c_0_49,plain,(
    ! [X29,X30] :
      ( ~ l1_pre_topc(X29)
      | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
      | m1_subset_1(k2_tops_1(X29,X30),k1_zfmisc_1(u1_struct_0(X29))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_1])])).

fof(c_0_50,plain,(
    ! [X33,X34] :
      ( ~ l1_pre_topc(X33)
      | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))
      | ~ v4_pre_topc(X34,X33)
      | r1_tarski(k2_tops_1(X33,X34),X34) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t69_tops_1])])])).

cnf(c_0_51,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_52,plain,(
    ! [X12,X13] :
      ( ~ r1_tarski(X12,X13)
      | k3_xboole_0(X12,X13) = X12 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1),esk2_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_41])).

cnf(c_0_54,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0)) = k2_tops_1(esk1_0,esk2_0)
    | k2_pre_topc(esk1_0,esk2_0) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_55,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[c_0_44,c_0_24])).

cnf(c_0_56,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_57,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_58,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

fof(c_0_59,plain,(
    ! [X21,X22,X23] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(X21))
      | ~ m1_subset_1(X23,k1_zfmisc_1(X21))
      | k4_subset_1(X21,X22,X23) = k2_xboole_0(X22,X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_60,plain,
    ( m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_61,plain,(
    ! [X31,X32] :
      ( ~ l1_pre_topc(X31)
      | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
      | k2_pre_topc(X31,X32) = k4_subset_1(u1_struct_0(X31),X32,k2_tops_1(X31,X32)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_tops_1])])])).

cnf(c_0_62,plain,
    ( r1_tarski(k2_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_63,plain,
    ( k2_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_51,c_0_24])).

cnf(c_0_64,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_65,negated_conjecture,
    ( k2_pre_topc(esk1_0,esk2_0) = esk2_0
    | r1_tarski(k2_tops_1(esk1_0,esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_66,plain,
    ( k5_xboole_0(X1,X1) = k3_xboole_0(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_55]),c_0_56])).

cnf(c_0_67,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_68,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_69,negated_conjecture,
    ( m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_33]),c_0_35])])).

cnf(c_0_70,plain,
    ( k2_pre_topc(X1,X2) = k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_71,negated_conjecture,
    ( r1_tarski(k2_tops_1(esk1_0,esk2_0),esk2_0)
    | ~ v4_pre_topc(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_33]),c_0_35])])).

cnf(c_0_72,plain,
    ( k2_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))) = k2_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_63,c_0_57])).

cnf(c_0_73,negated_conjecture,
    ( k3_xboole_0(esk2_0,k2_tops_1(esk1_0,esk2_0)) = k2_tops_1(esk1_0,esk2_0)
    | k2_pre_topc(esk1_0,esk2_0) = esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_57])).

cnf(c_0_74,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_75,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),X1,k2_tops_1(esk1_0,esk2_0)) = k2_xboole_0(X1,k2_tops_1(esk1_0,esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_76,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),esk2_0,k2_tops_1(esk1_0,esk2_0)) = k2_pre_topc(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_33]),c_0_35])])).

fof(c_0_77,plain,(
    ! [X35,X36] :
      ( ~ l1_pre_topc(X35)
      | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))
      | k1_tops_1(X35,X36) = k7_subset_1(u1_struct_0(X35),X36,k2_tops_1(X35,X36)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_tops_1])])])).

cnf(c_0_78,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0)) = k2_tops_1(esk1_0,esk2_0)
    | r1_tarski(k2_tops_1(esk1_0,esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_43])).

cnf(c_0_79,negated_conjecture,
    ( k2_xboole_0(esk2_0,k2_tops_1(esk1_0,esk2_0)) = esk2_0
    | k2_pre_topc(esk1_0,esk2_0) = esk2_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_74]),c_0_47])).

cnf(c_0_80,negated_conjecture,
    ( k2_xboole_0(esk2_0,k2_tops_1(esk1_0,esk2_0)) = k2_pre_topc(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_33]),c_0_76])).

cnf(c_0_81,plain,
    ( k1_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_82,negated_conjecture,
    ( ~ v4_pre_topc(esk2_0,esk1_0)
    | k2_tops_1(esk1_0,esk2_0) != k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_83,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0)) = k2_tops_1(esk1_0,esk2_0)
    | k3_xboole_0(esk2_0,k2_tops_1(esk1_0,esk2_0)) = k2_tops_1(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_78]),c_0_57])).

cnf(c_0_84,plain,
    ( v4_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | k2_pre_topc(X1,X2) != X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_85,negated_conjecture,
    ( k2_pre_topc(esk1_0,esk2_0) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_86,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_87,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk2_0,k2_tops_1(esk1_0,esk2_0)) = k1_tops_1(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_33]),c_0_35])])).

cnf(c_0_88,negated_conjecture,
    ( k3_xboole_0(esk2_0,k2_tops_1(esk1_0,esk2_0)) = k2_tops_1(esk1_0,esk2_0)
    | ~ v4_pre_topc(esk2_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_89,negated_conjecture,
    ( v4_pre_topc(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_86]),c_0_35]),c_0_33])])).

cnf(c_0_90,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_87])).

cnf(c_0_91,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_30]),c_0_57])).

cnf(c_0_92,negated_conjecture,
    ( k3_xboole_0(esk2_0,k2_tops_1(esk1_0,esk2_0)) = k2_tops_1(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_88,c_0_89])])).

cnf(c_0_93,negated_conjecture,
    ( k3_xboole_0(esk2_0,k1_tops_1(esk1_0,esk2_0)) = k1_tops_1(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_90]),c_0_57])).

cnf(c_0_94,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_31,c_0_91])).

cnf(c_0_95,negated_conjecture,
    ( k5_xboole_0(esk2_0,k2_tops_1(esk1_0,esk2_0)) = k1_tops_1(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_92]),c_0_87])).

cnf(c_0_96,negated_conjecture,
    ( k5_xboole_0(esk2_0,k1_tops_1(esk1_0,esk2_0)) = k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_93])).

cnf(c_0_97,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0)) != k2_tops_1(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_89])])).

cnf(c_0_98,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_92]),c_0_95]),c_0_96]),c_0_97]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:12:25 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S2mI
% 0.20/0.39  # and selection function SelectCQArNTNpEqFirst.
% 0.20/0.39  #
% 0.20/0.39  # Preprocessing time       : 0.028 s
% 0.20/0.39  # Presaturation interreduction done
% 0.20/0.39  
% 0.20/0.39  # Proof found!
% 0.20/0.39  # SZS status Theorem
% 0.20/0.39  # SZS output start CNFRefutation
% 0.20/0.39  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.20/0.39  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.20/0.39  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.20/0.39  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 0.20/0.39  fof(t77_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)<=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k1_tops_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tops_1)).
% 0.20/0.39  fof(t52_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v4_pre_topc(X2,X1)=>k2_pre_topc(X1,X2)=X2)&((v2_pre_topc(X1)&k2_pre_topc(X1,X2)=X2)=>v4_pre_topc(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 0.20/0.39  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.20/0.39  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.20/0.39  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 0.20/0.39  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.20/0.39  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.20/0.39  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.20/0.39  fof(dt_k2_tops_1, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 0.20/0.39  fof(t69_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)=>r1_tarski(k2_tops_1(X1,X2),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_tops_1)).
% 0.20/0.39  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.20/0.39  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 0.20/0.39  fof(t65_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_pre_topc(X1,X2)=k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 0.20/0.39  fof(t74_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k1_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tops_1)).
% 0.20/0.39  fof(c_0_18, plain, ![X14, X15]:r1_tarski(k4_xboole_0(X14,X15),X14), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.20/0.39  fof(c_0_19, plain, ![X7, X8]:k4_xboole_0(X7,X8)=k5_xboole_0(X7,k3_xboole_0(X7,X8)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.20/0.39  fof(c_0_20, plain, ![X19, X20]:k4_xboole_0(X19,k4_xboole_0(X19,X20))=k3_xboole_0(X19,X20), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.20/0.39  fof(c_0_21, plain, ![X24, X25, X26]:(~m1_subset_1(X25,k1_zfmisc_1(X24))|k7_subset_1(X24,X25,X26)=k4_xboole_0(X25,X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 0.20/0.39  fof(c_0_22, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)<=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k1_tops_1(X1,X2)))))), inference(assume_negation,[status(cth)],[t77_tops_1])).
% 0.20/0.39  cnf(c_0_23, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.39  cnf(c_0_24, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.39  cnf(c_0_25, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.39  cnf(c_0_26, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.39  fof(c_0_27, negated_conjecture, ((v2_pre_topc(esk1_0)&l1_pre_topc(esk1_0))&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&((~v4_pre_topc(esk2_0,esk1_0)|k2_tops_1(esk1_0,esk2_0)!=k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0)))&(v4_pre_topc(esk2_0,esk1_0)|k2_tops_1(esk1_0,esk2_0)=k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])).
% 0.20/0.39  fof(c_0_28, plain, ![X27, X28]:((~v4_pre_topc(X28,X27)|k2_pre_topc(X27,X28)=X28|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))|~l1_pre_topc(X27))&(~v2_pre_topc(X27)|k2_pre_topc(X27,X28)!=X28|v4_pre_topc(X28,X27)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))|~l1_pre_topc(X27))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).
% 0.20/0.39  fof(c_0_29, plain, ![X9, X10]:(~r1_tarski(X9,X10)|k2_xboole_0(X9,X10)=X10), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.20/0.39  cnf(c_0_30, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 0.20/0.39  cnf(c_0_31, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_24]), c_0_24])).
% 0.20/0.39  cnf(c_0_32, plain, (k7_subset_1(X2,X1,X3)=k5_xboole_0(X1,k3_xboole_0(X1,X3))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_26, c_0_24])).
% 0.20/0.39  cnf(c_0_33, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.39  cnf(c_0_34, plain, (k2_pre_topc(X2,X1)=X1|~v4_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.39  cnf(c_0_35, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.39  fof(c_0_36, plain, ![X18]:k4_xboole_0(X18,k1_xboole_0)=X18, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.20/0.39  fof(c_0_37, plain, ![X11]:k2_xboole_0(X11,k1_xboole_0)=X11, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.20/0.39  cnf(c_0_38, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.39  cnf(c_0_39, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.20/0.39  fof(c_0_40, plain, ![X16, X17]:k2_xboole_0(X16,k4_xboole_0(X17,X16))=k2_xboole_0(X16,X17), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.20/0.39  cnf(c_0_41, negated_conjecture, (k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,X1))=k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.20/0.39  cnf(c_0_42, negated_conjecture, (k2_pre_topc(esk1_0,esk2_0)=esk2_0|~v4_pre_topc(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_33]), c_0_35])])).
% 0.20/0.39  cnf(c_0_43, negated_conjecture, (v4_pre_topc(esk2_0,esk1_0)|k2_tops_1(esk1_0,esk2_0)=k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.39  cnf(c_0_44, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.39  fof(c_0_45, plain, ![X6]:k3_xboole_0(X6,X6)=X6, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.20/0.39  fof(c_0_46, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.20/0.39  cnf(c_0_47, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.39  cnf(c_0_48, plain, (k2_xboole_0(k3_xboole_0(X1,X2),X1)=X1), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.20/0.39  fof(c_0_49, plain, ![X29, X30]:(~l1_pre_topc(X29)|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))|m1_subset_1(k2_tops_1(X29,X30),k1_zfmisc_1(u1_struct_0(X29)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_1])])).
% 0.20/0.39  fof(c_0_50, plain, ![X33, X34]:(~l1_pre_topc(X33)|(~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))|(~v4_pre_topc(X34,X33)|r1_tarski(k2_tops_1(X33,X34),X34)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t69_tops_1])])])).
% 0.20/0.39  cnf(c_0_51, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.39  fof(c_0_52, plain, ![X12, X13]:(~r1_tarski(X12,X13)|k3_xboole_0(X12,X13)=X12), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.20/0.39  cnf(c_0_53, negated_conjecture, (r1_tarski(k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1),esk2_0)), inference(spm,[status(thm)],[c_0_30, c_0_41])).
% 0.20/0.39  cnf(c_0_54, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0))=k2_tops_1(esk1_0,esk2_0)|k2_pre_topc(esk1_0,esk2_0)=esk2_0), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.20/0.39  cnf(c_0_55, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[c_0_44, c_0_24])).
% 0.20/0.39  cnf(c_0_56, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.20/0.39  cnf(c_0_57, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.20/0.39  cnf(c_0_58, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.20/0.39  fof(c_0_59, plain, ![X21, X22, X23]:(~m1_subset_1(X22,k1_zfmisc_1(X21))|~m1_subset_1(X23,k1_zfmisc_1(X21))|k4_subset_1(X21,X22,X23)=k2_xboole_0(X22,X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 0.20/0.39  cnf(c_0_60, plain, (m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.39  fof(c_0_61, plain, ![X31, X32]:(~l1_pre_topc(X31)|(~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))|k2_pre_topc(X31,X32)=k4_subset_1(u1_struct_0(X31),X32,k2_tops_1(X31,X32)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_tops_1])])])).
% 0.20/0.39  cnf(c_0_62, plain, (r1_tarski(k2_tops_1(X1,X2),X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v4_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.39  cnf(c_0_63, plain, (k2_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_51, c_0_24])).
% 0.20/0.39  cnf(c_0_64, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.20/0.39  cnf(c_0_65, negated_conjecture, (k2_pre_topc(esk1_0,esk2_0)=esk2_0|r1_tarski(k2_tops_1(esk1_0,esk2_0),esk2_0)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.20/0.39  cnf(c_0_66, plain, (k5_xboole_0(X1,X1)=k3_xboole_0(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_55]), c_0_56])).
% 0.20/0.39  cnf(c_0_67, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.20/0.39  cnf(c_0_68, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.20/0.39  cnf(c_0_69, negated_conjecture, (m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_33]), c_0_35])])).
% 0.20/0.39  cnf(c_0_70, plain, (k2_pre_topc(X1,X2)=k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.20/0.39  cnf(c_0_71, negated_conjecture, (r1_tarski(k2_tops_1(esk1_0,esk2_0),esk2_0)|~v4_pre_topc(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_33]), c_0_35])])).
% 0.20/0.39  cnf(c_0_72, plain, (k2_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2)))=k2_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_63, c_0_57])).
% 0.20/0.39  cnf(c_0_73, negated_conjecture, (k3_xboole_0(esk2_0,k2_tops_1(esk1_0,esk2_0))=k2_tops_1(esk1_0,esk2_0)|k2_pre_topc(esk1_0,esk2_0)=esk2_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_57])).
% 0.20/0.39  cnf(c_0_74, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_66, c_0_67])).
% 0.20/0.39  cnf(c_0_75, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),X1,k2_tops_1(esk1_0,esk2_0))=k2_xboole_0(X1,k2_tops_1(esk1_0,esk2_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.20/0.39  cnf(c_0_76, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),esk2_0,k2_tops_1(esk1_0,esk2_0))=k2_pre_topc(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_33]), c_0_35])])).
% 0.20/0.39  fof(c_0_77, plain, ![X35, X36]:(~l1_pre_topc(X35)|(~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))|k1_tops_1(X35,X36)=k7_subset_1(u1_struct_0(X35),X36,k2_tops_1(X35,X36)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_tops_1])])])).
% 0.20/0.39  cnf(c_0_78, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0))=k2_tops_1(esk1_0,esk2_0)|r1_tarski(k2_tops_1(esk1_0,esk2_0),esk2_0)), inference(spm,[status(thm)],[c_0_71, c_0_43])).
% 0.20/0.39  cnf(c_0_79, negated_conjecture, (k2_xboole_0(esk2_0,k2_tops_1(esk1_0,esk2_0))=esk2_0|k2_pre_topc(esk1_0,esk2_0)=esk2_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_74]), c_0_47])).
% 0.20/0.39  cnf(c_0_80, negated_conjecture, (k2_xboole_0(esk2_0,k2_tops_1(esk1_0,esk2_0))=k2_pre_topc(esk1_0,esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_33]), c_0_76])).
% 0.20/0.39  cnf(c_0_81, plain, (k1_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.20/0.39  cnf(c_0_82, negated_conjecture, (~v4_pre_topc(esk2_0,esk1_0)|k2_tops_1(esk1_0,esk2_0)!=k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.39  cnf(c_0_83, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0))=k2_tops_1(esk1_0,esk2_0)|k3_xboole_0(esk2_0,k2_tops_1(esk1_0,esk2_0))=k2_tops_1(esk1_0,esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_78]), c_0_57])).
% 0.20/0.39  cnf(c_0_84, plain, (v4_pre_topc(X2,X1)|~v2_pre_topc(X1)|k2_pre_topc(X1,X2)!=X2|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.39  cnf(c_0_85, negated_conjecture, (k2_pre_topc(esk1_0,esk2_0)=esk2_0), inference(spm,[status(thm)],[c_0_79, c_0_80])).
% 0.20/0.39  cnf(c_0_86, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.39  cnf(c_0_87, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk2_0,k2_tops_1(esk1_0,esk2_0))=k1_tops_1(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_33]), c_0_35])])).
% 0.20/0.39  cnf(c_0_88, negated_conjecture, (k3_xboole_0(esk2_0,k2_tops_1(esk1_0,esk2_0))=k2_tops_1(esk1_0,esk2_0)|~v4_pre_topc(esk2_0,esk1_0)), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 0.20/0.39  cnf(c_0_89, negated_conjecture, (v4_pre_topc(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_86]), c_0_35]), c_0_33])])).
% 0.20/0.39  cnf(c_0_90, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,esk2_0),esk2_0)), inference(spm,[status(thm)],[c_0_53, c_0_87])).
% 0.20/0.39  cnf(c_0_91, plain, (k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_30]), c_0_57])).
% 0.20/0.39  cnf(c_0_92, negated_conjecture, (k3_xboole_0(esk2_0,k2_tops_1(esk1_0,esk2_0))=k2_tops_1(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_88, c_0_89])])).
% 0.20/0.39  cnf(c_0_93, negated_conjecture, (k3_xboole_0(esk2_0,k1_tops_1(esk1_0,esk2_0))=k1_tops_1(esk1_0,esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_90]), c_0_57])).
% 0.20/0.39  cnf(c_0_94, plain, (k5_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_31, c_0_91])).
% 0.20/0.39  cnf(c_0_95, negated_conjecture, (k5_xboole_0(esk2_0,k2_tops_1(esk1_0,esk2_0))=k1_tops_1(esk1_0,esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_92]), c_0_87])).
% 0.20/0.39  cnf(c_0_96, negated_conjecture, (k5_xboole_0(esk2_0,k1_tops_1(esk1_0,esk2_0))=k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_41, c_0_93])).
% 0.20/0.39  cnf(c_0_97, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0))!=k2_tops_1(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_82, c_0_89])])).
% 0.20/0.39  cnf(c_0_98, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_92]), c_0_95]), c_0_96]), c_0_97]), ['proof']).
% 0.20/0.39  # SZS output end CNFRefutation
% 0.20/0.39  # Proof object total steps             : 99
% 0.20/0.39  # Proof object clause steps            : 62
% 0.20/0.39  # Proof object formula steps           : 37
% 0.20/0.39  # Proof object conjectures             : 33
% 0.20/0.39  # Proof object clause conjectures      : 30
% 0.20/0.39  # Proof object formula conjectures     : 3
% 0.20/0.39  # Proof object initial clauses used    : 23
% 0.20/0.39  # Proof object initial formulas used   : 18
% 0.20/0.39  # Proof object generating inferences   : 30
% 0.20/0.39  # Proof object simplifying inferences  : 38
% 0.20/0.39  # Training examples: 0 positive, 0 negative
% 0.20/0.39  # Parsed axioms                        : 18
% 0.20/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.39  # Initial clauses                      : 23
% 0.20/0.39  # Removed in clause preprocessing      : 1
% 0.20/0.39  # Initial clauses in saturation        : 22
% 0.20/0.39  # Processed clauses                    : 165
% 0.20/0.39  # ...of these trivial                  : 28
% 0.20/0.39  # ...subsumed                          : 6
% 0.20/0.39  # ...remaining for further processing  : 130
% 0.20/0.39  # Other redundant clauses eliminated   : 0
% 0.20/0.39  # Clauses deleted for lack of memory   : 0
% 0.20/0.39  # Backward-subsumed                    : 1
% 0.20/0.39  # Backward-rewritten                   : 20
% 0.20/0.39  # Generated clauses                    : 411
% 0.20/0.39  # ...of the previous two non-trivial   : 235
% 0.20/0.39  # Contextual simplify-reflections      : 0
% 0.20/0.39  # Paramodulations                      : 409
% 0.20/0.39  # Factorizations                       : 0
% 0.20/0.39  # Equation resolutions                 : 0
% 0.20/0.39  # Propositional unsat checks           : 0
% 0.20/0.39  #    Propositional check models        : 0
% 0.20/0.39  #    Propositional check unsatisfiable : 0
% 0.20/0.39  #    Propositional clauses             : 0
% 0.20/0.39  #    Propositional clauses after purity: 0
% 0.20/0.39  #    Propositional unsat core size     : 0
% 0.20/0.39  #    Propositional preprocessing time  : 0.000
% 0.20/0.39  #    Propositional encoding time       : 0.000
% 0.20/0.39  #    Propositional solver time         : 0.000
% 0.20/0.39  #    Success case prop preproc time    : 0.000
% 0.20/0.39  #    Success case prop encoding time   : 0.000
% 0.20/0.39  #    Success case prop solver time     : 0.000
% 0.20/0.39  # Current number of processed clauses  : 85
% 0.20/0.39  #    Positive orientable unit clauses  : 65
% 0.20/0.39  #    Positive unorientable unit clauses: 1
% 0.20/0.39  #    Negative unit clauses             : 1
% 0.20/0.39  #    Non-unit-clauses                  : 18
% 0.20/0.39  # Current number of unprocessed clauses: 105
% 0.20/0.39  # ...number of literals in the above   : 136
% 0.20/0.39  # Current number of archived formulas  : 0
% 0.20/0.39  # Current number of archived clauses   : 46
% 0.20/0.39  # Clause-clause subsumption calls (NU) : 99
% 0.20/0.39  # Rec. Clause-clause subsumption calls : 95
% 0.20/0.39  # Non-unit clause-clause subsumptions  : 6
% 0.20/0.39  # Unit Clause-clause subsumption calls : 99
% 0.20/0.39  # Rewrite failures with RHS unbound    : 0
% 0.20/0.39  # BW rewrite match attempts            : 83
% 0.20/0.39  # BW rewrite match successes           : 19
% 0.20/0.39  # Condensation attempts                : 0
% 0.20/0.39  # Condensation successes               : 0
% 0.20/0.39  # Termbank termtop insertions          : 7233
% 0.20/0.39  
% 0.20/0.39  # -------------------------------------------------
% 0.20/0.39  # User time                : 0.035 s
% 0.20/0.39  # System time              : 0.006 s
% 0.20/0.39  # Total time               : 0.040 s
% 0.20/0.39  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------

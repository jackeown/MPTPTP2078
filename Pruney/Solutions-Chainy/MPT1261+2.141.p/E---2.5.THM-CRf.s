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
% DateTime   : Thu Dec  3 11:11:47 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  122 (4162 expanded)
%              Number of clauses        :   83 (1988 expanded)
%              Number of leaves         :   19 (1074 expanded)
%              Depth                    :   21
%              Number of atoms          :  216 (5693 expanded)
%              Number of equality atoms :   98 (3053 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    9 (   1 average)
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

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

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

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

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

fof(dt_k2_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

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

fof(c_0_19,plain,(
    ! [X11,X12] : r1_tarski(k4_xboole_0(X11,X12),X11) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_20,plain,(
    ! [X6,X7] : k4_xboole_0(X6,X7) = k5_xboole_0(X6,k3_xboole_0(X6,X7)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_21,plain,(
    ! [X16,X17] : k4_xboole_0(X16,k4_xboole_0(X16,X17)) = k3_xboole_0(X16,X17) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_22,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_25,plain,(
    ! [X8,X9] :
      ( ~ r1_tarski(X8,X9)
      | k2_xboole_0(X8,X9) = X9 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_26,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_27,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_23]),c_0_23])).

fof(c_0_28,plain,(
    ! [X15] : k4_xboole_0(X15,k1_xboole_0) = X15 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_29,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_30,plain,(
    ! [X10] : k2_xboole_0(X10,k1_xboole_0) = X10 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_31,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_33,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),X1) = X1 ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

fof(c_0_37,plain,(
    ! [X25,X26,X27] :
      ( ~ m1_subset_1(X26,k1_zfmisc_1(X25))
      | k7_subset_1(X25,X26,X27) = k4_xboole_0(X26,X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

fof(c_0_38,plain,(
    ! [X28,X29] :
      ( ( ~ m1_subset_1(X28,k1_zfmisc_1(X29))
        | r1_tarski(X28,X29) )
      & ( ~ r1_tarski(X28,X29)
        | m1_subset_1(X28,k1_zfmisc_1(X29)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_39,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[c_0_33,c_0_23])).

fof(c_0_40,plain,(
    ! [X18,X19] :
      ( ~ m1_subset_1(X19,k1_zfmisc_1(X18))
      | k3_subset_1(X18,X19) = k4_xboole_0(X18,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_41,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_34])).

cnf(c_0_42,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_43,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_39])).

cnf(c_0_46,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_47,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_48,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_34,c_0_42])).

cnf(c_0_49,plain,
    ( k7_subset_1(X2,X1,X3) = k5_xboole_0(X1,k3_xboole_0(X1,X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_43,c_0_23])).

cnf(c_0_50,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

fof(c_0_51,plain,(
    ! [X20,X21] :
      ( ~ m1_subset_1(X21,k1_zfmisc_1(X20))
      | k3_subset_1(X20,k3_subset_1(X20,X21)) = X21 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

cnf(c_0_52,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k3_xboole_0(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_46,c_0_23])).

cnf(c_0_53,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_47])).

cnf(c_0_54,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_39,c_0_48])).

cnf(c_0_55,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X1,X1,X2) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_56,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_57,plain,
    ( k3_subset_1(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_48]),c_0_54])).

fof(c_0_58,plain,(
    ! [X13,X14] : k2_xboole_0(X13,k4_xboole_0(X14,X13)) = k2_xboole_0(X13,X14) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_59,plain,
    ( k7_subset_1(X1,X1,k7_subset_1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_55]),c_0_55])).

cnf(c_0_60,plain,
    ( k3_subset_1(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_53]),c_0_57])).

cnf(c_0_61,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_62,plain,
    ( k7_subset_1(X1,X1,X2) = k3_subset_1(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_52,c_0_55])).

cnf(c_0_63,plain,
    ( m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_32])).

cnf(c_0_64,plain,
    ( k7_subset_1(X1,X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k7_subset_1(X1,X1,X2)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_59])).

cnf(c_0_65,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_50]),c_0_60])).

fof(c_0_66,plain,(
    ! [X22,X23,X24] :
      ( ~ m1_subset_1(X23,k1_zfmisc_1(X22))
      | ~ m1_subset_1(X24,k1_zfmisc_1(X22))
      | k4_subset_1(X22,X23,X24) = k2_xboole_0(X23,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_67,plain,
    ( k2_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_61,c_0_23])).

cnf(c_0_68,plain,
    ( k7_subset_1(X1,X2,X3) = k7_subset_1(X2,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_49,c_0_55])).

cnf(c_0_69,plain,
    ( k3_xboole_0(X1,k7_subset_1(X1,X1,X2)) = k3_subset_1(X1,k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64])).

cnf(c_0_70,plain,
    ( k3_subset_1(X1,k3_subset_1(X1,k3_xboole_0(X1,X2))) = k3_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_56,c_0_63])).

cnf(c_0_71,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_65]),c_0_48]),c_0_54])).

fof(c_0_72,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v4_pre_topc(X2,X1)
            <=> k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k1_tops_1(X1,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t77_tops_1])).

cnf(c_0_73,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_74,plain,
    ( k2_xboole_0(X1,k7_subset_1(X2,X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_67,c_0_55])).

cnf(c_0_75,plain,
    ( k7_subset_1(k3_xboole_0(X1,X2),k3_xboole_0(X1,X2),X3) = k7_subset_1(X1,k3_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_68,c_0_63])).

cnf(c_0_76,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X2,X1)) = k7_subset_1(X1,X1,X2) ),
    inference(spm,[status(thm)],[c_0_55,c_0_34])).

cnf(c_0_77,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_69]),c_0_59]),c_0_70])).

cnf(c_0_78,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_65,c_0_71])).

cnf(c_0_79,plain,
    ( m1_subset_1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_26])).

fof(c_0_80,plain,(
    ! [X30,X31] :
      ( ( ~ v4_pre_topc(X31,X30)
        | k2_pre_topc(X30,X31) = X31
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ l1_pre_topc(X30) )
      & ( ~ v2_pre_topc(X30)
        | k2_pre_topc(X30,X31) != X31
        | v4_pre_topc(X31,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ l1_pre_topc(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).

fof(c_0_81,negated_conjecture,
    ( v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & ( ~ v4_pre_topc(esk2_0,esk1_0)
      | k2_tops_1(esk1_0,esk2_0) != k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0)) )
    & ( v4_pre_topc(esk2_0,esk1_0)
      | k2_tops_1(esk1_0,esk2_0) = k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_72])])])).

fof(c_0_82,plain,(
    ! [X32,X33] :
      ( ~ l1_pre_topc(X32)
      | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))
      | m1_subset_1(k2_tops_1(X32,X33),k1_zfmisc_1(u1_struct_0(X32))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_1])])).

cnf(c_0_83,plain,
    ( k4_subset_1(X1,X2,k3_xboole_0(X1,X3)) = k2_xboole_0(X2,k3_xboole_0(X1,X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_63])).

cnf(c_0_84,plain,
    ( k2_xboole_0(X1,k7_subset_1(X2,k3_xboole_0(X2,X3),X1)) = k2_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_85,plain,
    ( k7_subset_1(X1,k3_xboole_0(X1,X2),X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_78]),c_0_75])).

cnf(c_0_86,plain,
    ( m1_subset_1(k7_subset_1(X1,X1,X2),k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_79,c_0_55])).

cnf(c_0_87,plain,
    ( k2_pre_topc(X2,X1) = X1
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_88,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_89,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_90,plain,
    ( m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

fof(c_0_91,plain,(
    ! [X38,X39] :
      ( ~ l1_pre_topc(X38)
      | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))
      | k2_pre_topc(X38,X39) = k4_subset_1(u1_struct_0(X38),X39,k2_tops_1(X38,X39)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_tops_1])])])).

cnf(c_0_92,plain,
    ( k4_subset_1(X1,X1,k3_xboole_0(X1,X2)) = k2_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_83,c_0_50])).

cnf(c_0_93,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_35])).

cnf(c_0_94,plain,
    ( k4_subset_1(X1,X2,k7_subset_1(X1,X1,X3)) = k2_xboole_0(X2,k7_subset_1(X1,X1,X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_86])).

cnf(c_0_95,negated_conjecture,
    ( k2_pre_topc(esk1_0,esk2_0) = esk2_0
    | ~ v4_pre_topc(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_89])])).

cnf(c_0_96,negated_conjecture,
    ( v4_pre_topc(esk2_0,esk1_0)
    | k2_tops_1(esk1_0,esk2_0) = k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_97,negated_conjecture,
    ( m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_88]),c_0_89])])).

cnf(c_0_98,plain,
    ( k2_pre_topc(X1,X2) = k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_91])).

fof(c_0_99,plain,(
    ! [X34,X35] :
      ( ~ v2_pre_topc(X34)
      | ~ l1_pre_topc(X34)
      | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))
      | v4_pre_topc(k2_pre_topc(X34,X35),X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_tops_1])])).

cnf(c_0_100,plain,
    ( k4_subset_1(X1,X1,k3_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_101,plain,
    ( k3_xboole_0(X1,k7_subset_1(X1,X1,X2)) = k7_subset_1(X1,X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_77]),c_0_55]),c_0_64])).

cnf(c_0_102,plain,
    ( k4_subset_1(X1,X1,k7_subset_1(X1,X1,X2)) = k2_xboole_0(X1,k7_subset_1(X1,X1,X2)) ),
    inference(spm,[status(thm)],[c_0_94,c_0_50])).

cnf(c_0_103,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0)) = k2_tops_1(esk1_0,esk2_0)
    | k2_pre_topc(esk1_0,esk2_0) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_95,c_0_96])).

cnf(c_0_104,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1) = k7_subset_1(esk2_0,esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_68,c_0_88])).

cnf(c_0_105,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),X1,k2_tops_1(esk1_0,esk2_0)) = k2_xboole_0(X1,k2_tops_1(esk1_0,esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_73,c_0_97])).

cnf(c_0_106,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),esk2_0,k2_tops_1(esk1_0,esk2_0)) = k2_pre_topc(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_88]),c_0_89])])).

cnf(c_0_107,plain,
    ( v4_pre_topc(k2_pre_topc(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_99])).

cnf(c_0_108,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_109,plain,
    ( k2_xboole_0(X1,k7_subset_1(X1,X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_102])).

cnf(c_0_110,negated_conjecture,
    ( k7_subset_1(esk2_0,esk2_0,k1_tops_1(esk1_0,esk2_0)) = k2_tops_1(esk1_0,esk2_0)
    | k2_pre_topc(esk1_0,esk2_0) = esk2_0 ),
    inference(rw,[status(thm)],[c_0_103,c_0_104])).

cnf(c_0_111,negated_conjecture,
    ( k2_xboole_0(esk2_0,k2_tops_1(esk1_0,esk2_0)) = k2_pre_topc(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_88]),c_0_106])).

fof(c_0_112,plain,(
    ! [X36,X37] :
      ( ~ l1_pre_topc(X36)
      | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))
      | k2_tops_1(X36,X37) = k7_subset_1(u1_struct_0(X36),k2_pre_topc(X36,X37),k1_tops_1(X36,X37)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l78_tops_1])])])).

cnf(c_0_113,negated_conjecture,
    ( ~ v4_pre_topc(esk2_0,esk1_0)
    | k2_tops_1(esk1_0,esk2_0) != k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_114,negated_conjecture,
    ( v4_pre_topc(k2_pre_topc(esk1_0,esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_88]),c_0_108]),c_0_89])])).

cnf(c_0_115,negated_conjecture,
    ( k2_pre_topc(esk1_0,esk2_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_110]),c_0_111])])).

cnf(c_0_116,plain,
    ( k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_112])).

cnf(c_0_117,negated_conjecture,
    ( k7_subset_1(esk2_0,esk2_0,k1_tops_1(esk1_0,esk2_0)) != k2_tops_1(esk1_0,esk2_0)
    | ~ v4_pre_topc(esk2_0,esk1_0) ),
    inference(rw,[status(thm)],[c_0_113,c_0_104])).

cnf(c_0_118,negated_conjecture,
    ( v4_pre_topc(esk2_0,esk1_0) ),
    inference(rw,[status(thm)],[c_0_114,c_0_115])).

cnf(c_0_119,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),k1_tops_1(esk1_0,esk2_0)) = k2_tops_1(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_88]),c_0_89])])).

cnf(c_0_120,negated_conjecture,
    ( k7_subset_1(esk2_0,esk2_0,k1_tops_1(esk1_0,esk2_0)) != k2_tops_1(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_117,c_0_118])])).

cnf(c_0_121,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_119,c_0_115]),c_0_104]),c_0_120]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:06:10 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.43  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S2mI
% 0.20/0.43  # and selection function SelectCQArNTNpEqFirst.
% 0.20/0.43  #
% 0.20/0.43  # Preprocessing time       : 0.027 s
% 0.20/0.43  # Presaturation interreduction done
% 0.20/0.43  
% 0.20/0.43  # Proof found!
% 0.20/0.43  # SZS status Theorem
% 0.20/0.43  # SZS output start CNFRefutation
% 0.20/0.43  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.20/0.43  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.20/0.43  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.20/0.43  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.20/0.43  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.20/0.43  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.20/0.43  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 0.20/0.43  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 0.20/0.43  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.43  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 0.20/0.43  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 0.20/0.43  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.20/0.43  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 0.20/0.43  fof(t77_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)<=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k1_tops_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tops_1)).
% 0.20/0.43  fof(t52_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v4_pre_topc(X2,X1)=>k2_pre_topc(X1,X2)=X2)&((v2_pre_topc(X1)&k2_pre_topc(X1,X2)=X2)=>v4_pre_topc(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 0.20/0.43  fof(dt_k2_tops_1, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 0.20/0.43  fof(t65_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_pre_topc(X1,X2)=k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 0.20/0.43  fof(fc1_tops_1, axiom, ![X1, X2]:(((v2_pre_topc(X1)&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v4_pre_topc(k2_pre_topc(X1,X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_tops_1)).
% 0.20/0.43  fof(l78_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 0.20/0.43  fof(c_0_19, plain, ![X11, X12]:r1_tarski(k4_xboole_0(X11,X12),X11), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.20/0.43  fof(c_0_20, plain, ![X6, X7]:k4_xboole_0(X6,X7)=k5_xboole_0(X6,k3_xboole_0(X6,X7)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.20/0.43  fof(c_0_21, plain, ![X16, X17]:k4_xboole_0(X16,k4_xboole_0(X16,X17))=k3_xboole_0(X16,X17), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.20/0.43  cnf(c_0_22, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.43  cnf(c_0_23, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.43  cnf(c_0_24, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.43  fof(c_0_25, plain, ![X8, X9]:(~r1_tarski(X8,X9)|k2_xboole_0(X8,X9)=X9), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.20/0.43  cnf(c_0_26, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 0.20/0.43  cnf(c_0_27, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_23]), c_0_23])).
% 0.20/0.43  fof(c_0_28, plain, ![X15]:k4_xboole_0(X15,k1_xboole_0)=X15, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.20/0.43  fof(c_0_29, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.20/0.43  fof(c_0_30, plain, ![X10]:k2_xboole_0(X10,k1_xboole_0)=X10, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.20/0.43  cnf(c_0_31, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.43  cnf(c_0_32, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.20/0.43  cnf(c_0_33, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.43  cnf(c_0_34, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.43  cnf(c_0_35, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.43  cnf(c_0_36, plain, (k2_xboole_0(k3_xboole_0(X1,X2),X1)=X1), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.20/0.43  fof(c_0_37, plain, ![X25, X26, X27]:(~m1_subset_1(X26,k1_zfmisc_1(X25))|k7_subset_1(X25,X26,X27)=k4_xboole_0(X26,X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 0.20/0.43  fof(c_0_38, plain, ![X28, X29]:((~m1_subset_1(X28,k1_zfmisc_1(X29))|r1_tarski(X28,X29))&(~r1_tarski(X28,X29)|m1_subset_1(X28,k1_zfmisc_1(X29)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.43  cnf(c_0_39, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[c_0_33, c_0_23])).
% 0.20/0.43  fof(c_0_40, plain, ![X18, X19]:(~m1_subset_1(X19,k1_zfmisc_1(X18))|k3_subset_1(X18,X19)=k4_xboole_0(X18,X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.20/0.43  cnf(c_0_41, plain, (r1_tarski(k3_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_32, c_0_34])).
% 0.20/0.43  cnf(c_0_42, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.20/0.43  cnf(c_0_43, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.43  cnf(c_0_44, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.43  cnf(c_0_45, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_26, c_0_39])).
% 0.20/0.43  cnf(c_0_46, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.43  cnf(c_0_47, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.20/0.43  cnf(c_0_48, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_34, c_0_42])).
% 0.20/0.43  cnf(c_0_49, plain, (k7_subset_1(X2,X1,X3)=k5_xboole_0(X1,k3_xboole_0(X1,X3))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_43, c_0_23])).
% 0.20/0.43  cnf(c_0_50, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.20/0.43  fof(c_0_51, plain, ![X20, X21]:(~m1_subset_1(X21,k1_zfmisc_1(X20))|k3_subset_1(X20,k3_subset_1(X20,X21))=X21), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 0.20/0.43  cnf(c_0_52, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k3_xboole_0(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_46, c_0_23])).
% 0.20/0.43  cnf(c_0_53, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_44, c_0_47])).
% 0.20/0.43  cnf(c_0_54, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_39, c_0_48])).
% 0.20/0.43  cnf(c_0_55, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=k7_subset_1(X1,X1,X2)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.20/0.43  cnf(c_0_56, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.20/0.43  cnf(c_0_57, plain, (k3_subset_1(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_48]), c_0_54])).
% 0.20/0.43  fof(c_0_58, plain, ![X13, X14]:k2_xboole_0(X13,k4_xboole_0(X14,X13))=k2_xboole_0(X13,X14), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.20/0.43  cnf(c_0_59, plain, (k7_subset_1(X1,X1,k7_subset_1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_55]), c_0_55])).
% 0.20/0.43  cnf(c_0_60, plain, (k3_subset_1(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_53]), c_0_57])).
% 0.20/0.43  cnf(c_0_61, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.20/0.43  cnf(c_0_62, plain, (k7_subset_1(X1,X1,X2)=k3_subset_1(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_52, c_0_55])).
% 0.20/0.43  cnf(c_0_63, plain, (m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_44, c_0_32])).
% 0.20/0.43  cnf(c_0_64, plain, (k7_subset_1(X1,X1,k3_xboole_0(X1,X2))=k3_xboole_0(X1,k7_subset_1(X1,X1,X2))), inference(spm,[status(thm)],[c_0_59, c_0_59])).
% 0.20/0.43  cnf(c_0_65, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X1))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_50]), c_0_60])).
% 0.20/0.43  fof(c_0_66, plain, ![X22, X23, X24]:(~m1_subset_1(X23,k1_zfmisc_1(X22))|~m1_subset_1(X24,k1_zfmisc_1(X22))|k4_subset_1(X22,X23,X24)=k2_xboole_0(X23,X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 0.20/0.43  cnf(c_0_67, plain, (k2_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_61, c_0_23])).
% 0.20/0.43  cnf(c_0_68, plain, (k7_subset_1(X1,X2,X3)=k7_subset_1(X2,X2,X3)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_49, c_0_55])).
% 0.20/0.43  cnf(c_0_69, plain, (k3_xboole_0(X1,k7_subset_1(X1,X1,X2))=k3_subset_1(X1,k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_64])).
% 0.20/0.43  cnf(c_0_70, plain, (k3_subset_1(X1,k3_subset_1(X1,k3_xboole_0(X1,X2)))=k3_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_56, c_0_63])).
% 0.20/0.43  cnf(c_0_71, plain, (k3_xboole_0(X1,X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_65]), c_0_48]), c_0_54])).
% 0.20/0.43  fof(c_0_72, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)<=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k1_tops_1(X1,X2)))))), inference(assume_negation,[status(cth)],[t77_tops_1])).
% 0.20/0.43  cnf(c_0_73, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.20/0.43  cnf(c_0_74, plain, (k2_xboole_0(X1,k7_subset_1(X2,X2,X1))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_67, c_0_55])).
% 0.20/0.43  cnf(c_0_75, plain, (k7_subset_1(k3_xboole_0(X1,X2),k3_xboole_0(X1,X2),X3)=k7_subset_1(X1,k3_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_68, c_0_63])).
% 0.20/0.43  cnf(c_0_76, plain, (k5_xboole_0(X1,k3_xboole_0(X2,X1))=k7_subset_1(X1,X1,X2)), inference(spm,[status(thm)],[c_0_55, c_0_34])).
% 0.20/0.43  cnf(c_0_77, plain, (k3_xboole_0(X1,k3_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_69]), c_0_59]), c_0_70])).
% 0.20/0.43  cnf(c_0_78, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_65, c_0_71])).
% 0.20/0.43  cnf(c_0_79, plain, (m1_subset_1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_44, c_0_26])).
% 0.20/0.43  fof(c_0_80, plain, ![X30, X31]:((~v4_pre_topc(X31,X30)|k2_pre_topc(X30,X31)=X31|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))|~l1_pre_topc(X30))&(~v2_pre_topc(X30)|k2_pre_topc(X30,X31)!=X31|v4_pre_topc(X31,X30)|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))|~l1_pre_topc(X30))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).
% 0.20/0.43  fof(c_0_81, negated_conjecture, ((v2_pre_topc(esk1_0)&l1_pre_topc(esk1_0))&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&((~v4_pre_topc(esk2_0,esk1_0)|k2_tops_1(esk1_0,esk2_0)!=k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0)))&(v4_pre_topc(esk2_0,esk1_0)|k2_tops_1(esk1_0,esk2_0)=k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_72])])])).
% 0.20/0.43  fof(c_0_82, plain, ![X32, X33]:(~l1_pre_topc(X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))|m1_subset_1(k2_tops_1(X32,X33),k1_zfmisc_1(u1_struct_0(X32)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_1])])).
% 0.20/0.43  cnf(c_0_83, plain, (k4_subset_1(X1,X2,k3_xboole_0(X1,X3))=k2_xboole_0(X2,k3_xboole_0(X1,X3))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_73, c_0_63])).
% 0.20/0.43  cnf(c_0_84, plain, (k2_xboole_0(X1,k7_subset_1(X2,k3_xboole_0(X2,X3),X1))=k2_xboole_0(X1,k3_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.20/0.43  cnf(c_0_85, plain, (k7_subset_1(X1,k3_xboole_0(X1,X2),X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_78]), c_0_75])).
% 0.20/0.43  cnf(c_0_86, plain, (m1_subset_1(k7_subset_1(X1,X1,X2),k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_79, c_0_55])).
% 0.20/0.43  cnf(c_0_87, plain, (k2_pre_topc(X2,X1)=X1|~v4_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.20/0.43  cnf(c_0_88, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.20/0.43  cnf(c_0_89, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.20/0.43  cnf(c_0_90, plain, (m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_82])).
% 0.20/0.43  fof(c_0_91, plain, ![X38, X39]:(~l1_pre_topc(X38)|(~m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))|k2_pre_topc(X38,X39)=k4_subset_1(u1_struct_0(X38),X39,k2_tops_1(X38,X39)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_tops_1])])])).
% 0.20/0.43  cnf(c_0_92, plain, (k4_subset_1(X1,X1,k3_xboole_0(X1,X2))=k2_xboole_0(X1,k3_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_83, c_0_50])).
% 0.20/0.43  cnf(c_0_93, plain, (k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_35])).
% 0.20/0.43  cnf(c_0_94, plain, (k4_subset_1(X1,X2,k7_subset_1(X1,X1,X3))=k2_xboole_0(X2,k7_subset_1(X1,X1,X3))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_73, c_0_86])).
% 0.20/0.43  cnf(c_0_95, negated_conjecture, (k2_pre_topc(esk1_0,esk2_0)=esk2_0|~v4_pre_topc(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_89])])).
% 0.20/0.43  cnf(c_0_96, negated_conjecture, (v4_pre_topc(esk2_0,esk1_0)|k2_tops_1(esk1_0,esk2_0)=k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.20/0.43  cnf(c_0_97, negated_conjecture, (m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_88]), c_0_89])])).
% 0.20/0.43  cnf(c_0_98, plain, (k2_pre_topc(X1,X2)=k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_91])).
% 0.20/0.43  fof(c_0_99, plain, ![X34, X35]:(~v2_pre_topc(X34)|~l1_pre_topc(X34)|~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))|v4_pre_topc(k2_pre_topc(X34,X35),X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_tops_1])])).
% 0.20/0.43  cnf(c_0_100, plain, (k4_subset_1(X1,X1,k3_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[c_0_92, c_0_93])).
% 0.20/0.43  cnf(c_0_101, plain, (k3_xboole_0(X1,k7_subset_1(X1,X1,X2))=k7_subset_1(X1,X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_77]), c_0_55]), c_0_64])).
% 0.20/0.43  cnf(c_0_102, plain, (k4_subset_1(X1,X1,k7_subset_1(X1,X1,X2))=k2_xboole_0(X1,k7_subset_1(X1,X1,X2))), inference(spm,[status(thm)],[c_0_94, c_0_50])).
% 0.20/0.43  cnf(c_0_103, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0))=k2_tops_1(esk1_0,esk2_0)|k2_pre_topc(esk1_0,esk2_0)=esk2_0), inference(spm,[status(thm)],[c_0_95, c_0_96])).
% 0.20/0.43  cnf(c_0_104, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)=k7_subset_1(esk2_0,esk2_0,X1)), inference(spm,[status(thm)],[c_0_68, c_0_88])).
% 0.20/0.43  cnf(c_0_105, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),X1,k2_tops_1(esk1_0,esk2_0))=k2_xboole_0(X1,k2_tops_1(esk1_0,esk2_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_73, c_0_97])).
% 0.20/0.43  cnf(c_0_106, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),esk2_0,k2_tops_1(esk1_0,esk2_0))=k2_pre_topc(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_88]), c_0_89])])).
% 0.20/0.43  cnf(c_0_107, plain, (v4_pre_topc(k2_pre_topc(X1,X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_99])).
% 0.20/0.43  cnf(c_0_108, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.20/0.43  cnf(c_0_109, plain, (k2_xboole_0(X1,k7_subset_1(X1,X1,X2))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_101]), c_0_102])).
% 0.20/0.43  cnf(c_0_110, negated_conjecture, (k7_subset_1(esk2_0,esk2_0,k1_tops_1(esk1_0,esk2_0))=k2_tops_1(esk1_0,esk2_0)|k2_pre_topc(esk1_0,esk2_0)=esk2_0), inference(rw,[status(thm)],[c_0_103, c_0_104])).
% 0.20/0.43  cnf(c_0_111, negated_conjecture, (k2_xboole_0(esk2_0,k2_tops_1(esk1_0,esk2_0))=k2_pre_topc(esk1_0,esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_88]), c_0_106])).
% 0.20/0.43  fof(c_0_112, plain, ![X36, X37]:(~l1_pre_topc(X36)|(~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))|k2_tops_1(X36,X37)=k7_subset_1(u1_struct_0(X36),k2_pre_topc(X36,X37),k1_tops_1(X36,X37)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l78_tops_1])])])).
% 0.20/0.43  cnf(c_0_113, negated_conjecture, (~v4_pre_topc(esk2_0,esk1_0)|k2_tops_1(esk1_0,esk2_0)!=k7_subset_1(u1_struct_0(esk1_0),esk2_0,k1_tops_1(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.20/0.43  cnf(c_0_114, negated_conjecture, (v4_pre_topc(k2_pre_topc(esk1_0,esk2_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_88]), c_0_108]), c_0_89])])).
% 0.20/0.43  cnf(c_0_115, negated_conjecture, (k2_pre_topc(esk1_0,esk2_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_110]), c_0_111])])).
% 0.20/0.43  cnf(c_0_116, plain, (k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_112])).
% 0.20/0.43  cnf(c_0_117, negated_conjecture, (k7_subset_1(esk2_0,esk2_0,k1_tops_1(esk1_0,esk2_0))!=k2_tops_1(esk1_0,esk2_0)|~v4_pre_topc(esk2_0,esk1_0)), inference(rw,[status(thm)],[c_0_113, c_0_104])).
% 0.20/0.43  cnf(c_0_118, negated_conjecture, (v4_pre_topc(esk2_0,esk1_0)), inference(rw,[status(thm)],[c_0_114, c_0_115])).
% 0.20/0.43  cnf(c_0_119, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),k1_tops_1(esk1_0,esk2_0))=k2_tops_1(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_88]), c_0_89])])).
% 0.20/0.43  cnf(c_0_120, negated_conjecture, (k7_subset_1(esk2_0,esk2_0,k1_tops_1(esk1_0,esk2_0))!=k2_tops_1(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_117, c_0_118])])).
% 0.20/0.43  cnf(c_0_121, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_119, c_0_115]), c_0_104]), c_0_120]), ['proof']).
% 0.20/0.43  # SZS output end CNFRefutation
% 0.20/0.43  # Proof object total steps             : 122
% 0.20/0.43  # Proof object clause steps            : 83
% 0.20/0.43  # Proof object formula steps           : 39
% 0.20/0.43  # Proof object conjectures             : 23
% 0.20/0.43  # Proof object clause conjectures      : 20
% 0.20/0.43  # Proof object formula conjectures     : 3
% 0.20/0.43  # Proof object initial clauses used    : 23
% 0.20/0.43  # Proof object initial formulas used   : 19
% 0.20/0.43  # Proof object generating inferences   : 41
% 0.20/0.43  # Proof object simplifying inferences  : 53
% 0.20/0.43  # Training examples: 0 positive, 0 negative
% 0.20/0.43  # Parsed axioms                        : 19
% 0.20/0.43  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.43  # Initial clauses                      : 25
% 0.20/0.43  # Removed in clause preprocessing      : 1
% 0.20/0.43  # Initial clauses in saturation        : 24
% 0.20/0.43  # Processed clauses                    : 575
% 0.20/0.43  # ...of these trivial                  : 103
% 0.20/0.43  # ...subsumed                          : 29
% 0.20/0.43  # ...remaining for further processing  : 442
% 0.20/0.43  # Other redundant clauses eliminated   : 0
% 0.20/0.43  # Clauses deleted for lack of memory   : 0
% 0.20/0.43  # Backward-subsumed                    : 1
% 0.20/0.43  # Backward-rewritten                   : 58
% 0.20/0.43  # Generated clauses                    : 3406
% 0.20/0.43  # ...of the previous two non-trivial   : 2542
% 0.20/0.43  # Contextual simplify-reflections      : 0
% 0.20/0.43  # Paramodulations                      : 3406
% 0.20/0.43  # Factorizations                       : 0
% 0.20/0.43  # Equation resolutions                 : 0
% 0.20/0.43  # Propositional unsat checks           : 0
% 0.20/0.43  #    Propositional check models        : 0
% 0.20/0.43  #    Propositional check unsatisfiable : 0
% 0.20/0.43  #    Propositional clauses             : 0
% 0.20/0.43  #    Propositional clauses after purity: 0
% 0.20/0.43  #    Propositional unsat core size     : 0
% 0.20/0.43  #    Propositional preprocessing time  : 0.000
% 0.20/0.43  #    Propositional encoding time       : 0.000
% 0.20/0.43  #    Propositional solver time         : 0.000
% 0.20/0.43  #    Success case prop preproc time    : 0.000
% 0.20/0.43  #    Success case prop encoding time   : 0.000
% 0.20/0.43  #    Success case prop solver time     : 0.000
% 0.20/0.43  # Current number of processed clauses  : 359
% 0.20/0.43  #    Positive orientable unit clauses  : 300
% 0.20/0.43  #    Positive unorientable unit clauses: 2
% 0.20/0.43  #    Negative unit clauses             : 1
% 0.20/0.43  #    Non-unit-clauses                  : 56
% 0.20/0.43  # Current number of unprocessed clauses: 1967
% 0.20/0.43  # ...number of literals in the above   : 2200
% 0.20/0.43  # Current number of archived formulas  : 0
% 0.20/0.43  # Current number of archived clauses   : 84
% 0.20/0.43  # Clause-clause subsumption calls (NU) : 519
% 0.20/0.43  # Rec. Clause-clause subsumption calls : 471
% 0.20/0.43  # Non-unit clause-clause subsumptions  : 28
% 0.20/0.43  # Unit Clause-clause subsumption calls : 817
% 0.20/0.43  # Rewrite failures with RHS unbound    : 0
% 0.20/0.43  # BW rewrite match attempts            : 2159
% 0.20/0.43  # BW rewrite match successes           : 40
% 0.20/0.43  # Condensation attempts                : 0
% 0.20/0.43  # Condensation successes               : 0
% 0.20/0.43  # Termbank termtop insertions          : 79975
% 0.20/0.43  
% 0.20/0.43  # -------------------------------------------------
% 0.20/0.43  # User time                : 0.084 s
% 0.20/0.43  # System time              : 0.006 s
% 0.20/0.43  # Total time               : 0.090 s
% 0.20/0.43  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:11:20 EST 2020

% Result     : Theorem 3.65s
% Output     : CNFRefutation 3.65s
% Verified   : 
% Statistics : Number of formulae       :  224 (16570 expanded)
%              Number of clauses        :  161 (7695 expanded)
%              Number of leaves         :   31 (4295 expanded)
%              Depth                    :   21
%              Number of atoms          :  384 (25936 expanded)
%              Number of equality atoms :  175 (14503 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(t76_tops_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t62_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_tops_1(X1,X2) = k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_1)).

fof(dt_k2_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(t74_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k1_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(t65_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_pre_topc(X1,X2) = k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(dt_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

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

fof(c_0_31,plain,(
    ! [X12,X13] : k4_xboole_0(X12,X13) = k5_xboole_0(X12,k3_xboole_0(X12,X13)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_32,plain,(
    ! [X59,X60] : k1_setfam_1(k2_tarski(X59,X60)) = k3_xboole_0(X59,X60) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_33,plain,(
    ! [X23,X24] : k2_xboole_0(X23,k4_xboole_0(X24,X23)) = k2_xboole_0(X23,X24) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_34,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_35,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_36,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k3_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_37,plain,(
    ! [X61,X62] :
      ( ( ~ m1_subset_1(X61,k1_zfmisc_1(X62))
        | r1_tarski(X61,X62) )
      & ( ~ r1_tarski(X61,X62)
        | m1_subset_1(X61,k1_zfmisc_1(X62)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_38,plain,(
    ! [X58] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X58)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_39,plain,(
    ! [X21,X22] : r1_tarski(k4_xboole_0(X21,X22),X21) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_40,plain,(
    ! [X30,X31] : k4_xboole_0(X30,k4_xboole_0(X30,X31)) = k3_xboole_0(X30,X31) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_41,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_43,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_44,plain,(
    ! [X10,X11] :
      ( ( k4_xboole_0(X10,X11) != k1_xboole_0
        | r1_tarski(X10,X11) )
      & ( ~ r1_tarski(X10,X11)
        | k4_xboole_0(X10,X11) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_45,plain,(
    ! [X8,X9] :
      ( ( r1_tarski(X8,X9)
        | X8 != X9 )
      & ( r1_tarski(X9,X8)
        | X8 != X9 )
      & ( ~ r1_tarski(X8,X9)
        | ~ r1_tarski(X9,X8)
        | X8 = X9 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_46,plain,(
    ! [X25,X26] : k4_xboole_0(k2_xboole_0(X25,X26),X26) = k4_xboole_0(X25,X26) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_48,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_49,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_50,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_51,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_52,plain,(
    ! [X14,X15] :
      ( ~ r1_tarski(X14,X15)
      | k2_xboole_0(X14,X15) = X15 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_53,plain,
    ( k2_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_54,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k1_setfam_1(k2_tarski(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_35]),c_0_35])).

cnf(c_0_55,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_56,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_57,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

fof(c_0_58,plain,(
    ! [X19,X20] :
      ( ~ r1_tarski(X19,X20)
      | k3_xboole_0(X19,X20) = X19 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_59,plain,(
    ! [X49,X50,X51] :
      ( ~ m1_subset_1(X50,k1_zfmisc_1(X49))
      | k7_subset_1(X49,X50,X51) = k4_xboole_0(X50,X51) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

fof(c_0_60,plain,(
    ! [X35] : m1_subset_1(k2_subset_1(X35),k1_zfmisc_1(X35)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_61,plain,(
    ! [X32] : k2_subset_1(X32) = X32 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_62,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_63,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_64,plain,
    ( r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X1) ),
    inference(rw,[status(thm)],[c_0_49,c_0_42])).

cnf(c_0_65,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))))) = k1_setfam_1(k2_tarski(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_35]),c_0_42]),c_0_42])).

cnf(c_0_66,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_67,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_68,plain,
    ( k2_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X1,X2)))) = k2_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_69,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_55,c_0_42])).

cnf(c_0_70,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_56])).

cnf(c_0_71,plain,
    ( k5_xboole_0(k2_xboole_0(X1,X2),k1_setfam_1(k2_tarski(k2_xboole_0(X1,X2),X2))) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_42]),c_0_42])).

cnf(c_0_72,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_73,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_74,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_75,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

fof(c_0_76,plain,(
    ! [X52,X53,X54] :
      ( ~ m1_subset_1(X54,k1_zfmisc_1(X52))
      | k9_subset_1(X52,X53,X54) = k3_xboole_0(X53,X54) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

cnf(c_0_77,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_78,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_79,plain,
    ( k2_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_80,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = k2_xboole_0(X1,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70])])).

cnf(c_0_81,plain,
    ( k5_xboole_0(k2_xboole_0(X1,X2),k1_setfam_1(k2_tarski(X2,k2_xboole_0(X1,X2)))) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_71,c_0_54])).

cnf(c_0_82,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_72,c_0_35])).

cnf(c_0_83,plain,
    ( k7_subset_1(X2,X1,X3) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_73,c_0_42])).

cnf(c_0_84,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_74,c_0_75])).

fof(c_0_85,plain,(
    ! [X33,X34] :
      ( ~ m1_subset_1(X34,k1_zfmisc_1(X33))
      | k3_subset_1(X33,X34) = k4_xboole_0(X33,X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_86,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_87,plain,
    ( k1_setfam_1(k2_tarski(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_88,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_63])])).

cnf(c_0_89,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_90,plain,
    ( k5_xboole_0(k2_xboole_0(X1,X2),X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))
    | ~ r1_tarski(X2,k2_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_91,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X1,X1,X2) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_92,plain,
    ( k5_xboole_0(k2_xboole_0(X1,X2),k1_setfam_1(k2_tarski(X1,k2_xboole_0(X1,X2)))) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_81,c_0_66])).

cnf(c_0_93,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_69,c_0_82])).

fof(c_0_94,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v3_pre_topc(X2,X1)
            <=> k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t76_tops_1])).

cnf(c_0_95,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

fof(c_0_96,plain,(
    ! [X36,X37] :
      ( ~ m1_subset_1(X37,k1_zfmisc_1(X36))
      | m1_subset_1(k3_subset_1(X36,X37),k1_zfmisc_1(X36)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

fof(c_0_97,plain,(
    ! [X44,X45] :
      ( ~ m1_subset_1(X45,k1_zfmisc_1(X44))
      | k3_subset_1(X44,k3_subset_1(X44,X45)) = X45 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

cnf(c_0_98,plain,
    ( k9_subset_1(X2,X3,X1) = k1_setfam_1(k2_tarski(X3,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_86,c_0_35])).

cnf(c_0_99,plain,
    ( k1_setfam_1(k2_tarski(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_54,c_0_87])).

cnf(c_0_100,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k2_xboole_0(X2,X1)
    | ~ r1_tarski(X2,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_67,c_0_53])).

cnf(c_0_101,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_80,c_0_88])).

fof(c_0_102,plain,(
    ! [X27,X28,X29] : k4_xboole_0(k4_xboole_0(X27,X28),X29) = k4_xboole_0(X27,k2_xboole_0(X28,X29)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_103,plain,
    ( r1_tarski(X1,X2)
    | k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_89,c_0_42])).

cnf(c_0_104,plain,
    ( k5_xboole_0(k2_xboole_0(X1,X2),X2) = k7_subset_1(X1,X1,X2)
    | ~ r1_tarski(X2,k2_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_105,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_92]),c_0_53])).

cnf(c_0_106,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_93,c_0_70])).

fof(c_0_107,plain,(
    ! [X75,X76] :
      ( ~ l1_pre_topc(X75)
      | ~ m1_subset_1(X76,k1_zfmisc_1(u1_struct_0(X75)))
      | k2_tops_1(X75,X76) = k2_tops_1(X75,k3_subset_1(u1_struct_0(X75),X76)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_tops_1])])])).

fof(c_0_108,negated_conjecture,
    ( v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & ( ~ v3_pre_topc(esk2_0,esk1_0)
      | k2_tops_1(esk1_0,esk2_0) != k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0) )
    & ( v3_pre_topc(esk2_0,esk1_0)
      | k2_tops_1(esk1_0,esk2_0) = k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_94])])])).

cnf(c_0_109,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_95,c_0_42])).

cnf(c_0_110,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_96])).

cnf(c_0_111,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_97])).

cnf(c_0_112,plain,
    ( k9_subset_1(X1,X2,X1) = k1_setfam_1(k2_tarski(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_98,c_0_84])).

cnf(c_0_113,plain,
    ( k9_subset_1(X1,X2,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_48]),c_0_99])).

cnf(c_0_114,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_99]),c_0_63])])).

cnf(c_0_115,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_66,c_0_101])).

cnf(c_0_116,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_117,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_102])).

cnf(c_0_118,plain,
    ( r1_tarski(X1,X2)
    | k7_subset_1(X1,X1,X2) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_103,c_0_91])).

cnf(c_0_119,plain,
    ( k7_subset_1(X1,X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_105]),c_0_106]),c_0_70])])).

fof(c_0_120,plain,(
    ! [X66,X67] :
      ( ~ l1_pre_topc(X66)
      | ~ m1_subset_1(X67,k1_zfmisc_1(u1_struct_0(X66)))
      | m1_subset_1(k2_tops_1(X66,X67),k1_zfmisc_1(u1_struct_0(X66))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_1])])).

cnf(c_0_121,plain,
    ( k2_tops_1(X1,X2) = k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_107])).

cnf(c_0_122,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_108])).

cnf(c_0_123,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_108])).

cnf(c_0_124,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k3_subset_1(X1,X2)))) = k3_subset_1(X1,k3_subset_1(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_109,c_0_110])).

cnf(c_0_125,plain,
    ( k3_subset_1(X1,k3_subset_1(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_111,c_0_48])).

cnf(c_0_126,plain,
    ( k3_subset_1(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_48]),c_0_112]),c_0_113]),c_0_114]),c_0_115])).

cnf(c_0_127,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_69,c_0_54])).

cnf(c_0_128,plain,
    ( k7_subset_1(X1,X2,X3) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3)))
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_83,c_0_116])).

cnf(c_0_129,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_setfam_1(k2_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X3))) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k2_xboole_0(X2,X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_117,c_0_42]),c_0_42]),c_0_42])).

cnf(c_0_130,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_118,c_0_119])).

cnf(c_0_131,plain,
    ( m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_120])).

cnf(c_0_132,negated_conjecture,
    ( k2_tops_1(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)) = k2_tops_1(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_122]),c_0_123])])).

cnf(c_0_133,plain,
    ( r1_tarski(k3_subset_1(X1,X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_110])).

fof(c_0_134,plain,(
    ! [X79,X80] :
      ( ~ l1_pre_topc(X79)
      | ~ m1_subset_1(X80,k1_zfmisc_1(u1_struct_0(X79)))
      | k1_tops_1(X79,X80) = k7_subset_1(u1_struct_0(X79),X80,k2_tops_1(X79,X80)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_tops_1])])])).

fof(c_0_135,plain,(
    ! [X77,X78] :
      ( ~ l1_pre_topc(X77)
      | ~ m1_subset_1(X78,k1_zfmisc_1(u1_struct_0(X77)))
      | k2_pre_topc(X77,X78) = k4_subset_1(u1_struct_0(X77),X78,k2_tops_1(X77,X78)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_tops_1])])])).

cnf(c_0_136,plain,
    ( k7_subset_1(X1,X1,k3_subset_1(X1,X2)) = k3_subset_1(X1,k3_subset_1(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_124,c_0_91])).

cnf(c_0_137,plain,
    ( k3_subset_1(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_125,c_0_126])).

cnf(c_0_138,plain,
    ( k7_subset_1(X1,X2,X2) = k1_xboole_0
    | ~ r1_tarski(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_128]),c_0_70])])).

cnf(c_0_139,plain,
    ( k7_subset_1(k7_subset_1(X1,X1,X2),k7_subset_1(X1,X1,X2),X3) = k7_subset_1(X1,X1,k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_129,c_0_91]),c_0_91]),c_0_91]),c_0_91])).

cnf(c_0_140,plain,
    ( k2_xboole_0(X1,k7_subset_1(X2,X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_53,c_0_91])).

cnf(c_0_141,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_130,c_0_66])).

fof(c_0_142,plain,(
    ! [X46,X47,X48] :
      ( ~ m1_subset_1(X47,k1_zfmisc_1(X46))
      | ~ m1_subset_1(X48,k1_zfmisc_1(X46))
      | k4_subset_1(X46,X47,X48) = k2_xboole_0(X47,X48) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_143,negated_conjecture,
    ( m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_132]),c_0_123])])).

cnf(c_0_144,negated_conjecture,
    ( r1_tarski(k3_subset_1(u1_struct_0(esk1_0),esk2_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_133,c_0_122])).

cnf(c_0_145,plain,
    ( k1_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_134])).

fof(c_0_146,plain,(
    ! [X38,X39,X40] :
      ( ~ m1_subset_1(X39,k1_zfmisc_1(X38))
      | ~ m1_subset_1(X40,k1_zfmisc_1(X38))
      | m1_subset_1(k4_subset_1(X38,X39,X40),k1_zfmisc_1(X38)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_subset_1])])).

cnf(c_0_147,plain,
    ( k2_pre_topc(X1,X2) = k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_135])).

cnf(c_0_148,plain,
    ( k5_xboole_0(k2_xboole_0(X1,X2),k1_setfam_1(k2_tarski(k2_xboole_0(X1,X2),k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))))) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_53]),c_0_54])).

cnf(c_0_149,plain,
    ( k7_subset_1(X1,X1,k7_subset_1(X1,X1,X2)) = k1_setfam_1(k2_tarski(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_91]),c_0_91])).

cnf(c_0_150,plain,
    ( k7_subset_1(X1,X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136,c_0_84]),c_0_137]),c_0_137]),c_0_126])).

cnf(c_0_151,plain,
    ( k7_subset_1(X1,X1,k2_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_139]),c_0_140]),c_0_70])])).

cnf(c_0_152,plain,
    ( k5_xboole_0(k2_xboole_0(X1,X2),X2) = k7_subset_1(X1,X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_104,c_0_141])])).

cnf(c_0_153,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_142])).

cnf(c_0_154,negated_conjecture,
    ( m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_116]),c_0_144])])).

cnf(c_0_155,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk2_0,k2_tops_1(esk1_0,esk2_0)) = k1_tops_1(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_145,c_0_122]),c_0_123])])).

cnf(c_0_156,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1) = k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1))) ),
    inference(spm,[status(thm)],[c_0_83,c_0_122])).

cnf(c_0_157,plain,
    ( m1_subset_1(k4_subset_1(X2,X1,X3),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_146])).

cnf(c_0_158,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),esk2_0,k2_tops_1(esk1_0,esk2_0)) = k2_pre_topc(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_147,c_0_122]),c_0_123])])).

cnf(c_0_159,plain,
    ( k7_subset_1(k2_xboole_0(X1,X2),k2_xboole_0(X1,X2),k7_subset_1(X2,X2,X1)) = k7_subset_1(X1,X1,k7_subset_1(X2,X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_148,c_0_91]),c_0_91]),c_0_91]),c_0_91])).

cnf(c_0_160,plain,
    ( k1_setfam_1(k2_tarski(X1,k2_xboole_0(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_149,c_0_119]),c_0_150])).

cnf(c_0_161,plain,
    ( k5_xboole_0(k2_xboole_0(X1,X2),k1_setfam_1(k2_tarski(X1,k2_xboole_0(X1,X2)))) = k7_subset_1(X2,X2,X1) ),
    inference(rw,[status(thm)],[c_0_92,c_0_91])).

cnf(c_0_162,plain,
    ( k1_setfam_1(k2_tarski(X1,k2_xboole_0(X2,X1))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_149,c_0_151]),c_0_152]),c_0_101]),c_0_114]),c_0_115])).

cnf(c_0_163,plain,
    ( k9_subset_1(X1,X2,X1) = k1_setfam_1(k2_tarski(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_112])).

cnf(c_0_164,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),X1,k2_tops_1(esk1_0,esk2_0)) = k2_xboole_0(X1,k2_tops_1(esk1_0,esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_153,c_0_154])).

cnf(c_0_165,negated_conjecture,
    ( k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,k2_tops_1(esk1_0,esk2_0)))) = k1_tops_1(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_155,c_0_156])).

cnf(c_0_166,negated_conjecture,
    ( m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_157,c_0_158]),c_0_122])])).

cnf(c_0_167,plain,
    ( k7_subset_1(X1,X1,k5_xboole_0(k2_xboole_0(X1,X2),X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_159,c_0_105]),c_0_149]),c_0_152]),c_0_66]),c_0_105]),c_0_54]),c_0_160])).

cnf(c_0_168,plain,
    ( k5_xboole_0(k2_xboole_0(X1,X2),X1) = k7_subset_1(X2,X2,X1) ),
    inference(rw,[status(thm)],[c_0_161,c_0_160])).

cnf(c_0_169,plain,
    ( k9_subset_1(X1,k2_xboole_0(X2,X1),X1) = X1 ),
    inference(spm,[status(thm)],[c_0_162,c_0_163])).

cnf(c_0_170,negated_conjecture,
    ( k2_xboole_0(esk2_0,k2_tops_1(esk1_0,esk2_0)) = k2_pre_topc(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_164,c_0_122]),c_0_158])).

cnf(c_0_171,negated_conjecture,
    ( k7_subset_1(esk2_0,esk2_0,k2_tops_1(esk1_0,esk2_0)) = k1_tops_1(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_165,c_0_91])).

cnf(c_0_172,plain,
    ( k7_subset_1(X1,X2,X3) = k7_subset_1(X2,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_83,c_0_91])).

cnf(c_0_173,negated_conjecture,
    ( m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_166,c_0_154])])).

fof(c_0_174,plain,(
    ! [X72,X73,X74] :
      ( ~ l1_pre_topc(X72)
      | ~ m1_subset_1(X73,k1_zfmisc_1(u1_struct_0(X72)))
      | ~ m1_subset_1(X74,k1_zfmisc_1(u1_struct_0(X72)))
      | ~ v3_pre_topc(X73,X72)
      | ~ r1_tarski(X73,X74)
      | r1_tarski(X73,k1_tops_1(X72,X74)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_tops_1])])])).

cnf(c_0_175,plain,
    ( k7_subset_1(X1,X1,k7_subset_1(X2,X2,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_167,c_0_168])).

cnf(c_0_176,plain,
    ( k7_subset_1(X1,X2,X3) = k7_subset_1(X2,X2,X3)
    | ~ r1_tarski(X2,X1) ),
    inference(rw,[status(thm)],[c_0_128,c_0_91])).

cnf(c_0_177,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))) = k7_subset_1(X1,X1,X2) ),
    inference(spm,[status(thm)],[c_0_91,c_0_54])).

cnf(c_0_178,negated_conjecture,
    ( k1_setfam_1(k2_tarski(k2_tops_1(esk1_0,esk2_0),k2_pre_topc(esk1_0,esk2_0))) = k2_tops_1(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_169,c_0_170]),c_0_112]),c_0_54])).

cnf(c_0_179,negated_conjecture,
    ( k5_xboole_0(k2_pre_topc(esk1_0,esk2_0),k2_tops_1(esk1_0,esk2_0)) = k1_tops_1(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_152,c_0_170]),c_0_171])).

cnf(c_0_180,negated_conjecture,
    ( k7_subset_1(k2_pre_topc(esk1_0,esk2_0),k2_pre_topc(esk1_0,esk2_0),X1) = k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_172,c_0_173])).

cnf(c_0_181,negated_conjecture,
    ( r1_tarski(k2_pre_topc(esk1_0,esk2_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_47,c_0_166])).

cnf(c_0_182,negated_conjecture,
    ( k7_subset_1(k2_tops_1(esk1_0,esk2_0),k2_tops_1(esk1_0,esk2_0),X1) = k7_subset_1(u1_struct_0(esk1_0),k2_tops_1(esk1_0,esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_172,c_0_154])).

cnf(c_0_183,plain,
    ( r1_tarski(X2,k1_tops_1(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X2,X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_174])).

cnf(c_0_184,plain,
    ( k7_subset_1(k2_xboole_0(X1,X2),k2_xboole_0(X1,X2),k7_subset_1(X2,X2,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_159,c_0_175])).

cnf(c_0_185,negated_conjecture,
    ( k2_xboole_0(esk2_0,k2_pre_topc(esk1_0,esk2_0)) = k2_pre_topc(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_105,c_0_170])).

cnf(c_0_186,plain,
    ( k7_subset_1(X1,X1,k7_subset_1(X2,X1,X3)) = k1_setfam_1(k2_tarski(X1,X3))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_149,c_0_176])).

cnf(c_0_187,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),k2_tops_1(esk1_0,esk2_0)) = k1_tops_1(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_177,c_0_178]),c_0_179]),c_0_180])).

cnf(c_0_188,negated_conjecture,
    ( r1_tarski(k2_pre_topc(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_181,c_0_131]),c_0_123]),c_0_122])])).

cnf(c_0_189,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),k1_tops_1(esk1_0,esk2_0)) = k7_subset_1(u1_struct_0(esk1_0),k2_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk2_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_159,c_0_171]),c_0_66]),c_0_66]),c_0_170]),c_0_170]),c_0_180]),c_0_182])).

cnf(c_0_190,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_81]),c_0_53])).

fof(c_0_191,plain,(
    ! [X68,X69] :
      ( ~ v2_pre_topc(X68)
      | ~ l1_pre_topc(X68)
      | ~ m1_subset_1(X69,k1_zfmisc_1(u1_struct_0(X68)))
      | v3_pre_topc(k1_tops_1(X68,X69),X68) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).

cnf(c_0_192,negated_conjecture,
    ( r1_tarski(X1,k1_tops_1(esk1_0,esk2_0))
    | ~ v3_pre_topc(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_183,c_0_122]),c_0_123])])).

cnf(c_0_193,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0)) = esk2_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_184,c_0_185]),c_0_180]),c_0_180])).

cnf(c_0_194,negated_conjecture,
    ( v3_pre_topc(esk2_0,esk1_0)
    | k2_tops_1(esk1_0,esk2_0) = k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_108])).

cnf(c_0_195,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_165])).

cnf(c_0_196,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k2_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk2_0)) = k2_tops_1(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_186,c_0_187]),c_0_180]),c_0_54]),c_0_178]),c_0_188])]),c_0_189])).

cnf(c_0_197,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),k5_xboole_0(X2,k1_setfam_1(k2_tarski(X1,X2)))) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_190,c_0_68]),c_0_66]),c_0_66]),c_0_68])).

cnf(c_0_198,negated_conjecture,
    ( k2_xboole_0(k2_tops_1(esk1_0,esk2_0),k2_pre_topc(esk1_0,esk2_0)) = k2_pre_topc(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_190,c_0_170]),c_0_66]),c_0_170])).

cnf(c_0_199,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k3_subset_1(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_109,c_0_116])).

cnf(c_0_200,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk2_0,k2_pre_topc(esk1_0,esk2_0))) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_160,c_0_170])).

cnf(c_0_201,negated_conjecture,
    ( ~ v3_pre_topc(esk2_0,esk1_0)
    | k2_tops_1(esk1_0,esk2_0) != k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_108])).

cnf(c_0_202,plain,
    ( k7_subset_1(X1,X2,X3) = k7_subset_1(X4,X2,X3)
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X2,X4) ),
    inference(spm,[status(thm)],[c_0_176,c_0_176])).

cnf(c_0_203,plain,
    ( v3_pre_topc(k1_tops_1(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_191])).

cnf(c_0_204,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_108])).

cnf(c_0_205,negated_conjecture,
    ( r1_tarski(esk2_0,k1_tops_1(esk1_0,esk2_0))
    | ~ v3_pre_topc(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_192,c_0_122]),c_0_70])])).

cnf(c_0_206,negated_conjecture,
    ( k1_tops_1(esk1_0,esk2_0) = esk2_0
    | v3_pre_topc(esk2_0,esk1_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_193,c_0_194]),c_0_187])).

cnf(c_0_207,negated_conjecture,
    ( k1_tops_1(esk1_0,esk2_0) = esk2_0
    | ~ r1_tarski(esk2_0,k1_tops_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_195])).

cnf(c_0_208,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),k1_tops_1(esk1_0,esk2_0)) = k2_tops_1(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_189,c_0_196])).

cnf(c_0_209,negated_conjecture,
    ( k5_xboole_0(k2_xboole_0(k2_pre_topc(esk1_0,esk2_0),X1),X1) = k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_152,c_0_180])).

cnf(c_0_210,negated_conjecture,
    ( k2_xboole_0(k1_tops_1(esk1_0,esk2_0),k2_pre_topc(esk1_0,esk2_0)) = k2_pre_topc(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_197,c_0_178]),c_0_198]),c_0_179]),c_0_198]),c_0_66])).

cnf(c_0_211,plain,
    ( k5_xboole_0(X1,k9_subset_1(X2,X1,X2)) = k3_subset_1(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_199,c_0_112])).

cnf(c_0_212,negated_conjecture,
    ( k9_subset_1(esk2_0,k2_pre_topc(esk1_0,esk2_0),esk2_0) = esk2_0 ),
    inference(rw,[status(thm)],[c_0_200,c_0_163])).

cnf(c_0_213,negated_conjecture,
    ( r1_tarski(esk2_0,k2_pre_topc(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_130,c_0_170])).

cnf(c_0_214,negated_conjecture,
    ( k7_subset_1(X1,k2_pre_topc(esk1_0,esk2_0),esk2_0) != k2_tops_1(esk1_0,esk2_0)
    | ~ v3_pre_topc(esk2_0,esk1_0)
    | ~ r1_tarski(k2_pre_topc(esk1_0,esk2_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_201,c_0_202]),c_0_188])])).

cnf(c_0_215,plain,
    ( k7_subset_1(X1,X1,X2) = k3_subset_1(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_199,c_0_91])).

cnf(c_0_216,negated_conjecture,
    ( v3_pre_topc(k1_tops_1(esk1_0,esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_203,c_0_122]),c_0_204]),c_0_123])])).

cnf(c_0_217,negated_conjecture,
    ( k1_tops_1(esk1_0,esk2_0) = esk2_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_205,c_0_206]),c_0_207])).

cnf(c_0_218,negated_conjecture,
    ( k5_xboole_0(k2_pre_topc(esk1_0,esk2_0),k1_tops_1(esk1_0,esk2_0)) = k2_tops_1(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_208,c_0_209]),c_0_66]),c_0_210])).

cnf(c_0_219,negated_conjecture,
    ( k5_xboole_0(k2_pre_topc(esk1_0,esk2_0),esk2_0) = k3_subset_1(k2_pre_topc(esk1_0,esk2_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_211,c_0_212]),c_0_213])])).

cnf(c_0_220,negated_conjecture,
    ( k3_subset_1(k2_pre_topc(esk1_0,esk2_0),esk2_0) != k2_tops_1(esk1_0,esk2_0)
    | ~ v3_pre_topc(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_214,c_0_215]),c_0_70]),c_0_213])])).

cnf(c_0_221,negated_conjecture,
    ( v3_pre_topc(esk2_0,esk1_0) ),
    inference(rw,[status(thm)],[c_0_216,c_0_217])).

cnf(c_0_222,negated_conjecture,
    ( k3_subset_1(k2_pre_topc(esk1_0,esk2_0),esk2_0) = k2_tops_1(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_218,c_0_217]),c_0_219])).

cnf(c_0_223,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_220,c_0_221])]),c_0_222])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:07:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 3.65/3.82  # AutoSched0-Mode selected heuristic G_E___107_C36_F1_PI_AE_Q4_CS_SP_PS_S0Y
% 3.65/3.82  # and selection function SelectMaxLComplexAvoidPosPred.
% 3.65/3.82  #
% 3.65/3.82  # Preprocessing time       : 0.028 s
% 3.65/3.82  # Presaturation interreduction done
% 3.65/3.82  
% 3.65/3.82  # Proof found!
% 3.65/3.82  # SZS status Theorem
% 3.65/3.82  # SZS output start CNFRefutation
% 3.65/3.82  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.65/3.82  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.65/3.82  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.65/3.82  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.65/3.82  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.65/3.82  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.65/3.82  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.65/3.82  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.65/3.82  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.65/3.82  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.65/3.82  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 3.65/3.82  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.65/3.82  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.65/3.82  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.65/3.82  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 3.65/3.82  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.65/3.82  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.65/3.82  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 3.65/3.82  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 3.65/3.82  fof(t76_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_tops_1)).
% 3.65/3.82  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 3.65/3.82  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 3.65/3.82  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 3.65/3.82  fof(t62_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_tops_1(X1,X2)=k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tops_1)).
% 3.65/3.82  fof(dt_k2_tops_1, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 3.65/3.82  fof(t74_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k1_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 3.65/3.82  fof(t65_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_pre_topc(X1,X2)=k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 3.65/3.82  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 3.65/3.82  fof(dt_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 3.65/3.82  fof(t56_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v3_pre_topc(X2,X1)&r1_tarski(X2,X3))=>r1_tarski(X2,k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tops_1)).
% 3.65/3.82  fof(fc9_tops_1, axiom, ![X1, X2]:(((v2_pre_topc(X1)&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v3_pre_topc(k1_tops_1(X1,X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 3.65/3.82  fof(c_0_31, plain, ![X12, X13]:k4_xboole_0(X12,X13)=k5_xboole_0(X12,k3_xboole_0(X12,X13)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 3.65/3.82  fof(c_0_32, plain, ![X59, X60]:k1_setfam_1(k2_tarski(X59,X60))=k3_xboole_0(X59,X60), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 3.65/3.82  fof(c_0_33, plain, ![X23, X24]:k2_xboole_0(X23,k4_xboole_0(X24,X23))=k2_xboole_0(X23,X24), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 3.65/3.82  cnf(c_0_34, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 3.65/3.82  cnf(c_0_35, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 3.65/3.82  fof(c_0_36, plain, ![X6, X7]:k3_xboole_0(X6,X7)=k3_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 3.65/3.82  fof(c_0_37, plain, ![X61, X62]:((~m1_subset_1(X61,k1_zfmisc_1(X62))|r1_tarski(X61,X62))&(~r1_tarski(X61,X62)|m1_subset_1(X61,k1_zfmisc_1(X62)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 3.65/3.82  fof(c_0_38, plain, ![X58]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X58)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 3.65/3.82  fof(c_0_39, plain, ![X21, X22]:r1_tarski(k4_xboole_0(X21,X22),X21), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 3.65/3.82  fof(c_0_40, plain, ![X30, X31]:k4_xboole_0(X30,k4_xboole_0(X30,X31))=k3_xboole_0(X30,X31), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 3.65/3.82  cnf(c_0_41, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 3.65/3.82  cnf(c_0_42, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_34, c_0_35])).
% 3.65/3.82  cnf(c_0_43, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 3.65/3.82  fof(c_0_44, plain, ![X10, X11]:((k4_xboole_0(X10,X11)!=k1_xboole_0|r1_tarski(X10,X11))&(~r1_tarski(X10,X11)|k4_xboole_0(X10,X11)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 3.65/3.82  fof(c_0_45, plain, ![X8, X9]:(((r1_tarski(X8,X9)|X8!=X9)&(r1_tarski(X9,X8)|X8!=X9))&(~r1_tarski(X8,X9)|~r1_tarski(X9,X8)|X8=X9)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 3.65/3.82  fof(c_0_46, plain, ![X25, X26]:k4_xboole_0(k2_xboole_0(X25,X26),X26)=k4_xboole_0(X25,X26), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 3.65/3.82  cnf(c_0_47, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 3.65/3.82  cnf(c_0_48, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 3.65/3.82  cnf(c_0_49, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 3.65/3.82  cnf(c_0_50, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 3.65/3.82  fof(c_0_51, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 3.65/3.82  fof(c_0_52, plain, ![X14, X15]:(~r1_tarski(X14,X15)|k2_xboole_0(X14,X15)=X15), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 3.65/3.82  cnf(c_0_53, plain, (k2_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1))))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_41, c_0_42])).
% 3.65/3.82  cnf(c_0_54, plain, (k1_setfam_1(k2_tarski(X1,X2))=k1_setfam_1(k2_tarski(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_35]), c_0_35])).
% 3.65/3.82  cnf(c_0_55, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 3.65/3.82  cnf(c_0_56, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_45])).
% 3.65/3.82  cnf(c_0_57, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 3.65/3.82  fof(c_0_58, plain, ![X19, X20]:(~r1_tarski(X19,X20)|k3_xboole_0(X19,X20)=X19), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 3.65/3.82  fof(c_0_59, plain, ![X49, X50, X51]:(~m1_subset_1(X50,k1_zfmisc_1(X49))|k7_subset_1(X49,X50,X51)=k4_xboole_0(X50,X51)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 3.65/3.82  fof(c_0_60, plain, ![X35]:m1_subset_1(k2_subset_1(X35),k1_zfmisc_1(X35)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 3.65/3.82  fof(c_0_61, plain, ![X32]:k2_subset_1(X32)=X32, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 3.65/3.82  cnf(c_0_62, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 3.65/3.82  cnf(c_0_63, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 3.65/3.82  cnf(c_0_64, plain, (r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X1)), inference(rw,[status(thm)],[c_0_49, c_0_42])).
% 3.65/3.82  cnf(c_0_65, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))))))=k1_setfam_1(k2_tarski(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_35]), c_0_42]), c_0_42])).
% 3.65/3.82  cnf(c_0_66, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 3.65/3.82  cnf(c_0_67, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 3.65/3.82  cnf(c_0_68, plain, (k2_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X1,X2))))=k2_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 3.65/3.82  cnf(c_0_69, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k1_xboole_0|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_55, c_0_42])).
% 3.65/3.82  cnf(c_0_70, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_56])).
% 3.65/3.82  cnf(c_0_71, plain, (k5_xboole_0(k2_xboole_0(X1,X2),k1_setfam_1(k2_tarski(k2_xboole_0(X1,X2),X2)))=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_42]), c_0_42])).
% 3.65/3.82  cnf(c_0_72, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 3.65/3.82  cnf(c_0_73, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 3.65/3.82  cnf(c_0_74, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 3.65/3.82  cnf(c_0_75, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_61])).
% 3.65/3.82  fof(c_0_76, plain, ![X52, X53, X54]:(~m1_subset_1(X54,k1_zfmisc_1(X52))|k9_subset_1(X52,X53,X54)=k3_xboole_0(X53,X54)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 3.65/3.82  cnf(c_0_77, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 3.65/3.82  cnf(c_0_78, plain, (r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X1)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 3.65/3.82  cnf(c_0_79, plain, (k2_xboole_0(X1,X2)=X1|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 3.65/3.82  cnf(c_0_80, plain, (k2_xboole_0(X1,k1_xboole_0)=k2_xboole_0(X1,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_70])])).
% 3.65/3.82  cnf(c_0_81, plain, (k5_xboole_0(k2_xboole_0(X1,X2),k1_setfam_1(k2_tarski(X2,k2_xboole_0(X1,X2))))=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_71, c_0_54])).
% 3.65/3.82  cnf(c_0_82, plain, (k1_setfam_1(k2_tarski(X1,X2))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_72, c_0_35])).
% 3.65/3.82  cnf(c_0_83, plain, (k7_subset_1(X2,X1,X3)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_73, c_0_42])).
% 3.65/3.82  cnf(c_0_84, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_74, c_0_75])).
% 3.65/3.82  fof(c_0_85, plain, ![X33, X34]:(~m1_subset_1(X34,k1_zfmisc_1(X33))|k3_subset_1(X33,X34)=k4_xboole_0(X33,X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 3.65/3.82  cnf(c_0_86, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_76])).
% 3.65/3.82  cnf(c_0_87, plain, (k1_setfam_1(k2_tarski(k1_xboole_0,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 3.65/3.82  cnf(c_0_88, plain, (k2_xboole_0(X1,X1)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_63])])).
% 3.65/3.82  cnf(c_0_89, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_44])).
% 3.65/3.82  cnf(c_0_90, plain, (k5_xboole_0(k2_xboole_0(X1,X2),X2)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))|~r1_tarski(X2,k2_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 3.65/3.82  cnf(c_0_91, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k7_subset_1(X1,X1,X2)), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 3.65/3.82  cnf(c_0_92, plain, (k5_xboole_0(k2_xboole_0(X1,X2),k1_setfam_1(k2_tarski(X1,k2_xboole_0(X1,X2))))=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))), inference(spm,[status(thm)],[c_0_81, c_0_66])).
% 3.65/3.82  cnf(c_0_93, plain, (k5_xboole_0(X1,X1)=k1_xboole_0|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_69, c_0_82])).
% 3.65/3.82  fof(c_0_94, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2))))), inference(assume_negation,[status(cth)],[t76_tops_1])).
% 3.65/3.82  cnf(c_0_95, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_85])).
% 3.65/3.82  fof(c_0_96, plain, ![X36, X37]:(~m1_subset_1(X37,k1_zfmisc_1(X36))|m1_subset_1(k3_subset_1(X36,X37),k1_zfmisc_1(X36))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 3.65/3.82  fof(c_0_97, plain, ![X44, X45]:(~m1_subset_1(X45,k1_zfmisc_1(X44))|k3_subset_1(X44,k3_subset_1(X44,X45))=X45), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 3.65/3.82  cnf(c_0_98, plain, (k9_subset_1(X2,X3,X1)=k1_setfam_1(k2_tarski(X3,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_86, c_0_35])).
% 3.65/3.82  cnf(c_0_99, plain, (k1_setfam_1(k2_tarski(X1,k1_xboole_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_54, c_0_87])).
% 3.65/3.82  cnf(c_0_100, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k2_xboole_0(X2,X1)|~r1_tarski(X2,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))))), inference(spm,[status(thm)],[c_0_67, c_0_53])).
% 3.65/3.82  cnf(c_0_101, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_80, c_0_88])).
% 3.65/3.82  fof(c_0_102, plain, ![X27, X28, X29]:k4_xboole_0(k4_xboole_0(X27,X28),X29)=k4_xboole_0(X27,k2_xboole_0(X28,X29)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 3.65/3.82  cnf(c_0_103, plain, (r1_tarski(X1,X2)|k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_89, c_0_42])).
% 3.65/3.82  cnf(c_0_104, plain, (k5_xboole_0(k2_xboole_0(X1,X2),X2)=k7_subset_1(X1,X1,X2)|~r1_tarski(X2,k2_xboole_0(X1,X2))), inference(rw,[status(thm)],[c_0_90, c_0_91])).
% 3.65/3.82  cnf(c_0_105, plain, (k2_xboole_0(X1,k2_xboole_0(X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_92]), c_0_53])).
% 3.65/3.82  cnf(c_0_106, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_93, c_0_70])).
% 3.65/3.82  fof(c_0_107, plain, ![X75, X76]:(~l1_pre_topc(X75)|(~m1_subset_1(X76,k1_zfmisc_1(u1_struct_0(X75)))|k2_tops_1(X75,X76)=k2_tops_1(X75,k3_subset_1(u1_struct_0(X75),X76)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_tops_1])])])).
% 3.65/3.82  fof(c_0_108, negated_conjecture, ((v2_pre_topc(esk1_0)&l1_pre_topc(esk1_0))&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&((~v3_pre_topc(esk2_0,esk1_0)|k2_tops_1(esk1_0,esk2_0)!=k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0))&(v3_pre_topc(esk2_0,esk1_0)|k2_tops_1(esk1_0,esk2_0)=k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_94])])])).
% 3.65/3.82  cnf(c_0_109, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_95, c_0_42])).
% 3.65/3.82  cnf(c_0_110, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_96])).
% 3.65/3.82  cnf(c_0_111, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_97])).
% 3.65/3.82  cnf(c_0_112, plain, (k9_subset_1(X1,X2,X1)=k1_setfam_1(k2_tarski(X2,X1))), inference(spm,[status(thm)],[c_0_98, c_0_84])).
% 3.65/3.82  cnf(c_0_113, plain, (k9_subset_1(X1,X2,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_48]), c_0_99])).
% 3.65/3.82  cnf(c_0_114, plain, (k5_xboole_0(X1,k1_xboole_0)=k2_xboole_0(k1_xboole_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_99]), c_0_63])])).
% 3.65/3.82  cnf(c_0_115, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_66, c_0_101])).
% 3.65/3.82  cnf(c_0_116, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 3.65/3.82  cnf(c_0_117, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_102])).
% 3.65/3.82  cnf(c_0_118, plain, (r1_tarski(X1,X2)|k7_subset_1(X1,X1,X2)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_103, c_0_91])).
% 3.65/3.82  cnf(c_0_119, plain, (k7_subset_1(X1,X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_105]), c_0_106]), c_0_70])])).
% 3.65/3.82  fof(c_0_120, plain, ![X66, X67]:(~l1_pre_topc(X66)|~m1_subset_1(X67,k1_zfmisc_1(u1_struct_0(X66)))|m1_subset_1(k2_tops_1(X66,X67),k1_zfmisc_1(u1_struct_0(X66)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_1])])).
% 3.65/3.82  cnf(c_0_121, plain, (k2_tops_1(X1,X2)=k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_107])).
% 3.65/3.82  cnf(c_0_122, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_108])).
% 3.65/3.82  cnf(c_0_123, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_108])).
% 3.65/3.82  cnf(c_0_124, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k3_subset_1(X1,X2))))=k3_subset_1(X1,k3_subset_1(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_109, c_0_110])).
% 3.65/3.82  cnf(c_0_125, plain, (k3_subset_1(X1,k3_subset_1(X1,k1_xboole_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_111, c_0_48])).
% 3.65/3.82  cnf(c_0_126, plain, (k3_subset_1(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_48]), c_0_112]), c_0_113]), c_0_114]), c_0_115])).
% 3.65/3.82  cnf(c_0_127, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1)))=k1_xboole_0|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_69, c_0_54])).
% 3.65/3.82  cnf(c_0_128, plain, (k7_subset_1(X1,X2,X3)=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3)))|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_83, c_0_116])).
% 3.65/3.82  cnf(c_0_129, plain, (k5_xboole_0(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_setfam_1(k2_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X3)))=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k2_xboole_0(X2,X3))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_117, c_0_42]), c_0_42]), c_0_42])).
% 3.65/3.82  cnf(c_0_130, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_118, c_0_119])).
% 3.65/3.82  cnf(c_0_131, plain, (m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_120])).
% 3.65/3.82  cnf(c_0_132, negated_conjecture, (k2_tops_1(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0))=k2_tops_1(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121, c_0_122]), c_0_123])])).
% 3.65/3.82  cnf(c_0_133, plain, (r1_tarski(k3_subset_1(X1,X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_47, c_0_110])).
% 3.65/3.82  fof(c_0_134, plain, ![X79, X80]:(~l1_pre_topc(X79)|(~m1_subset_1(X80,k1_zfmisc_1(u1_struct_0(X79)))|k1_tops_1(X79,X80)=k7_subset_1(u1_struct_0(X79),X80,k2_tops_1(X79,X80)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_tops_1])])])).
% 3.65/3.82  fof(c_0_135, plain, ![X77, X78]:(~l1_pre_topc(X77)|(~m1_subset_1(X78,k1_zfmisc_1(u1_struct_0(X77)))|k2_pre_topc(X77,X78)=k4_subset_1(u1_struct_0(X77),X78,k2_tops_1(X77,X78)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_tops_1])])])).
% 3.65/3.82  cnf(c_0_136, plain, (k7_subset_1(X1,X1,k3_subset_1(X1,X2))=k3_subset_1(X1,k3_subset_1(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_124, c_0_91])).
% 3.65/3.82  cnf(c_0_137, plain, (k3_subset_1(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_125, c_0_126])).
% 3.65/3.82  cnf(c_0_138, plain, (k7_subset_1(X1,X2,X2)=k1_xboole_0|~r1_tarski(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127, c_0_128]), c_0_70])])).
% 3.65/3.82  cnf(c_0_139, plain, (k7_subset_1(k7_subset_1(X1,X1,X2),k7_subset_1(X1,X1,X2),X3)=k7_subset_1(X1,X1,k2_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_129, c_0_91]), c_0_91]), c_0_91]), c_0_91])).
% 3.65/3.82  cnf(c_0_140, plain, (k2_xboole_0(X1,k7_subset_1(X2,X2,X1))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_53, c_0_91])).
% 3.65/3.82  cnf(c_0_141, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_130, c_0_66])).
% 3.65/3.82  fof(c_0_142, plain, ![X46, X47, X48]:(~m1_subset_1(X47,k1_zfmisc_1(X46))|~m1_subset_1(X48,k1_zfmisc_1(X46))|k4_subset_1(X46,X47,X48)=k2_xboole_0(X47,X48)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 3.65/3.82  cnf(c_0_143, negated_conjecture, (m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131, c_0_132]), c_0_123])])).
% 3.65/3.82  cnf(c_0_144, negated_conjecture, (r1_tarski(k3_subset_1(u1_struct_0(esk1_0),esk2_0),u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_133, c_0_122])).
% 3.65/3.82  cnf(c_0_145, plain, (k1_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_134])).
% 3.65/3.82  fof(c_0_146, plain, ![X38, X39, X40]:(~m1_subset_1(X39,k1_zfmisc_1(X38))|~m1_subset_1(X40,k1_zfmisc_1(X38))|m1_subset_1(k4_subset_1(X38,X39,X40),k1_zfmisc_1(X38))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_subset_1])])).
% 3.65/3.82  cnf(c_0_147, plain, (k2_pre_topc(X1,X2)=k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_135])).
% 3.65/3.82  cnf(c_0_148, plain, (k5_xboole_0(k2_xboole_0(X1,X2),k1_setfam_1(k2_tarski(k2_xboole_0(X1,X2),k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1))))))=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1))))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_53]), c_0_54])).
% 3.65/3.82  cnf(c_0_149, plain, (k7_subset_1(X1,X1,k7_subset_1(X1,X1,X2))=k1_setfam_1(k2_tarski(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_91]), c_0_91])).
% 3.65/3.82  cnf(c_0_150, plain, (k7_subset_1(X1,X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136, c_0_84]), c_0_137]), c_0_137]), c_0_126])).
% 3.65/3.82  cnf(c_0_151, plain, (k7_subset_1(X1,X1,k2_xboole_0(X2,X1))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_139]), c_0_140]), c_0_70])])).
% 3.65/3.82  cnf(c_0_152, plain, (k5_xboole_0(k2_xboole_0(X1,X2),X2)=k7_subset_1(X1,X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_104, c_0_141])])).
% 3.65/3.82  cnf(c_0_153, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_142])).
% 3.65/3.82  cnf(c_0_154, negated_conjecture, (m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143, c_0_116]), c_0_144])])).
% 3.65/3.82  cnf(c_0_155, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk2_0,k2_tops_1(esk1_0,esk2_0))=k1_tops_1(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_145, c_0_122]), c_0_123])])).
% 3.65/3.82  cnf(c_0_156, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)=k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1)))), inference(spm,[status(thm)],[c_0_83, c_0_122])).
% 3.65/3.82  cnf(c_0_157, plain, (m1_subset_1(k4_subset_1(X2,X1,X3),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_146])).
% 3.65/3.82  cnf(c_0_158, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),esk2_0,k2_tops_1(esk1_0,esk2_0))=k2_pre_topc(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_147, c_0_122]), c_0_123])])).
% 3.65/3.82  cnf(c_0_159, plain, (k7_subset_1(k2_xboole_0(X1,X2),k2_xboole_0(X1,X2),k7_subset_1(X2,X2,X1))=k7_subset_1(X1,X1,k7_subset_1(X2,X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_148, c_0_91]), c_0_91]), c_0_91]), c_0_91])).
% 3.65/3.82  cnf(c_0_160, plain, (k1_setfam_1(k2_tarski(X1,k2_xboole_0(X1,X2)))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_149, c_0_119]), c_0_150])).
% 3.65/3.82  cnf(c_0_161, plain, (k5_xboole_0(k2_xboole_0(X1,X2),k1_setfam_1(k2_tarski(X1,k2_xboole_0(X1,X2))))=k7_subset_1(X2,X2,X1)), inference(rw,[status(thm)],[c_0_92, c_0_91])).
% 3.65/3.82  cnf(c_0_162, plain, (k1_setfam_1(k2_tarski(X1,k2_xboole_0(X2,X1)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_149, c_0_151]), c_0_152]), c_0_101]), c_0_114]), c_0_115])).
% 3.65/3.82  cnf(c_0_163, plain, (k9_subset_1(X1,X2,X1)=k1_setfam_1(k2_tarski(X1,X2))), inference(spm,[status(thm)],[c_0_54, c_0_112])).
% 3.65/3.82  cnf(c_0_164, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),X1,k2_tops_1(esk1_0,esk2_0))=k2_xboole_0(X1,k2_tops_1(esk1_0,esk2_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_153, c_0_154])).
% 3.65/3.82  cnf(c_0_165, negated_conjecture, (k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,k2_tops_1(esk1_0,esk2_0))))=k1_tops_1(esk1_0,esk2_0)), inference(rw,[status(thm)],[c_0_155, c_0_156])).
% 3.65/3.82  cnf(c_0_166, negated_conjecture, (m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_157, c_0_158]), c_0_122])])).
% 3.65/3.82  cnf(c_0_167, plain, (k7_subset_1(X1,X1,k5_xboole_0(k2_xboole_0(X1,X2),X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_159, c_0_105]), c_0_149]), c_0_152]), c_0_66]), c_0_105]), c_0_54]), c_0_160])).
% 3.65/3.82  cnf(c_0_168, plain, (k5_xboole_0(k2_xboole_0(X1,X2),X1)=k7_subset_1(X2,X2,X1)), inference(rw,[status(thm)],[c_0_161, c_0_160])).
% 3.65/3.82  cnf(c_0_169, plain, (k9_subset_1(X1,k2_xboole_0(X2,X1),X1)=X1), inference(spm,[status(thm)],[c_0_162, c_0_163])).
% 3.65/3.82  cnf(c_0_170, negated_conjecture, (k2_xboole_0(esk2_0,k2_tops_1(esk1_0,esk2_0))=k2_pre_topc(esk1_0,esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_164, c_0_122]), c_0_158])).
% 3.65/3.82  cnf(c_0_171, negated_conjecture, (k7_subset_1(esk2_0,esk2_0,k2_tops_1(esk1_0,esk2_0))=k1_tops_1(esk1_0,esk2_0)), inference(rw,[status(thm)],[c_0_165, c_0_91])).
% 3.65/3.82  cnf(c_0_172, plain, (k7_subset_1(X1,X2,X3)=k7_subset_1(X2,X2,X3)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_83, c_0_91])).
% 3.65/3.82  cnf(c_0_173, negated_conjecture, (m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_166, c_0_154])])).
% 3.65/3.82  fof(c_0_174, plain, ![X72, X73, X74]:(~l1_pre_topc(X72)|(~m1_subset_1(X73,k1_zfmisc_1(u1_struct_0(X72)))|(~m1_subset_1(X74,k1_zfmisc_1(u1_struct_0(X72)))|(~v3_pre_topc(X73,X72)|~r1_tarski(X73,X74)|r1_tarski(X73,k1_tops_1(X72,X74)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_tops_1])])])).
% 3.65/3.82  cnf(c_0_175, plain, (k7_subset_1(X1,X1,k7_subset_1(X2,X2,X1))=X1), inference(spm,[status(thm)],[c_0_167, c_0_168])).
% 3.65/3.82  cnf(c_0_176, plain, (k7_subset_1(X1,X2,X3)=k7_subset_1(X2,X2,X3)|~r1_tarski(X2,X1)), inference(rw,[status(thm)],[c_0_128, c_0_91])).
% 3.65/3.82  cnf(c_0_177, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1)))=k7_subset_1(X1,X1,X2)), inference(spm,[status(thm)],[c_0_91, c_0_54])).
% 3.65/3.82  cnf(c_0_178, negated_conjecture, (k1_setfam_1(k2_tarski(k2_tops_1(esk1_0,esk2_0),k2_pre_topc(esk1_0,esk2_0)))=k2_tops_1(esk1_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_169, c_0_170]), c_0_112]), c_0_54])).
% 3.65/3.82  cnf(c_0_179, negated_conjecture, (k5_xboole_0(k2_pre_topc(esk1_0,esk2_0),k2_tops_1(esk1_0,esk2_0))=k1_tops_1(esk1_0,esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_152, c_0_170]), c_0_171])).
% 3.65/3.82  cnf(c_0_180, negated_conjecture, (k7_subset_1(k2_pre_topc(esk1_0,esk2_0),k2_pre_topc(esk1_0,esk2_0),X1)=k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),X1)), inference(spm,[status(thm)],[c_0_172, c_0_173])).
% 3.65/3.82  cnf(c_0_181, negated_conjecture, (r1_tarski(k2_pre_topc(esk1_0,esk2_0),u1_struct_0(esk1_0))|~m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_47, c_0_166])).
% 3.65/3.82  cnf(c_0_182, negated_conjecture, (k7_subset_1(k2_tops_1(esk1_0,esk2_0),k2_tops_1(esk1_0,esk2_0),X1)=k7_subset_1(u1_struct_0(esk1_0),k2_tops_1(esk1_0,esk2_0),X1)), inference(spm,[status(thm)],[c_0_172, c_0_154])).
% 3.65/3.82  cnf(c_0_183, plain, (r1_tarski(X2,k1_tops_1(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v3_pre_topc(X2,X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_174])).
% 3.65/3.82  cnf(c_0_184, plain, (k7_subset_1(k2_xboole_0(X1,X2),k2_xboole_0(X1,X2),k7_subset_1(X2,X2,X1))=X1), inference(rw,[status(thm)],[c_0_159, c_0_175])).
% 3.65/3.82  cnf(c_0_185, negated_conjecture, (k2_xboole_0(esk2_0,k2_pre_topc(esk1_0,esk2_0))=k2_pre_topc(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_105, c_0_170])).
% 3.65/3.82  cnf(c_0_186, plain, (k7_subset_1(X1,X1,k7_subset_1(X2,X1,X3))=k1_setfam_1(k2_tarski(X1,X3))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_149, c_0_176])).
% 3.65/3.82  cnf(c_0_187, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),k2_tops_1(esk1_0,esk2_0))=k1_tops_1(esk1_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_177, c_0_178]), c_0_179]), c_0_180])).
% 3.65/3.82  cnf(c_0_188, negated_conjecture, (r1_tarski(k2_pre_topc(esk1_0,esk2_0),u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_181, c_0_131]), c_0_123]), c_0_122])])).
% 3.65/3.82  cnf(c_0_189, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),k1_tops_1(esk1_0,esk2_0))=k7_subset_1(u1_struct_0(esk1_0),k2_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk2_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_159, c_0_171]), c_0_66]), c_0_66]), c_0_170]), c_0_170]), c_0_180]), c_0_182])).
% 3.65/3.82  cnf(c_0_190, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_81]), c_0_53])).
% 3.65/3.82  fof(c_0_191, plain, ![X68, X69]:(~v2_pre_topc(X68)|~l1_pre_topc(X68)|~m1_subset_1(X69,k1_zfmisc_1(u1_struct_0(X68)))|v3_pre_topc(k1_tops_1(X68,X69),X68)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).
% 3.65/3.82  cnf(c_0_192, negated_conjecture, (r1_tarski(X1,k1_tops_1(esk1_0,esk2_0))|~v3_pre_topc(X1,esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_183, c_0_122]), c_0_123])])).
% 3.65/3.82  cnf(c_0_193, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0))=esk2_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_184, c_0_185]), c_0_180]), c_0_180])).
% 3.65/3.82  cnf(c_0_194, negated_conjecture, (v3_pre_topc(esk2_0,esk1_0)|k2_tops_1(esk1_0,esk2_0)=k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_108])).
% 3.65/3.82  cnf(c_0_195, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,esk2_0),esk2_0)), inference(spm,[status(thm)],[c_0_64, c_0_165])).
% 3.65/3.82  cnf(c_0_196, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k2_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk2_0))=k2_tops_1(esk1_0,esk2_0)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_186, c_0_187]), c_0_180]), c_0_54]), c_0_178]), c_0_188])]), c_0_189])).
% 3.65/3.82  cnf(c_0_197, plain, (k2_xboole_0(k2_xboole_0(X1,X2),k5_xboole_0(X2,k1_setfam_1(k2_tarski(X1,X2))))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_190, c_0_68]), c_0_66]), c_0_66]), c_0_68])).
% 3.65/3.82  cnf(c_0_198, negated_conjecture, (k2_xboole_0(k2_tops_1(esk1_0,esk2_0),k2_pre_topc(esk1_0,esk2_0))=k2_pre_topc(esk1_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_190, c_0_170]), c_0_66]), c_0_170])).
% 3.65/3.82  cnf(c_0_199, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k3_subset_1(X1,X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_109, c_0_116])).
% 3.65/3.82  cnf(c_0_200, negated_conjecture, (k1_setfam_1(k2_tarski(esk2_0,k2_pre_topc(esk1_0,esk2_0)))=esk2_0), inference(spm,[status(thm)],[c_0_160, c_0_170])).
% 3.65/3.82  cnf(c_0_201, negated_conjecture, (~v3_pre_topc(esk2_0,esk1_0)|k2_tops_1(esk1_0,esk2_0)!=k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_108])).
% 3.65/3.82  cnf(c_0_202, plain, (k7_subset_1(X1,X2,X3)=k7_subset_1(X4,X2,X3)|~r1_tarski(X2,X1)|~r1_tarski(X2,X4)), inference(spm,[status(thm)],[c_0_176, c_0_176])).
% 3.65/3.82  cnf(c_0_203, plain, (v3_pre_topc(k1_tops_1(X1,X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_191])).
% 3.65/3.82  cnf(c_0_204, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_108])).
% 3.65/3.82  cnf(c_0_205, negated_conjecture, (r1_tarski(esk2_0,k1_tops_1(esk1_0,esk2_0))|~v3_pre_topc(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_192, c_0_122]), c_0_70])])).
% 3.65/3.82  cnf(c_0_206, negated_conjecture, (k1_tops_1(esk1_0,esk2_0)=esk2_0|v3_pre_topc(esk2_0,esk1_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_193, c_0_194]), c_0_187])).
% 3.65/3.82  cnf(c_0_207, negated_conjecture, (k1_tops_1(esk1_0,esk2_0)=esk2_0|~r1_tarski(esk2_0,k1_tops_1(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_62, c_0_195])).
% 3.65/3.82  cnf(c_0_208, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),k1_tops_1(esk1_0,esk2_0))=k2_tops_1(esk1_0,esk2_0)), inference(rw,[status(thm)],[c_0_189, c_0_196])).
% 3.65/3.82  cnf(c_0_209, negated_conjecture, (k5_xboole_0(k2_xboole_0(k2_pre_topc(esk1_0,esk2_0),X1),X1)=k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),X1)), inference(spm,[status(thm)],[c_0_152, c_0_180])).
% 3.65/3.82  cnf(c_0_210, negated_conjecture, (k2_xboole_0(k1_tops_1(esk1_0,esk2_0),k2_pre_topc(esk1_0,esk2_0))=k2_pre_topc(esk1_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_197, c_0_178]), c_0_198]), c_0_179]), c_0_198]), c_0_66])).
% 3.65/3.82  cnf(c_0_211, plain, (k5_xboole_0(X1,k9_subset_1(X2,X1,X2))=k3_subset_1(X1,X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_199, c_0_112])).
% 3.65/3.82  cnf(c_0_212, negated_conjecture, (k9_subset_1(esk2_0,k2_pre_topc(esk1_0,esk2_0),esk2_0)=esk2_0), inference(rw,[status(thm)],[c_0_200, c_0_163])).
% 3.65/3.82  cnf(c_0_213, negated_conjecture, (r1_tarski(esk2_0,k2_pre_topc(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_130, c_0_170])).
% 3.65/3.82  cnf(c_0_214, negated_conjecture, (k7_subset_1(X1,k2_pre_topc(esk1_0,esk2_0),esk2_0)!=k2_tops_1(esk1_0,esk2_0)|~v3_pre_topc(esk2_0,esk1_0)|~r1_tarski(k2_pre_topc(esk1_0,esk2_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_201, c_0_202]), c_0_188])])).
% 3.65/3.82  cnf(c_0_215, plain, (k7_subset_1(X1,X1,X2)=k3_subset_1(X1,X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_199, c_0_91])).
% 3.65/3.82  cnf(c_0_216, negated_conjecture, (v3_pre_topc(k1_tops_1(esk1_0,esk2_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_203, c_0_122]), c_0_204]), c_0_123])])).
% 3.65/3.82  cnf(c_0_217, negated_conjecture, (k1_tops_1(esk1_0,esk2_0)=esk2_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_205, c_0_206]), c_0_207])).
% 3.65/3.82  cnf(c_0_218, negated_conjecture, (k5_xboole_0(k2_pre_topc(esk1_0,esk2_0),k1_tops_1(esk1_0,esk2_0))=k2_tops_1(esk1_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_208, c_0_209]), c_0_66]), c_0_210])).
% 3.65/3.82  cnf(c_0_219, negated_conjecture, (k5_xboole_0(k2_pre_topc(esk1_0,esk2_0),esk2_0)=k3_subset_1(k2_pre_topc(esk1_0,esk2_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_211, c_0_212]), c_0_213])])).
% 3.65/3.82  cnf(c_0_220, negated_conjecture, (k3_subset_1(k2_pre_topc(esk1_0,esk2_0),esk2_0)!=k2_tops_1(esk1_0,esk2_0)|~v3_pre_topc(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_214, c_0_215]), c_0_70]), c_0_213])])).
% 3.65/3.82  cnf(c_0_221, negated_conjecture, (v3_pre_topc(esk2_0,esk1_0)), inference(rw,[status(thm)],[c_0_216, c_0_217])).
% 3.65/3.82  cnf(c_0_222, negated_conjecture, (k3_subset_1(k2_pre_topc(esk1_0,esk2_0),esk2_0)=k2_tops_1(esk1_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_218, c_0_217]), c_0_219])).
% 3.65/3.82  cnf(c_0_223, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_220, c_0_221])]), c_0_222])]), ['proof']).
% 3.65/3.82  # SZS output end CNFRefutation
% 3.65/3.82  # Proof object total steps             : 224
% 3.65/3.82  # Proof object clause steps            : 161
% 3.65/3.82  # Proof object formula steps           : 63
% 3.65/3.82  # Proof object conjectures             : 53
% 3.65/3.82  # Proof object clause conjectures      : 50
% 3.65/3.82  # Proof object formula conjectures     : 3
% 3.65/3.82  # Proof object initial clauses used    : 38
% 3.65/3.82  # Proof object initial formulas used   : 31
% 3.65/3.82  # Proof object generating inferences   : 83
% 3.65/3.82  # Proof object simplifying inferences  : 157
% 3.65/3.82  # Training examples: 0 positive, 0 negative
% 3.65/3.82  # Parsed axioms                        : 36
% 3.65/3.82  # Removed by relevancy pruning/SinE    : 0
% 3.65/3.82  # Initial clauses                      : 44
% 3.65/3.82  # Removed in clause preprocessing      : 3
% 3.65/3.82  # Initial clauses in saturation        : 41
% 3.65/3.82  # Processed clauses                    : 38622
% 3.65/3.82  # ...of these trivial                  : 1296
% 3.65/3.82  # ...subsumed                          : 32646
% 3.65/3.82  # ...remaining for further processing  : 4679
% 3.65/3.82  # Other redundant clauses eliminated   : 2
% 3.65/3.82  # Clauses deleted for lack of memory   : 0
% 3.65/3.82  # Backward-subsumed                    : 241
% 3.65/3.82  # Backward-rewritten                   : 619
% 3.65/3.82  # Generated clauses                    : 393222
% 3.65/3.82  # ...of the previous two non-trivial   : 329629
% 3.65/3.82  # Contextual simplify-reflections      : 245
% 3.65/3.82  # Paramodulations                      : 393205
% 3.65/3.82  # Factorizations                       : 0
% 3.65/3.82  # Equation resolutions                 : 17
% 3.65/3.82  # Propositional unsat checks           : 0
% 3.65/3.82  #    Propositional check models        : 0
% 3.65/3.82  #    Propositional check unsatisfiable : 0
% 3.65/3.82  #    Propositional clauses             : 0
% 3.65/3.82  #    Propositional clauses after purity: 0
% 3.65/3.82  #    Propositional unsat core size     : 0
% 3.65/3.82  #    Propositional preprocessing time  : 0.000
% 3.65/3.82  #    Propositional encoding time       : 0.000
% 3.65/3.82  #    Propositional solver time         : 0.000
% 3.65/3.82  #    Success case prop preproc time    : 0.000
% 3.65/3.82  #    Success case prop encoding time   : 0.000
% 3.65/3.82  #    Success case prop solver time     : 0.000
% 3.65/3.82  # Current number of processed clauses  : 3777
% 3.65/3.82  #    Positive orientable unit clauses  : 748
% 3.65/3.82  #    Positive unorientable unit clauses: 14
% 3.65/3.82  #    Negative unit clauses             : 135
% 3.65/3.82  #    Non-unit-clauses                  : 2880
% 3.65/3.82  # Current number of unprocessed clauses: 288499
% 3.65/3.82  # ...number of literals in the above   : 901649
% 3.65/3.82  # Current number of archived formulas  : 0
% 3.65/3.82  # Current number of archived clauses   : 903
% 3.65/3.82  # Clause-clause subsumption calls (NU) : 1953196
% 3.65/3.82  # Rec. Clause-clause subsumption calls : 1232221
% 3.65/3.82  # Non-unit clause-clause subsumptions  : 13837
% 3.65/3.82  # Unit Clause-clause subsumption calls : 46133
% 3.65/3.82  # Rewrite failures with RHS unbound    : 0
% 3.65/3.82  # BW rewrite match attempts            : 9226
% 3.65/3.82  # BW rewrite match successes           : 636
% 3.65/3.82  # Condensation attempts                : 0
% 3.65/3.82  # Condensation successes               : 0
% 3.65/3.82  # Termbank termtop insertions          : 8422443
% 3.65/3.83  
% 3.65/3.83  # -------------------------------------------------
% 3.65/3.83  # User time                : 3.358 s
% 3.65/3.83  # System time              : 0.131 s
% 3.65/3.83  # Total time               : 3.489 s
% 3.65/3.83  # Maximum resident set size: 1604 pages
%------------------------------------------------------------------------------

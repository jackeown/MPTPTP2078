%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:11:15 EST 2020

% Result     : Theorem 32.21s
% Output     : CNFRefutation 32.21s
% Verified   : 
% Statistics : Number of formulae       :  169 (13789 expanded)
%              Number of clauses        :  116 (6523 expanded)
%              Number of leaves         :   26 (3596 expanded)
%              Depth                    :   25
%              Number of atoms          :  341 (19996 expanded)
%              Number of equality atoms :  108 (10712 expanded)
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

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t44_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X1,X2),X3)
     => r1_tarski(X1,k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

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

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(t76_tops_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

fof(t74_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k1_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(t32_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => k7_subset_1(X1,X2,X3) = k9_subset_1(X1,X2,k3_subset_1(X1,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

fof(t48_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(X2,k2_pre_topc(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

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

fof(l78_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(fc9_tops_1,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => v3_pre_topc(k1_tops_1(X1,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(c_0_26,plain,(
    ! [X8,X9] : k4_xboole_0(X8,X9) = k5_xboole_0(X8,k3_xboole_0(X8,X9)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_27,plain,(
    ! [X47,X48] : k1_setfam_1(k2_tarski(X47,X48)) = k3_xboole_0(X47,X48) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_28,plain,(
    ! [X49,X50] :
      ( ( ~ m1_subset_1(X49,k1_zfmisc_1(X50))
        | r1_tarski(X49,X50) )
      & ( ~ r1_tarski(X49,X50)
        | m1_subset_1(X49,k1_zfmisc_1(X50)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_29,plain,(
    ! [X46] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X46)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_30,plain,(
    ! [X17,X18] : r1_tarski(k4_xboole_0(X17,X18),X17) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_31,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_33,plain,(
    ! [X24,X25] : k4_xboole_0(X24,k4_xboole_0(X24,X25)) = k3_xboole_0(X24,X25) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_34,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | X6 != X7 )
      & ( r1_tarski(X7,X6)
        | X6 != X7 )
      & ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,X6)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_39,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_40,plain,(
    ! [X19,X20] : k2_xboole_0(X19,k4_xboole_0(X20,X19)) = k2_xboole_0(X19,X20) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_41,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_43,plain,
    ( r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X1) ),
    inference(rw,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_44,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))))) = k1_setfam_1(k2_tarski(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_32]),c_0_38]),c_0_38])).

fof(c_0_45,plain,(
    ! [X26,X27] : k2_tarski(X26,X27) = k2_tarski(X27,X26) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

fof(c_0_46,plain,(
    ! [X10,X11] :
      ( ~ r1_tarski(X10,X11)
      | k2_xboole_0(X10,X11) = X11 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_47,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_48,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_49,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_50,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_51,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_52,plain,
    ( k2_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_47,c_0_38])).

cnf(c_0_53,plain,
    ( k1_setfam_1(k2_tarski(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

fof(c_0_54,plain,(
    ! [X21,X22,X23] :
      ( ~ r1_tarski(k4_xboole_0(X21,X22),X23)
      | r1_tarski(X21,k2_xboole_0(X22,X23)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).

cnf(c_0_55,plain,
    ( r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))),X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_50])).

cnf(c_0_56,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k2_xboole_0(X2,X1)
    | ~ r1_tarski(X2,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_57,plain,
    ( k1_setfam_1(k2_tarski(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_53,c_0_50])).

cnf(c_0_58,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_59,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_60,plain,(
    ! [X28,X29] :
      ( ~ m1_subset_1(X29,k1_zfmisc_1(X28))
      | k3_subset_1(X28,X29) = k4_xboole_0(X28,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_61,plain,
    ( r1_tarski(k5_xboole_0(X1,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_53])).

cnf(c_0_62,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_42])])).

cnf(c_0_63,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X3) ),
    inference(rw,[status(thm)],[c_0_58,c_0_38])).

cnf(c_0_64,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_59])).

fof(c_0_65,plain,(
    ! [X15,X16] :
      ( ~ r1_tarski(X15,X16)
      | k3_xboole_0(X15,X16) = X15 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_66,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_67,plain,
    ( r1_tarski(k2_xboole_0(k1_xboole_0,X1),X1) ),
    inference(rw,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_68,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_52])).

cnf(c_0_69,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

fof(c_0_70,plain,(
    ! [X37,X38,X39] :
      ( ~ m1_subset_1(X38,k1_zfmisc_1(X37))
      | k7_subset_1(X37,X38,X39) = k4_xboole_0(X38,X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

fof(c_0_71,plain,(
    ! [X40,X41,X42] :
      ( ~ m1_subset_1(X42,k1_zfmisc_1(X40))
      | k9_subset_1(X40,X41,X42) = k3_xboole_0(X41,X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

fof(c_0_72,plain,(
    ! [X30,X31] :
      ( ~ m1_subset_1(X31,k1_zfmisc_1(X30))
      | m1_subset_1(k3_subset_1(X30,X31),k1_zfmisc_1(X30)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

cnf(c_0_73,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_66,c_0_38])).

cnf(c_0_74,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_67]),c_0_68])])).

cnf(c_0_75,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_76,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_69,c_0_32])).

cnf(c_0_77,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

fof(c_0_78,plain,(
    ! [X54,X55] :
      ( ~ l1_pre_topc(X54)
      | ~ m1_subset_1(X55,k1_zfmisc_1(u1_struct_0(X54)))
      | m1_subset_1(k2_pre_topc(X54,X55),k1_zfmisc_1(u1_struct_0(X54))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

fof(c_0_79,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v3_pre_topc(X2,X1)
            <=> k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t76_tops_1])).

cnf(c_0_80,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_81,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_82,plain,
    ( k3_subset_1(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_36]),c_0_57]),c_0_62]),c_0_74])).

cnf(c_0_83,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k3_subset_1(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_75])).

cnf(c_0_84,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_76,c_0_50])).

cnf(c_0_85,plain,
    ( k7_subset_1(X2,X1,X3) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_77,c_0_38])).

cnf(c_0_86,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

fof(c_0_87,negated_conjecture,
    ( v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & ( ~ v3_pre_topc(esk2_0,esk1_0)
      | k2_tops_1(esk1_0,esk2_0) != k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0) )
    & ( v3_pre_topc(esk2_0,esk1_0)
      | k2_tops_1(esk1_0,esk2_0) = k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_79])])])).

cnf(c_0_88,plain,
    ( k9_subset_1(X2,X3,X1) = k1_setfam_1(k2_tarski(X3,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_80,c_0_32])).

cnf(c_0_89,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_36])])).

fof(c_0_90,plain,(
    ! [X67,X68] :
      ( ~ l1_pre_topc(X67)
      | ~ m1_subset_1(X68,k1_zfmisc_1(u1_struct_0(X67)))
      | k1_tops_1(X67,X68) = k7_subset_1(u1_struct_0(X67),X68,k2_tops_1(X67,X68)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_tops_1])])])).

cnf(c_0_91,plain,
    ( k5_xboole_0(X1,X2) = k3_subset_1(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_92,plain,
    ( k7_subset_1(X1,X2,X3) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3)))
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_85,c_0_75])).

cnf(c_0_93,plain,
    ( r1_tarski(k2_pre_topc(X1,X2),u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_86])).

cnf(c_0_94,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

cnf(c_0_95,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

cnf(c_0_96,plain,
    ( k9_subset_1(X1,X2,X1) = k1_setfam_1(k2_tarski(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

fof(c_0_97,plain,(
    ! [X43,X44,X45] :
      ( ~ m1_subset_1(X44,k1_zfmisc_1(X43))
      | ~ m1_subset_1(X45,k1_zfmisc_1(X43))
      | k7_subset_1(X43,X44,X45) = k9_subset_1(X43,X44,k3_subset_1(X43,X45)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_subset_1])])])).

cnf(c_0_98,plain,
    ( k1_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_99,negated_conjecture,
    ( ~ v3_pre_topc(esk2_0,esk1_0)
    | k2_tops_1(esk1_0,esk2_0) != k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

cnf(c_0_100,plain,
    ( k7_subset_1(X1,X2,X3) = k3_subset_1(X2,k1_setfam_1(k2_tarski(X2,X3)))
    | ~ r1_tarski(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_49])])).

cnf(c_0_101,negated_conjecture,
    ( r1_tarski(k2_pre_topc(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_95])])).

cnf(c_0_102,plain,
    ( k9_subset_1(X1,X2,X1) = k1_setfam_1(k2_tarski(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_96,c_0_50])).

cnf(c_0_103,plain,
    ( k9_subset_1(X1,X2,X3) = k1_setfam_1(k2_tarski(X2,X3))
    | ~ r1_tarski(X3,X1) ),
    inference(spm,[status(thm)],[c_0_88,c_0_75])).

cnf(c_0_104,plain,
    ( k7_subset_1(X2,X1,X3) = k9_subset_1(X2,X1,k3_subset_1(X2,X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_97])).

fof(c_0_105,plain,(
    ! [X56,X57] :
      ( ~ l1_pre_topc(X56)
      | ~ m1_subset_1(X57,k1_zfmisc_1(u1_struct_0(X56)))
      | r1_tarski(X57,k2_pre_topc(X56,X57)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_pre_topc])])])).

cnf(c_0_106,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk2_0,k2_tops_1(esk1_0,esk2_0)) = k1_tops_1(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_94]),c_0_95])])).

cnf(c_0_107,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1) = k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1))) ),
    inference(spm,[status(thm)],[c_0_85,c_0_94])).

cnf(c_0_108,negated_conjecture,
    ( k3_subset_1(k2_pre_topc(esk1_0,esk2_0),k9_subset_1(esk2_0,k2_pre_topc(esk1_0,esk2_0),esk2_0)) != k2_tops_1(esk1_0,esk2_0)
    | ~ v3_pre_topc(esk2_0,esk1_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100]),c_0_101])]),c_0_50]),c_0_102])).

cnf(c_0_109,plain,
    ( k9_subset_1(X1,X2,X3) = k9_subset_1(X2,X3,X2)
    | ~ r1_tarski(X3,X1) ),
    inference(spm,[status(thm)],[c_0_103,c_0_102])).

cnf(c_0_110,plain,
    ( k7_subset_1(X1,X2,k1_xboole_0) = k9_subset_1(X1,X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_36]),c_0_82])).

cnf(c_0_111,plain,
    ( r1_tarski(X2,k2_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_105])).

fof(c_0_112,plain,(
    ! [X35,X36] :
      ( ~ m1_subset_1(X36,k1_zfmisc_1(X35))
      | k3_subset_1(X35,k3_subset_1(X35,X36)) = X36 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

cnf(c_0_113,negated_conjecture,
    ( k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,k2_tops_1(esk1_0,esk2_0)))) = k1_tops_1(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_106,c_0_107])).

cnf(c_0_114,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

fof(c_0_115,plain,(
    ! [X12,X13,X14] :
      ( ~ r1_tarski(X12,X13)
      | ~ r1_tarski(X13,X14)
      | r1_tarski(X12,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_116,plain,
    ( r1_tarski(k5_xboole_0(X1,X2),X1)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_76])).

cnf(c_0_117,negated_conjecture,
    ( k3_subset_1(k2_pre_topc(esk1_0,esk2_0),k9_subset_1(X1,esk2_0,k2_pre_topc(esk1_0,esk2_0))) != k2_tops_1(esk1_0,esk2_0)
    | ~ v3_pre_topc(esk2_0,esk1_0)
    | ~ r1_tarski(k2_pre_topc(esk1_0,esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_108,c_0_109])).

cnf(c_0_118,plain,
    ( k7_subset_1(X1,X2,k1_xboole_0) = k9_subset_1(X1,X2,X1)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_110,c_0_75])).

cnf(c_0_119,negated_conjecture,
    ( r1_tarski(esk2_0,k2_pre_topc(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_94]),c_0_95])])).

cnf(c_0_120,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_112])).

cnf(c_0_121,negated_conjecture,
    ( k5_xboole_0(esk2_0,k9_subset_1(esk2_0,k2_tops_1(esk1_0,esk2_0),esk2_0)) = k1_tops_1(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_113,c_0_102])).

cnf(c_0_122,plain,
    ( r1_tarski(k9_subset_1(X1,X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_114,c_0_96])).

cnf(c_0_123,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_115])).

cnf(c_0_124,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk2_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_113]),c_0_49])])).

cnf(c_0_125,negated_conjecture,
    ( k3_subset_1(k2_pre_topc(esk1_0,esk2_0),k7_subset_1(k2_pre_topc(esk1_0,esk2_0),esk2_0,k1_xboole_0)) != k2_tops_1(esk1_0,esk2_0)
    | ~ v3_pre_topc(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_118]),c_0_64]),c_0_119])])).

cnf(c_0_126,plain,
    ( k7_subset_1(X1,X2,X3) = k7_subset_1(X4,X2,X3)
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X2,X4) ),
    inference(spm,[status(thm)],[c_0_92,c_0_92])).

cnf(c_0_127,plain,
    ( k7_subset_1(X1,X2,X3) = k9_subset_1(X1,X2,k3_subset_1(X1,X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X3,X1) ),
    inference(spm,[status(thm)],[c_0_104,c_0_75])).

cnf(c_0_128,plain,
    ( k3_subset_1(X1,k3_subset_1(X1,X2)) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_120,c_0_75])).

cnf(c_0_129,negated_conjecture,
    ( k3_subset_1(esk2_0,k9_subset_1(esk2_0,k2_tops_1(esk1_0,esk2_0),esk2_0)) = k1_tops_1(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_121]),c_0_122])])).

fof(c_0_130,plain,(
    ! [X62,X63,X64] :
      ( ~ l1_pre_topc(X62)
      | ~ m1_subset_1(X63,k1_zfmisc_1(u1_struct_0(X62)))
      | ~ m1_subset_1(X64,k1_zfmisc_1(u1_struct_0(X62)))
      | ~ v3_pre_topc(X63,X62)
      | ~ r1_tarski(X63,X64)
      | r1_tarski(X63,k1_tops_1(X62,X64)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_tops_1])])])).

cnf(c_0_131,negated_conjecture,
    ( r1_tarski(X1,k2_pre_topc(esk1_0,esk2_0))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_123,c_0_119])).

cnf(c_0_132,negated_conjecture,
    ( r1_tarski(X1,esk2_0)
    | ~ r1_tarski(X1,k1_tops_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_123,c_0_124])).

cnf(c_0_133,negated_conjecture,
    ( k3_subset_1(k2_pre_topc(esk1_0,esk2_0),k7_subset_1(X1,esk2_0,k1_xboole_0)) != k2_tops_1(esk1_0,esk2_0)
    | ~ v3_pre_topc(esk2_0,esk1_0)
    | ~ r1_tarski(esk2_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_126]),c_0_119])])).

cnf(c_0_134,plain,
    ( k7_subset_1(X1,X2,X3) = k9_subset_1(X1,X2,k3_subset_1(X1,X3))
    | ~ r1_tarski(X3,X1)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_127,c_0_75])).

cnf(c_0_135,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))) = k1_setfam_1(k2_tarski(X1,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_84]),c_0_43])])).

cnf(c_0_136,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,X2)))) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_84])).

cnf(c_0_137,negated_conjecture,
    ( k9_subset_1(esk2_0,k2_tops_1(esk1_0,esk2_0),esk2_0) = k3_subset_1(esk2_0,k1_tops_1(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_129]),c_0_122])])).

cnf(c_0_138,plain,
    ( r1_tarski(k9_subset_1(X1,X2,X3),X3)
    | ~ r1_tarski(X3,X1) ),
    inference(spm,[status(thm)],[c_0_114,c_0_103])).

cnf(c_0_139,plain,
    ( r1_tarski(X2,k1_tops_1(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X2,X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_130])).

fof(c_0_140,plain,(
    ! [X60,X61] :
      ( ~ l1_pre_topc(X60)
      | ~ m1_subset_1(X61,k1_zfmisc_1(u1_struct_0(X60)))
      | k2_tops_1(X60,X61) = k7_subset_1(u1_struct_0(X60),k2_pre_topc(X60,X61),k1_tops_1(X60,X61)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l78_tops_1])])])).

cnf(c_0_141,negated_conjecture,
    ( r1_tarski(X1,k2_xboole_0(X2,k2_pre_topc(esk1_0,esk2_0)))
    | ~ r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),esk2_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_131])).

cnf(c_0_142,negated_conjecture,
    ( r1_tarski(k5_xboole_0(k1_tops_1(esk1_0,esk2_0),X1),esk2_0)
    | ~ r1_tarski(X1,k1_tops_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_132,c_0_116])).

cnf(c_0_143,negated_conjecture,
    ( k3_subset_1(k2_pre_topc(esk1_0,esk2_0),k9_subset_1(X1,esk2_0,X1)) != k2_tops_1(esk1_0,esk2_0)
    | ~ v3_pre_topc(esk2_0,esk1_0)
    | ~ r1_tarski(esk2_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_133,c_0_134]),c_0_82]),c_0_42])])).

cnf(c_0_144,plain,
    ( k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,X2))) = k5_xboole_0(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_135,c_0_136])).

cnf(c_0_145,negated_conjecture,
    ( k5_xboole_0(esk2_0,k3_subset_1(esk2_0,k1_tops_1(esk1_0,esk2_0))) = k1_tops_1(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_121,c_0_137])).

cnf(c_0_146,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk2_0,k1_tops_1(esk1_0,esk2_0)),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_137]),c_0_64])])).

cnf(c_0_147,negated_conjecture,
    ( r1_tarski(X1,k1_tops_1(esk1_0,esk2_0))
    | ~ v3_pre_topc(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_139,c_0_94]),c_0_95])])).

cnf(c_0_148,plain,
    ( k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_140])).

cnf(c_0_149,plain,
    ( k7_subset_1(X1,X2,X3) = k3_subset_1(X2,X3)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_83,c_0_92])).

cnf(c_0_150,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk2_0),k2_xboole_0(X1,k2_pre_topc(esk1_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_141,c_0_142]),c_0_102]),c_0_122])])).

cnf(c_0_151,negated_conjecture,
    ( v3_pre_topc(esk2_0,esk1_0)
    | k2_tops_1(esk1_0,esk2_0) = k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

cnf(c_0_152,negated_conjecture,
    ( k3_subset_1(k2_pre_topc(esk1_0,esk2_0),k9_subset_1(esk2_0,X1,esk2_0)) != k2_tops_1(esk1_0,esk2_0)
    | ~ v3_pre_topc(esk2_0,esk1_0)
    | ~ r1_tarski(esk2_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_103]),c_0_102]),c_0_64])])).

cnf(c_0_153,negated_conjecture,
    ( k9_subset_1(esk2_0,k1_tops_1(esk1_0,esk2_0),esk2_0) = k1_tops_1(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_144,c_0_145]),c_0_102]),c_0_146])])).

cnf(c_0_154,negated_conjecture,
    ( r1_tarski(esk2_0,k1_tops_1(esk1_0,esk2_0))
    | ~ v3_pre_topc(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_147,c_0_94]),c_0_64])])).

cnf(c_0_155,plain,
    ( k3_subset_1(k2_pre_topc(X1,X2),k1_tops_1(X1,X2)) = k2_tops_1(X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k1_tops_1(X1,X2),k2_pre_topc(X1,X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_148,c_0_149]),c_0_93])).

cnf(c_0_156,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk2_0),k2_pre_topc(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_150,c_0_74])).

cnf(c_0_157,negated_conjecture,
    ( k3_subset_1(k2_pre_topc(esk1_0,esk2_0),esk2_0) = k2_tops_1(esk1_0,esk2_0)
    | v3_pre_topc(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_151,c_0_149]),c_0_119]),c_0_101])])).

cnf(c_0_158,negated_conjecture,
    ( k3_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_tops_1(esk1_0,esk2_0)) != k2_tops_1(esk1_0,esk2_0)
    | ~ v3_pre_topc(esk2_0,esk1_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_152,c_0_153]),c_0_154])).

cnf(c_0_159,negated_conjecture,
    ( k3_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_tops_1(esk1_0,esk2_0)) = k2_tops_1(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_155,c_0_94]),c_0_95]),c_0_156])])).

fof(c_0_160,plain,(
    ! [X58,X59] :
      ( ~ v2_pre_topc(X58)
      | ~ l1_pre_topc(X58)
      | ~ m1_subset_1(X59,k1_zfmisc_1(u1_struct_0(X58)))
      | v3_pre_topc(k1_tops_1(X58,X59),X58) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).

cnf(c_0_161,negated_conjecture,
    ( k3_subset_1(k2_pre_topc(esk1_0,esk2_0),k2_tops_1(esk1_0,esk2_0)) = esk2_0
    | v3_pre_topc(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_157]),c_0_119])])).

cnf(c_0_162,negated_conjecture,
    ( ~ v3_pre_topc(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_158,c_0_159])])).

cnf(c_0_163,plain,
    ( v3_pre_topc(k1_tops_1(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_160])).

cnf(c_0_164,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

cnf(c_0_165,negated_conjecture,
    ( k3_subset_1(k2_pre_topc(esk1_0,esk2_0),k2_tops_1(esk1_0,esk2_0)) = esk2_0 ),
    inference(sr,[status(thm)],[c_0_161,c_0_162])).

cnf(c_0_166,negated_conjecture,
    ( v3_pre_topc(k1_tops_1(esk1_0,esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_163,c_0_94]),c_0_164]),c_0_95])])).

cnf(c_0_167,negated_conjecture,
    ( k1_tops_1(esk1_0,esk2_0) = esk2_0 ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_159]),c_0_156])]),c_0_165])).

cnf(c_0_168,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_166,c_0_167]),c_0_162]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:13:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 32.21/32.38  # AutoSched0-Mode selected heuristic G_E___107_C36_F1_PI_AE_Q4_CS_SP_PS_S0Y
% 32.21/32.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 32.21/32.38  #
% 32.21/32.38  # Preprocessing time       : 0.032 s
% 32.21/32.38  # Presaturation interreduction done
% 32.21/32.38  
% 32.21/32.38  # Proof found!
% 32.21/32.38  # SZS status Theorem
% 32.21/32.38  # SZS output start CNFRefutation
% 32.21/32.38  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 32.21/32.38  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 32.21/32.38  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 32.21/32.38  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 32.21/32.38  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 32.21/32.38  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 32.21/32.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 32.21/32.38  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 32.21/32.38  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 32.21/32.38  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 32.21/32.38  fof(t44_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k4_xboole_0(X1,X2),X3)=>r1_tarski(X1,k2_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 32.21/32.38  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 32.21/32.38  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 32.21/32.38  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 32.21/32.38  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 32.21/32.38  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 32.21/32.38  fof(dt_k2_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 32.21/32.38  fof(t76_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_tops_1)).
% 32.21/32.38  fof(t74_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k1_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 32.21/32.38  fof(t32_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k9_subset_1(X1,X2,k3_subset_1(X1,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_subset_1)).
% 32.21/32.38  fof(t48_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(X2,k2_pre_topc(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_pre_topc)).
% 32.21/32.38  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 32.21/32.38  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 32.21/32.38  fof(t56_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v3_pre_topc(X2,X1)&r1_tarski(X2,X3))=>r1_tarski(X2,k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tops_1)).
% 32.21/32.38  fof(l78_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 32.21/32.38  fof(fc9_tops_1, axiom, ![X1, X2]:(((v2_pre_topc(X1)&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v3_pre_topc(k1_tops_1(X1,X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 32.21/32.38  fof(c_0_26, plain, ![X8, X9]:k4_xboole_0(X8,X9)=k5_xboole_0(X8,k3_xboole_0(X8,X9)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 32.21/32.38  fof(c_0_27, plain, ![X47, X48]:k1_setfam_1(k2_tarski(X47,X48))=k3_xboole_0(X47,X48), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 32.21/32.38  fof(c_0_28, plain, ![X49, X50]:((~m1_subset_1(X49,k1_zfmisc_1(X50))|r1_tarski(X49,X50))&(~r1_tarski(X49,X50)|m1_subset_1(X49,k1_zfmisc_1(X50)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 32.21/32.38  fof(c_0_29, plain, ![X46]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X46)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 32.21/32.38  fof(c_0_30, plain, ![X17, X18]:r1_tarski(k4_xboole_0(X17,X18),X17), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 32.21/32.38  cnf(c_0_31, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 32.21/32.38  cnf(c_0_32, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 32.21/32.38  fof(c_0_33, plain, ![X24, X25]:k4_xboole_0(X24,k4_xboole_0(X24,X25))=k3_xboole_0(X24,X25), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 32.21/32.38  fof(c_0_34, plain, ![X6, X7]:(((r1_tarski(X6,X7)|X6!=X7)&(r1_tarski(X7,X6)|X6!=X7))&(~r1_tarski(X6,X7)|~r1_tarski(X7,X6)|X6=X7)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 32.21/32.38  cnf(c_0_35, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 32.21/32.38  cnf(c_0_36, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 32.21/32.38  cnf(c_0_37, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 32.21/32.38  cnf(c_0_38, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_31, c_0_32])).
% 32.21/32.38  cnf(c_0_39, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 32.21/32.38  fof(c_0_40, plain, ![X19, X20]:k2_xboole_0(X19,k4_xboole_0(X20,X19))=k2_xboole_0(X19,X20), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 32.21/32.38  cnf(c_0_41, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 32.21/32.38  cnf(c_0_42, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 32.21/32.38  cnf(c_0_43, plain, (r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X1)), inference(rw,[status(thm)],[c_0_37, c_0_38])).
% 32.21/32.38  cnf(c_0_44, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))))))=k1_setfam_1(k2_tarski(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_32]), c_0_38]), c_0_38])).
% 32.21/32.38  fof(c_0_45, plain, ![X26, X27]:k2_tarski(X26,X27)=k2_tarski(X27,X26), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 32.21/32.38  fof(c_0_46, plain, ![X10, X11]:(~r1_tarski(X10,X11)|k2_xboole_0(X10,X11)=X11), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 32.21/32.38  cnf(c_0_47, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 32.21/32.38  cnf(c_0_48, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 32.21/32.38  cnf(c_0_49, plain, (r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X1)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 32.21/32.38  cnf(c_0_50, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 32.21/32.38  cnf(c_0_51, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 32.21/32.38  cnf(c_0_52, plain, (k2_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1))))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_47, c_0_38])).
% 32.21/32.38  cnf(c_0_53, plain, (k1_setfam_1(k2_tarski(k1_xboole_0,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 32.21/32.38  fof(c_0_54, plain, ![X21, X22, X23]:(~r1_tarski(k4_xboole_0(X21,X22),X23)|r1_tarski(X21,k2_xboole_0(X22,X23))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).
% 32.21/32.38  cnf(c_0_55, plain, (r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))),X1)), inference(spm,[status(thm)],[c_0_43, c_0_50])).
% 32.21/32.38  cnf(c_0_56, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k2_xboole_0(X2,X1)|~r1_tarski(X2,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 32.21/32.38  cnf(c_0_57, plain, (k1_setfam_1(k2_tarski(X1,k1_xboole_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_53, c_0_50])).
% 32.21/32.38  cnf(c_0_58, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 32.21/32.38  cnf(c_0_59, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_34])).
% 32.21/32.38  fof(c_0_60, plain, ![X28, X29]:(~m1_subset_1(X29,k1_zfmisc_1(X28))|k3_subset_1(X28,X29)=k4_xboole_0(X28,X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 32.21/32.38  cnf(c_0_61, plain, (r1_tarski(k5_xboole_0(X1,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_55, c_0_53])).
% 32.21/32.38  cnf(c_0_62, plain, (k5_xboole_0(X1,k1_xboole_0)=k2_xboole_0(k1_xboole_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_42])])).
% 32.21/32.38  cnf(c_0_63, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X3)), inference(rw,[status(thm)],[c_0_58, c_0_38])).
% 32.21/32.38  cnf(c_0_64, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_59])).
% 32.21/32.38  fof(c_0_65, plain, ![X15, X16]:(~r1_tarski(X15,X16)|k3_xboole_0(X15,X16)=X15), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 32.21/32.38  cnf(c_0_66, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 32.21/32.38  cnf(c_0_67, plain, (r1_tarski(k2_xboole_0(k1_xboole_0,X1),X1)), inference(rw,[status(thm)],[c_0_61, c_0_62])).
% 32.21/32.38  cnf(c_0_68, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_52])).
% 32.21/32.38  cnf(c_0_69, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 32.21/32.38  fof(c_0_70, plain, ![X37, X38, X39]:(~m1_subset_1(X38,k1_zfmisc_1(X37))|k7_subset_1(X37,X38,X39)=k4_xboole_0(X38,X39)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 32.21/32.38  fof(c_0_71, plain, ![X40, X41, X42]:(~m1_subset_1(X42,k1_zfmisc_1(X40))|k9_subset_1(X40,X41,X42)=k3_xboole_0(X41,X42)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 32.21/32.38  fof(c_0_72, plain, ![X30, X31]:(~m1_subset_1(X31,k1_zfmisc_1(X30))|m1_subset_1(k3_subset_1(X30,X31),k1_zfmisc_1(X30))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 32.21/32.38  cnf(c_0_73, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_66, c_0_38])).
% 32.21/32.38  cnf(c_0_74, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_67]), c_0_68])])).
% 32.21/32.38  cnf(c_0_75, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 32.21/32.38  cnf(c_0_76, plain, (k1_setfam_1(k2_tarski(X1,X2))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_69, c_0_32])).
% 32.21/32.38  cnf(c_0_77, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_70])).
% 32.21/32.38  fof(c_0_78, plain, ![X54, X55]:(~l1_pre_topc(X54)|~m1_subset_1(X55,k1_zfmisc_1(u1_struct_0(X54)))|m1_subset_1(k2_pre_topc(X54,X55),k1_zfmisc_1(u1_struct_0(X54)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).
% 32.21/32.38  fof(c_0_79, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2))))), inference(assume_negation,[status(cth)],[t76_tops_1])).
% 32.21/32.38  cnf(c_0_80, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_71])).
% 32.21/32.38  cnf(c_0_81, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_72])).
% 32.21/32.38  cnf(c_0_82, plain, (k3_subset_1(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_36]), c_0_57]), c_0_62]), c_0_74])).
% 32.21/32.38  cnf(c_0_83, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k3_subset_1(X1,X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_73, c_0_75])).
% 32.21/32.38  cnf(c_0_84, plain, (k1_setfam_1(k2_tarski(X1,X2))=X2|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_76, c_0_50])).
% 32.21/32.38  cnf(c_0_85, plain, (k7_subset_1(X2,X1,X3)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_77, c_0_38])).
% 32.21/32.38  cnf(c_0_86, plain, (m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_78])).
% 32.21/32.38  fof(c_0_87, negated_conjecture, ((v2_pre_topc(esk1_0)&l1_pre_topc(esk1_0))&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&((~v3_pre_topc(esk2_0,esk1_0)|k2_tops_1(esk1_0,esk2_0)!=k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0))&(v3_pre_topc(esk2_0,esk1_0)|k2_tops_1(esk1_0,esk2_0)=k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_79])])])).
% 32.21/32.38  cnf(c_0_88, plain, (k9_subset_1(X2,X3,X1)=k1_setfam_1(k2_tarski(X3,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_80, c_0_32])).
% 32.21/32.38  cnf(c_0_89, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_36])])).
% 32.21/32.38  fof(c_0_90, plain, ![X67, X68]:(~l1_pre_topc(X67)|(~m1_subset_1(X68,k1_zfmisc_1(u1_struct_0(X67)))|k1_tops_1(X67,X68)=k7_subset_1(u1_struct_0(X67),X68,k2_tops_1(X67,X68)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_tops_1])])])).
% 32.21/32.38  cnf(c_0_91, plain, (k5_xboole_0(X1,X2)=k3_subset_1(X1,X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 32.21/32.38  cnf(c_0_92, plain, (k7_subset_1(X1,X2,X3)=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3)))|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_85, c_0_75])).
% 32.21/32.38  cnf(c_0_93, plain, (r1_tarski(k2_pre_topc(X1,X2),u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_35, c_0_86])).
% 32.21/32.38  cnf(c_0_94, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_87])).
% 32.21/32.38  cnf(c_0_95, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_87])).
% 32.21/32.38  cnf(c_0_96, plain, (k9_subset_1(X1,X2,X1)=k1_setfam_1(k2_tarski(X2,X1))), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 32.21/32.38  fof(c_0_97, plain, ![X43, X44, X45]:(~m1_subset_1(X44,k1_zfmisc_1(X43))|(~m1_subset_1(X45,k1_zfmisc_1(X43))|k7_subset_1(X43,X44,X45)=k9_subset_1(X43,X44,k3_subset_1(X43,X45)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_subset_1])])])).
% 32.21/32.38  cnf(c_0_98, plain, (k1_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_90])).
% 32.21/32.38  cnf(c_0_99, negated_conjecture, (~v3_pre_topc(esk2_0,esk1_0)|k2_tops_1(esk1_0,esk2_0)!=k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_87])).
% 32.21/32.38  cnf(c_0_100, plain, (k7_subset_1(X1,X2,X3)=k3_subset_1(X2,k1_setfam_1(k2_tarski(X2,X3)))|~r1_tarski(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_49])])).
% 32.21/32.38  cnf(c_0_101, negated_conjecture, (r1_tarski(k2_pre_topc(esk1_0,esk2_0),u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_95])])).
% 32.21/32.38  cnf(c_0_102, plain, (k9_subset_1(X1,X2,X1)=k1_setfam_1(k2_tarski(X1,X2))), inference(spm,[status(thm)],[c_0_96, c_0_50])).
% 32.21/32.38  cnf(c_0_103, plain, (k9_subset_1(X1,X2,X3)=k1_setfam_1(k2_tarski(X2,X3))|~r1_tarski(X3,X1)), inference(spm,[status(thm)],[c_0_88, c_0_75])).
% 32.21/32.38  cnf(c_0_104, plain, (k7_subset_1(X2,X1,X3)=k9_subset_1(X2,X1,k3_subset_1(X2,X3))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_97])).
% 32.21/32.38  fof(c_0_105, plain, ![X56, X57]:(~l1_pre_topc(X56)|(~m1_subset_1(X57,k1_zfmisc_1(u1_struct_0(X56)))|r1_tarski(X57,k2_pre_topc(X56,X57)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_pre_topc])])])).
% 32.21/32.38  cnf(c_0_106, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk2_0,k2_tops_1(esk1_0,esk2_0))=k1_tops_1(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_94]), c_0_95])])).
% 32.21/32.38  cnf(c_0_107, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)=k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,X1)))), inference(spm,[status(thm)],[c_0_85, c_0_94])).
% 32.21/32.38  cnf(c_0_108, negated_conjecture, (k3_subset_1(k2_pre_topc(esk1_0,esk2_0),k9_subset_1(esk2_0,k2_pre_topc(esk1_0,esk2_0),esk2_0))!=k2_tops_1(esk1_0,esk2_0)|~v3_pre_topc(esk2_0,esk1_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_100]), c_0_101])]), c_0_50]), c_0_102])).
% 32.21/32.38  cnf(c_0_109, plain, (k9_subset_1(X1,X2,X3)=k9_subset_1(X2,X3,X2)|~r1_tarski(X3,X1)), inference(spm,[status(thm)],[c_0_103, c_0_102])).
% 32.21/32.38  cnf(c_0_110, plain, (k7_subset_1(X1,X2,k1_xboole_0)=k9_subset_1(X1,X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_36]), c_0_82])).
% 32.21/32.38  cnf(c_0_111, plain, (r1_tarski(X2,k2_pre_topc(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_105])).
% 32.21/32.38  fof(c_0_112, plain, ![X35, X36]:(~m1_subset_1(X36,k1_zfmisc_1(X35))|k3_subset_1(X35,k3_subset_1(X35,X36))=X36), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 32.21/32.38  cnf(c_0_113, negated_conjecture, (k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,k2_tops_1(esk1_0,esk2_0))))=k1_tops_1(esk1_0,esk2_0)), inference(rw,[status(thm)],[c_0_106, c_0_107])).
% 32.21/32.38  cnf(c_0_114, plain, (r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 32.21/32.38  fof(c_0_115, plain, ![X12, X13, X14]:(~r1_tarski(X12,X13)|~r1_tarski(X13,X14)|r1_tarski(X12,X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 32.21/32.38  cnf(c_0_116, plain, (r1_tarski(k5_xboole_0(X1,X2),X1)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_55, c_0_76])).
% 32.21/32.38  cnf(c_0_117, negated_conjecture, (k3_subset_1(k2_pre_topc(esk1_0,esk2_0),k9_subset_1(X1,esk2_0,k2_pre_topc(esk1_0,esk2_0)))!=k2_tops_1(esk1_0,esk2_0)|~v3_pre_topc(esk2_0,esk1_0)|~r1_tarski(k2_pre_topc(esk1_0,esk2_0),X1)), inference(spm,[status(thm)],[c_0_108, c_0_109])).
% 32.21/32.38  cnf(c_0_118, plain, (k7_subset_1(X1,X2,k1_xboole_0)=k9_subset_1(X1,X2,X1)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_110, c_0_75])).
% 32.21/32.38  cnf(c_0_119, negated_conjecture, (r1_tarski(esk2_0,k2_pre_topc(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_94]), c_0_95])])).
% 32.21/32.38  cnf(c_0_120, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_112])).
% 32.21/32.38  cnf(c_0_121, negated_conjecture, (k5_xboole_0(esk2_0,k9_subset_1(esk2_0,k2_tops_1(esk1_0,esk2_0),esk2_0))=k1_tops_1(esk1_0,esk2_0)), inference(rw,[status(thm)],[c_0_113, c_0_102])).
% 32.21/32.38  cnf(c_0_122, plain, (r1_tarski(k9_subset_1(X1,X2,X1),X1)), inference(spm,[status(thm)],[c_0_114, c_0_96])).
% 32.21/32.38  cnf(c_0_123, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_115])).
% 32.21/32.38  cnf(c_0_124, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,esk2_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_113]), c_0_49])])).
% 32.21/32.38  cnf(c_0_125, negated_conjecture, (k3_subset_1(k2_pre_topc(esk1_0,esk2_0),k7_subset_1(k2_pre_topc(esk1_0,esk2_0),esk2_0,k1_xboole_0))!=k2_tops_1(esk1_0,esk2_0)|~v3_pre_topc(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_118]), c_0_64]), c_0_119])])).
% 32.21/32.38  cnf(c_0_126, plain, (k7_subset_1(X1,X2,X3)=k7_subset_1(X4,X2,X3)|~r1_tarski(X2,X1)|~r1_tarski(X2,X4)), inference(spm,[status(thm)],[c_0_92, c_0_92])).
% 32.21/32.38  cnf(c_0_127, plain, (k7_subset_1(X1,X2,X3)=k9_subset_1(X1,X2,k3_subset_1(X1,X3))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X3,X1)), inference(spm,[status(thm)],[c_0_104, c_0_75])).
% 32.21/32.38  cnf(c_0_128, plain, (k3_subset_1(X1,k3_subset_1(X1,X2))=X2|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_120, c_0_75])).
% 32.21/32.38  cnf(c_0_129, negated_conjecture, (k3_subset_1(esk2_0,k9_subset_1(esk2_0,k2_tops_1(esk1_0,esk2_0),esk2_0))=k1_tops_1(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_121]), c_0_122])])).
% 32.21/32.38  fof(c_0_130, plain, ![X62, X63, X64]:(~l1_pre_topc(X62)|(~m1_subset_1(X63,k1_zfmisc_1(u1_struct_0(X62)))|(~m1_subset_1(X64,k1_zfmisc_1(u1_struct_0(X62)))|(~v3_pre_topc(X63,X62)|~r1_tarski(X63,X64)|r1_tarski(X63,k1_tops_1(X62,X64)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_tops_1])])])).
% 32.21/32.38  cnf(c_0_131, negated_conjecture, (r1_tarski(X1,k2_pre_topc(esk1_0,esk2_0))|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_123, c_0_119])).
% 32.21/32.38  cnf(c_0_132, negated_conjecture, (r1_tarski(X1,esk2_0)|~r1_tarski(X1,k1_tops_1(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_123, c_0_124])).
% 32.21/32.38  cnf(c_0_133, negated_conjecture, (k3_subset_1(k2_pre_topc(esk1_0,esk2_0),k7_subset_1(X1,esk2_0,k1_xboole_0))!=k2_tops_1(esk1_0,esk2_0)|~v3_pre_topc(esk2_0,esk1_0)|~r1_tarski(esk2_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125, c_0_126]), c_0_119])])).
% 32.21/32.38  cnf(c_0_134, plain, (k7_subset_1(X1,X2,X3)=k9_subset_1(X1,X2,k3_subset_1(X1,X3))|~r1_tarski(X3,X1)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_127, c_0_75])).
% 32.21/32.38  cnf(c_0_135, plain, (k5_xboole_0(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))))=k1_setfam_1(k2_tarski(X1,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_84]), c_0_43])])).
% 32.21/32.38  cnf(c_0_136, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,X2))))=X2|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_44, c_0_84])).
% 32.21/32.38  cnf(c_0_137, negated_conjecture, (k9_subset_1(esk2_0,k2_tops_1(esk1_0,esk2_0),esk2_0)=k3_subset_1(esk2_0,k1_tops_1(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_129]), c_0_122])])).
% 32.21/32.38  cnf(c_0_138, plain, (r1_tarski(k9_subset_1(X1,X2,X3),X3)|~r1_tarski(X3,X1)), inference(spm,[status(thm)],[c_0_114, c_0_103])).
% 32.21/32.38  cnf(c_0_139, plain, (r1_tarski(X2,k1_tops_1(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v3_pre_topc(X2,X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_130])).
% 32.21/32.38  fof(c_0_140, plain, ![X60, X61]:(~l1_pre_topc(X60)|(~m1_subset_1(X61,k1_zfmisc_1(u1_struct_0(X60)))|k2_tops_1(X60,X61)=k7_subset_1(u1_struct_0(X60),k2_pre_topc(X60,X61),k1_tops_1(X60,X61)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l78_tops_1])])])).
% 32.21/32.38  cnf(c_0_141, negated_conjecture, (r1_tarski(X1,k2_xboole_0(X2,k2_pre_topc(esk1_0,esk2_0)))|~r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),esk2_0)), inference(spm,[status(thm)],[c_0_63, c_0_131])).
% 32.21/32.38  cnf(c_0_142, negated_conjecture, (r1_tarski(k5_xboole_0(k1_tops_1(esk1_0,esk2_0),X1),esk2_0)|~r1_tarski(X1,k1_tops_1(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_132, c_0_116])).
% 32.21/32.38  cnf(c_0_143, negated_conjecture, (k3_subset_1(k2_pre_topc(esk1_0,esk2_0),k9_subset_1(X1,esk2_0,X1))!=k2_tops_1(esk1_0,esk2_0)|~v3_pre_topc(esk2_0,esk1_0)|~r1_tarski(esk2_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_133, c_0_134]), c_0_82]), c_0_42])])).
% 32.21/32.38  cnf(c_0_144, plain, (k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,X2)))=k5_xboole_0(X1,X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_135, c_0_136])).
% 32.21/32.38  cnf(c_0_145, negated_conjecture, (k5_xboole_0(esk2_0,k3_subset_1(esk2_0,k1_tops_1(esk1_0,esk2_0)))=k1_tops_1(esk1_0,esk2_0)), inference(rw,[status(thm)],[c_0_121, c_0_137])).
% 32.21/32.38  cnf(c_0_146, negated_conjecture, (r1_tarski(k3_subset_1(esk2_0,k1_tops_1(esk1_0,esk2_0)),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_137]), c_0_64])])).
% 32.21/32.38  cnf(c_0_147, negated_conjecture, (r1_tarski(X1,k1_tops_1(esk1_0,esk2_0))|~v3_pre_topc(X1,esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_139, c_0_94]), c_0_95])])).
% 32.21/32.38  cnf(c_0_148, plain, (k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_140])).
% 32.21/32.38  cnf(c_0_149, plain, (k7_subset_1(X1,X2,X3)=k3_subset_1(X2,X3)|~r1_tarski(X3,X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_83, c_0_92])).
% 32.21/32.38  cnf(c_0_150, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,esk2_0),k2_xboole_0(X1,k2_pre_topc(esk1_0,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_141, c_0_142]), c_0_102]), c_0_122])])).
% 32.21/32.38  cnf(c_0_151, negated_conjecture, (v3_pre_topc(esk2_0,esk1_0)|k2_tops_1(esk1_0,esk2_0)=k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_87])).
% 32.21/32.38  cnf(c_0_152, negated_conjecture, (k3_subset_1(k2_pre_topc(esk1_0,esk2_0),k9_subset_1(esk2_0,X1,esk2_0))!=k2_tops_1(esk1_0,esk2_0)|~v3_pre_topc(esk2_0,esk1_0)|~r1_tarski(esk2_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143, c_0_103]), c_0_102]), c_0_64])])).
% 32.21/32.38  cnf(c_0_153, negated_conjecture, (k9_subset_1(esk2_0,k1_tops_1(esk1_0,esk2_0),esk2_0)=k1_tops_1(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_144, c_0_145]), c_0_102]), c_0_146])])).
% 32.21/32.38  cnf(c_0_154, negated_conjecture, (r1_tarski(esk2_0,k1_tops_1(esk1_0,esk2_0))|~v3_pre_topc(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_147, c_0_94]), c_0_64])])).
% 32.21/32.38  cnf(c_0_155, plain, (k3_subset_1(k2_pre_topc(X1,X2),k1_tops_1(X1,X2))=k2_tops_1(X1,X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k1_tops_1(X1,X2),k2_pre_topc(X1,X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_148, c_0_149]), c_0_93])).
% 32.21/32.38  cnf(c_0_156, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,esk2_0),k2_pre_topc(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_150, c_0_74])).
% 32.21/32.38  cnf(c_0_157, negated_conjecture, (k3_subset_1(k2_pre_topc(esk1_0,esk2_0),esk2_0)=k2_tops_1(esk1_0,esk2_0)|v3_pre_topc(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_151, c_0_149]), c_0_119]), c_0_101])])).
% 32.21/32.38  cnf(c_0_158, negated_conjecture, (k3_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_tops_1(esk1_0,esk2_0))!=k2_tops_1(esk1_0,esk2_0)|~v3_pre_topc(esk2_0,esk1_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_152, c_0_153]), c_0_154])).
% 32.21/32.38  cnf(c_0_159, negated_conjecture, (k3_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_tops_1(esk1_0,esk2_0))=k2_tops_1(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_155, c_0_94]), c_0_95]), c_0_156])])).
% 32.21/32.38  fof(c_0_160, plain, ![X58, X59]:(~v2_pre_topc(X58)|~l1_pre_topc(X58)|~m1_subset_1(X59,k1_zfmisc_1(u1_struct_0(X58)))|v3_pre_topc(k1_tops_1(X58,X59),X58)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).
% 32.21/32.38  cnf(c_0_161, negated_conjecture, (k3_subset_1(k2_pre_topc(esk1_0,esk2_0),k2_tops_1(esk1_0,esk2_0))=esk2_0|v3_pre_topc(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_157]), c_0_119])])).
% 32.21/32.38  cnf(c_0_162, negated_conjecture, (~v3_pre_topc(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_158, c_0_159])])).
% 32.21/32.38  cnf(c_0_163, plain, (v3_pre_topc(k1_tops_1(X1,X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_160])).
% 32.21/32.38  cnf(c_0_164, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_87])).
% 32.21/32.38  cnf(c_0_165, negated_conjecture, (k3_subset_1(k2_pre_topc(esk1_0,esk2_0),k2_tops_1(esk1_0,esk2_0))=esk2_0), inference(sr,[status(thm)],[c_0_161, c_0_162])).
% 32.21/32.38  cnf(c_0_166, negated_conjecture, (v3_pre_topc(k1_tops_1(esk1_0,esk2_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_163, c_0_94]), c_0_164]), c_0_95])])).
% 32.21/32.38  cnf(c_0_167, negated_conjecture, (k1_tops_1(esk1_0,esk2_0)=esk2_0), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_159]), c_0_156])]), c_0_165])).
% 32.21/32.38  cnf(c_0_168, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_166, c_0_167]), c_0_162]), ['proof']).
% 32.21/32.38  # SZS output end CNFRefutation
% 32.21/32.38  # Proof object total steps             : 169
% 32.21/32.38  # Proof object clause steps            : 116
% 32.21/32.38  # Proof object formula steps           : 53
% 32.21/32.38  # Proof object conjectures             : 43
% 32.21/32.38  # Proof object clause conjectures      : 40
% 32.21/32.38  # Proof object formula conjectures     : 3
% 32.21/32.38  # Proof object initial clauses used    : 32
% 32.21/32.38  # Proof object initial formulas used   : 26
% 32.21/32.38  # Proof object generating inferences   : 67
% 32.21/32.38  # Proof object simplifying inferences  : 91
% 32.21/32.38  # Training examples: 0 positive, 0 negative
% 32.21/32.38  # Parsed axioms                        : 30
% 32.21/32.38  # Removed by relevancy pruning/SinE    : 0
% 32.21/32.38  # Initial clauses                      : 37
% 32.21/32.38  # Removed in clause preprocessing      : 2
% 32.21/32.38  # Initial clauses in saturation        : 35
% 32.21/32.38  # Processed clauses                    : 110968
% 32.21/32.38  # ...of these trivial                  : 1878
% 32.21/32.38  # ...subsumed                          : 97644
% 32.21/32.38  # ...remaining for further processing  : 11446
% 32.21/32.38  # Other redundant clauses eliminated   : 2
% 32.21/32.38  # Clauses deleted for lack of memory   : 894448
% 32.21/32.38  # Backward-subsumed                    : 875
% 32.21/32.38  # Backward-rewritten                   : 2776
% 32.21/32.38  # Generated clauses                    : 3592143
% 32.21/32.38  # ...of the previous two non-trivial   : 3024385
% 32.21/32.38  # Contextual simplify-reflections      : 347
% 32.21/32.38  # Paramodulations                      : 3592038
% 32.21/32.38  # Factorizations                       : 0
% 32.21/32.38  # Equation resolutions                 : 2
% 32.21/32.38  # Propositional unsat checks           : 0
% 32.21/32.38  #    Propositional check models        : 0
% 32.21/32.38  #    Propositional check unsatisfiable : 0
% 32.21/32.38  #    Propositional clauses             : 0
% 32.21/32.38  #    Propositional clauses after purity: 0
% 32.21/32.38  #    Propositional unsat core size     : 0
% 32.21/32.38  #    Propositional preprocessing time  : 0.000
% 32.21/32.38  #    Propositional encoding time       : 0.000
% 32.21/32.38  #    Propositional solver time         : 0.000
% 32.21/32.38  #    Success case prop preproc time    : 0.000
% 32.21/32.38  #    Success case prop encoding time   : 0.000
% 32.21/32.38  #    Success case prop solver time     : 0.000
% 32.21/32.38  # Current number of processed clauses  : 7670
% 32.21/32.38  #    Positive orientable unit clauses  : 991
% 32.21/32.38  #    Positive unorientable unit clauses: 5
% 32.21/32.38  #    Negative unit clauses             : 185
% 32.21/32.38  #    Non-unit-clauses                  : 6489
% 32.21/32.38  # Current number of unprocessed clauses: 1732455
% 32.21/32.38  # ...number of literals in the above   : 5394979
% 32.21/32.38  # Current number of archived formulas  : 0
% 32.21/32.38  # Current number of archived clauses   : 3769
% 32.21/32.38  # Clause-clause subsumption calls (NU) : 9331279
% 32.21/32.38  # Rec. Clause-clause subsumption calls : 6966827
% 32.21/32.38  # Non-unit clause-clause subsumptions  : 53708
% 32.21/32.38  # Unit Clause-clause subsumption calls : 223127
% 32.21/32.38  # Rewrite failures with RHS unbound    : 0
% 32.21/32.38  # BW rewrite match attempts            : 78321
% 32.21/32.38  # BW rewrite match successes           : 640
% 32.21/32.38  # Condensation attempts                : 0
% 32.21/32.38  # Condensation successes               : 0
% 32.21/32.38  # Termbank termtop insertions          : 74647033
% 32.28/32.48  
% 32.28/32.48  # -------------------------------------------------
% 32.28/32.48  # User time                : 31.135 s
% 32.28/32.48  # System time              : 0.990 s
% 32.28/32.48  # Total time               : 32.126 s
% 32.28/32.48  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------

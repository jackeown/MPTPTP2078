%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:12:14 EST 2020

% Result     : Theorem 0.85s
% Output     : CNFRefutation 0.85s
% Verified   : 
% Statistics : Number of formulae       :  153 (10998 expanded)
%              Number of clauses        :   88 (5064 expanded)
%              Number of leaves         :   32 (2934 expanded)
%              Depth                    :   24
%              Number of atoms          :  306 (14336 expanded)
%              Number of equality atoms :   76 (8231 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(t22_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = k3_subset_1(X1,k1_subset_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(d3_subset_1,axiom,(
    ! [X1] : k1_subset_1(X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(t33_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => k3_subset_1(X1,k7_subset_1(X1,X2,X3)) = k4_subset_1(X1,k3_subset_1(X1,X2),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_subset_1)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t11_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X1,X2),X3)
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(t91_tops_1,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_tops_1(X2,X1)
           => v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_tops_1)).

fof(t38_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k4_xboole_0(X2,X1))
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

fof(t43_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_xboole_0(X2,X3))
     => r1_tarski(k4_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

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

fof(t88_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v2_tops_1(X2,X1)
          <=> r1_tarski(X2,k2_tops_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tops_1)).

fof(d4_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v2_tops_1(X2,X1)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t72_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(k2_tops_1(X1,k2_pre_topc(X1,X2)),k2_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_tops_1)).

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(d5_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_tops_1(X2,X1)
          <=> v2_tops_1(k2_pre_topc(X1,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tops_1)).

fof(c_0_32,plain,(
    ! [X6,X7] : k4_xboole_0(X6,X7) = k5_xboole_0(X6,k3_xboole_0(X6,X7)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_33,plain,(
    ! [X46,X47] : k1_setfam_1(k2_tarski(X46,X47)) = k3_xboole_0(X46,X47) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_34,plain,(
    ! [X11,X12] : r1_tarski(k3_xboole_0(X11,X12),X11) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_35,plain,(
    ! [X16,X17] : r1_tarski(k4_xboole_0(X16,X17),X16) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_36,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_37,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_38,plain,(
    ! [X20] :
      ( ~ r1_tarski(X20,k1_xboole_0)
      | X20 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

cnf(c_0_39,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_40,plain,(
    ! [X38,X39,X40] :
      ( ~ m1_subset_1(X39,k1_zfmisc_1(X38))
      | k7_subset_1(X38,X39,X40) = k4_xboole_0(X39,X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

cnf(c_0_41,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_42,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_43,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_44,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_39,c_0_37])).

cnf(c_0_45,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_46,plain,
    ( r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X1) ),
    inference(rw,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_47,plain,
    ( k1_setfam_1(k2_tarski(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

fof(c_0_48,plain,(
    ! [X45] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X45)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_49,plain,(
    ! [X41] : k2_subset_1(X41) = k3_subset_1(X41,k1_subset_1(X41)) ),
    inference(variable_rename,[status(thm)],[t22_subset_1])).

fof(c_0_50,plain,(
    ! [X29] : k2_subset_1(X29) = X29 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_51,plain,(
    ! [X28] : k1_subset_1(X28) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[d3_subset_1])).

fof(c_0_52,plain,(
    ! [X42,X43,X44] :
      ( ~ m1_subset_1(X43,k1_zfmisc_1(X42))
      | ~ m1_subset_1(X44,k1_zfmisc_1(X42))
      | k3_subset_1(X42,k7_subset_1(X42,X43,X44)) = k4_subset_1(X42,k3_subset_1(X42,X43),X44) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_subset_1])])])).

cnf(c_0_53,plain,
    ( k7_subset_1(X2,X1,X3) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_45,c_0_42])).

cnf(c_0_54,plain,
    ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_46]),c_0_47])).

cnf(c_0_55,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_56,plain,
    ( k2_subset_1(X1) = k3_subset_1(X1,k1_subset_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_57,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_58,plain,
    ( k1_subset_1(X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

fof(c_0_59,plain,(
    ! [X32] : m1_subset_1(k2_subset_1(X32),k1_zfmisc_1(X32)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_60,plain,(
    ! [X30,X31] :
      ( ~ m1_subset_1(X31,k1_zfmisc_1(X30))
      | k3_subset_1(X30,X31) = k4_xboole_0(X30,X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_61,plain,(
    ! [X26,X27] : k2_tarski(X26,X27) = k2_tarski(X27,X26) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

fof(c_0_62,plain,(
    ! [X8,X9,X10] :
      ( ~ r1_tarski(k2_xboole_0(X8,X9),X10)
      | r1_tarski(X8,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

fof(c_0_63,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_64,plain,(
    ! [X35,X36,X37] :
      ( ~ m1_subset_1(X36,k1_zfmisc_1(X35))
      | ~ m1_subset_1(X37,k1_zfmisc_1(X35))
      | k4_subset_1(X35,X36,X37) = k2_xboole_0(X36,X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_65,plain,
    ( k3_subset_1(X2,k7_subset_1(X2,X1,X3)) = k4_subset_1(X2,k3_subset_1(X2,X1),X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_66,plain,
    ( k7_subset_1(X1,k1_xboole_0,X2) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_47]),c_0_54]),c_0_55])])).

cnf(c_0_67,plain,
    ( X1 = k3_subset_1(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_57]),c_0_58])).

cnf(c_0_68,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_69,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_70,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_71,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_72,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_73,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_74,plain,
    ( k4_subset_1(X1,X1,X2) = X1
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67]),c_0_67]),c_0_55])])).

cnf(c_0_75,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_68,c_0_57])).

fof(c_0_76,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v3_tops_1(X2,X1)
             => v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t91_tops_1])).

cnf(c_0_77,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_69,c_0_42])).

cnf(c_0_78,plain,
    ( k1_setfam_1(k2_tarski(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_47,c_0_70])).

fof(c_0_79,plain,(
    ! [X18,X19] :
      ( ~ r1_tarski(X18,k4_xboole_0(X19,X18))
      | X18 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_xboole_1])])).

fof(c_0_80,plain,(
    ! [X21,X22,X23] :
      ( ~ r1_tarski(X21,k2_xboole_0(X22,X23))
      | r1_tarski(k4_xboole_0(X21,X22),X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).

cnf(c_0_81,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(k2_xboole_0(X3,X1),X2) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_82,plain,
    ( k2_xboole_0(X1,X2) = X1
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_75])])).

fof(c_0_83,negated_conjecture,
    ( l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & v3_tops_1(esk2_0,esk1_0)
    & ~ v1_tops_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_76])])])).

cnf(c_0_84,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_67]),c_0_55])])).

cnf(c_0_85,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_86,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_87,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_88,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_89,plain,
    ( r1_tarski(X1,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_78]),c_0_84])).

fof(c_0_90,plain,(
    ! [X24,X25] : k4_xboole_0(X24,k4_xboole_0(X24,X25)) = k3_xboole_0(X24,X25) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_91,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))) ),
    inference(rw,[status(thm)],[c_0_85,c_0_42])).

cnf(c_0_92,plain,
    ( r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[c_0_86,c_0_42])).

cnf(c_0_93,negated_conjecture,
    ( r1_tarski(esk2_0,X1)
    | ~ r1_tarski(u1_struct_0(esk1_0),X1) ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_94,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_89])).

cnf(c_0_95,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_96,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k1_xboole_0
    | ~ r1_tarski(X1,k2_xboole_0(X2,k5_xboole_0(X3,k1_setfam_1(k2_tarski(X3,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))))))) ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_97,negated_conjecture,
    ( r1_tarski(esk2_0,k2_xboole_0(u1_struct_0(esk1_0),X1)) ),
    inference(spm,[status(thm)],[c_0_93,c_0_94])).

cnf(c_0_98,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))))) = k1_setfam_1(k2_tarski(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_95,c_0_37]),c_0_42]),c_0_42])).

cnf(c_0_99,negated_conjecture,
    ( k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,u1_struct_0(esk1_0)))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_96,c_0_97])).

cnf(c_0_100,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))) = k3_subset_1(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_70])).

cnf(c_0_101,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk2_0,u1_struct_0(esk1_0))) = esk2_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_78]),c_0_84])).

cnf(c_0_102,plain,
    ( k7_subset_1(X1,X2,X3) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X3,X2)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_70])).

cnf(c_0_103,negated_conjecture,
    ( k5_xboole_0(u1_struct_0(esk1_0),esk2_0) = k3_subset_1(u1_struct_0(esk1_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_88])])).

fof(c_0_104,plain,(
    ! [X48,X49] :
      ( ( ~ m1_subset_1(X48,k1_zfmisc_1(X49))
        | r1_tarski(X48,X49) )
      & ( ~ r1_tarski(X48,X49)
        | m1_subset_1(X48,k1_zfmisc_1(X49)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_105,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k7_subset_1(X2,X1,X3)))) = k1_setfam_1(k2_tarski(X1,X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_98,c_0_53])).

cnf(c_0_106,negated_conjecture,
    ( k7_subset_1(X1,u1_struct_0(esk1_0),esk2_0) = k3_subset_1(u1_struct_0(esk1_0),esk2_0)
    | ~ m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_101]),c_0_103])).

cnf(c_0_107,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_104])).

cnf(c_0_108,plain,
    ( r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))),X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_70])).

cnf(c_0_109,negated_conjecture,
    ( k5_xboole_0(u1_struct_0(esk1_0),k1_setfam_1(k2_tarski(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)))) = esk2_0
    | ~ m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_106]),c_0_70]),c_0_101])).

cnf(c_0_110,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_107,c_0_94])).

cnf(c_0_111,negated_conjecture,
    ( r1_tarski(k3_subset_1(u1_struct_0(esk1_0),esk2_0),u1_struct_0(esk1_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_101]),c_0_103])).

fof(c_0_112,plain,(
    ! [X63,X64] :
      ( ~ l1_pre_topc(X63)
      | ~ m1_subset_1(X64,k1_zfmisc_1(u1_struct_0(X63)))
      | k2_pre_topc(X63,X64) = k4_subset_1(u1_struct_0(X63),X64,k2_tops_1(X63,X64)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_tops_1])])])).

fof(c_0_113,plain,(
    ! [X61,X62] :
      ( ~ l1_pre_topc(X61)
      | ~ m1_subset_1(X62,k1_zfmisc_1(u1_struct_0(X61)))
      | k2_tops_1(X61,X62) = k2_tops_1(X61,k3_subset_1(u1_struct_0(X61),X62)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_tops_1])])])).

fof(c_0_114,plain,(
    ! [X33,X34] :
      ( ~ m1_subset_1(X34,k1_zfmisc_1(X33))
      | m1_subset_1(k3_subset_1(X33,X34),k1_zfmisc_1(X33)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

cnf(c_0_115,negated_conjecture,
    ( k5_xboole_0(u1_struct_0(esk1_0),k1_setfam_1(k2_tarski(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)))) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_109,c_0_110])).

cnf(c_0_116,negated_conjecture,
    ( m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_107,c_0_111])).

cnf(c_0_117,plain,
    ( k2_pre_topc(X1,X2) = k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_112])).

cnf(c_0_118,plain,
    ( k2_tops_1(X1,X2) = k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_113])).

cnf(c_0_119,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_114])).

cnf(c_0_120,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_115]),c_0_116])])).

cnf(c_0_121,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

fof(c_0_122,plain,(
    ! [X59,X60] :
      ( ~ l1_pre_topc(X59)
      | ~ m1_subset_1(X60,k1_zfmisc_1(u1_struct_0(X59)))
      | m1_subset_1(k2_tops_1(X59,X60),k1_zfmisc_1(u1_struct_0(X59))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_1])])).

fof(c_0_123,plain,(
    ! [X67,X68] :
      ( ( ~ v2_tops_1(X68,X67)
        | r1_tarski(X68,k2_tops_1(X67,X68))
        | ~ m1_subset_1(X68,k1_zfmisc_1(u1_struct_0(X67)))
        | ~ l1_pre_topc(X67) )
      & ( ~ r1_tarski(X68,k2_tops_1(X67,X68))
        | v2_tops_1(X68,X67)
        | ~ m1_subset_1(X68,k1_zfmisc_1(u1_struct_0(X67)))
        | ~ l1_pre_topc(X67) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_tops_1])])])])).

fof(c_0_124,plain,(
    ! [X55,X56] :
      ( ( ~ v2_tops_1(X56,X55)
        | v1_tops_1(k3_subset_1(u1_struct_0(X55),X56),X55)
        | ~ m1_subset_1(X56,k1_zfmisc_1(u1_struct_0(X55)))
        | ~ l1_pre_topc(X55) )
      & ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X55),X56),X55)
        | v2_tops_1(X56,X55)
        | ~ m1_subset_1(X56,k1_zfmisc_1(u1_struct_0(X55)))
        | ~ l1_pre_topc(X55) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tops_1])])])])).

cnf(c_0_125,plain,
    ( k4_subset_1(u1_struct_0(X1),k3_subset_1(u1_struct_0(X1),X2),k2_tops_1(X1,X2)) = k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_118]),c_0_119])).

cnf(c_0_126,negated_conjecture,
    ( k2_tops_1(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)) = k2_tops_1(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_120]),c_0_121]),c_0_116])])).

cnf(c_0_127,plain,
    ( m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_122])).

fof(c_0_128,plain,(
    ! [X13,X14,X15] :
      ( ~ r1_tarski(X13,X14)
      | ~ r1_tarski(X14,X15)
      | r1_tarski(X13,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_129,plain,(
    ! [X65,X66] :
      ( ~ l1_pre_topc(X65)
      | ~ m1_subset_1(X66,k1_zfmisc_1(u1_struct_0(X65)))
      | r1_tarski(k2_tops_1(X65,k2_pre_topc(X65,X66)),k2_tops_1(X65,X66)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t72_tops_1])])])).

cnf(c_0_130,plain,
    ( v2_tops_1(X1,X2)
    | ~ r1_tarski(X1,k2_tops_1(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_123])).

cnf(c_0_131,negated_conjecture,
    ( ~ v1_tops_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_132,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(X2),X1),X2)
    | ~ v2_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_124])).

cnf(c_0_133,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),esk2_0,k2_tops_1(esk1_0,esk2_0)) = k2_pre_topc(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_126]),c_0_120]),c_0_120]),c_0_121]),c_0_116])])).

cnf(c_0_134,negated_conjecture,
    ( m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_126]),c_0_121]),c_0_116])])).

cnf(c_0_135,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_128])).

cnf(c_0_136,plain,
    ( r1_tarski(k2_tops_1(X1,k2_pre_topc(X1,X2)),k2_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_129])).

fof(c_0_137,plain,(
    ! [X53,X54] :
      ( ~ l1_pre_topc(X53)
      | ~ m1_subset_1(X54,k1_zfmisc_1(u1_struct_0(X53)))
      | m1_subset_1(k2_pre_topc(X53,X54),k1_zfmisc_1(u1_struct_0(X53))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

cnf(c_0_138,plain,
    ( v2_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k3_subset_1(u1_struct_0(X1),X2),k2_tops_1(X1,X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_130,c_0_118]),c_0_119])).

cnf(c_0_139,negated_conjecture,
    ( ~ v2_tops_1(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_132]),c_0_121]),c_0_88])])).

cnf(c_0_140,negated_conjecture,
    ( k2_xboole_0(esk2_0,k2_tops_1(esk1_0,esk2_0)) = k2_pre_topc(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_133]),c_0_134]),c_0_88])])).

cnf(c_0_141,plain,
    ( r1_tarski(X1,k2_tops_1(X2,X3))
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(X1,k2_tops_1(X2,k2_pre_topc(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_135,c_0_136])).

cnf(c_0_142,plain,
    ( r1_tarski(X1,k2_tops_1(X2,X1))
    | ~ v2_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_123])).

cnf(c_0_143,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_137])).

cnf(c_0_144,negated_conjecture,
    ( ~ r1_tarski(esk2_0,k2_tops_1(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_120]),c_0_121]),c_0_116])]),c_0_139])).

cnf(c_0_145,negated_conjecture,
    ( r1_tarski(esk2_0,X1)
    | ~ r1_tarski(k2_pre_topc(esk1_0,esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_140])).

cnf(c_0_146,plain,
    ( r1_tarski(k2_pre_topc(X1,X2),k2_tops_1(X1,X2))
    | ~ v2_tops_1(k2_pre_topc(X1,X2),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_141,c_0_142]),c_0_143])).

cnf(c_0_147,negated_conjecture,
    ( ~ r1_tarski(esk2_0,k2_tops_1(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_144,c_0_118]),c_0_121]),c_0_88])])).

fof(c_0_148,plain,(
    ! [X57,X58] :
      ( ( ~ v3_tops_1(X58,X57)
        | v2_tops_1(k2_pre_topc(X57,X58),X57)
        | ~ m1_subset_1(X58,k1_zfmisc_1(u1_struct_0(X57)))
        | ~ l1_pre_topc(X57) )
      & ( ~ v2_tops_1(k2_pre_topc(X57,X58),X57)
        | v3_tops_1(X58,X57)
        | ~ m1_subset_1(X58,k1_zfmisc_1(u1_struct_0(X57)))
        | ~ l1_pre_topc(X57) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_tops_1])])])])).

cnf(c_0_149,negated_conjecture,
    ( ~ v2_tops_1(k2_pre_topc(esk1_0,esk2_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_145,c_0_146]),c_0_121]),c_0_88])]),c_0_147])).

cnf(c_0_150,plain,
    ( v2_tops_1(k2_pre_topc(X2,X1),X2)
    | ~ v3_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_148])).

cnf(c_0_151,negated_conjecture,
    ( v3_tops_1(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_152,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_149,c_0_150]),c_0_151]),c_0_121]),c_0_88])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:22:45 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.85/1.06  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.85/1.06  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.85/1.06  #
% 0.85/1.06  # Preprocessing time       : 0.029 s
% 0.85/1.06  # Presaturation interreduction done
% 0.85/1.06  
% 0.85/1.06  # Proof found!
% 0.85/1.06  # SZS status Theorem
% 0.85/1.06  # SZS output start CNFRefutation
% 0.85/1.06  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.85/1.06  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.85/1.06  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.85/1.06  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.85/1.06  fof(t3_xboole_1, axiom, ![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 0.85/1.06  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 0.85/1.06  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.85/1.06  fof(t22_subset_1, axiom, ![X1]:k2_subset_1(X1)=k3_subset_1(X1,k1_subset_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 0.85/1.06  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 0.85/1.06  fof(d3_subset_1, axiom, ![X1]:k1_subset_1(X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 0.85/1.06  fof(t33_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k3_subset_1(X1,k7_subset_1(X1,X2,X3))=k4_subset_1(X1,k3_subset_1(X1,X2),X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_subset_1)).
% 0.85/1.06  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.85/1.06  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 0.85/1.06  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.85/1.06  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 0.85/1.06  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.85/1.06  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 0.85/1.06  fof(t91_tops_1, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_tops_1(X2,X1)=>v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_tops_1)).
% 0.85/1.06  fof(t38_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,k4_xboole_0(X2,X1))=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_xboole_1)).
% 0.85/1.06  fof(t43_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_xboole_0(X2,X3))=>r1_tarski(k4_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 0.85/1.06  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.85/1.06  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.85/1.06  fof(t65_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_pre_topc(X1,X2)=k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 0.85/1.06  fof(t62_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_tops_1(X1,X2)=k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tops_1)).
% 0.85/1.06  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 0.85/1.06  fof(dt_k2_tops_1, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 0.85/1.06  fof(t88_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tops_1(X2,X1)<=>r1_tarski(X2,k2_tops_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tops_1)).
% 0.85/1.06  fof(d4_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tops_1(X2,X1)<=>v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_1)).
% 0.85/1.06  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.85/1.06  fof(t72_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k2_tops_1(X1,k2_pre_topc(X1,X2)),k2_tops_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_tops_1)).
% 0.85/1.06  fof(dt_k2_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 0.85/1.06  fof(d5_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_tops_1(X2,X1)<=>v2_tops_1(k2_pre_topc(X1,X2),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tops_1)).
% 0.85/1.06  fof(c_0_32, plain, ![X6, X7]:k4_xboole_0(X6,X7)=k5_xboole_0(X6,k3_xboole_0(X6,X7)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.85/1.06  fof(c_0_33, plain, ![X46, X47]:k1_setfam_1(k2_tarski(X46,X47))=k3_xboole_0(X46,X47), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.85/1.06  fof(c_0_34, plain, ![X11, X12]:r1_tarski(k3_xboole_0(X11,X12),X11), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.85/1.06  fof(c_0_35, plain, ![X16, X17]:r1_tarski(k4_xboole_0(X16,X17),X16), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.85/1.06  cnf(c_0_36, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.85/1.06  cnf(c_0_37, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.85/1.06  fof(c_0_38, plain, ![X20]:(~r1_tarski(X20,k1_xboole_0)|X20=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).
% 0.85/1.06  cnf(c_0_39, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.85/1.06  fof(c_0_40, plain, ![X38, X39, X40]:(~m1_subset_1(X39,k1_zfmisc_1(X38))|k7_subset_1(X38,X39,X40)=k4_xboole_0(X39,X40)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 0.85/1.06  cnf(c_0_41, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.85/1.06  cnf(c_0_42, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_36, c_0_37])).
% 0.85/1.06  cnf(c_0_43, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.85/1.06  cnf(c_0_44, plain, (r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_39, c_0_37])).
% 0.85/1.06  cnf(c_0_45, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.85/1.06  cnf(c_0_46, plain, (r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X1)), inference(rw,[status(thm)],[c_0_41, c_0_42])).
% 0.85/1.06  cnf(c_0_47, plain, (k1_setfam_1(k2_tarski(k1_xboole_0,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.85/1.06  fof(c_0_48, plain, ![X45]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X45)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.85/1.06  fof(c_0_49, plain, ![X41]:k2_subset_1(X41)=k3_subset_1(X41,k1_subset_1(X41)), inference(variable_rename,[status(thm)],[t22_subset_1])).
% 0.85/1.06  fof(c_0_50, plain, ![X29]:k2_subset_1(X29)=X29, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.85/1.06  fof(c_0_51, plain, ![X28]:k1_subset_1(X28)=k1_xboole_0, inference(variable_rename,[status(thm)],[d3_subset_1])).
% 0.85/1.06  fof(c_0_52, plain, ![X42, X43, X44]:(~m1_subset_1(X43,k1_zfmisc_1(X42))|(~m1_subset_1(X44,k1_zfmisc_1(X42))|k3_subset_1(X42,k7_subset_1(X42,X43,X44))=k4_subset_1(X42,k3_subset_1(X42,X43),X44))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_subset_1])])])).
% 0.85/1.06  cnf(c_0_53, plain, (k7_subset_1(X2,X1,X3)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_45, c_0_42])).
% 0.85/1.06  cnf(c_0_54, plain, (k5_xboole_0(k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_46]), c_0_47])).
% 0.85/1.06  cnf(c_0_55, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.85/1.06  cnf(c_0_56, plain, (k2_subset_1(X1)=k3_subset_1(X1,k1_subset_1(X1))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.85/1.06  cnf(c_0_57, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.85/1.06  cnf(c_0_58, plain, (k1_subset_1(X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.85/1.06  fof(c_0_59, plain, ![X32]:m1_subset_1(k2_subset_1(X32),k1_zfmisc_1(X32)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.85/1.06  fof(c_0_60, plain, ![X30, X31]:(~m1_subset_1(X31,k1_zfmisc_1(X30))|k3_subset_1(X30,X31)=k4_xboole_0(X30,X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.85/1.06  fof(c_0_61, plain, ![X26, X27]:k2_tarski(X26,X27)=k2_tarski(X27,X26), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.85/1.06  fof(c_0_62, plain, ![X8, X9, X10]:(~r1_tarski(k2_xboole_0(X8,X9),X10)|r1_tarski(X8,X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 0.85/1.06  fof(c_0_63, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.85/1.06  fof(c_0_64, plain, ![X35, X36, X37]:(~m1_subset_1(X36,k1_zfmisc_1(X35))|~m1_subset_1(X37,k1_zfmisc_1(X35))|k4_subset_1(X35,X36,X37)=k2_xboole_0(X36,X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 0.85/1.06  cnf(c_0_65, plain, (k3_subset_1(X2,k7_subset_1(X2,X1,X3))=k4_subset_1(X2,k3_subset_1(X2,X1),X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.85/1.06  cnf(c_0_66, plain, (k7_subset_1(X1,k1_xboole_0,X2)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_47]), c_0_54]), c_0_55])])).
% 0.85/1.06  cnf(c_0_67, plain, (X1=k3_subset_1(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_57]), c_0_58])).
% 0.85/1.06  cnf(c_0_68, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.85/1.06  cnf(c_0_69, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.85/1.06  cnf(c_0_70, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.85/1.06  cnf(c_0_71, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.85/1.06  cnf(c_0_72, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.85/1.06  cnf(c_0_73, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.85/1.06  cnf(c_0_74, plain, (k4_subset_1(X1,X1,X2)=X1|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67]), c_0_67]), c_0_55])])).
% 0.85/1.06  cnf(c_0_75, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_68, c_0_57])).
% 0.85/1.06  fof(c_0_76, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_tops_1(X2,X1)=>v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1))))), inference(assume_negation,[status(cth)],[t91_tops_1])).
% 0.85/1.06  cnf(c_0_77, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_69, c_0_42])).
% 0.85/1.06  cnf(c_0_78, plain, (k1_setfam_1(k2_tarski(X1,k1_xboole_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_47, c_0_70])).
% 0.85/1.06  fof(c_0_79, plain, ![X18, X19]:(~r1_tarski(X18,k4_xboole_0(X19,X18))|X18=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_xboole_1])])).
% 0.85/1.06  fof(c_0_80, plain, ![X21, X22, X23]:(~r1_tarski(X21,k2_xboole_0(X22,X23))|r1_tarski(k4_xboole_0(X21,X22),X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).
% 0.85/1.06  cnf(c_0_81, plain, (r1_tarski(X1,X2)|~r1_tarski(k2_xboole_0(X3,X1),X2)), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.85/1.06  cnf(c_0_82, plain, (k2_xboole_0(X1,X2)=X1|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_75])])).
% 0.85/1.06  fof(c_0_83, negated_conjecture, (l1_pre_topc(esk1_0)&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(v3_tops_1(esk2_0,esk1_0)&~v1_tops_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk1_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_76])])])).
% 0.85/1.06  cnf(c_0_84, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_67]), c_0_55])])).
% 0.85/1.06  cnf(c_0_85, plain, (X1=k1_xboole_0|~r1_tarski(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.85/1.06  cnf(c_0_86, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.85/1.06  cnf(c_0_87, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X3))|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 0.85/1.06  cnf(c_0_88, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_83])).
% 0.85/1.06  cnf(c_0_89, plain, (r1_tarski(X1,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_78]), c_0_84])).
% 0.85/1.06  fof(c_0_90, plain, ![X24, X25]:k4_xboole_0(X24,k4_xboole_0(X24,X25))=k3_xboole_0(X24,X25), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.85/1.06  cnf(c_0_91, plain, (X1=k1_xboole_0|~r1_tarski(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1))))), inference(rw,[status(thm)],[c_0_85, c_0_42])).
% 0.85/1.06  cnf(c_0_92, plain, (r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X3)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(rw,[status(thm)],[c_0_86, c_0_42])).
% 0.85/1.06  cnf(c_0_93, negated_conjecture, (r1_tarski(esk2_0,X1)|~r1_tarski(u1_struct_0(esk1_0),X1)), inference(spm,[status(thm)],[c_0_87, c_0_88])).
% 0.85/1.06  cnf(c_0_94, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_71, c_0_89])).
% 0.85/1.06  cnf(c_0_95, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_90])).
% 0.85/1.06  cnf(c_0_96, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k1_xboole_0|~r1_tarski(X1,k2_xboole_0(X2,k5_xboole_0(X3,k1_setfam_1(k2_tarski(X3,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))))))))), inference(spm,[status(thm)],[c_0_91, c_0_92])).
% 0.85/1.06  cnf(c_0_97, negated_conjecture, (r1_tarski(esk2_0,k2_xboole_0(u1_struct_0(esk1_0),X1))), inference(spm,[status(thm)],[c_0_93, c_0_94])).
% 0.85/1.06  cnf(c_0_98, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))))))=k1_setfam_1(k2_tarski(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_95, c_0_37]), c_0_42]), c_0_42])).
% 0.85/1.06  cnf(c_0_99, negated_conjecture, (k5_xboole_0(esk2_0,k1_setfam_1(k2_tarski(esk2_0,u1_struct_0(esk1_0))))=k1_xboole_0), inference(spm,[status(thm)],[c_0_96, c_0_97])).
% 0.85/1.06  cnf(c_0_100, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1)))=k3_subset_1(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_77, c_0_70])).
% 0.85/1.06  cnf(c_0_101, negated_conjecture, (k1_setfam_1(k2_tarski(esk2_0,u1_struct_0(esk1_0)))=esk2_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_78]), c_0_84])).
% 0.85/1.06  cnf(c_0_102, plain, (k7_subset_1(X1,X2,X3)=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X3,X2)))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_53, c_0_70])).
% 0.85/1.06  cnf(c_0_103, negated_conjecture, (k5_xboole_0(u1_struct_0(esk1_0),esk2_0)=k3_subset_1(u1_struct_0(esk1_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_101]), c_0_88])])).
% 0.85/1.06  fof(c_0_104, plain, ![X48, X49]:((~m1_subset_1(X48,k1_zfmisc_1(X49))|r1_tarski(X48,X49))&(~r1_tarski(X48,X49)|m1_subset_1(X48,k1_zfmisc_1(X49)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.85/1.06  cnf(c_0_105, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k7_subset_1(X2,X1,X3))))=k1_setfam_1(k2_tarski(X1,X3))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_98, c_0_53])).
% 0.85/1.06  cnf(c_0_106, negated_conjecture, (k7_subset_1(X1,u1_struct_0(esk1_0),esk2_0)=k3_subset_1(u1_struct_0(esk1_0),esk2_0)|~m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_101]), c_0_103])).
% 0.85/1.06  cnf(c_0_107, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_104])).
% 0.85/1.06  cnf(c_0_108, plain, (r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))),X1)), inference(spm,[status(thm)],[c_0_46, c_0_70])).
% 0.85/1.06  cnf(c_0_109, negated_conjecture, (k5_xboole_0(u1_struct_0(esk1_0),k1_setfam_1(k2_tarski(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))))=esk2_0|~m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_106]), c_0_70]), c_0_101])).
% 0.85/1.06  cnf(c_0_110, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_107, c_0_94])).
% 0.85/1.06  cnf(c_0_111, negated_conjecture, (r1_tarski(k3_subset_1(u1_struct_0(esk1_0),esk2_0),u1_struct_0(esk1_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_101]), c_0_103])).
% 0.85/1.06  fof(c_0_112, plain, ![X63, X64]:(~l1_pre_topc(X63)|(~m1_subset_1(X64,k1_zfmisc_1(u1_struct_0(X63)))|k2_pre_topc(X63,X64)=k4_subset_1(u1_struct_0(X63),X64,k2_tops_1(X63,X64)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_tops_1])])])).
% 0.85/1.06  fof(c_0_113, plain, ![X61, X62]:(~l1_pre_topc(X61)|(~m1_subset_1(X62,k1_zfmisc_1(u1_struct_0(X61)))|k2_tops_1(X61,X62)=k2_tops_1(X61,k3_subset_1(u1_struct_0(X61),X62)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_tops_1])])])).
% 0.85/1.06  fof(c_0_114, plain, ![X33, X34]:(~m1_subset_1(X34,k1_zfmisc_1(X33))|m1_subset_1(k3_subset_1(X33,X34),k1_zfmisc_1(X33))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 0.85/1.06  cnf(c_0_115, negated_conjecture, (k5_xboole_0(u1_struct_0(esk1_0),k1_setfam_1(k2_tarski(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))))=esk2_0), inference(spm,[status(thm)],[c_0_109, c_0_110])).
% 0.85/1.06  cnf(c_0_116, negated_conjecture, (m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_107, c_0_111])).
% 0.85/1.06  cnf(c_0_117, plain, (k2_pre_topc(X1,X2)=k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_112])).
% 0.85/1.06  cnf(c_0_118, plain, (k2_tops_1(X1,X2)=k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_113])).
% 0.85/1.06  cnf(c_0_119, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_114])).
% 0.85/1.06  cnf(c_0_120, negated_conjecture, (k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_115]), c_0_116])])).
% 0.85/1.06  cnf(c_0_121, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_83])).
% 0.85/1.06  fof(c_0_122, plain, ![X59, X60]:(~l1_pre_topc(X59)|~m1_subset_1(X60,k1_zfmisc_1(u1_struct_0(X59)))|m1_subset_1(k2_tops_1(X59,X60),k1_zfmisc_1(u1_struct_0(X59)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_1])])).
% 0.85/1.06  fof(c_0_123, plain, ![X67, X68]:((~v2_tops_1(X68,X67)|r1_tarski(X68,k2_tops_1(X67,X68))|~m1_subset_1(X68,k1_zfmisc_1(u1_struct_0(X67)))|~l1_pre_topc(X67))&(~r1_tarski(X68,k2_tops_1(X67,X68))|v2_tops_1(X68,X67)|~m1_subset_1(X68,k1_zfmisc_1(u1_struct_0(X67)))|~l1_pre_topc(X67))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_tops_1])])])])).
% 0.85/1.06  fof(c_0_124, plain, ![X55, X56]:((~v2_tops_1(X56,X55)|v1_tops_1(k3_subset_1(u1_struct_0(X55),X56),X55)|~m1_subset_1(X56,k1_zfmisc_1(u1_struct_0(X55)))|~l1_pre_topc(X55))&(~v1_tops_1(k3_subset_1(u1_struct_0(X55),X56),X55)|v2_tops_1(X56,X55)|~m1_subset_1(X56,k1_zfmisc_1(u1_struct_0(X55)))|~l1_pre_topc(X55))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tops_1])])])])).
% 0.85/1.06  cnf(c_0_125, plain, (k4_subset_1(u1_struct_0(X1),k3_subset_1(u1_struct_0(X1),X2),k2_tops_1(X1,X2))=k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_118]), c_0_119])).
% 0.85/1.06  cnf(c_0_126, negated_conjecture, (k2_tops_1(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0))=k2_tops_1(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118, c_0_120]), c_0_121]), c_0_116])])).
% 0.85/1.06  cnf(c_0_127, plain, (m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_122])).
% 0.85/1.06  fof(c_0_128, plain, ![X13, X14, X15]:(~r1_tarski(X13,X14)|~r1_tarski(X14,X15)|r1_tarski(X13,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.85/1.06  fof(c_0_129, plain, ![X65, X66]:(~l1_pre_topc(X65)|(~m1_subset_1(X66,k1_zfmisc_1(u1_struct_0(X65)))|r1_tarski(k2_tops_1(X65,k2_pre_topc(X65,X66)),k2_tops_1(X65,X66)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t72_tops_1])])])).
% 0.85/1.06  cnf(c_0_130, plain, (v2_tops_1(X1,X2)|~r1_tarski(X1,k2_tops_1(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_123])).
% 0.85/1.06  cnf(c_0_131, negated_conjecture, (~v1_tops_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk1_0)), inference(split_conjunct,[status(thm)],[c_0_83])).
% 0.85/1.06  cnf(c_0_132, plain, (v1_tops_1(k3_subset_1(u1_struct_0(X2),X1),X2)|~v2_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_124])).
% 0.85/1.06  cnf(c_0_133, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),esk2_0,k2_tops_1(esk1_0,esk2_0))=k2_pre_topc(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125, c_0_126]), c_0_120]), c_0_120]), c_0_121]), c_0_116])])).
% 0.85/1.06  cnf(c_0_134, negated_conjecture, (m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127, c_0_126]), c_0_121]), c_0_116])])).
% 0.85/1.06  cnf(c_0_135, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_128])).
% 0.85/1.06  cnf(c_0_136, plain, (r1_tarski(k2_tops_1(X1,k2_pre_topc(X1,X2)),k2_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_129])).
% 0.85/1.06  fof(c_0_137, plain, ![X53, X54]:(~l1_pre_topc(X53)|~m1_subset_1(X54,k1_zfmisc_1(u1_struct_0(X53)))|m1_subset_1(k2_pre_topc(X53,X54),k1_zfmisc_1(u1_struct_0(X53)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).
% 0.85/1.06  cnf(c_0_138, plain, (v2_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k3_subset_1(u1_struct_0(X1),X2),k2_tops_1(X1,X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_130, c_0_118]), c_0_119])).
% 0.85/1.06  cnf(c_0_139, negated_conjecture, (~v2_tops_1(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131, c_0_132]), c_0_121]), c_0_88])])).
% 0.85/1.06  cnf(c_0_140, negated_conjecture, (k2_xboole_0(esk2_0,k2_tops_1(esk1_0,esk2_0))=k2_pre_topc(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_133]), c_0_134]), c_0_88])])).
% 0.85/1.06  cnf(c_0_141, plain, (r1_tarski(X1,k2_tops_1(X2,X3))|~l1_pre_topc(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(X1,k2_tops_1(X2,k2_pre_topc(X2,X3)))), inference(spm,[status(thm)],[c_0_135, c_0_136])).
% 0.85/1.06  cnf(c_0_142, plain, (r1_tarski(X1,k2_tops_1(X2,X1))|~v2_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_123])).
% 0.85/1.06  cnf(c_0_143, plain, (m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_137])).
% 0.85/1.06  cnf(c_0_144, negated_conjecture, (~r1_tarski(esk2_0,k2_tops_1(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_120]), c_0_121]), c_0_116])]), c_0_139])).
% 0.85/1.06  cnf(c_0_145, negated_conjecture, (r1_tarski(esk2_0,X1)|~r1_tarski(k2_pre_topc(esk1_0,esk2_0),X1)), inference(spm,[status(thm)],[c_0_71, c_0_140])).
% 0.85/1.06  cnf(c_0_146, plain, (r1_tarski(k2_pre_topc(X1,X2),k2_tops_1(X1,X2))|~v2_tops_1(k2_pre_topc(X1,X2),X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_141, c_0_142]), c_0_143])).
% 0.85/1.06  cnf(c_0_147, negated_conjecture, (~r1_tarski(esk2_0,k2_tops_1(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_144, c_0_118]), c_0_121]), c_0_88])])).
% 0.85/1.06  fof(c_0_148, plain, ![X57, X58]:((~v3_tops_1(X58,X57)|v2_tops_1(k2_pre_topc(X57,X58),X57)|~m1_subset_1(X58,k1_zfmisc_1(u1_struct_0(X57)))|~l1_pre_topc(X57))&(~v2_tops_1(k2_pre_topc(X57,X58),X57)|v3_tops_1(X58,X57)|~m1_subset_1(X58,k1_zfmisc_1(u1_struct_0(X57)))|~l1_pre_topc(X57))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_tops_1])])])])).
% 0.85/1.06  cnf(c_0_149, negated_conjecture, (~v2_tops_1(k2_pre_topc(esk1_0,esk2_0),esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_145, c_0_146]), c_0_121]), c_0_88])]), c_0_147])).
% 0.85/1.06  cnf(c_0_150, plain, (v2_tops_1(k2_pre_topc(X2,X1),X2)|~v3_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_148])).
% 0.85/1.06  cnf(c_0_151, negated_conjecture, (v3_tops_1(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_83])).
% 0.85/1.06  cnf(c_0_152, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_149, c_0_150]), c_0_151]), c_0_121]), c_0_88])]), ['proof']).
% 0.85/1.06  # SZS output end CNFRefutation
% 0.85/1.06  # Proof object total steps             : 153
% 0.85/1.06  # Proof object clause steps            : 88
% 0.85/1.06  # Proof object formula steps           : 65
% 0.85/1.06  # Proof object conjectures             : 28
% 0.85/1.06  # Proof object clause conjectures      : 25
% 0.85/1.06  # Proof object formula conjectures     : 3
% 0.85/1.06  # Proof object initial clauses used    : 36
% 0.85/1.06  # Proof object initial formulas used   : 32
% 0.85/1.06  # Proof object generating inferences   : 42
% 0.85/1.06  # Proof object simplifying inferences  : 72
% 0.85/1.06  # Training examples: 0 positive, 0 negative
% 0.85/1.06  # Parsed axioms                        : 33
% 0.85/1.06  # Removed by relevancy pruning/SinE    : 0
% 0.85/1.06  # Initial clauses                      : 40
% 0.85/1.06  # Removed in clause preprocessing      : 4
% 0.85/1.06  # Initial clauses in saturation        : 36
% 0.85/1.06  # Processed clauses                    : 10458
% 0.85/1.06  # ...of these trivial                  : 145
% 0.85/1.06  # ...subsumed                          : 8580
% 0.85/1.06  # ...remaining for further processing  : 1733
% 0.85/1.06  # Other redundant clauses eliminated   : 0
% 0.85/1.06  # Clauses deleted for lack of memory   : 0
% 0.85/1.06  # Backward-subsumed                    : 41
% 0.85/1.06  # Backward-rewritten                   : 52
% 0.85/1.06  # Generated clauses                    : 67567
% 0.85/1.06  # ...of the previous two non-trivial   : 59860
% 0.85/1.06  # Contextual simplify-reflections      : 34
% 0.85/1.06  # Paramodulations                      : 67567
% 0.85/1.06  # Factorizations                       : 0
% 0.85/1.06  # Equation resolutions                 : 0
% 0.85/1.06  # Propositional unsat checks           : 0
% 0.85/1.06  #    Propositional check models        : 0
% 0.85/1.06  #    Propositional check unsatisfiable : 0
% 0.85/1.07  #    Propositional clauses             : 0
% 0.85/1.07  #    Propositional clauses after purity: 0
% 0.85/1.07  #    Propositional unsat core size     : 0
% 0.85/1.07  #    Propositional preprocessing time  : 0.000
% 0.85/1.07  #    Propositional encoding time       : 0.000
% 0.85/1.07  #    Propositional solver time         : 0.000
% 0.85/1.07  #    Success case prop preproc time    : 0.000
% 0.85/1.07  #    Success case prop encoding time   : 0.000
% 0.85/1.07  #    Success case prop solver time     : 0.000
% 0.85/1.07  # Current number of processed clauses  : 1604
% 0.85/1.07  #    Positive orientable unit clauses  : 158
% 0.85/1.07  #    Positive unorientable unit clauses: 2
% 0.85/1.07  #    Negative unit clauses             : 13
% 0.85/1.07  #    Non-unit-clauses                  : 1431
% 0.85/1.07  # Current number of unprocessed clauses: 49204
% 0.85/1.07  # ...number of literals in the above   : 170862
% 0.85/1.07  # Current number of archived formulas  : 0
% 0.85/1.07  # Current number of archived clauses   : 133
% 0.85/1.07  # Clause-clause subsumption calls (NU) : 304770
% 0.85/1.07  # Rec. Clause-clause subsumption calls : 234678
% 0.85/1.07  # Non-unit clause-clause subsumptions  : 6084
% 0.85/1.07  # Unit Clause-clause subsumption calls : 2914
% 0.85/1.07  # Rewrite failures with RHS unbound    : 0
% 0.85/1.07  # BW rewrite match attempts            : 434
% 0.85/1.07  # BW rewrite match successes           : 39
% 0.85/1.07  # Condensation attempts                : 0
% 0.85/1.07  # Condensation successes               : 0
% 0.85/1.07  # Termbank termtop insertions          : 1136318
% 0.85/1.07  
% 0.85/1.07  # -------------------------------------------------
% 0.85/1.07  # User time                : 0.712 s
% 0.85/1.07  # System time              : 0.024 s
% 0.85/1.07  # Total time               : 0.736 s
% 0.85/1.07  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------

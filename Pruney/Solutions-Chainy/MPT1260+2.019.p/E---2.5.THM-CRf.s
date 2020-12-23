%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:11:17 EST 2020

% Result     : Theorem 0.72s
% Output     : CNFRefutation 0.72s
% Verified   : 
% Statistics : Number of formulae       :  187 (66324 expanded)
%              Number of clauses        :  126 (32112 expanded)
%              Number of leaves         :   30 (17062 expanded)
%              Depth                    :   24
%              Number of atoms          :  379 (89757 expanded)
%              Number of equality atoms :  133 (60215 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(dt_k6_subset_1,axiom,(
    ! [X1,X2] : m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

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

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t48_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(X2,k2_pre_topc(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

fof(t51_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(l78_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(t32_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => k7_subset_1(X1,X2,X3) = k9_subset_1(X1,X2,k3_subset_1(X1,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

fof(t74_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k1_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(idempotence_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

fof(rc2_subset_1,axiom,(
    ! [X1] :
    ? [X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
      & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_subset_1)).

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

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(fc9_tops_1,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => v3_pre_topc(k1_tops_1(X1,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(c_0_30,plain,(
    ! [X17,X18] : k4_xboole_0(X17,X18) = k5_xboole_0(X17,k3_xboole_0(X17,X18)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_31,plain,(
    ! [X54,X55] : k1_setfam_1(k2_tarski(X54,X55)) = k3_xboole_0(X54,X55) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_32,plain,(
    ! [X26,X27] : k2_xboole_0(X26,X27) = k5_xboole_0(X26,k4_xboole_0(X27,X26)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

cnf(c_0_33,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_34,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_35,plain,(
    ! [X34,X35] : m1_subset_1(k6_subset_1(X34,X35),k1_zfmisc_1(X34)) ),
    inference(variable_rename,[status(thm)],[dt_k6_subset_1])).

fof(c_0_36,plain,(
    ! [X46,X47] : k6_subset_1(X46,X47) = k4_xboole_0(X46,X47) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

fof(c_0_37,plain,(
    ! [X19,X20] : r1_tarski(k3_xboole_0(X19,X20),X19) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_38,plain,(
    ! [X21] : k2_xboole_0(X21,k1_xboole_0) = X21 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_39,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_33,c_0_34])).

fof(c_0_41,plain,(
    ! [X23] : k4_xboole_0(k1_xboole_0,X23) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

cnf(c_0_42,plain,
    ( m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_44,plain,(
    ! [X28,X29] : k2_tarski(X28,X29) = k2_tarski(X29,X28) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

fof(c_0_45,plain,(
    ! [X22] :
      ( ~ r1_tarski(X22,k1_xboole_0)
      | X22 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

cnf(c_0_46,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_47,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_48,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))) ),
    inference(rw,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_49,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_50,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( r2_hidden(X8,X5)
        | ~ r2_hidden(X8,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X8,X6)
        | ~ r2_hidden(X8,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k4_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k4_xboole_0(X10,X11) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k4_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_51,plain,(
    ! [X14] : k3_xboole_0(X14,X14) = X14 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

fof(c_0_52,plain,(
    ! [X30,X31] :
      ( ~ m1_subset_1(X31,k1_zfmisc_1(X30))
      | k3_subset_1(X30,X31) = k4_xboole_0(X30,X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_53,plain,
    ( m1_subset_1(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_43]),c_0_40])).

cnf(c_0_54,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_55,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_56,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_46,c_0_34])).

cnf(c_0_57,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,X1)))) = X1 ),
    inference(rw,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_58,plain,
    ( k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,X1))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_49,c_0_40])).

cnf(c_0_59,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_60,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_61,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_62,plain,
    ( m1_subset_1(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_63,plain,
    ( k1_setfam_1(k2_tarski(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_64,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_65,plain,
    ( X3 != k5_xboole_0(X4,k1_setfam_1(k2_tarski(X4,X2)))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_59,c_0_40])).

cnf(c_0_66,plain,
    ( k1_setfam_1(k2_tarski(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_60,c_0_34])).

cnf(c_0_67,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_61,c_0_40])).

cnf(c_0_68,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64])).

cnf(c_0_69,plain,
    ( X1 != k5_xboole_0(X2,X2)
    | ~ r2_hidden(X3,X1)
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

fof(c_0_70,plain,(
    ! [X41,X42,X43] :
      ( ~ m1_subset_1(X42,k1_zfmisc_1(X41))
      | ~ r2_hidden(X43,X42)
      | r2_hidden(X43,X41) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_71,plain,
    ( m1_subset_1(k5_xboole_0(X1,X1),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_66])).

cnf(c_0_72,plain,
    ( k5_xboole_0(X1,X1) = k3_subset_1(X1,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_66])).

cnf(c_0_73,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_69])).

cnf(c_0_74,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

fof(c_0_75,plain,(
    ! [X48,X49,X50] :
      ( ~ m1_subset_1(X49,k1_zfmisc_1(X48))
      | k7_subset_1(X48,X49,X50) = k4_xboole_0(X49,X50) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

cnf(c_0_76,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_77,plain,
    ( m1_subset_1(k3_subset_1(X1,X1),k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_78,plain,
    ( ~ r2_hidden(X1,k3_subset_1(X2,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_73,c_0_72])).

cnf(c_0_79,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_64])).

cnf(c_0_80,plain,
    ( X3 = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_74,c_0_40])).

fof(c_0_81,plain,(
    ! [X39,X40] :
      ( ~ m1_subset_1(X40,k1_zfmisc_1(X39))
      | k3_subset_1(X39,k3_subset_1(X39,X40)) = X40 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

cnf(c_0_82,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

fof(c_0_83,plain,(
    ! [X32,X33] :
      ( ~ m1_subset_1(X33,k1_zfmisc_1(X32))
      | m1_subset_1(k3_subset_1(X32,X33),k1_zfmisc_1(X32)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

cnf(c_0_84,plain,
    ( ~ r2_hidden(X1,k3_subset_1(X2,X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_78])).

cnf(c_0_85,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_3(k1_xboole_0,X2,X1),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_58])).

cnf(c_0_86,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

fof(c_0_87,plain,(
    ! [X58,X59] :
      ( ~ l1_pre_topc(X58)
      | ~ m1_subset_1(X59,k1_zfmisc_1(u1_struct_0(X58)))
      | m1_subset_1(k2_pre_topc(X58,X59),k1_zfmisc_1(u1_struct_0(X58))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

cnf(c_0_88,plain,
    ( k7_subset_1(X2,X1,X3) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_82,c_0_40])).

cnf(c_0_89,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_90,plain,
    ( k3_subset_1(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_91,plain,
    ( k3_subset_1(X1,k3_subset_1(X1,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_86,c_0_68])).

cnf(c_0_92,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

cnf(c_0_93,plain,
    ( k5_xboole_0(k3_subset_1(X1,X2),k1_setfam_1(k2_tarski(k3_subset_1(X1,X2),X3))) = k7_subset_1(X1,k3_subset_1(X1,X2),X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_94,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_77,c_0_90])).

cnf(c_0_95,plain,
    ( k3_subset_1(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_91,c_0_90])).

fof(c_0_96,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v3_pre_topc(X2,X1)
            <=> k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t76_tops_1])).

fof(c_0_97,plain,(
    ! [X56,X57] :
      ( ( ~ m1_subset_1(X56,k1_zfmisc_1(X57))
        | r1_tarski(X56,X57) )
      & ( ~ r1_tarski(X56,X57)
        | m1_subset_1(X56,k1_zfmisc_1(X57)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_98,plain,
    ( k5_xboole_0(k2_pre_topc(X1,X2),k1_setfam_1(k2_tarski(k2_pre_topc(X1,X2),X3))) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_88,c_0_92])).

cnf(c_0_99,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X1,X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_95]),c_0_95]),c_0_95])).

fof(c_0_100,negated_conjecture,
    ( v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & ( ~ v3_pre_topc(esk4_0,esk3_0)
      | k2_tops_1(esk3_0,esk4_0) != k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0) )
    & ( v3_pre_topc(esk4_0,esk3_0)
      | k2_tops_1(esk3_0,esk4_0) = k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_96])])])).

cnf(c_0_101,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_97])).

cnf(c_0_102,plain,
    ( k7_subset_1(k2_pre_topc(X1,X2),k2_pre_topc(X1,X2),X3) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(rw,[status(thm)],[c_0_98,c_0_99])).

cnf(c_0_103,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_100])).

cnf(c_0_104,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_100])).

cnf(c_0_105,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k3_subset_1(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_67,c_0_101])).

cnf(c_0_106,plain,
    ( k7_subset_1(X1,X2,X3) = k7_subset_1(X2,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_88,c_0_99])).

fof(c_0_107,plain,(
    ! [X60,X61] :
      ( ~ l1_pre_topc(X60)
      | ~ m1_subset_1(X61,k1_zfmisc_1(u1_struct_0(X60)))
      | r1_tarski(X61,k2_pre_topc(X60,X61)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_pre_topc])])])).

cnf(c_0_108,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_97])).

fof(c_0_109,plain,(
    ! [X24,X25] : k2_xboole_0(k3_xboole_0(X24,X25),k4_xboole_0(X24,X25)) = X24 ),
    inference(variable_rename,[status(thm)],[t51_xboole_1])).

cnf(c_0_110,plain,
    ( m1_subset_1(k7_subset_1(X1,X1,X2),k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_53,c_0_99])).

cnf(c_0_111,negated_conjecture,
    ( k7_subset_1(k2_pre_topc(esk3_0,esk4_0),k2_pre_topc(esk3_0,esk4_0),X1) = k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_103]),c_0_104])])).

fof(c_0_112,plain,(
    ! [X64,X65] :
      ( ~ l1_pre_topc(X64)
      | ~ m1_subset_1(X65,k1_zfmisc_1(u1_struct_0(X64)))
      | k2_tops_1(X64,X65) = k7_subset_1(u1_struct_0(X64),k2_pre_topc(X64,X65),k1_tops_1(X64,X65)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l78_tops_1])])])).

cnf(c_0_113,plain,
    ( k7_subset_1(X1,X1,X2) = k3_subset_1(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_105,c_0_99])).

cnf(c_0_114,plain,
    ( k7_subset_1(X1,X2,X3) = k7_subset_1(X2,X2,X3)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_106,c_0_101])).

cnf(c_0_115,plain,
    ( r1_tarski(X2,k2_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_107])).

cnf(c_0_116,plain,
    ( r1_tarski(k2_pre_topc(X1,X2),u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_108,c_0_92])).

cnf(c_0_117,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_109])).

cnf(c_0_118,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

fof(c_0_119,plain,(
    ! [X51,X52,X53] :
      ( ~ m1_subset_1(X52,k1_zfmisc_1(X51))
      | ~ m1_subset_1(X53,k1_zfmisc_1(X51))
      | k7_subset_1(X51,X52,X53) = k9_subset_1(X51,X52,k3_subset_1(X51,X53)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_subset_1])])])).

cnf(c_0_120,negated_conjecture,
    ( m1_subset_1(k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),X1),k1_zfmisc_1(k2_pre_topc(esk3_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_110,c_0_111])).

cnf(c_0_121,plain,
    ( k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_112])).

cnf(c_0_122,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk3_0)
    | k2_tops_1(esk3_0,esk4_0) = k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_100])).

cnf(c_0_123,plain,
    ( k7_subset_1(X1,X2,X3) = k3_subset_1(X2,X3)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_113,c_0_114])).

cnf(c_0_124,negated_conjecture,
    ( r1_tarski(esk4_0,k2_pre_topc(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_103]),c_0_104])])).

cnf(c_0_125,negated_conjecture,
    ( r1_tarski(k2_pre_topc(esk3_0,esk4_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_103]),c_0_104])])).

fof(c_0_126,plain,(
    ! [X71,X72] :
      ( ~ l1_pre_topc(X71)
      | ~ m1_subset_1(X72,k1_zfmisc_1(u1_struct_0(X71)))
      | k1_tops_1(X71,X72) = k7_subset_1(u1_struct_0(X71),X72,k2_tops_1(X71,X72)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_tops_1])])])).

cnf(c_0_127,plain,
    ( k5_xboole_0(k1_setfam_1(k2_tarski(X1,X2)),k5_xboole_0(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_setfam_1(k2_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_setfam_1(k2_tarski(X1,X2)))))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_117,c_0_34]),c_0_40]),c_0_48])).

cnf(c_0_128,plain,
    ( X3 = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(rw,[status(thm)],[c_0_118,c_0_40])).

cnf(c_0_129,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(X3,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_76,c_0_101])).

cnf(c_0_130,plain,
    ( k7_subset_1(X2,X1,X3) = k9_subset_1(X2,X1,k3_subset_1(X2,X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_119])).

cnf(c_0_131,negated_conjecture,
    ( m1_subset_1(k2_tops_1(esk3_0,esk4_0),k1_zfmisc_1(k2_pre_topc(esk3_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_121]),c_0_104]),c_0_103])])).

cnf(c_0_132,plain,
    ( k3_subset_1(X1,k3_subset_1(X1,X2)) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_86,c_0_101])).

cnf(c_0_133,negated_conjecture,
    ( k3_subset_1(k2_pre_topc(esk3_0,esk4_0),esk4_0) = k2_tops_1(esk3_0,esk4_0)
    | v3_pre_topc(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_123]),c_0_124]),c_0_125])])).

fof(c_0_134,plain,(
    ! [X36,X37,X38] :
      ( ~ m1_subset_1(X38,k1_zfmisc_1(X36))
      | k9_subset_1(X36,X37,X37) = X37 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[idempotence_k9_subset_1])])).

fof(c_0_135,plain,(
    ! [X44] :
      ( m1_subset_1(esk2_1(X44),k1_zfmisc_1(X44))
      & v1_xboole_0(esk2_1(X44)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc2_subset_1])])).

cnf(c_0_136,plain,
    ( k1_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_126])).

cnf(c_0_137,plain,
    ( k5_xboole_0(k1_setfam_1(k2_tarski(X1,X2)),k5_xboole_0(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X1,X2)),k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))))))) = X1 ),
    inference(rw,[status(thm)],[c_0_127,c_0_54])).

cnf(c_0_138,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_setfam_1(k2_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X3))) = k7_subset_1(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X3) ),
    inference(spm,[status(thm)],[c_0_88,c_0_53])).

cnf(c_0_139,plain,
    ( X1 = k7_subset_1(X2,X2,X3)
    | r2_hidden(esk1_3(X2,X3,X1),X1)
    | ~ r2_hidden(esk1_3(X2,X3,X1),X3) ),
    inference(rw,[status(thm)],[c_0_128,c_0_99])).

cnf(c_0_140,negated_conjecture,
    ( r2_hidden(X1,k2_pre_topc(esk3_0,esk4_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_129,c_0_124])).

cnf(c_0_141,plain,
    ( X1 = k7_subset_1(X2,X2,X3)
    | r2_hidden(esk1_3(X2,X3,X1),X2)
    | r2_hidden(esk1_3(X2,X3,X1),X1) ),
    inference(rw,[status(thm)],[c_0_80,c_0_99])).

fof(c_0_142,plain,(
    ! [X66,X67,X68] :
      ( ~ l1_pre_topc(X66)
      | ~ m1_subset_1(X67,k1_zfmisc_1(u1_struct_0(X66)))
      | ~ m1_subset_1(X68,k1_zfmisc_1(u1_struct_0(X66)))
      | ~ v3_pre_topc(X67,X66)
      | ~ r1_tarski(X67,X68)
      | r1_tarski(X67,k1_tops_1(X66,X68)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_tops_1])])])).

fof(c_0_143,plain,(
    ! [X15,X16] :
      ( ( r1_tarski(X15,X16)
        | X15 != X16 )
      & ( r1_tarski(X16,X15)
        | X15 != X16 )
      & ( ~ r1_tarski(X15,X16)
        | ~ r1_tarski(X16,X15)
        | X15 = X16 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_144,negated_conjecture,
    ( k9_subset_1(k2_pre_topc(esk3_0,esk4_0),X1,k3_subset_1(k2_pre_topc(esk3_0,esk4_0),k2_tops_1(esk3_0,esk4_0))) = k7_subset_1(k2_pre_topc(esk3_0,esk4_0),X1,k2_tops_1(esk3_0,esk4_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_pre_topc(esk3_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_130,c_0_131])).

cnf(c_0_145,negated_conjecture,
    ( k3_subset_1(k2_pre_topc(esk3_0,esk4_0),k2_tops_1(esk3_0,esk4_0)) = esk4_0
    | v3_pre_topc(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132,c_0_133]),c_0_124])])).

cnf(c_0_146,plain,
    ( k9_subset_1(X2,X3,X3) = X3
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_134])).

cnf(c_0_147,plain,
    ( m1_subset_1(esk2_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_135])).

cnf(c_0_148,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk3_0),esk4_0,k2_tops_1(esk3_0,esk4_0)) = k1_tops_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136,c_0_103]),c_0_104])])).

cnf(c_0_149,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk3_0),esk4_0,X1) = k5_xboole_0(esk4_0,k1_setfam_1(k2_tarski(esk4_0,X1))) ),
    inference(spm,[status(thm)],[c_0_88,c_0_103])).

cnf(c_0_150,plain,
    ( k5_xboole_0(k1_setfam_1(k2_tarski(X1,X2)),k5_xboole_0(k7_subset_1(X1,X1,X2),k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X1,X2)),k7_subset_1(X1,X1,X2))))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_137,c_0_99]),c_0_99])).

cnf(c_0_151,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))) = k7_subset_1(X1,X1,X2) ),
    inference(spm,[status(thm)],[c_0_99,c_0_54])).

cnf(c_0_152,plain,
    ( k7_subset_1(k7_subset_1(X1,X1,X2),k7_subset_1(X1,X1,X2),X3) = k7_subset_1(X1,k7_subset_1(X1,X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_138,c_0_99]),c_0_99]),c_0_99]),c_0_99])).

cnf(c_0_153,negated_conjecture,
    ( X1 = k7_subset_1(X2,X2,k2_pre_topc(esk3_0,esk4_0))
    | r2_hidden(esk1_3(X2,k2_pre_topc(esk3_0,esk4_0),X1),X1)
    | ~ r2_hidden(esk1_3(X2,k2_pre_topc(esk3_0,esk4_0),X1),esk4_0) ),
    inference(spm,[status(thm)],[c_0_139,c_0_140])).

cnf(c_0_154,plain,
    ( k7_subset_1(X1,X1,X2) = k1_xboole_0
    | r2_hidden(esk1_3(X1,X2,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_79,c_0_141])).

cnf(c_0_155,plain,
    ( r1_tarski(X2,k1_tops_1(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X2,X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_142])).

cnf(c_0_156,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_143])).

cnf(c_0_157,negated_conjecture,
    ( k7_subset_1(k2_pre_topc(esk3_0,esk4_0),X1,k2_tops_1(esk3_0,esk4_0)) = k9_subset_1(k2_pre_topc(esk3_0,esk4_0),X1,esk4_0)
    | v3_pre_topc(esk4_0,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_pre_topc(esk3_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_144,c_0_145])).

cnf(c_0_158,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk3_0)
    | m1_subset_1(esk4_0,k1_zfmisc_1(k2_pre_topc(esk3_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_145]),c_0_131])])).

cnf(c_0_159,plain,
    ( k9_subset_1(X1,X2,X2) = X2 ),
    inference(spm,[status(thm)],[c_0_146,c_0_147])).

cnf(c_0_160,negated_conjecture,
    ( k5_xboole_0(esk4_0,k1_setfam_1(k2_tarski(esk4_0,k2_tops_1(esk3_0,esk4_0)))) = k1_tops_1(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_148,c_0_149])).

cnf(c_0_161,plain,
    ( r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X1) ),
    inference(spm,[status(thm)],[c_0_108,c_0_53])).

cnf(c_0_162,plain,
    ( k5_xboole_0(k1_setfam_1(k2_tarski(X1,X2)),k7_subset_1(X1,k7_subset_1(X1,X1,X2),k1_setfam_1(k2_tarski(X1,X2)))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_150,c_0_151]),c_0_152])).

cnf(c_0_163,negated_conjecture,
    ( k7_subset_1(esk4_0,esk4_0,k2_pre_topc(esk3_0,esk4_0)) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_153,c_0_154]),c_0_79])).

cnf(c_0_164,plain,
    ( k7_subset_1(X1,k1_xboole_0,X2) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_94]),c_0_63]),c_0_64])).

fof(c_0_165,plain,(
    ! [X62,X63] :
      ( ~ v2_pre_topc(X62)
      | ~ l1_pre_topc(X62)
      | ~ m1_subset_1(X63,k1_zfmisc_1(u1_struct_0(X62)))
      | v3_pre_topc(k1_tops_1(X62,X63),X62) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).

cnf(c_0_166,negated_conjecture,
    ( r1_tarski(X1,k1_tops_1(esk3_0,esk4_0))
    | ~ v3_pre_topc(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r1_tarski(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_155,c_0_103]),c_0_104])])).

cnf(c_0_167,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_156])).

cnf(c_0_168,negated_conjecture,
    ( k7_subset_1(k2_pre_topc(esk3_0,esk4_0),esk4_0,k2_tops_1(esk3_0,esk4_0)) = esk4_0
    | v3_pre_topc(esk4_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_157,c_0_158]),c_0_159])).

cnf(c_0_169,negated_conjecture,
    ( k7_subset_1(esk4_0,esk4_0,k2_tops_1(esk3_0,esk4_0)) = k1_tops_1(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_160,c_0_99])).

cnf(c_0_170,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_143])).

cnf(c_0_171,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk3_0,esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_161,c_0_160])).

cnf(c_0_172,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk4_0,k2_pre_topc(esk3_0,esk4_0))) = esk4_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_162,c_0_163]),c_0_164]),c_0_64])).

cnf(c_0_173,plain,
    ( v3_pre_topc(k1_tops_1(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_165])).

cnf(c_0_174,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_100])).

cnf(c_0_175,negated_conjecture,
    ( r1_tarski(esk4_0,k1_tops_1(esk3_0,esk4_0))
    | ~ v3_pre_topc(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_166,c_0_103]),c_0_167])])).

cnf(c_0_176,negated_conjecture,
    ( k1_tops_1(esk3_0,esk4_0) = esk4_0
    | v3_pre_topc(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_168]),c_0_169]),c_0_124])])).

cnf(c_0_177,negated_conjecture,
    ( k1_tops_1(esk3_0,esk4_0) = esk4_0
    | ~ r1_tarski(esk4_0,k1_tops_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_170,c_0_171])).

cnf(c_0_178,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0) = k5_xboole_0(k2_pre_topc(esk3_0,esk4_0),esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_151,c_0_172]),c_0_111])).

cnf(c_0_179,negated_conjecture,
    ( ~ v3_pre_topc(esk4_0,esk3_0)
    | k2_tops_1(esk3_0,esk4_0) != k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_100])).

cnf(c_0_180,negated_conjecture,
    ( v3_pre_topc(k1_tops_1(esk3_0,esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_173,c_0_103]),c_0_174]),c_0_104])])).

cnf(c_0_181,negated_conjecture,
    ( k1_tops_1(esk3_0,esk4_0) = esk4_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_175,c_0_176]),c_0_177])).

cnf(c_0_182,negated_conjecture,
    ( k5_xboole_0(k2_pre_topc(esk3_0,esk4_0),esk4_0) = k3_subset_1(k2_pre_topc(esk3_0,esk4_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_178]),c_0_124]),c_0_125])])).

cnf(c_0_183,negated_conjecture,
    ( k3_subset_1(k2_pre_topc(esk3_0,esk4_0),esk4_0) != k2_tops_1(esk3_0,esk4_0)
    | ~ v3_pre_topc(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_179,c_0_123]),c_0_124]),c_0_125])])).

cnf(c_0_184,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_180,c_0_181])).

cnf(c_0_185,negated_conjecture,
    ( k3_subset_1(k2_pre_topc(esk3_0,esk4_0),esk4_0) = k2_tops_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_181]),c_0_178]),c_0_182]),c_0_104]),c_0_103])])).

cnf(c_0_186,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_183,c_0_184])]),c_0_185])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:25:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.72/0.90  # AutoSched0-Mode selected heuristic G_E___107_C36_F1_PI_AE_Q4_CS_SP_PS_S0Y
% 0.72/0.90  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.72/0.90  #
% 0.72/0.90  # Preprocessing time       : 0.029 s
% 0.72/0.90  # Presaturation interreduction done
% 0.72/0.90  
% 0.72/0.90  # Proof found!
% 0.72/0.90  # SZS status Theorem
% 0.72/0.90  # SZS output start CNFRefutation
% 0.72/0.90  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.72/0.90  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.72/0.90  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.72/0.90  fof(dt_k6_subset_1, axiom, ![X1, X2]:m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 0.72/0.90  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 0.72/0.90  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.72/0.90  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 0.72/0.90  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 0.72/0.90  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.72/0.90  fof(t3_xboole_1, axiom, ![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 0.72/0.90  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.72/0.90  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.72/0.90  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 0.72/0.90  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 0.72/0.90  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 0.72/0.90  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 0.72/0.90  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 0.72/0.90  fof(dt_k2_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 0.72/0.90  fof(t76_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_tops_1)).
% 0.72/0.90  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.72/0.90  fof(t48_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(X2,k2_pre_topc(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_pre_topc)).
% 0.72/0.90  fof(t51_xboole_1, axiom, ![X1, X2]:k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 0.72/0.90  fof(l78_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 0.72/0.90  fof(t32_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k9_subset_1(X1,X2,k3_subset_1(X1,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_subset_1)).
% 0.72/0.90  fof(t74_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k1_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 0.72/0.90  fof(idempotence_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k9_subset_1)).
% 0.72/0.90  fof(rc2_subset_1, axiom, ![X1]:?[X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))&v1_xboole_0(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc2_subset_1)).
% 0.72/0.90  fof(t56_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v3_pre_topc(X2,X1)&r1_tarski(X2,X3))=>r1_tarski(X2,k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tops_1)).
% 0.72/0.90  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.72/0.90  fof(fc9_tops_1, axiom, ![X1, X2]:(((v2_pre_topc(X1)&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v3_pre_topc(k1_tops_1(X1,X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 0.72/0.90  fof(c_0_30, plain, ![X17, X18]:k4_xboole_0(X17,X18)=k5_xboole_0(X17,k3_xboole_0(X17,X18)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.72/0.90  fof(c_0_31, plain, ![X54, X55]:k1_setfam_1(k2_tarski(X54,X55))=k3_xboole_0(X54,X55), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.72/0.90  fof(c_0_32, plain, ![X26, X27]:k2_xboole_0(X26,X27)=k5_xboole_0(X26,k4_xboole_0(X27,X26)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.72/0.90  cnf(c_0_33, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.72/0.90  cnf(c_0_34, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.72/0.90  fof(c_0_35, plain, ![X34, X35]:m1_subset_1(k6_subset_1(X34,X35),k1_zfmisc_1(X34)), inference(variable_rename,[status(thm)],[dt_k6_subset_1])).
% 0.72/0.90  fof(c_0_36, plain, ![X46, X47]:k6_subset_1(X46,X47)=k4_xboole_0(X46,X47), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 0.72/0.90  fof(c_0_37, plain, ![X19, X20]:r1_tarski(k3_xboole_0(X19,X20),X19), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.72/0.90  fof(c_0_38, plain, ![X21]:k2_xboole_0(X21,k1_xboole_0)=X21, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.72/0.90  cnf(c_0_39, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.72/0.90  cnf(c_0_40, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_33, c_0_34])).
% 0.72/0.90  fof(c_0_41, plain, ![X23]:k4_xboole_0(k1_xboole_0,X23)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 0.72/0.90  cnf(c_0_42, plain, (m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.72/0.90  cnf(c_0_43, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.72/0.90  fof(c_0_44, plain, ![X28, X29]:k2_tarski(X28,X29)=k2_tarski(X29,X28), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.72/0.90  fof(c_0_45, plain, ![X22]:(~r1_tarski(X22,k1_xboole_0)|X22=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).
% 0.72/0.90  cnf(c_0_46, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.72/0.90  cnf(c_0_47, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.72/0.90  cnf(c_0_48, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1))))), inference(rw,[status(thm)],[c_0_39, c_0_40])).
% 0.72/0.90  cnf(c_0_49, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.72/0.90  fof(c_0_50, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6))&(~r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k4_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k4_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))&(~r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.72/0.90  fof(c_0_51, plain, ![X14]:k3_xboole_0(X14,X14)=X14, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.72/0.90  fof(c_0_52, plain, ![X30, X31]:(~m1_subset_1(X31,k1_zfmisc_1(X30))|k3_subset_1(X30,X31)=k4_xboole_0(X30,X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.72/0.90  cnf(c_0_53, plain, (m1_subset_1(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_zfmisc_1(X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_43]), c_0_40])).
% 0.72/0.90  cnf(c_0_54, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.72/0.90  cnf(c_0_55, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.72/0.90  cnf(c_0_56, plain, (r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_46, c_0_34])).
% 0.72/0.90  cnf(c_0_57, plain, (k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,X1))))=X1), inference(rw,[status(thm)],[c_0_47, c_0_48])).
% 0.72/0.90  cnf(c_0_58, plain, (k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,X1)))=k1_xboole_0), inference(rw,[status(thm)],[c_0_49, c_0_40])).
% 0.72/0.90  cnf(c_0_59, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.72/0.90  cnf(c_0_60, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.72/0.90  cnf(c_0_61, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.72/0.90  cnf(c_0_62, plain, (m1_subset_1(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.72/0.90  cnf(c_0_63, plain, (k1_setfam_1(k2_tarski(k1_xboole_0,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.72/0.90  cnf(c_0_64, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_57, c_0_58])).
% 0.72/0.90  cnf(c_0_65, plain, (X3!=k5_xboole_0(X4,k1_setfam_1(k2_tarski(X4,X2)))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_59, c_0_40])).
% 0.72/0.90  cnf(c_0_66, plain, (k1_setfam_1(k2_tarski(X1,X1))=X1), inference(rw,[status(thm)],[c_0_60, c_0_34])).
% 0.72/0.90  cnf(c_0_67, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_61, c_0_40])).
% 0.72/0.90  cnf(c_0_68, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_64])).
% 0.72/0.90  cnf(c_0_69, plain, (X1!=k5_xboole_0(X2,X2)|~r2_hidden(X3,X1)|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.72/0.90  fof(c_0_70, plain, ![X41, X42, X43]:(~m1_subset_1(X42,k1_zfmisc_1(X41))|(~r2_hidden(X43,X42)|r2_hidden(X43,X41))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.72/0.90  cnf(c_0_71, plain, (m1_subset_1(k5_xboole_0(X1,X1),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_53, c_0_66])).
% 0.72/0.90  cnf(c_0_72, plain, (k5_xboole_0(X1,X1)=k3_subset_1(X1,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_66])).
% 0.72/0.90  cnf(c_0_73, plain, (~r2_hidden(X1,k5_xboole_0(X2,X2))|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_69])).
% 0.72/0.90  cnf(c_0_74, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.72/0.90  fof(c_0_75, plain, ![X48, X49, X50]:(~m1_subset_1(X49,k1_zfmisc_1(X48))|k7_subset_1(X48,X49,X50)=k4_xboole_0(X49,X50)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 0.72/0.90  cnf(c_0_76, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.72/0.90  cnf(c_0_77, plain, (m1_subset_1(k3_subset_1(X1,X1),k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_71, c_0_72])).
% 0.72/0.90  cnf(c_0_78, plain, (~r2_hidden(X1,k3_subset_1(X2,X2))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_73, c_0_72])).
% 0.72/0.90  cnf(c_0_79, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_73, c_0_64])).
% 0.72/0.90  cnf(c_0_80, plain, (X3=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_74, c_0_40])).
% 0.72/0.90  fof(c_0_81, plain, ![X39, X40]:(~m1_subset_1(X40,k1_zfmisc_1(X39))|k3_subset_1(X39,k3_subset_1(X39,X40))=X40), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 0.72/0.90  cnf(c_0_82, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.72/0.90  fof(c_0_83, plain, ![X32, X33]:(~m1_subset_1(X33,k1_zfmisc_1(X32))|m1_subset_1(k3_subset_1(X32,X33),k1_zfmisc_1(X32))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 0.72/0.90  cnf(c_0_84, plain, (~r2_hidden(X1,k3_subset_1(X2,X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_78])).
% 0.72/0.90  cnf(c_0_85, plain, (X1=k1_xboole_0|r2_hidden(esk1_3(k1_xboole_0,X2,X1),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_58])).
% 0.72/0.90  cnf(c_0_86, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.72/0.90  fof(c_0_87, plain, ![X58, X59]:(~l1_pre_topc(X58)|~m1_subset_1(X59,k1_zfmisc_1(u1_struct_0(X58)))|m1_subset_1(k2_pre_topc(X58,X59),k1_zfmisc_1(u1_struct_0(X58)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).
% 0.72/0.90  cnf(c_0_88, plain, (k7_subset_1(X2,X1,X3)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_82, c_0_40])).
% 0.72/0.90  cnf(c_0_89, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_83])).
% 0.72/0.90  cnf(c_0_90, plain, (k3_subset_1(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_84, c_0_85])).
% 0.72/0.90  cnf(c_0_91, plain, (k3_subset_1(X1,k3_subset_1(X1,X1))=X1), inference(spm,[status(thm)],[c_0_86, c_0_68])).
% 0.72/0.90  cnf(c_0_92, plain, (m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_87])).
% 0.72/0.90  cnf(c_0_93, plain, (k5_xboole_0(k3_subset_1(X1,X2),k1_setfam_1(k2_tarski(k3_subset_1(X1,X2),X3)))=k7_subset_1(X1,k3_subset_1(X1,X2),X3)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 0.72/0.90  cnf(c_0_94, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_77, c_0_90])).
% 0.72/0.90  cnf(c_0_95, plain, (k3_subset_1(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_91, c_0_90])).
% 0.72/0.90  fof(c_0_96, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2))))), inference(assume_negation,[status(cth)],[t76_tops_1])).
% 0.72/0.90  fof(c_0_97, plain, ![X56, X57]:((~m1_subset_1(X56,k1_zfmisc_1(X57))|r1_tarski(X56,X57))&(~r1_tarski(X56,X57)|m1_subset_1(X56,k1_zfmisc_1(X57)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.72/0.90  cnf(c_0_98, plain, (k5_xboole_0(k2_pre_topc(X1,X2),k1_setfam_1(k2_tarski(k2_pre_topc(X1,X2),X3)))=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X3)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_88, c_0_92])).
% 0.72/0.90  cnf(c_0_99, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k7_subset_1(X1,X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_95]), c_0_95]), c_0_95])).
% 0.72/0.90  fof(c_0_100, negated_conjecture, ((v2_pre_topc(esk3_0)&l1_pre_topc(esk3_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&((~v3_pre_topc(esk4_0,esk3_0)|k2_tops_1(esk3_0,esk4_0)!=k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0))&(v3_pre_topc(esk4_0,esk3_0)|k2_tops_1(esk3_0,esk4_0)=k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_96])])])).
% 0.72/0.90  cnf(c_0_101, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_97])).
% 0.72/0.90  cnf(c_0_102, plain, (k7_subset_1(k2_pre_topc(X1,X2),k2_pre_topc(X1,X2),X3)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X3)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(rw,[status(thm)],[c_0_98, c_0_99])).
% 0.72/0.90  cnf(c_0_103, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_100])).
% 0.72/0.90  cnf(c_0_104, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_100])).
% 0.72/0.90  cnf(c_0_105, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k3_subset_1(X1,X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_67, c_0_101])).
% 0.72/0.90  cnf(c_0_106, plain, (k7_subset_1(X1,X2,X3)=k7_subset_1(X2,X2,X3)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_88, c_0_99])).
% 0.72/0.90  fof(c_0_107, plain, ![X60, X61]:(~l1_pre_topc(X60)|(~m1_subset_1(X61,k1_zfmisc_1(u1_struct_0(X60)))|r1_tarski(X61,k2_pre_topc(X60,X61)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_pre_topc])])])).
% 0.72/0.90  cnf(c_0_108, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_97])).
% 0.72/0.90  fof(c_0_109, plain, ![X24, X25]:k2_xboole_0(k3_xboole_0(X24,X25),k4_xboole_0(X24,X25))=X24, inference(variable_rename,[status(thm)],[t51_xboole_1])).
% 0.72/0.90  cnf(c_0_110, plain, (m1_subset_1(k7_subset_1(X1,X1,X2),k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_53, c_0_99])).
% 0.72/0.90  cnf(c_0_111, negated_conjecture, (k7_subset_1(k2_pre_topc(esk3_0,esk4_0),k2_pre_topc(esk3_0,esk4_0),X1)=k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_103]), c_0_104])])).
% 0.72/0.90  fof(c_0_112, plain, ![X64, X65]:(~l1_pre_topc(X64)|(~m1_subset_1(X65,k1_zfmisc_1(u1_struct_0(X64)))|k2_tops_1(X64,X65)=k7_subset_1(u1_struct_0(X64),k2_pre_topc(X64,X65),k1_tops_1(X64,X65)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l78_tops_1])])])).
% 0.72/0.90  cnf(c_0_113, plain, (k7_subset_1(X1,X1,X2)=k3_subset_1(X1,X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_105, c_0_99])).
% 0.72/0.90  cnf(c_0_114, plain, (k7_subset_1(X1,X2,X3)=k7_subset_1(X2,X2,X3)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_106, c_0_101])).
% 0.72/0.90  cnf(c_0_115, plain, (r1_tarski(X2,k2_pre_topc(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_107])).
% 0.72/0.90  cnf(c_0_116, plain, (r1_tarski(k2_pre_topc(X1,X2),u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_108, c_0_92])).
% 0.72/0.90  cnf(c_0_117, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_109])).
% 0.72/0.90  cnf(c_0_118, plain, (r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.72/0.90  fof(c_0_119, plain, ![X51, X52, X53]:(~m1_subset_1(X52,k1_zfmisc_1(X51))|(~m1_subset_1(X53,k1_zfmisc_1(X51))|k7_subset_1(X51,X52,X53)=k9_subset_1(X51,X52,k3_subset_1(X51,X53)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_subset_1])])])).
% 0.72/0.90  cnf(c_0_120, negated_conjecture, (m1_subset_1(k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),X1),k1_zfmisc_1(k2_pre_topc(esk3_0,esk4_0)))), inference(spm,[status(thm)],[c_0_110, c_0_111])).
% 0.72/0.90  cnf(c_0_121, plain, (k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_112])).
% 0.72/0.90  cnf(c_0_122, negated_conjecture, (v3_pre_topc(esk4_0,esk3_0)|k2_tops_1(esk3_0,esk4_0)=k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_100])).
% 0.72/0.90  cnf(c_0_123, plain, (k7_subset_1(X1,X2,X3)=k3_subset_1(X2,X3)|~r1_tarski(X3,X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_113, c_0_114])).
% 0.72/0.90  cnf(c_0_124, negated_conjecture, (r1_tarski(esk4_0,k2_pre_topc(esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_103]), c_0_104])])).
% 0.72/0.90  cnf(c_0_125, negated_conjecture, (r1_tarski(k2_pre_topc(esk3_0,esk4_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_103]), c_0_104])])).
% 0.72/0.90  fof(c_0_126, plain, ![X71, X72]:(~l1_pre_topc(X71)|(~m1_subset_1(X72,k1_zfmisc_1(u1_struct_0(X71)))|k1_tops_1(X71,X72)=k7_subset_1(u1_struct_0(X71),X72,k2_tops_1(X71,X72)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_tops_1])])])).
% 0.72/0.90  cnf(c_0_127, plain, (k5_xboole_0(k1_setfam_1(k2_tarski(X1,X2)),k5_xboole_0(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_setfam_1(k2_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_setfam_1(k2_tarski(X1,X2))))))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_117, c_0_34]), c_0_40]), c_0_48])).
% 0.72/0.90  cnf(c_0_128, plain, (X3=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))|r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(rw,[status(thm)],[c_0_118, c_0_40])).
% 0.72/0.90  cnf(c_0_129, plain, (r2_hidden(X1,X2)|~r1_tarski(X3,X2)|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_76, c_0_101])).
% 0.72/0.90  cnf(c_0_130, plain, (k7_subset_1(X2,X1,X3)=k9_subset_1(X2,X1,k3_subset_1(X2,X3))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_119])).
% 0.72/0.90  cnf(c_0_131, negated_conjecture, (m1_subset_1(k2_tops_1(esk3_0,esk4_0),k1_zfmisc_1(k2_pre_topc(esk3_0,esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_121]), c_0_104]), c_0_103])])).
% 0.72/0.90  cnf(c_0_132, plain, (k3_subset_1(X1,k3_subset_1(X1,X2))=X2|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_86, c_0_101])).
% 0.72/0.90  cnf(c_0_133, negated_conjecture, (k3_subset_1(k2_pre_topc(esk3_0,esk4_0),esk4_0)=k2_tops_1(esk3_0,esk4_0)|v3_pre_topc(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122, c_0_123]), c_0_124]), c_0_125])])).
% 0.72/0.90  fof(c_0_134, plain, ![X36, X37, X38]:(~m1_subset_1(X38,k1_zfmisc_1(X36))|k9_subset_1(X36,X37,X37)=X37), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[idempotence_k9_subset_1])])).
% 0.72/0.90  fof(c_0_135, plain, ![X44]:(m1_subset_1(esk2_1(X44),k1_zfmisc_1(X44))&v1_xboole_0(esk2_1(X44))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc2_subset_1])])).
% 0.72/0.90  cnf(c_0_136, plain, (k1_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_126])).
% 0.72/0.90  cnf(c_0_137, plain, (k5_xboole_0(k1_setfam_1(k2_tarski(X1,X2)),k5_xboole_0(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X1,X2)),k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))))))=X1), inference(rw,[status(thm)],[c_0_127, c_0_54])).
% 0.72/0.90  cnf(c_0_138, plain, (k5_xboole_0(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_setfam_1(k2_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X3)))=k7_subset_1(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X3)), inference(spm,[status(thm)],[c_0_88, c_0_53])).
% 0.72/0.90  cnf(c_0_139, plain, (X1=k7_subset_1(X2,X2,X3)|r2_hidden(esk1_3(X2,X3,X1),X1)|~r2_hidden(esk1_3(X2,X3,X1),X3)), inference(rw,[status(thm)],[c_0_128, c_0_99])).
% 0.72/0.90  cnf(c_0_140, negated_conjecture, (r2_hidden(X1,k2_pre_topc(esk3_0,esk4_0))|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_129, c_0_124])).
% 0.72/0.90  cnf(c_0_141, plain, (X1=k7_subset_1(X2,X2,X3)|r2_hidden(esk1_3(X2,X3,X1),X2)|r2_hidden(esk1_3(X2,X3,X1),X1)), inference(rw,[status(thm)],[c_0_80, c_0_99])).
% 0.72/0.90  fof(c_0_142, plain, ![X66, X67, X68]:(~l1_pre_topc(X66)|(~m1_subset_1(X67,k1_zfmisc_1(u1_struct_0(X66)))|(~m1_subset_1(X68,k1_zfmisc_1(u1_struct_0(X66)))|(~v3_pre_topc(X67,X66)|~r1_tarski(X67,X68)|r1_tarski(X67,k1_tops_1(X66,X68)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_tops_1])])])).
% 0.72/0.90  fof(c_0_143, plain, ![X15, X16]:(((r1_tarski(X15,X16)|X15!=X16)&(r1_tarski(X16,X15)|X15!=X16))&(~r1_tarski(X15,X16)|~r1_tarski(X16,X15)|X15=X16)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.72/0.90  cnf(c_0_144, negated_conjecture, (k9_subset_1(k2_pre_topc(esk3_0,esk4_0),X1,k3_subset_1(k2_pre_topc(esk3_0,esk4_0),k2_tops_1(esk3_0,esk4_0)))=k7_subset_1(k2_pre_topc(esk3_0,esk4_0),X1,k2_tops_1(esk3_0,esk4_0))|~m1_subset_1(X1,k1_zfmisc_1(k2_pre_topc(esk3_0,esk4_0)))), inference(spm,[status(thm)],[c_0_130, c_0_131])).
% 0.72/0.90  cnf(c_0_145, negated_conjecture, (k3_subset_1(k2_pre_topc(esk3_0,esk4_0),k2_tops_1(esk3_0,esk4_0))=esk4_0|v3_pre_topc(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132, c_0_133]), c_0_124])])).
% 0.72/0.90  cnf(c_0_146, plain, (k9_subset_1(X2,X3,X3)=X3|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_134])).
% 0.72/0.90  cnf(c_0_147, plain, (m1_subset_1(esk2_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_135])).
% 0.72/0.90  cnf(c_0_148, negated_conjecture, (k7_subset_1(u1_struct_0(esk3_0),esk4_0,k2_tops_1(esk3_0,esk4_0))=k1_tops_1(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136, c_0_103]), c_0_104])])).
% 0.72/0.90  cnf(c_0_149, negated_conjecture, (k7_subset_1(u1_struct_0(esk3_0),esk4_0,X1)=k5_xboole_0(esk4_0,k1_setfam_1(k2_tarski(esk4_0,X1)))), inference(spm,[status(thm)],[c_0_88, c_0_103])).
% 0.72/0.90  cnf(c_0_150, plain, (k5_xboole_0(k1_setfam_1(k2_tarski(X1,X2)),k5_xboole_0(k7_subset_1(X1,X1,X2),k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X1,X2)),k7_subset_1(X1,X1,X2)))))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_137, c_0_99]), c_0_99])).
% 0.72/0.90  cnf(c_0_151, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1)))=k7_subset_1(X1,X1,X2)), inference(spm,[status(thm)],[c_0_99, c_0_54])).
% 0.72/0.90  cnf(c_0_152, plain, (k7_subset_1(k7_subset_1(X1,X1,X2),k7_subset_1(X1,X1,X2),X3)=k7_subset_1(X1,k7_subset_1(X1,X1,X2),X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_138, c_0_99]), c_0_99]), c_0_99]), c_0_99])).
% 0.72/0.90  cnf(c_0_153, negated_conjecture, (X1=k7_subset_1(X2,X2,k2_pre_topc(esk3_0,esk4_0))|r2_hidden(esk1_3(X2,k2_pre_topc(esk3_0,esk4_0),X1),X1)|~r2_hidden(esk1_3(X2,k2_pre_topc(esk3_0,esk4_0),X1),esk4_0)), inference(spm,[status(thm)],[c_0_139, c_0_140])).
% 0.72/0.90  cnf(c_0_154, plain, (k7_subset_1(X1,X1,X2)=k1_xboole_0|r2_hidden(esk1_3(X1,X2,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_79, c_0_141])).
% 0.72/0.90  cnf(c_0_155, plain, (r1_tarski(X2,k1_tops_1(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v3_pre_topc(X2,X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_142])).
% 0.72/0.90  cnf(c_0_156, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_143])).
% 0.72/0.90  cnf(c_0_157, negated_conjecture, (k7_subset_1(k2_pre_topc(esk3_0,esk4_0),X1,k2_tops_1(esk3_0,esk4_0))=k9_subset_1(k2_pre_topc(esk3_0,esk4_0),X1,esk4_0)|v3_pre_topc(esk4_0,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(k2_pre_topc(esk3_0,esk4_0)))), inference(spm,[status(thm)],[c_0_144, c_0_145])).
% 0.72/0.90  cnf(c_0_158, negated_conjecture, (v3_pre_topc(esk4_0,esk3_0)|m1_subset_1(esk4_0,k1_zfmisc_1(k2_pre_topc(esk3_0,esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_145]), c_0_131])])).
% 0.72/0.90  cnf(c_0_159, plain, (k9_subset_1(X1,X2,X2)=X2), inference(spm,[status(thm)],[c_0_146, c_0_147])).
% 0.72/0.90  cnf(c_0_160, negated_conjecture, (k5_xboole_0(esk4_0,k1_setfam_1(k2_tarski(esk4_0,k2_tops_1(esk3_0,esk4_0))))=k1_tops_1(esk3_0,esk4_0)), inference(rw,[status(thm)],[c_0_148, c_0_149])).
% 0.72/0.90  cnf(c_0_161, plain, (r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X1)), inference(spm,[status(thm)],[c_0_108, c_0_53])).
% 0.72/0.90  cnf(c_0_162, plain, (k5_xboole_0(k1_setfam_1(k2_tarski(X1,X2)),k7_subset_1(X1,k7_subset_1(X1,X1,X2),k1_setfam_1(k2_tarski(X1,X2))))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_150, c_0_151]), c_0_152])).
% 0.72/0.90  cnf(c_0_163, negated_conjecture, (k7_subset_1(esk4_0,esk4_0,k2_pre_topc(esk3_0,esk4_0))=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_153, c_0_154]), c_0_79])).
% 0.72/0.90  cnf(c_0_164, plain, (k7_subset_1(X1,k1_xboole_0,X2)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_94]), c_0_63]), c_0_64])).
% 0.72/0.90  fof(c_0_165, plain, ![X62, X63]:(~v2_pre_topc(X62)|~l1_pre_topc(X62)|~m1_subset_1(X63,k1_zfmisc_1(u1_struct_0(X62)))|v3_pre_topc(k1_tops_1(X62,X63),X62)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).
% 0.72/0.90  cnf(c_0_166, negated_conjecture, (r1_tarski(X1,k1_tops_1(esk3_0,esk4_0))|~v3_pre_topc(X1,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r1_tarski(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_155, c_0_103]), c_0_104])])).
% 0.72/0.90  cnf(c_0_167, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_156])).
% 0.72/0.90  cnf(c_0_168, negated_conjecture, (k7_subset_1(k2_pre_topc(esk3_0,esk4_0),esk4_0,k2_tops_1(esk3_0,esk4_0))=esk4_0|v3_pre_topc(esk4_0,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_157, c_0_158]), c_0_159])).
% 0.72/0.90  cnf(c_0_169, negated_conjecture, (k7_subset_1(esk4_0,esk4_0,k2_tops_1(esk3_0,esk4_0))=k1_tops_1(esk3_0,esk4_0)), inference(rw,[status(thm)],[c_0_160, c_0_99])).
% 0.72/0.90  cnf(c_0_170, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_143])).
% 0.72/0.90  cnf(c_0_171, negated_conjecture, (r1_tarski(k1_tops_1(esk3_0,esk4_0),esk4_0)), inference(spm,[status(thm)],[c_0_161, c_0_160])).
% 0.72/0.90  cnf(c_0_172, negated_conjecture, (k1_setfam_1(k2_tarski(esk4_0,k2_pre_topc(esk3_0,esk4_0)))=esk4_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_162, c_0_163]), c_0_164]), c_0_64])).
% 0.72/0.90  cnf(c_0_173, plain, (v3_pre_topc(k1_tops_1(X1,X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_165])).
% 0.72/0.90  cnf(c_0_174, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_100])).
% 0.72/0.90  cnf(c_0_175, negated_conjecture, (r1_tarski(esk4_0,k1_tops_1(esk3_0,esk4_0))|~v3_pre_topc(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_166, c_0_103]), c_0_167])])).
% 0.72/0.90  cnf(c_0_176, negated_conjecture, (k1_tops_1(esk3_0,esk4_0)=esk4_0|v3_pre_topc(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_168]), c_0_169]), c_0_124])])).
% 0.72/0.90  cnf(c_0_177, negated_conjecture, (k1_tops_1(esk3_0,esk4_0)=esk4_0|~r1_tarski(esk4_0,k1_tops_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_170, c_0_171])).
% 0.72/0.90  cnf(c_0_178, negated_conjecture, (k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0)=k5_xboole_0(k2_pre_topc(esk3_0,esk4_0),esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_151, c_0_172]), c_0_111])).
% 0.72/0.90  cnf(c_0_179, negated_conjecture, (~v3_pre_topc(esk4_0,esk3_0)|k2_tops_1(esk3_0,esk4_0)!=k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_100])).
% 0.72/0.90  cnf(c_0_180, negated_conjecture, (v3_pre_topc(k1_tops_1(esk3_0,esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_173, c_0_103]), c_0_174]), c_0_104])])).
% 0.72/0.90  cnf(c_0_181, negated_conjecture, (k1_tops_1(esk3_0,esk4_0)=esk4_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_175, c_0_176]), c_0_177])).
% 0.72/0.90  cnf(c_0_182, negated_conjecture, (k5_xboole_0(k2_pre_topc(esk3_0,esk4_0),esk4_0)=k3_subset_1(k2_pre_topc(esk3_0,esk4_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123, c_0_178]), c_0_124]), c_0_125])])).
% 0.72/0.90  cnf(c_0_183, negated_conjecture, (k3_subset_1(k2_pre_topc(esk3_0,esk4_0),esk4_0)!=k2_tops_1(esk3_0,esk4_0)|~v3_pre_topc(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_179, c_0_123]), c_0_124]), c_0_125])])).
% 0.72/0.90  cnf(c_0_184, negated_conjecture, (v3_pre_topc(esk4_0,esk3_0)), inference(rw,[status(thm)],[c_0_180, c_0_181])).
% 0.72/0.90  cnf(c_0_185, negated_conjecture, (k3_subset_1(k2_pre_topc(esk3_0,esk4_0),esk4_0)=k2_tops_1(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121, c_0_181]), c_0_178]), c_0_182]), c_0_104]), c_0_103])])).
% 0.72/0.90  cnf(c_0_186, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_183, c_0_184])]), c_0_185])]), ['proof']).
% 0.72/0.90  # SZS output end CNFRefutation
% 0.72/0.90  # Proof object total steps             : 187
% 0.72/0.90  # Proof object clause steps            : 126
% 0.72/0.90  # Proof object formula steps           : 61
% 0.72/0.90  # Proof object conjectures             : 40
% 0.72/0.90  # Proof object clause conjectures      : 37
% 0.72/0.90  # Proof object formula conjectures     : 3
% 0.72/0.90  # Proof object initial clauses used    : 38
% 0.72/0.90  # Proof object initial formulas used   : 30
% 0.72/0.90  # Proof object generating inferences   : 56
% 0.72/0.90  # Proof object simplifying inferences  : 97
% 0.72/0.90  # Training examples: 0 positive, 0 negative
% 0.72/0.90  # Parsed axioms                        : 31
% 0.72/0.90  # Removed by relevancy pruning/SinE    : 0
% 0.72/0.90  # Initial clauses                      : 44
% 0.72/0.90  # Removed in clause preprocessing      : 4
% 0.72/0.90  # Initial clauses in saturation        : 40
% 0.72/0.90  # Processed clauses                    : 7312
% 0.72/0.90  # ...of these trivial                  : 513
% 0.72/0.90  # ...subsumed                          : 5298
% 0.72/0.90  # ...remaining for further processing  : 1500
% 0.72/0.90  # Other redundant clauses eliminated   : 124
% 0.72/0.90  # Clauses deleted for lack of memory   : 0
% 0.72/0.90  # Backward-subsumed                    : 51
% 0.72/0.90  # Backward-rewritten                   : 307
% 0.72/0.90  # Generated clauses                    : 47136
% 0.72/0.90  # ...of the previous two non-trivial   : 37045
% 0.72/0.90  # Contextual simplify-reflections      : 26
% 0.72/0.90  # Paramodulations                      : 46899
% 0.72/0.90  # Factorizations                       : 40
% 0.72/0.90  # Equation resolutions                 : 191
% 0.72/0.90  # Propositional unsat checks           : 0
% 0.72/0.90  #    Propositional check models        : 0
% 0.72/0.90  #    Propositional check unsatisfiable : 0
% 0.72/0.90  #    Propositional clauses             : 0
% 0.72/0.90  #    Propositional clauses after purity: 0
% 0.72/0.90  #    Propositional unsat core size     : 0
% 0.72/0.90  #    Propositional preprocessing time  : 0.000
% 0.72/0.90  #    Propositional encoding time       : 0.000
% 0.72/0.90  #    Propositional solver time         : 0.000
% 0.72/0.90  #    Success case prop preproc time    : 0.000
% 0.72/0.90  #    Success case prop encoding time   : 0.000
% 0.72/0.90  #    Success case prop solver time     : 0.000
% 0.72/0.90  # Current number of processed clauses  : 1097
% 0.72/0.90  #    Positive orientable unit clauses  : 218
% 0.72/0.90  #    Positive unorientable unit clauses: 3
% 0.72/0.90  #    Negative unit clauses             : 36
% 0.72/0.90  #    Non-unit-clauses                  : 840
% 0.72/0.90  # Current number of unprocessed clauses: 29099
% 0.72/0.90  # ...number of literals in the above   : 92404
% 0.72/0.90  # Current number of archived formulas  : 0
% 0.72/0.90  # Current number of archived clauses   : 404
% 0.72/0.90  # Clause-clause subsumption calls (NU) : 101713
% 0.72/0.90  # Rec. Clause-clause subsumption calls : 71928
% 0.72/0.90  # Non-unit clause-clause subsumptions  : 2842
% 0.72/0.90  # Unit Clause-clause subsumption calls : 6038
% 0.72/0.90  # Rewrite failures with RHS unbound    : 0
% 0.72/0.90  # BW rewrite match attempts            : 1320
% 0.72/0.90  # BW rewrite match successes           : 80
% 0.72/0.90  # Condensation attempts                : 0
% 0.72/0.90  # Condensation successes               : 0
% 0.72/0.90  # Termbank termtop insertions          : 743842
% 0.72/0.90  
% 0.72/0.90  # -------------------------------------------------
% 0.72/0.90  # User time                : 0.541 s
% 0.72/0.90  # System time              : 0.021 s
% 0.72/0.90  # Total time               : 0.562 s
% 0.72/0.90  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------

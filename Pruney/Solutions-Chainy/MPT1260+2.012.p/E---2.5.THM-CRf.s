%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:11:16 EST 2020

% Result     : Theorem 14.84s
% Output     : CNFRefutation 14.84s
% Verified   : 
% Statistics : Number of formulae       :  185 (11858 expanded)
%              Number of clauses        :  132 (5578 expanded)
%              Number of leaves         :   26 (3110 expanded)
%              Depth                    :   26
%              Number of atoms          :  393 (15989 expanded)
%              Number of equality atoms :  136 (10127 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t51_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(dt_k6_subset_1,axiom,(
    ! [X1,X2] : m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

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

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(t76_tops_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).

fof(t65_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_pre_topc(X1,X2) = k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

fof(dt_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(t62_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_tops_1(X1,X2) = k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_1)).

fof(t74_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k1_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

fof(dt_k2_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

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

fof(l78_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(c_0_26,plain,(
    ! [X24] : k2_xboole_0(X24,k1_xboole_0) = X24 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_27,plain,(
    ! [X31,X32] : k3_tarski(k2_tarski(X31,X32)) = k2_xboole_0(X31,X32) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_28,plain,(
    ! [X27,X28] : r1_tarski(X27,k2_xboole_0(X27,X28)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_29,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_30,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_31,plain,(
    ! [X29,X30] : k2_tarski(X29,X30) = k2_tarski(X30,X29) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

fof(c_0_32,plain,(
    ! [X22,X23] : k4_xboole_0(X22,X23) = k5_xboole_0(X22,k3_xboole_0(X22,X23)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_33,plain,(
    ! [X49,X50] : k1_setfam_1(k2_tarski(X49,X50)) = k3_xboole_0(X49,X50) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,plain,
    ( k3_tarski(k2_tarski(X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_36,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_37,plain,(
    ! [X25,X26] : k2_xboole_0(k3_xboole_0(X25,X26),k4_xboole_0(X25,X26)) = X25 ),
    inference(variable_rename,[status(thm)],[t51_xboole_1])).

cnf(c_0_38,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_40,plain,(
    ! [X20,X21] :
      ( ( r1_tarski(X20,X21)
        | X20 != X21 )
      & ( r1_tarski(X21,X20)
        | X20 != X21 )
      & ( ~ r1_tarski(X20,X21)
        | ~ r1_tarski(X21,X20)
        | X20 = X21 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_34,c_0_30])).

cnf(c_0_42,plain,
    ( k3_tarski(k2_tarski(k1_xboole_0,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_43,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_45,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_46,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_47,plain,
    ( k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X1,X2)),k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_30]),c_0_39]),c_0_44])).

fof(c_0_48,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17,X18] :
      ( ( r2_hidden(X14,X11)
        | ~ r2_hidden(X14,X13)
        | X13 != k4_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X14,X12)
        | ~ r2_hidden(X14,X13)
        | X13 != k4_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X15,X11)
        | r2_hidden(X15,X12)
        | r2_hidden(X15,X13)
        | X13 != k4_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk2_3(X16,X17,X18),X18)
        | ~ r2_hidden(esk2_3(X16,X17,X18),X16)
        | r2_hidden(esk2_3(X16,X17,X18),X17)
        | X18 = k4_xboole_0(X16,X17) )
      & ( r2_hidden(esk2_3(X16,X17,X18),X16)
        | r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k4_xboole_0(X16,X17) )
      & ( ~ r2_hidden(esk2_3(X16,X17,X18),X17)
        | r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k4_xboole_0(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_49,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_50,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_47])).

cnf(c_0_51,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_52,plain,
    ( k1_setfam_1(k2_tarski(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_53,plain,
    ( X3 != k5_xboole_0(X4,k1_setfam_1(k2_tarski(X4,X2)))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_51,c_0_44])).

cnf(c_0_54,plain,
    ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_52]),c_0_42])).

fof(c_0_55,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_56,plain,(
    ! [X33,X34] :
      ( ~ m1_subset_1(X34,k1_zfmisc_1(X33))
      | k3_subset_1(X33,X34) = k4_xboole_0(X33,X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_57,plain,(
    ! [X40,X41] : m1_subset_1(k6_subset_1(X40,X41),k1_zfmisc_1(X40)) ),
    inference(variable_rename,[status(thm)],[dt_k6_subset_1])).

fof(c_0_58,plain,(
    ! [X44,X45] : k6_subset_1(X44,X45) = k4_xboole_0(X44,X45) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

cnf(c_0_59,plain,
    ( X1 != k1_xboole_0
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_52]),c_0_54])).

cnf(c_0_60,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

fof(c_0_61,plain,(
    ! [X51,X52] :
      ( ( ~ m1_subset_1(X51,k1_zfmisc_1(X52))
        | r1_tarski(X51,X52) )
      & ( ~ r1_tarski(X51,X52)
        | m1_subset_1(X51,k1_zfmisc_1(X52)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_62,plain,(
    ! [X35,X36] :
      ( ~ m1_subset_1(X36,k1_zfmisc_1(X35))
      | m1_subset_1(k3_subset_1(X35,X36),k1_zfmisc_1(X35)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

cnf(c_0_63,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_64,plain,
    ( m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_65,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_66,plain,
    ( r1_tarski(X1,X2)
    | X1 != k1_xboole_0
    | ~ r2_hidden(esk1_2(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_67,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_68,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

fof(c_0_69,plain,(
    ! [X42,X43] :
      ( ~ m1_subset_1(X43,k1_zfmisc_1(X42))
      | k3_subset_1(X42,k3_subset_1(X42,X43)) = X43 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

cnf(c_0_70,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_63,c_0_44])).

cnf(c_0_71,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_72,plain,
    ( k1_setfam_1(k2_tarski(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_52,c_0_36])).

cnf(c_0_73,plain,
    ( m1_subset_1(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_65]),c_0_44])).

cnf(c_0_74,plain,
    ( r1_tarski(X1,X2)
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_66,c_0_60])).

cnf(c_0_75,plain,
    ( r1_tarski(k3_subset_1(X1,X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_76,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_77,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k3_subset_1(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_78,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_72]),c_0_42])).

cnf(c_0_79,plain,
    ( m1_subset_1(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_36])).

cnf(c_0_80,plain,
    ( X1 = X2
    | X2 != k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_45,c_0_74])).

cnf(c_0_81,plain,
    ( r1_tarski(k3_subset_1(X1,X2),X1)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_75,c_0_71])).

cnf(c_0_82,plain,
    ( k3_subset_1(X1,k3_subset_1(X1,X2)) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_76,c_0_71])).

cnf(c_0_83,plain,
    ( k3_subset_1(X1,k1_xboole_0) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_72]),c_0_78]),c_0_46])])).

cnf(c_0_84,plain,
    ( m1_subset_1(k5_xboole_0(X1,k1_xboole_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_52])).

fof(c_0_85,plain,(
    ! [X46,X47,X48] :
      ( ~ m1_subset_1(X47,k1_zfmisc_1(X46))
      | k7_subset_1(X46,X47,X48) = k4_xboole_0(X47,X48) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

cnf(c_0_86,plain,
    ( k3_subset_1(X1,X2) = X1
    | X1 != k1_xboole_0
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_87,plain,
    ( k3_subset_1(X1,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_46])])).

cnf(c_0_88,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_84,c_0_78])).

fof(c_0_89,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v3_pre_topc(X2,X1)
            <=> k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t76_tops_1])).

cnf(c_0_90,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_91,plain,
    ( k3_subset_1(X1,X1) = X2
    | X1 != k1_xboole_0
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_82,c_0_86])).

cnf(c_0_92,plain,
    ( X1 != k5_xboole_0(X2,k1_setfam_1(k2_tarski(X3,X2)))
    | ~ r2_hidden(X4,X1)
    | ~ r2_hidden(X4,X3) ),
    inference(spm,[status(thm)],[c_0_53,c_0_36])).

cnf(c_0_93,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_94,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k3_subset_1(X1,X2)))) = k3_subset_1(X1,k3_subset_1(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_68])).

cnf(c_0_95,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_87]),c_0_88])])).

fof(c_0_96,negated_conjecture,
    ( v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & ( ~ v3_pre_topc(esk4_0,esk3_0)
      | k2_tops_1(esk3_0,esk4_0) != k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0) )
    & ( v3_pre_topc(esk4_0,esk3_0)
      | k2_tops_1(esk3_0,esk4_0) = k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_89])])])).

cnf(c_0_97,plain,
    ( k7_subset_1(X2,X1,X3) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_90,c_0_44])).

cnf(c_0_98,plain,
    ( k1_xboole_0 = X1
    | X2 != k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_91,c_0_87])).

cnf(c_0_99,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_50,c_0_36])).

cnf(c_0_100,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X3,X2))))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_92])).

cnf(c_0_101,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_93,c_0_46])).

cnf(c_0_102,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_103,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X1))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_83]),c_0_83]),c_0_87])).

fof(c_0_104,plain,(
    ! [X64,X65] :
      ( ~ l1_pre_topc(X64)
      | ~ m1_subset_1(X65,k1_zfmisc_1(u1_struct_0(X64)))
      | k2_pre_topc(X64,X65) = k4_subset_1(u1_struct_0(X64),X65,k2_tops_1(X64,X65)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_tops_1])])])).

cnf(c_0_105,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_96])).

cnf(c_0_106,plain,
    ( k7_subset_1(X1,X2,X3) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3)))
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_97,c_0_71])).

cnf(c_0_107,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k1_xboole_0
    | X2 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_98,c_0_99])).

cnf(c_0_108,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_52]),c_0_101])).

cnf(c_0_109,plain,
    ( X3 = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | r2_hidden(esk2_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_102,c_0_44])).

cnf(c_0_110,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_111,plain,
    ( k1_setfam_1(k2_tarski(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_103]),c_0_35])).

fof(c_0_112,plain,(
    ! [X37,X38,X39] :
      ( ~ m1_subset_1(X38,k1_zfmisc_1(X37))
      | ~ m1_subset_1(X39,k1_zfmisc_1(X37))
      | m1_subset_1(k4_subset_1(X37,X38,X39),k1_zfmisc_1(X37)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_subset_1])])).

cnf(c_0_113,plain,
    ( k2_pre_topc(X1,X2) = k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_104])).

cnf(c_0_114,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_96])).

cnf(c_0_115,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk3_0),esk4_0,X1) = k5_xboole_0(esk4_0,k1_setfam_1(k2_tarski(esk4_0,X1))) ),
    inference(spm,[status(thm)],[c_0_97,c_0_105])).

cnf(c_0_116,plain,
    ( k7_subset_1(X1,X2,X3) = X2
    | X3 != k1_xboole_0
    | ~ r1_tarski(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_107]),c_0_78])).

cnf(c_0_117,negated_conjecture,
    ( r1_tarski(esk4_0,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_105])).

fof(c_0_118,plain,(
    ! [X62,X63] :
      ( ~ l1_pre_topc(X62)
      | ~ m1_subset_1(X63,k1_zfmisc_1(u1_struct_0(X62)))
      | k2_tops_1(X62,X63) = k2_tops_1(X62,k3_subset_1(u1_struct_0(X62),X63)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_tops_1])])])).

cnf(c_0_119,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3))))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_53])).

cnf(c_0_120,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X1,X1,X2) ),
    inference(spm,[status(thm)],[c_0_97,c_0_88])).

cnf(c_0_121,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_setfam_1(k2_tarski(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_93,c_0_50])).

cnf(c_0_122,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_3(k1_xboole_0,X2,X1),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_109]),c_0_52]),c_0_54])).

cnf(c_0_123,plain,
    ( X3 = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2) ),
    inference(rw,[status(thm)],[c_0_110,c_0_44])).

cnf(c_0_124,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_103,c_0_111])).

cnf(c_0_125,plain,
    ( m1_subset_1(k4_subset_1(X2,X1,X3),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_112])).

cnf(c_0_126,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk3_0),esk4_0,k2_tops_1(esk3_0,esk4_0)) = k2_pre_topc(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_105]),c_0_114])])).

fof(c_0_127,plain,(
    ! [X66,X67] :
      ( ~ l1_pre_topc(X66)
      | ~ m1_subset_1(X67,k1_zfmisc_1(u1_struct_0(X66)))
      | k1_tops_1(X66,X67) = k7_subset_1(u1_struct_0(X66),X67,k2_tops_1(X66,X67)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_tops_1])])])).

cnf(c_0_128,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_setfam_1(k2_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X3))) = k7_subset_1(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X3) ),
    inference(spm,[status(thm)],[c_0_97,c_0_73])).

cnf(c_0_129,negated_conjecture,
    ( k5_xboole_0(esk4_0,k1_setfam_1(k2_tarski(esk4_0,X1))) = esk4_0
    | X1 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_116]),c_0_117])])).

fof(c_0_130,plain,(
    ! [X53,X54] :
      ( ~ l1_pre_topc(X53)
      | ~ m1_subset_1(X54,k1_zfmisc_1(u1_struct_0(X53)))
      | m1_subset_1(k2_tops_1(X53,X54),k1_zfmisc_1(u1_struct_0(X53))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_1])])).

cnf(c_0_131,plain,
    ( k2_tops_1(X1,X2) = k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_118])).

cnf(c_0_132,negated_conjecture,
    ( k5_xboole_0(u1_struct_0(esk3_0),k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0)))) = k3_subset_1(u1_struct_0(esk3_0),esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_105]),c_0_36])).

cnf(c_0_133,plain,
    ( ~ r2_hidden(X1,k7_subset_1(X2,X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_119,c_0_120])).

cnf(c_0_134,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k1_xboole_0
    | r2_hidden(esk2_3(k1_xboole_0,X3,k1_setfam_1(k2_tarski(X1,X2))),X1) ),
    inference(spm,[status(thm)],[c_0_121,c_0_122])).

cnf(c_0_135,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_setfam_1(k2_tarski(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_93,c_0_99])).

cnf(c_0_136,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_3(X2,X2,X1),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_109]),c_0_111]),c_0_124])).

cnf(c_0_137,negated_conjecture,
    ( m1_subset_1(k2_pre_topc(esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(k2_tops_1(esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_126]),c_0_105])])).

cnf(c_0_138,plain,
    ( k1_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_127])).

cnf(c_0_139,negated_conjecture,
    ( k5_xboole_0(esk4_0,k1_setfam_1(k2_tarski(esk4_0,X1))) = k7_subset_1(esk4_0,esk4_0,X1)
    | X2 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_128,c_0_129])).

cnf(c_0_140,plain,
    ( m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_130])).

cnf(c_0_141,negated_conjecture,
    ( k2_tops_1(esk3_0,k3_subset_1(u1_struct_0(esk3_0),esk4_0)) = k2_tops_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_105]),c_0_114])])).

cnf(c_0_142,negated_conjecture,
    ( m1_subset_1(k3_subset_1(u1_struct_0(esk3_0),esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_79,c_0_132])).

fof(c_0_143,plain,(
    ! [X59,X60,X61] :
      ( ~ l1_pre_topc(X59)
      | ~ m1_subset_1(X60,k1_zfmisc_1(u1_struct_0(X59)))
      | ~ m1_subset_1(X61,k1_zfmisc_1(u1_struct_0(X59)))
      | ~ v3_pre_topc(X60,X59)
      | ~ r1_tarski(X60,X61)
      | r1_tarski(X60,k1_tops_1(X59,X61)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_tops_1])])])).

cnf(c_0_144,plain,
    ( k1_setfam_1(k2_tarski(k7_subset_1(X1,X1,X2),X3)) = k1_xboole_0
    | ~ r2_hidden(esk2_3(k1_xboole_0,X4,k1_setfam_1(k2_tarski(k7_subset_1(X1,X1,X2),X3))),X2) ),
    inference(spm,[status(thm)],[c_0_133,c_0_134])).

cnf(c_0_145,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k1_xboole_0
    | r2_hidden(esk2_3(X3,X3,k1_setfam_1(k2_tarski(X1,X2))),X2) ),
    inference(spm,[status(thm)],[c_0_135,c_0_136])).

cnf(c_0_146,plain,
    ( k7_subset_1(X1,X2,X3) = k7_subset_1(X2,X2,X3)
    | ~ r1_tarski(X2,X1) ),
    inference(rw,[status(thm)],[c_0_106,c_0_120])).

cnf(c_0_147,negated_conjecture,
    ( r1_tarski(k2_pre_topc(esk3_0,esk4_0),u1_struct_0(esk3_0))
    | ~ m1_subset_1(k2_tops_1(esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_67,c_0_137])).

cnf(c_0_148,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk3_0),esk4_0,k2_tops_1(esk3_0,esk4_0)) = k1_tops_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_105]),c_0_114])])).

cnf(c_0_149,plain,
    ( r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X1) ),
    inference(spm,[status(thm)],[c_0_67,c_0_73])).

cnf(c_0_150,negated_conjecture,
    ( k5_xboole_0(esk4_0,k1_setfam_1(k2_tarski(esk4_0,X1))) = k7_subset_1(esk4_0,esk4_0,X1) ),
    inference(er,[status(thm)],[c_0_139])).

cnf(c_0_151,negated_conjecture,
    ( m1_subset_1(k2_tops_1(esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_140,c_0_141]),c_0_114])]),c_0_142])])).

cnf(c_0_152,plain,
    ( r1_tarski(X2,k1_tops_1(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X2,X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_143])).

cnf(c_0_153,plain,
    ( k1_setfam_1(k2_tarski(X1,k7_subset_1(X2,X2,X1))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_144,c_0_145]),c_0_36])).

cnf(c_0_154,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk3_0)
    | k2_tops_1(esk3_0,esk4_0) = k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_96])).

cnf(c_0_155,plain,
    ( k7_subset_1(X1,X2,X3) = k7_subset_1(X4,X2,X3)
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X2,X4) ),
    inference(spm,[status(thm)],[c_0_146,c_0_146])).

cnf(c_0_156,negated_conjecture,
    ( r1_tarski(k2_pre_topc(esk3_0,esk4_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_147,c_0_140]),c_0_114]),c_0_105])])).

cnf(c_0_157,negated_conjecture,
    ( k5_xboole_0(esk4_0,k1_setfam_1(k2_tarski(esk4_0,k2_tops_1(esk3_0,esk4_0)))) = k1_tops_1(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_148,c_0_115])).

cnf(c_0_158,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_159,negated_conjecture,
    ( r1_tarski(k7_subset_1(esk4_0,esk4_0,X1),esk4_0) ),
    inference(spm,[status(thm)],[c_0_149,c_0_150])).

cnf(c_0_160,plain,
    ( k7_subset_1(X1,X2,X3) = k7_subset_1(X2,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_97,c_0_120])).

cnf(c_0_161,negated_conjecture,
    ( m1_subset_1(k2_pre_topc(esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_137,c_0_151])])).

fof(c_0_162,plain,(
    ! [X55,X56] :
      ( ~ v2_pre_topc(X55)
      | ~ l1_pre_topc(X55)
      | ~ m1_subset_1(X56,k1_zfmisc_1(u1_struct_0(X55)))
      | v3_pre_topc(k1_tops_1(X55,X56),X55) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).

cnf(c_0_163,negated_conjecture,
    ( r1_tarski(X1,k1_tops_1(esk3_0,esk4_0))
    | ~ v3_pre_topc(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r1_tarski(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_152,c_0_105]),c_0_114])])).

cnf(c_0_164,plain,
    ( k7_subset_1(X1,X1,k7_subset_1(X2,X2,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_153]),c_0_78])).

cnf(c_0_165,negated_conjecture,
    ( k7_subset_1(X1,k2_pre_topc(esk3_0,esk4_0),esk4_0) = k2_tops_1(esk3_0,esk4_0)
    | v3_pre_topc(esk4_0,esk3_0)
    | ~ r1_tarski(k2_pre_topc(esk3_0,esk4_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_154,c_0_155]),c_0_156])])).

cnf(c_0_166,negated_conjecture,
    ( k7_subset_1(esk4_0,esk4_0,k2_tops_1(esk3_0,esk4_0)) = k1_tops_1(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_157,c_0_150])).

cnf(c_0_167,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_158])).

cnf(c_0_168,negated_conjecture,
    ( k7_subset_1(esk4_0,esk4_0,X1) = esk4_0
    | ~ r1_tarski(esk4_0,k7_subset_1(esk4_0,esk4_0,X1)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_159])).

fof(c_0_169,plain,(
    ! [X57,X58] :
      ( ~ l1_pre_topc(X57)
      | ~ m1_subset_1(X58,k1_zfmisc_1(u1_struct_0(X57)))
      | k2_tops_1(X57,X58) = k7_subset_1(u1_struct_0(X57),k2_pre_topc(X57,X58),k1_tops_1(X57,X58)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l78_tops_1])])])).

cnf(c_0_170,negated_conjecture,
    ( k7_subset_1(k2_pre_topc(esk3_0,esk4_0),k2_pre_topc(esk3_0,esk4_0),X1) = k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_160,c_0_161])).

cnf(c_0_171,plain,
    ( v3_pre_topc(k1_tops_1(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_162])).

cnf(c_0_172,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_96])).

cnf(c_0_173,negated_conjecture,
    ( r1_tarski(X1,k1_tops_1(esk3_0,esk4_0))
    | ~ v3_pre_topc(X1,esk3_0)
    | ~ r1_tarski(X1,u1_struct_0(esk3_0))
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_163,c_0_71])).

cnf(c_0_174,negated_conjecture,
    ( k1_tops_1(esk3_0,esk4_0) = esk4_0
    | v3_pre_topc(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_164,c_0_165]),c_0_166]),c_0_167])])).

cnf(c_0_175,negated_conjecture,
    ( k1_tops_1(esk3_0,esk4_0) = esk4_0
    | ~ r1_tarski(esk4_0,k1_tops_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_168,c_0_166])).

cnf(c_0_176,plain,
    ( k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_169])).

cnf(c_0_177,negated_conjecture,
    ( k7_subset_1(X1,k2_pre_topc(esk3_0,esk4_0),X2) = k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),X2)
    | ~ r1_tarski(k2_pre_topc(esk3_0,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_146,c_0_170])).

cnf(c_0_178,negated_conjecture,
    ( v3_pre_topc(k1_tops_1(esk3_0,esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_171,c_0_105]),c_0_172]),c_0_114])])).

cnf(c_0_179,negated_conjecture,
    ( k1_tops_1(esk3_0,esk4_0) = esk4_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_173,c_0_174]),c_0_117]),c_0_167])]),c_0_175])).

cnf(c_0_180,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),k1_tops_1(esk3_0,esk4_0)) = k2_tops_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_176,c_0_177]),c_0_114]),c_0_105]),c_0_156])])).

cnf(c_0_181,negated_conjecture,
    ( ~ v3_pre_topc(esk4_0,esk3_0)
    | k2_tops_1(esk3_0,esk4_0) != k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_96])).

cnf(c_0_182,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_178,c_0_179])).

cnf(c_0_183,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0) = k2_tops_1(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_180,c_0_179])).

cnf(c_0_184,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_181,c_0_182])]),c_0_183])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:38:47 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 14.84/15.06  # AutoSched0-Mode selected heuristic G_E___107_C36_F1_PI_AE_Q4_CS_SP_PS_S0Y
% 14.84/15.06  # and selection function SelectMaxLComplexAvoidPosPred.
% 14.84/15.06  #
% 14.84/15.06  # Preprocessing time       : 0.029 s
% 14.84/15.06  # Presaturation interreduction done
% 14.84/15.06  
% 14.84/15.06  # Proof found!
% 14.84/15.06  # SZS status Theorem
% 14.84/15.06  # SZS output start CNFRefutation
% 14.84/15.06  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 14.84/15.06  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 14.84/15.06  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 14.84/15.06  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 14.84/15.06  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 14.84/15.06  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 14.84/15.06  fof(t51_xboole_1, axiom, ![X1, X2]:k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 14.84/15.06  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 14.84/15.06  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 14.84/15.06  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 14.84/15.06  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 14.84/15.06  fof(dt_k6_subset_1, axiom, ![X1, X2]:m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 14.84/15.06  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 14.84/15.06  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 14.84/15.06  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 14.84/15.06  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 14.84/15.06  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 14.84/15.06  fof(t76_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_tops_1)).
% 14.84/15.06  fof(t65_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_pre_topc(X1,X2)=k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 14.84/15.06  fof(dt_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 14.84/15.06  fof(t62_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_tops_1(X1,X2)=k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_tops_1)).
% 14.84/15.06  fof(t74_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k1_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tops_1)).
% 14.84/15.06  fof(dt_k2_tops_1, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 14.84/15.06  fof(t56_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v3_pre_topc(X2,X1)&r1_tarski(X2,X3))=>r1_tarski(X2,k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tops_1)).
% 14.84/15.06  fof(fc9_tops_1, axiom, ![X1, X2]:(((v2_pre_topc(X1)&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v3_pre_topc(k1_tops_1(X1,X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 14.84/15.06  fof(l78_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 14.84/15.06  fof(c_0_26, plain, ![X24]:k2_xboole_0(X24,k1_xboole_0)=X24, inference(variable_rename,[status(thm)],[t1_boole])).
% 14.84/15.06  fof(c_0_27, plain, ![X31, X32]:k3_tarski(k2_tarski(X31,X32))=k2_xboole_0(X31,X32), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 14.84/15.06  fof(c_0_28, plain, ![X27, X28]:r1_tarski(X27,k2_xboole_0(X27,X28)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 14.84/15.06  cnf(c_0_29, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_26])).
% 14.84/15.06  cnf(c_0_30, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 14.84/15.06  fof(c_0_31, plain, ![X29, X30]:k2_tarski(X29,X30)=k2_tarski(X30,X29), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 14.84/15.06  fof(c_0_32, plain, ![X22, X23]:k4_xboole_0(X22,X23)=k5_xboole_0(X22,k3_xboole_0(X22,X23)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 14.84/15.06  fof(c_0_33, plain, ![X49, X50]:k1_setfam_1(k2_tarski(X49,X50))=k3_xboole_0(X49,X50), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 14.84/15.06  cnf(c_0_34, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 14.84/15.06  cnf(c_0_35, plain, (k3_tarski(k2_tarski(X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[c_0_29, c_0_30])).
% 14.84/15.06  cnf(c_0_36, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 14.84/15.06  fof(c_0_37, plain, ![X25, X26]:k2_xboole_0(k3_xboole_0(X25,X26),k4_xboole_0(X25,X26))=X25, inference(variable_rename,[status(thm)],[t51_xboole_1])).
% 14.84/15.06  cnf(c_0_38, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 14.84/15.06  cnf(c_0_39, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 14.84/15.06  fof(c_0_40, plain, ![X20, X21]:(((r1_tarski(X20,X21)|X20!=X21)&(r1_tarski(X21,X20)|X20!=X21))&(~r1_tarski(X20,X21)|~r1_tarski(X21,X20)|X20=X21)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 14.84/15.06  cnf(c_0_41, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_34, c_0_30])).
% 14.84/15.06  cnf(c_0_42, plain, (k3_tarski(k2_tarski(k1_xboole_0,X1))=X1), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 14.84/15.06  cnf(c_0_43, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_37])).
% 14.84/15.06  cnf(c_0_44, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_38, c_0_39])).
% 14.84/15.06  cnf(c_0_45, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 14.84/15.06  cnf(c_0_46, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 14.84/15.06  cnf(c_0_47, plain, (k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X1,X2)),k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_30]), c_0_39]), c_0_44])).
% 14.84/15.06  fof(c_0_48, plain, ![X11, X12, X13, X14, X15, X16, X17, X18]:((((r2_hidden(X14,X11)|~r2_hidden(X14,X13)|X13!=k4_xboole_0(X11,X12))&(~r2_hidden(X14,X12)|~r2_hidden(X14,X13)|X13!=k4_xboole_0(X11,X12)))&(~r2_hidden(X15,X11)|r2_hidden(X15,X12)|r2_hidden(X15,X13)|X13!=k4_xboole_0(X11,X12)))&((~r2_hidden(esk2_3(X16,X17,X18),X18)|(~r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X17))|X18=k4_xboole_0(X16,X17))&((r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k4_xboole_0(X16,X17))&(~r2_hidden(esk2_3(X16,X17,X18),X17)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k4_xboole_0(X16,X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 14.84/15.06  cnf(c_0_49, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 14.84/15.06  cnf(c_0_50, plain, (r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X1)), inference(spm,[status(thm)],[c_0_41, c_0_47])).
% 14.84/15.06  cnf(c_0_51, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 14.84/15.06  cnf(c_0_52, plain, (k1_setfam_1(k2_tarski(k1_xboole_0,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 14.84/15.06  cnf(c_0_53, plain, (X3!=k5_xboole_0(X4,k1_setfam_1(k2_tarski(X4,X2)))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_51, c_0_44])).
% 14.84/15.06  cnf(c_0_54, plain, (k5_xboole_0(k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_52]), c_0_42])).
% 14.84/15.06  fof(c_0_55, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 14.84/15.06  fof(c_0_56, plain, ![X33, X34]:(~m1_subset_1(X34,k1_zfmisc_1(X33))|k3_subset_1(X33,X34)=k4_xboole_0(X33,X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 14.84/15.06  fof(c_0_57, plain, ![X40, X41]:m1_subset_1(k6_subset_1(X40,X41),k1_zfmisc_1(X40)), inference(variable_rename,[status(thm)],[dt_k6_subset_1])).
% 14.84/15.06  fof(c_0_58, plain, ![X44, X45]:k6_subset_1(X44,X45)=k4_xboole_0(X44,X45), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 14.84/15.06  cnf(c_0_59, plain, (X1!=k1_xboole_0|~r2_hidden(X2,X1)|~r2_hidden(X2,X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_52]), c_0_54])).
% 14.84/15.06  cnf(c_0_60, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 14.84/15.06  fof(c_0_61, plain, ![X51, X52]:((~m1_subset_1(X51,k1_zfmisc_1(X52))|r1_tarski(X51,X52))&(~r1_tarski(X51,X52)|m1_subset_1(X51,k1_zfmisc_1(X52)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 14.84/15.06  fof(c_0_62, plain, ![X35, X36]:(~m1_subset_1(X36,k1_zfmisc_1(X35))|m1_subset_1(k3_subset_1(X35,X36),k1_zfmisc_1(X35))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 14.84/15.06  cnf(c_0_63, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 14.84/15.06  cnf(c_0_64, plain, (m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 14.84/15.06  cnf(c_0_65, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 14.84/15.06  cnf(c_0_66, plain, (r1_tarski(X1,X2)|X1!=k1_xboole_0|~r2_hidden(esk1_2(X1,X2),X3)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 14.84/15.06  cnf(c_0_67, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 14.84/15.06  cnf(c_0_68, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_62])).
% 14.84/15.06  fof(c_0_69, plain, ![X42, X43]:(~m1_subset_1(X43,k1_zfmisc_1(X42))|k3_subset_1(X42,k3_subset_1(X42,X43))=X43), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 14.84/15.06  cnf(c_0_70, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_63, c_0_44])).
% 14.84/15.06  cnf(c_0_71, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 14.84/15.06  cnf(c_0_72, plain, (k1_setfam_1(k2_tarski(X1,k1_xboole_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_52, c_0_36])).
% 14.84/15.06  cnf(c_0_73, plain, (m1_subset_1(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_zfmisc_1(X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_65]), c_0_44])).
% 14.84/15.06  cnf(c_0_74, plain, (r1_tarski(X1,X2)|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_66, c_0_60])).
% 14.84/15.06  cnf(c_0_75, plain, (r1_tarski(k3_subset_1(X1,X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 14.84/15.06  cnf(c_0_76, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_69])).
% 14.84/15.06  cnf(c_0_77, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k3_subset_1(X1,X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 14.84/15.06  cnf(c_0_78, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_72]), c_0_42])).
% 14.84/15.06  cnf(c_0_79, plain, (m1_subset_1(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_73, c_0_36])).
% 14.84/15.06  cnf(c_0_80, plain, (X1=X2|X2!=k1_xboole_0|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_45, c_0_74])).
% 14.84/15.06  cnf(c_0_81, plain, (r1_tarski(k3_subset_1(X1,X2),X1)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_75, c_0_71])).
% 14.84/15.06  cnf(c_0_82, plain, (k3_subset_1(X1,k3_subset_1(X1,X2))=X2|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_76, c_0_71])).
% 14.84/15.06  cnf(c_0_83, plain, (k3_subset_1(X1,k1_xboole_0)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_72]), c_0_78]), c_0_46])])).
% 14.84/15.06  cnf(c_0_84, plain, (m1_subset_1(k5_xboole_0(X1,k1_xboole_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_79, c_0_52])).
% 14.84/15.06  fof(c_0_85, plain, ![X46, X47, X48]:(~m1_subset_1(X47,k1_zfmisc_1(X46))|k7_subset_1(X46,X47,X48)=k4_xboole_0(X47,X48)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 14.84/15.06  cnf(c_0_86, plain, (k3_subset_1(X1,X2)=X1|X1!=k1_xboole_0|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 14.84/15.06  cnf(c_0_87, plain, (k3_subset_1(X1,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_46])])).
% 14.84/15.06  cnf(c_0_88, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_84, c_0_78])).
% 14.84/15.06  fof(c_0_89, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2))))), inference(assume_negation,[status(cth)],[t76_tops_1])).
% 14.84/15.06  cnf(c_0_90, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_85])).
% 14.84/15.06  cnf(c_0_91, plain, (k3_subset_1(X1,X1)=X2|X1!=k1_xboole_0|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_82, c_0_86])).
% 14.84/15.06  cnf(c_0_92, plain, (X1!=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X3,X2)))|~r2_hidden(X4,X1)|~r2_hidden(X4,X3)), inference(spm,[status(thm)],[c_0_53, c_0_36])).
% 14.84/15.06  cnf(c_0_93, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 14.84/15.06  cnf(c_0_94, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k3_subset_1(X1,X2))))=k3_subset_1(X1,k3_subset_1(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_70, c_0_68])).
% 14.84/15.06  cnf(c_0_95, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_87]), c_0_88])])).
% 14.84/15.06  fof(c_0_96, negated_conjecture, ((v2_pre_topc(esk3_0)&l1_pre_topc(esk3_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&((~v3_pre_topc(esk4_0,esk3_0)|k2_tops_1(esk3_0,esk4_0)!=k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0))&(v3_pre_topc(esk4_0,esk3_0)|k2_tops_1(esk3_0,esk4_0)=k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_89])])])).
% 14.84/15.06  cnf(c_0_97, plain, (k7_subset_1(X2,X1,X3)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_90, c_0_44])).
% 14.84/15.06  cnf(c_0_98, plain, (k1_xboole_0=X1|X2!=k1_xboole_0|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_91, c_0_87])).
% 14.84/15.06  cnf(c_0_99, plain, (r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_50, c_0_36])).
% 14.84/15.06  cnf(c_0_100, plain, (~r2_hidden(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X3,X2))))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_92])).
% 14.84/15.06  cnf(c_0_101, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_93, c_0_46])).
% 14.84/15.06  cnf(c_0_102, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 14.84/15.06  cnf(c_0_103, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X1)))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_83]), c_0_83]), c_0_87])).
% 14.84/15.06  fof(c_0_104, plain, ![X64, X65]:(~l1_pre_topc(X64)|(~m1_subset_1(X65,k1_zfmisc_1(u1_struct_0(X64)))|k2_pre_topc(X64,X65)=k4_subset_1(u1_struct_0(X64),X65,k2_tops_1(X64,X65)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_tops_1])])])).
% 14.84/15.06  cnf(c_0_105, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_96])).
% 14.84/15.06  cnf(c_0_106, plain, (k7_subset_1(X1,X2,X3)=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3)))|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_97, c_0_71])).
% 14.84/15.06  cnf(c_0_107, plain, (k1_setfam_1(k2_tarski(X1,X2))=k1_xboole_0|X2!=k1_xboole_0), inference(spm,[status(thm)],[c_0_98, c_0_99])).
% 14.84/15.06  cnf(c_0_108, plain, (~r2_hidden(X1,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_52]), c_0_101])).
% 14.84/15.06  cnf(c_0_109, plain, (X3=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))|r2_hidden(esk2_3(X1,X2,X3),X3)|r2_hidden(esk2_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_102, c_0_44])).
% 14.84/15.06  cnf(c_0_110, plain, (r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 14.84/15.06  cnf(c_0_111, plain, (k1_setfam_1(k2_tarski(X1,X1))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_103]), c_0_35])).
% 14.84/15.06  fof(c_0_112, plain, ![X37, X38, X39]:(~m1_subset_1(X38,k1_zfmisc_1(X37))|~m1_subset_1(X39,k1_zfmisc_1(X37))|m1_subset_1(k4_subset_1(X37,X38,X39),k1_zfmisc_1(X37))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_subset_1])])).
% 14.84/15.06  cnf(c_0_113, plain, (k2_pre_topc(X1,X2)=k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_104])).
% 14.84/15.06  cnf(c_0_114, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_96])).
% 14.84/15.06  cnf(c_0_115, negated_conjecture, (k7_subset_1(u1_struct_0(esk3_0),esk4_0,X1)=k5_xboole_0(esk4_0,k1_setfam_1(k2_tarski(esk4_0,X1)))), inference(spm,[status(thm)],[c_0_97, c_0_105])).
% 14.84/15.06  cnf(c_0_116, plain, (k7_subset_1(X1,X2,X3)=X2|X3!=k1_xboole_0|~r1_tarski(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_107]), c_0_78])).
% 14.84/15.06  cnf(c_0_117, negated_conjecture, (r1_tarski(esk4_0,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_67, c_0_105])).
% 14.84/15.06  fof(c_0_118, plain, ![X62, X63]:(~l1_pre_topc(X62)|(~m1_subset_1(X63,k1_zfmisc_1(u1_struct_0(X62)))|k2_tops_1(X62,X63)=k2_tops_1(X62,k3_subset_1(u1_struct_0(X62),X63)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_tops_1])])])).
% 14.84/15.06  cnf(c_0_119, plain, (~r2_hidden(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3))))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_53])).
% 14.84/15.06  cnf(c_0_120, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k7_subset_1(X1,X1,X2)), inference(spm,[status(thm)],[c_0_97, c_0_88])).
% 14.84/15.06  cnf(c_0_121, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_setfam_1(k2_tarski(X2,X3)))), inference(spm,[status(thm)],[c_0_93, c_0_50])).
% 14.84/15.06  cnf(c_0_122, plain, (X1=k1_xboole_0|r2_hidden(esk2_3(k1_xboole_0,X2,X1),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_109]), c_0_52]), c_0_54])).
% 14.84/15.06  cnf(c_0_123, plain, (X3=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))|r2_hidden(esk2_3(X1,X2,X3),X3)|~r2_hidden(esk2_3(X1,X2,X3),X2)), inference(rw,[status(thm)],[c_0_110, c_0_44])).
% 14.84/15.06  cnf(c_0_124, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_103, c_0_111])).
% 14.84/15.06  cnf(c_0_125, plain, (m1_subset_1(k4_subset_1(X2,X1,X3),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_112])).
% 14.84/15.06  cnf(c_0_126, negated_conjecture, (k4_subset_1(u1_struct_0(esk3_0),esk4_0,k2_tops_1(esk3_0,esk4_0))=k2_pre_topc(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_105]), c_0_114])])).
% 14.84/15.06  fof(c_0_127, plain, ![X66, X67]:(~l1_pre_topc(X66)|(~m1_subset_1(X67,k1_zfmisc_1(u1_struct_0(X66)))|k1_tops_1(X66,X67)=k7_subset_1(u1_struct_0(X66),X67,k2_tops_1(X66,X67)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_tops_1])])])).
% 14.84/15.06  cnf(c_0_128, plain, (k5_xboole_0(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_setfam_1(k2_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X3)))=k7_subset_1(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X3)), inference(spm,[status(thm)],[c_0_97, c_0_73])).
% 14.84/15.06  cnf(c_0_129, negated_conjecture, (k5_xboole_0(esk4_0,k1_setfam_1(k2_tarski(esk4_0,X1)))=esk4_0|X1!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_116]), c_0_117])])).
% 14.84/15.06  fof(c_0_130, plain, ![X53, X54]:(~l1_pre_topc(X53)|~m1_subset_1(X54,k1_zfmisc_1(u1_struct_0(X53)))|m1_subset_1(k2_tops_1(X53,X54),k1_zfmisc_1(u1_struct_0(X53)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_1])])).
% 14.84/15.06  cnf(c_0_131, plain, (k2_tops_1(X1,X2)=k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_118])).
% 14.84/15.06  cnf(c_0_132, negated_conjecture, (k5_xboole_0(u1_struct_0(esk3_0),k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))))=k3_subset_1(u1_struct_0(esk3_0),esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_105]), c_0_36])).
% 14.84/15.06  cnf(c_0_133, plain, (~r2_hidden(X1,k7_subset_1(X2,X2,X3))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_119, c_0_120])).
% 14.84/15.06  cnf(c_0_134, plain, (k1_setfam_1(k2_tarski(X1,X2))=k1_xboole_0|r2_hidden(esk2_3(k1_xboole_0,X3,k1_setfam_1(k2_tarski(X1,X2))),X1)), inference(spm,[status(thm)],[c_0_121, c_0_122])).
% 14.84/15.06  cnf(c_0_135, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_setfam_1(k2_tarski(X3,X2)))), inference(spm,[status(thm)],[c_0_93, c_0_99])).
% 14.84/15.06  cnf(c_0_136, plain, (X1=k1_xboole_0|r2_hidden(esk2_3(X2,X2,X1),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123, c_0_109]), c_0_111]), c_0_124])).
% 14.84/15.06  cnf(c_0_137, negated_conjecture, (m1_subset_1(k2_pre_topc(esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(k2_tops_1(esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125, c_0_126]), c_0_105])])).
% 14.84/15.06  cnf(c_0_138, plain, (k1_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_127])).
% 14.84/15.06  cnf(c_0_139, negated_conjecture, (k5_xboole_0(esk4_0,k1_setfam_1(k2_tarski(esk4_0,X1)))=k7_subset_1(esk4_0,esk4_0,X1)|X2!=k1_xboole_0), inference(spm,[status(thm)],[c_0_128, c_0_129])).
% 14.84/15.06  cnf(c_0_140, plain, (m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_130])).
% 14.84/15.06  cnf(c_0_141, negated_conjecture, (k2_tops_1(esk3_0,k3_subset_1(u1_struct_0(esk3_0),esk4_0))=k2_tops_1(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131, c_0_105]), c_0_114])])).
% 14.84/15.06  cnf(c_0_142, negated_conjecture, (m1_subset_1(k3_subset_1(u1_struct_0(esk3_0),esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_79, c_0_132])).
% 14.84/15.06  fof(c_0_143, plain, ![X59, X60, X61]:(~l1_pre_topc(X59)|(~m1_subset_1(X60,k1_zfmisc_1(u1_struct_0(X59)))|(~m1_subset_1(X61,k1_zfmisc_1(u1_struct_0(X59)))|(~v3_pre_topc(X60,X59)|~r1_tarski(X60,X61)|r1_tarski(X60,k1_tops_1(X59,X61)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_tops_1])])])).
% 14.84/15.06  cnf(c_0_144, plain, (k1_setfam_1(k2_tarski(k7_subset_1(X1,X1,X2),X3))=k1_xboole_0|~r2_hidden(esk2_3(k1_xboole_0,X4,k1_setfam_1(k2_tarski(k7_subset_1(X1,X1,X2),X3))),X2)), inference(spm,[status(thm)],[c_0_133, c_0_134])).
% 14.84/15.06  cnf(c_0_145, plain, (k1_setfam_1(k2_tarski(X1,X2))=k1_xboole_0|r2_hidden(esk2_3(X3,X3,k1_setfam_1(k2_tarski(X1,X2))),X2)), inference(spm,[status(thm)],[c_0_135, c_0_136])).
% 14.84/15.06  cnf(c_0_146, plain, (k7_subset_1(X1,X2,X3)=k7_subset_1(X2,X2,X3)|~r1_tarski(X2,X1)), inference(rw,[status(thm)],[c_0_106, c_0_120])).
% 14.84/15.06  cnf(c_0_147, negated_conjecture, (r1_tarski(k2_pre_topc(esk3_0,esk4_0),u1_struct_0(esk3_0))|~m1_subset_1(k2_tops_1(esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_67, c_0_137])).
% 14.84/15.06  cnf(c_0_148, negated_conjecture, (k7_subset_1(u1_struct_0(esk3_0),esk4_0,k2_tops_1(esk3_0,esk4_0))=k1_tops_1(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_105]), c_0_114])])).
% 14.84/15.06  cnf(c_0_149, plain, (r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X1)), inference(spm,[status(thm)],[c_0_67, c_0_73])).
% 14.84/15.06  cnf(c_0_150, negated_conjecture, (k5_xboole_0(esk4_0,k1_setfam_1(k2_tarski(esk4_0,X1)))=k7_subset_1(esk4_0,esk4_0,X1)), inference(er,[status(thm)],[c_0_139])).
% 14.84/15.06  cnf(c_0_151, negated_conjecture, (m1_subset_1(k2_tops_1(esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_140, c_0_141]), c_0_114])]), c_0_142])])).
% 14.84/15.06  cnf(c_0_152, plain, (r1_tarski(X2,k1_tops_1(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v3_pre_topc(X2,X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_143])).
% 14.84/15.06  cnf(c_0_153, plain, (k1_setfam_1(k2_tarski(X1,k7_subset_1(X2,X2,X1)))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_144, c_0_145]), c_0_36])).
% 14.84/15.06  cnf(c_0_154, negated_conjecture, (v3_pre_topc(esk4_0,esk3_0)|k2_tops_1(esk3_0,esk4_0)=k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_96])).
% 14.84/15.06  cnf(c_0_155, plain, (k7_subset_1(X1,X2,X3)=k7_subset_1(X4,X2,X3)|~r1_tarski(X2,X1)|~r1_tarski(X2,X4)), inference(spm,[status(thm)],[c_0_146, c_0_146])).
% 14.84/15.06  cnf(c_0_156, negated_conjecture, (r1_tarski(k2_pre_topc(esk3_0,esk4_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_147, c_0_140]), c_0_114]), c_0_105])])).
% 14.84/15.06  cnf(c_0_157, negated_conjecture, (k5_xboole_0(esk4_0,k1_setfam_1(k2_tarski(esk4_0,k2_tops_1(esk3_0,esk4_0))))=k1_tops_1(esk3_0,esk4_0)), inference(rw,[status(thm)],[c_0_148, c_0_115])).
% 14.84/15.06  cnf(c_0_158, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_40])).
% 14.84/15.06  cnf(c_0_159, negated_conjecture, (r1_tarski(k7_subset_1(esk4_0,esk4_0,X1),esk4_0)), inference(spm,[status(thm)],[c_0_149, c_0_150])).
% 14.84/15.06  cnf(c_0_160, plain, (k7_subset_1(X1,X2,X3)=k7_subset_1(X2,X2,X3)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_97, c_0_120])).
% 14.84/15.06  cnf(c_0_161, negated_conjecture, (m1_subset_1(k2_pre_topc(esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_137, c_0_151])])).
% 14.84/15.06  fof(c_0_162, plain, ![X55, X56]:(~v2_pre_topc(X55)|~l1_pre_topc(X55)|~m1_subset_1(X56,k1_zfmisc_1(u1_struct_0(X55)))|v3_pre_topc(k1_tops_1(X55,X56),X55)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).
% 14.84/15.06  cnf(c_0_163, negated_conjecture, (r1_tarski(X1,k1_tops_1(esk3_0,esk4_0))|~v3_pre_topc(X1,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r1_tarski(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_152, c_0_105]), c_0_114])])).
% 14.84/15.06  cnf(c_0_164, plain, (k7_subset_1(X1,X1,k7_subset_1(X2,X2,X1))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_153]), c_0_78])).
% 14.84/15.06  cnf(c_0_165, negated_conjecture, (k7_subset_1(X1,k2_pre_topc(esk3_0,esk4_0),esk4_0)=k2_tops_1(esk3_0,esk4_0)|v3_pre_topc(esk4_0,esk3_0)|~r1_tarski(k2_pre_topc(esk3_0,esk4_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_154, c_0_155]), c_0_156])])).
% 14.84/15.06  cnf(c_0_166, negated_conjecture, (k7_subset_1(esk4_0,esk4_0,k2_tops_1(esk3_0,esk4_0))=k1_tops_1(esk3_0,esk4_0)), inference(rw,[status(thm)],[c_0_157, c_0_150])).
% 14.84/15.06  cnf(c_0_167, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_158])).
% 14.84/15.06  cnf(c_0_168, negated_conjecture, (k7_subset_1(esk4_0,esk4_0,X1)=esk4_0|~r1_tarski(esk4_0,k7_subset_1(esk4_0,esk4_0,X1))), inference(spm,[status(thm)],[c_0_45, c_0_159])).
% 14.84/15.06  fof(c_0_169, plain, ![X57, X58]:(~l1_pre_topc(X57)|(~m1_subset_1(X58,k1_zfmisc_1(u1_struct_0(X57)))|k2_tops_1(X57,X58)=k7_subset_1(u1_struct_0(X57),k2_pre_topc(X57,X58),k1_tops_1(X57,X58)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l78_tops_1])])])).
% 14.84/15.06  cnf(c_0_170, negated_conjecture, (k7_subset_1(k2_pre_topc(esk3_0,esk4_0),k2_pre_topc(esk3_0,esk4_0),X1)=k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),X1)), inference(spm,[status(thm)],[c_0_160, c_0_161])).
% 14.84/15.06  cnf(c_0_171, plain, (v3_pre_topc(k1_tops_1(X1,X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_162])).
% 14.84/15.06  cnf(c_0_172, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_96])).
% 14.84/15.06  cnf(c_0_173, negated_conjecture, (r1_tarski(X1,k1_tops_1(esk3_0,esk4_0))|~v3_pre_topc(X1,esk3_0)|~r1_tarski(X1,u1_struct_0(esk3_0))|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_163, c_0_71])).
% 14.84/15.06  cnf(c_0_174, negated_conjecture, (k1_tops_1(esk3_0,esk4_0)=esk4_0|v3_pre_topc(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_164, c_0_165]), c_0_166]), c_0_167])])).
% 14.84/15.06  cnf(c_0_175, negated_conjecture, (k1_tops_1(esk3_0,esk4_0)=esk4_0|~r1_tarski(esk4_0,k1_tops_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_168, c_0_166])).
% 14.84/15.06  cnf(c_0_176, plain, (k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_169])).
% 14.84/15.06  cnf(c_0_177, negated_conjecture, (k7_subset_1(X1,k2_pre_topc(esk3_0,esk4_0),X2)=k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),X2)|~r1_tarski(k2_pre_topc(esk3_0,esk4_0),X1)), inference(spm,[status(thm)],[c_0_146, c_0_170])).
% 14.84/15.06  cnf(c_0_178, negated_conjecture, (v3_pre_topc(k1_tops_1(esk3_0,esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_171, c_0_105]), c_0_172]), c_0_114])])).
% 14.84/15.06  cnf(c_0_179, negated_conjecture, (k1_tops_1(esk3_0,esk4_0)=esk4_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_173, c_0_174]), c_0_117]), c_0_167])]), c_0_175])).
% 14.84/15.06  cnf(c_0_180, negated_conjecture, (k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),k1_tops_1(esk3_0,esk4_0))=k2_tops_1(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_176, c_0_177]), c_0_114]), c_0_105]), c_0_156])])).
% 14.84/15.06  cnf(c_0_181, negated_conjecture, (~v3_pre_topc(esk4_0,esk3_0)|k2_tops_1(esk3_0,esk4_0)!=k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_96])).
% 14.84/15.06  cnf(c_0_182, negated_conjecture, (v3_pre_topc(esk4_0,esk3_0)), inference(rw,[status(thm)],[c_0_178, c_0_179])).
% 14.84/15.06  cnf(c_0_183, negated_conjecture, (k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0)=k2_tops_1(esk3_0,esk4_0)), inference(rw,[status(thm)],[c_0_180, c_0_179])).
% 14.84/15.06  cnf(c_0_184, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_181, c_0_182])]), c_0_183])]), ['proof']).
% 14.84/15.06  # SZS output end CNFRefutation
% 14.84/15.06  # Proof object total steps             : 185
% 14.84/15.06  # Proof object clause steps            : 132
% 14.84/15.06  # Proof object formula steps           : 53
% 14.84/15.06  # Proof object conjectures             : 40
% 14.84/15.06  # Proof object clause conjectures      : 37
% 14.84/15.06  # Proof object formula conjectures     : 3
% 14.84/15.06  # Proof object initial clauses used    : 35
% 14.84/15.06  # Proof object initial formulas used   : 26
% 14.84/15.06  # Proof object generating inferences   : 74
% 14.84/15.06  # Proof object simplifying inferences  : 88
% 14.84/15.06  # Training examples: 0 positive, 0 negative
% 14.84/15.06  # Parsed axioms                        : 26
% 14.84/15.06  # Removed by relevancy pruning/SinE    : 0
% 14.84/15.06  # Initial clauses                      : 40
% 14.84/15.06  # Removed in clause preprocessing      : 4
% 14.84/15.06  # Initial clauses in saturation        : 36
% 14.84/15.06  # Processed clauses                    : 59942
% 14.84/15.06  # ...of these trivial                  : 3989
% 14.84/15.06  # ...subsumed                          : 48964
% 14.84/15.06  # ...remaining for further processing  : 6988
% 14.84/15.06  # Other redundant clauses eliminated   : 432
% 14.84/15.06  # Clauses deleted for lack of memory   : 0
% 14.84/15.06  # Backward-subsumed                    : 557
% 14.84/15.06  # Backward-rewritten                   : 804
% 14.84/15.06  # Generated clauses                    : 1044982
% 14.84/15.06  # ...of the previous two non-trivial   : 925010
% 14.84/15.06  # Contextual simplify-reflections      : 820
% 14.84/15.06  # Paramodulations                      : 1044372
% 14.84/15.06  # Factorizations                       : 52
% 14.84/15.06  # Equation resolutions                 : 551
% 14.84/15.06  # Propositional unsat checks           : 0
% 14.84/15.06  #    Propositional check models        : 0
% 14.84/15.06  #    Propositional check unsatisfiable : 0
% 14.84/15.06  #    Propositional clauses             : 0
% 14.84/15.06  #    Propositional clauses after purity: 0
% 14.84/15.06  #    Propositional unsat core size     : 0
% 14.84/15.06  #    Propositional preprocessing time  : 0.000
% 14.84/15.06  #    Propositional encoding time       : 0.000
% 14.84/15.06  #    Propositional solver time         : 0.000
% 14.84/15.06  #    Success case prop preproc time    : 0.000
% 14.84/15.06  #    Success case prop encoding time   : 0.000
% 14.84/15.06  #    Success case prop solver time     : 0.000
% 14.84/15.06  # Current number of processed clauses  : 5585
% 14.84/15.06  #    Positive orientable unit clauses  : 1230
% 14.84/15.06  #    Positive unorientable unit clauses: 1
% 14.84/15.06  #    Negative unit clauses             : 76
% 14.84/15.06  #    Non-unit-clauses                  : 4278
% 14.84/15.06  # Current number of unprocessed clauses: 859137
% 14.84/15.06  # ...number of literals in the above   : 3481246
% 14.84/15.06  # Current number of archived formulas  : 0
% 14.84/15.06  # Current number of archived clauses   : 1404
% 14.84/15.06  # Clause-clause subsumption calls (NU) : 5644207
% 14.84/15.06  # Rec. Clause-clause subsumption calls : 2527759
% 14.84/15.06  # Non-unit clause-clause subsumptions  : 25129
% 14.84/15.06  # Unit Clause-clause subsumption calls : 108759
% 14.84/15.06  # Rewrite failures with RHS unbound    : 0
% 14.84/15.06  # BW rewrite match attempts            : 21493
% 14.84/15.06  # BW rewrite match successes           : 198
% 14.84/15.06  # Condensation attempts                : 0
% 14.84/15.06  # Condensation successes               : 0
% 14.84/15.06  # Termbank termtop insertions          : 28828542
% 14.90/15.10  
% 14.90/15.10  # -------------------------------------------------
% 14.90/15.10  # User time                : 14.275 s
% 14.90/15.10  # System time              : 0.457 s
% 14.90/15.10  # Total time               : 14.732 s
% 14.90/15.10  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------

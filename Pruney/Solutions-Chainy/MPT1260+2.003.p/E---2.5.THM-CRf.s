%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:11:15 EST 2020

% Result     : Theorem 20.11s
% Output     : CNFRefutation 20.11s
% Verified   : 
% Statistics : Number of formulae       :  242 (56840 expanded)
%              Number of clauses        :  185 (25996 expanded)
%              Number of leaves         :   28 (15360 expanded)
%              Depth                    :   25
%              Number of atoms          :  452 (66303 expanded)
%              Number of equality atoms :  192 (52618 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

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

fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(dt_k6_subset_1,axiom,(
    ! [X1,X2] : m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(t52_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t32_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => k7_subset_1(X1,X2,X3) = k9_subset_1(X1,X2,k3_subset_1(X1,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

fof(t76_tops_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t74_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k1_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(t48_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(X2,k2_pre_topc(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(l78_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

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

fof(c_0_28,plain,(
    ! [X19,X20] : k4_xboole_0(X19,X20) = k5_xboole_0(X19,k3_xboole_0(X19,X20)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_29,plain,(
    ! [X55,X56] : k1_setfam_1(k2_tarski(X55,X56)) = k3_xboole_0(X55,X56) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_30,plain,(
    ! [X7,X8,X9,X10,X11,X12,X13,X14] :
      ( ( r2_hidden(X10,X7)
        | ~ r2_hidden(X10,X9)
        | X9 != k4_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X10,X8)
        | ~ r2_hidden(X10,X9)
        | X9 != k4_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X11,X7)
        | r2_hidden(X11,X8)
        | r2_hidden(X11,X9)
        | X9 != k4_xboole_0(X7,X8) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X12)
        | r2_hidden(esk1_3(X12,X13,X14),X13)
        | X14 = k4_xboole_0(X12,X13) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X12)
        | r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k4_xboole_0(X12,X13) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X13)
        | r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k4_xboole_0(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_31,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_32,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_33,plain,(
    ! [X16] : k3_xboole_0(X16,X16) = X16 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

fof(c_0_34,plain,(
    ! [X24,X25] : k4_xboole_0(X24,k2_xboole_0(X24,X25)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

cnf(c_0_35,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_37,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_38,plain,(
    ! [X23] : k4_xboole_0(X23,k1_xboole_0) = X23 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_39,plain,(
    ! [X22] : k3_xboole_0(X22,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_40,plain,(
    ! [X35,X36] : m1_subset_1(k6_subset_1(X35,X36),k1_zfmisc_1(X35)) ),
    inference(variable_rename,[status(thm)],[dt_k6_subset_1])).

fof(c_0_41,plain,(
    ! [X45,X46] : k6_subset_1(X45,X46) = k4_xboole_0(X45,X46) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

fof(c_0_42,plain,(
    ! [X31,X32] :
      ( ~ m1_subset_1(X32,k1_zfmisc_1(X31))
      | k3_subset_1(X31,X32) = k4_xboole_0(X31,X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_43,plain,(
    ! [X26,X27,X28] : k4_xboole_0(X26,k4_xboole_0(X27,X28)) = k2_xboole_0(k4_xboole_0(X26,X27),k3_xboole_0(X26,X28)) ),
    inference(variable_rename,[status(thm)],[t52_xboole_1])).

cnf(c_0_44,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_45,plain,(
    ! [X21] : k2_xboole_0(X21,k1_xboole_0) = X21 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_46,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_47,plain,
    ( X3 != k5_xboole_0(X4,k1_setfam_1(k2_tarski(X4,X2)))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_48,plain,
    ( k1_setfam_1(k2_tarski(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_37,c_0_32])).

cnf(c_0_49,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_50,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_51,plain,(
    ! [X40,X41] :
      ( ~ m1_subset_1(X41,k1_zfmisc_1(X40))
      | k3_subset_1(X40,k3_subset_1(X40,X41)) = X41 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

cnf(c_0_52,plain,
    ( m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_53,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_54,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_55,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_56,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k2_xboole_0(X1,X2)))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_44,c_0_36])).

cnf(c_0_57,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_58,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

fof(c_0_59,plain,(
    ! [X29,X30] : k2_tarski(X29,X30) = k2_tarski(X30,X29) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_60,plain,
    ( X1 != k5_xboole_0(X2,X2)
    | ~ r2_hidden(X3,X1)
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_61,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_xboole_0))) = X1 ),
    inference(rw,[status(thm)],[c_0_49,c_0_36])).

cnf(c_0_62,plain,
    ( k1_setfam_1(k2_tarski(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_50,c_0_32])).

cnf(c_0_63,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_64,plain,
    ( m1_subset_1(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_53]),c_0_36])).

cnf(c_0_65,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_54,c_0_36])).

cnf(c_0_66,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3)))))) = k2_xboole_0(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_setfam_1(k2_tarski(X1,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_32]),c_0_36]),c_0_36]),c_0_36])).

cnf(c_0_67,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_48])).

cnf(c_0_68,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_69,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_70,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_71,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_60])).

cnf(c_0_72,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_73,plain,
    ( k3_subset_1(X1,k3_subset_1(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))))) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_74,plain,
    ( k3_subset_1(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))) = k1_setfam_1(k2_tarski(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_64]),c_0_66]),c_0_48]),c_0_67]),c_0_68])).

cnf(c_0_75,plain,
    ( r2_hidden(X1,X2)
    | X3 != k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X4)))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_69,c_0_36])).

cnf(c_0_76,plain,
    ( k1_setfam_1(k2_tarski(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_62,c_0_70])).

cnf(c_0_77,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_78,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_79,plain,(
    ! [X33,X34] :
      ( ~ m1_subset_1(X34,k1_zfmisc_1(X33))
      | m1_subset_1(k3_subset_1(X33,X34),k1_zfmisc_1(X33)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

cnf(c_0_80,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_81,plain,
    ( X1 != k1_xboole_0
    | ~ r2_hidden(X2,X1) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_72]),c_0_77])).

cnf(c_0_82,plain,
    ( X3 = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_78,c_0_36])).

cnf(c_0_83,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_84,plain,
    ( k3_subset_1(X1,k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,X2)))) = k1_setfam_1(k2_tarski(X1,X2)) ),
    inference(rw,[status(thm)],[c_0_74,c_0_80])).

cnf(c_0_85,plain,
    ( m1_subset_1(k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_64,c_0_80])).

cnf(c_0_86,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_56])).

fof(c_0_87,plain,(
    ! [X47,X48,X49] :
      ( ~ m1_subset_1(X48,k1_zfmisc_1(X47))
      | k7_subset_1(X47,X48,X49) = k4_xboole_0(X48,X49) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

fof(c_0_88,plain,(
    ! [X57,X58] :
      ( ( ~ m1_subset_1(X57,k1_zfmisc_1(X58))
        | r1_tarski(X57,X58) )
      & ( ~ r1_tarski(X57,X58)
        | m1_subset_1(X57,k1_zfmisc_1(X58)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_89,plain,
    ( X1 = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3)))
    | r2_hidden(esk1_3(X2,X3,X1),X2)
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

fof(c_0_90,plain,(
    ! [X50,X51,X52] :
      ( ~ m1_subset_1(X51,k1_zfmisc_1(X50))
      | ~ m1_subset_1(X52,k1_zfmisc_1(X50))
      | k7_subset_1(X50,X51,X52) = k9_subset_1(X50,X51,k3_subset_1(X50,X52)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_subset_1])])])).

cnf(c_0_91,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(X1,X2)),k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_85])])).

cnf(c_0_92,plain,
    ( k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,k2_xboole_0(X1,X2)))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_56,c_0_80])).

cnf(c_0_93,plain,
    ( k3_subset_1(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_86]),c_0_62]),c_0_72])).

cnf(c_0_94,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

fof(c_0_95,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v3_pre_topc(X2,X1)
            <=> k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t76_tops_1])).

cnf(c_0_96,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

cnf(c_0_97,plain,
    ( X1 = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3)))
    | X2 != k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_81,c_0_89])).

cnf(c_0_98,plain,
    ( k7_subset_1(X2,X1,X3) = k9_subset_1(X2,X1,k3_subset_1(X2,X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_99,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

cnf(c_0_100,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(X1,X2)),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_91,c_0_70])).

cnf(c_0_101,plain,
    ( k1_setfam_1(k2_tarski(X1,k2_xboole_0(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_92]),c_0_93])).

cnf(c_0_102,plain,
    ( k7_subset_1(X2,X1,X3) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_94,c_0_36])).

fof(c_0_103,negated_conjecture,
    ( v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & ( ~ v3_pre_topc(esk4_0,esk3_0)
      | k2_tops_1(esk3_0,esk4_0) != k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0) )
    & ( v3_pre_topc(esk4_0,esk3_0)
      | k2_tops_1(esk3_0,esk4_0) = k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_95])])])).

cnf(c_0_104,plain,
    ( r1_tarski(k3_subset_1(X1,X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_96,c_0_83])).

cnf(c_0_105,plain,
    ( r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X1) ),
    inference(spm,[status(thm)],[c_0_96,c_0_64])).

cnf(c_0_106,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_97])).

cnf(c_0_107,plain,
    ( k7_subset_1(X1,X2,X3) = k9_subset_1(X1,X2,k3_subset_1(X1,X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X3,X1) ),
    inference(spm,[status(thm)],[c_0_98,c_0_99])).

cnf(c_0_108,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_100,c_0_101])).

cnf(c_0_109,plain,
    ( k7_subset_1(X1,X2,X3) = k3_subset_1(X2,k1_setfam_1(k2_tarski(X2,X3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_102,c_0_80])).

fof(c_0_110,plain,(
    ! [X17,X18] :
      ( ( r1_tarski(X17,X18)
        | X17 != X18 )
      & ( r1_tarski(X18,X17)
        | X17 != X18 )
      & ( ~ r1_tarski(X17,X18)
        | ~ r1_tarski(X18,X17)
        | X17 = X18 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_111,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k2_xboole_0(X2,X1)))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_56,c_0_58])).

cnf(c_0_112,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_103])).

cnf(c_0_113,plain,
    ( r1_tarski(k3_subset_1(X1,X2),X1)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_104,c_0_99])).

cnf(c_0_114,plain,
    ( r1_tarski(k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,X2))),X1) ),
    inference(rw,[status(thm)],[c_0_105,c_0_80])).

fof(c_0_115,plain,(
    ! [X72,X73] :
      ( ~ l1_pre_topc(X72)
      | ~ m1_subset_1(X73,k1_zfmisc_1(u1_struct_0(X72)))
      | k1_tops_1(X72,X73) = k7_subset_1(u1_struct_0(X72),X73,k2_tops_1(X72,X73)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_tops_1])])])).

cnf(c_0_116,plain,
    ( k2_xboole_0(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_setfam_1(k2_tarski(X1,X3))) = X1
    | X2 != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_106]),c_0_62]),c_0_72])).

cnf(c_0_117,plain,
    ( k7_subset_1(k2_xboole_0(X1,X2),X1,X3) = k9_subset_1(k2_xboole_0(X1,X2),X1,k3_subset_1(k2_xboole_0(X1,X2),X3))
    | ~ r1_tarski(X3,k2_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_107,c_0_108])).

cnf(c_0_118,plain,
    ( k7_subset_1(k2_xboole_0(X1,X2),X1,X3) = k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_109,c_0_108])).

cnf(c_0_119,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_62]),c_0_72])).

cnf(c_0_120,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_110])).

cnf(c_0_121,plain,
    ( k2_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_76]),c_0_72]),c_0_62]),c_0_72]),c_0_62]),c_0_72])).

cnf(c_0_122,plain,
    ( k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,k2_xboole_0(X2,X1)))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_111,c_0_80])).

cnf(c_0_123,negated_conjecture,
    ( k5_xboole_0(u1_struct_0(esk3_0),k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0)))) = k3_subset_1(u1_struct_0(esk3_0),esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_112]),c_0_70])).

cnf(c_0_124,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))) = k3_subset_1(X1,k1_setfam_1(k2_tarski(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_80,c_0_70])).

cnf(c_0_125,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_84]),c_0_114])])).

fof(c_0_126,plain,(
    ! [X42,X43,X44] :
      ( ~ m1_subset_1(X43,k1_zfmisc_1(X42))
      | ~ r2_hidden(X44,X43)
      | r2_hidden(X44,X42) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

fof(c_0_127,plain,(
    ! [X61,X62] :
      ( ~ l1_pre_topc(X61)
      | ~ m1_subset_1(X62,k1_zfmisc_1(u1_struct_0(X61)))
      | r1_tarski(X62,k2_pre_topc(X61,X62)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_pre_topc])])])).

cnf(c_0_128,plain,
    ( k1_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_115])).

cnf(c_0_129,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_103])).

cnf(c_0_130,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X1
    | X1 != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_48]),c_0_67]),c_0_68])).

cnf(c_0_131,plain,
    ( k9_subset_1(k2_xboole_0(X1,X2),X1,k3_subset_1(k2_xboole_0(X1,X2),X3)) = k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,X3)))
    | ~ r1_tarski(X3,k2_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[c_0_117,c_0_118])).

cnf(c_0_132,plain,
    ( k3_subset_1(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_119]),c_0_48]),c_0_67])).

cnf(c_0_133,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_120])).

cnf(c_0_134,plain,
    ( k2_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))) = X1 ),
    inference(spm,[status(thm)],[c_0_121,c_0_70])).

cnf(c_0_135,plain,
    ( k1_setfam_1(k2_tarski(X1,k2_xboole_0(X2,X1))) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_122]),c_0_93])).

cnf(c_0_136,plain,
    ( k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,k3_subset_1(X2,k1_setfam_1(k2_tarski(X2,X3)))))) = k2_xboole_0(k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_setfam_1(k2_tarski(X1,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_80]),c_0_80]),c_0_80])).

cnf(c_0_137,plain,
    ( k3_subset_1(X1,k3_subset_1(X1,X2)) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_99])).

cnf(c_0_138,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk3_0),k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0)))) = k3_subset_1(u1_struct_0(esk3_0),esk4_0) ),
    inference(rw,[status(thm)],[c_0_123,c_0_124])).

cnf(c_0_139,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk3_0),k3_subset_1(u1_struct_0(esk3_0),esk4_0)) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_63,c_0_112])).

cnf(c_0_140,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_125,c_0_70])).

cnf(c_0_141,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_142,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_126])).

cnf(c_0_143,plain,
    ( r1_tarski(X2,k2_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_127])).

cnf(c_0_144,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk3_0),esk4_0,k2_tops_1(esk3_0,esk4_0)) = k1_tops_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_112]),c_0_129])])).

cnf(c_0_145,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk3_0),esk4_0,X1) = k5_xboole_0(esk4_0,k1_setfam_1(k2_tarski(esk4_0,X1))) ),
    inference(spm,[status(thm)],[c_0_102,c_0_112])).

cnf(c_0_146,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = X1
    | X2 != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_62]),c_0_57])).

cnf(c_0_147,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X2
    | X2 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_130,c_0_70])).

cnf(c_0_148,plain,
    ( m1_subset_1(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_70])).

cnf(c_0_149,plain,
    ( k9_subset_1(k2_xboole_0(X1,X2),X1,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_132]),c_0_101]),c_0_132]),c_0_133])])).

cnf(c_0_150,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X1)) = k2_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134,c_0_135]),c_0_58])).

cnf(c_0_151,plain,
    ( k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,k3_subset_1(X2,k1_setfam_1(k2_tarski(X2,X1)))))) = k2_xboole_0(X1,k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,X2)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136,c_0_48]),c_0_58])).

cnf(c_0_152,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137,c_0_138]),c_0_139]),c_0_140])])).

cnf(c_0_153,plain,
    ( X3 = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(rw,[status(thm)],[c_0_141,c_0_36])).

cnf(c_0_154,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(X3,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_142,c_0_99])).

cnf(c_0_155,negated_conjecture,
    ( r1_tarski(esk4_0,k2_pre_topc(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_112]),c_0_129])])).

cnf(c_0_156,plain,
    ( r2_hidden(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,k3_subset_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_142,c_0_83])).

cnf(c_0_157,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k1_xboole_0
    | r2_hidden(esk1_3(X1,X2,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_77,c_0_82])).

cnf(c_0_158,plain,
    ( k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,X2))) = k3_subset_1(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_65,c_0_80])).

cnf(c_0_159,negated_conjecture,
    ( k5_xboole_0(esk4_0,k1_setfam_1(k2_tarski(esk4_0,k2_tops_1(esk3_0,esk4_0)))) = k1_tops_1(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_144,c_0_145])).

cnf(c_0_160,plain,
    ( k5_xboole_0(X1,X2) = X1
    | X2 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_146,c_0_147])).

cnf(c_0_161,plain,
    ( k5_xboole_0(X1,X2) = k3_subset_1(X1,X2)
    | X2 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_80,c_0_147])).

cnf(c_0_162,negated_conjecture,
    ( m1_subset_1(k3_subset_1(u1_struct_0(esk3_0),esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_148,c_0_123])).

cnf(c_0_163,plain,
    ( k9_subset_1(k2_xboole_0(X1,X2),X2,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_149,c_0_150])).

cnf(c_0_164,negated_conjecture,
    ( k2_xboole_0(u1_struct_0(esk3_0),k3_subset_1(u1_struct_0(esk3_0),esk4_0)) = u1_struct_0(esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_151,c_0_152]),c_0_132]),c_0_62]),c_0_93]),c_0_70]),c_0_152])).

cnf(c_0_165,plain,
    ( X1 = k3_subset_1(X2,k1_setfam_1(k2_tarski(X2,X3)))
    | r2_hidden(esk1_3(X2,X3,X1),X1)
    | ~ r2_hidden(esk1_3(X2,X3,X1),X3) ),
    inference(rw,[status(thm)],[c_0_153,c_0_80])).

cnf(c_0_166,negated_conjecture,
    ( r2_hidden(X1,k2_pre_topc(esk3_0,esk4_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_154,c_0_155])).

cnf(c_0_167,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_setfam_1(k2_tarski(X2,X3))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_156,c_0_84]),c_0_85])])).

cnf(c_0_168,plain,
    ( k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,X2))) = k1_xboole_0
    | r2_hidden(esk1_3(X1,X2,k1_xboole_0),X1) ),
    inference(rw,[status(thm)],[c_0_157,c_0_80])).

cnf(c_0_169,plain,
    ( k3_subset_1(k1_setfam_1(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X1,X2)),X3))) = k7_subset_1(X1,k1_setfam_1(k2_tarski(X1,X2)),X3) ),
    inference(spm,[status(thm)],[c_0_109,c_0_91])).

cnf(c_0_170,plain,
    ( k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,X2))) = k3_subset_1(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_158,c_0_99])).

cnf(c_0_171,plain,
    ( k2_xboole_0(k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_setfam_1(k2_tarski(X1,k2_xboole_0(X2,X3)))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136,c_0_101]),c_0_132]),c_0_62]),c_0_93])).

cnf(c_0_172,negated_conjecture,
    ( m1_subset_1(k1_tops_1(esk3_0,esk4_0),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_159])).

cnf(c_0_173,plain,
    ( k3_subset_1(X1,X2) = X1
    | X2 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_160,c_0_161])).

cnf(c_0_174,plain,
    ( k7_subset_1(X1,X2,X1) = k9_subset_1(X1,X2,k1_xboole_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_119]),c_0_132])).

cnf(c_0_175,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk3_0),k3_subset_1(u1_struct_0(esk3_0),esk4_0),X1) = k3_subset_1(k3_subset_1(u1_struct_0(esk3_0),esk4_0),k1_setfam_1(k2_tarski(k3_subset_1(u1_struct_0(esk3_0),esk4_0),X1))) ),
    inference(spm,[status(thm)],[c_0_109,c_0_162])).

cnf(c_0_176,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk3_0),k3_subset_1(u1_struct_0(esk3_0),esk4_0),k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_163,c_0_164])).

fof(c_0_177,plain,(
    ! [X59,X60] :
      ( ~ l1_pre_topc(X59)
      | ~ m1_subset_1(X60,k1_zfmisc_1(u1_struct_0(X59)))
      | m1_subset_1(k2_pre_topc(X59,X60),k1_zfmisc_1(u1_struct_0(X59))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

cnf(c_0_178,negated_conjecture,
    ( X1 = k3_subset_1(X2,k1_setfam_1(k2_tarski(X2,k2_pre_topc(esk3_0,esk4_0))))
    | r2_hidden(esk1_3(X2,k2_pre_topc(esk3_0,esk4_0),X1),X1)
    | ~ r2_hidden(esk1_3(X2,k2_pre_topc(esk3_0,esk4_0),X1),esk4_0) ),
    inference(spm,[status(thm)],[c_0_165,c_0_166])).

cnf(c_0_179,plain,
    ( k7_subset_1(X1,k1_setfam_1(k2_tarski(X1,X2)),X3) = k1_xboole_0
    | r2_hidden(esk1_3(k1_setfam_1(k2_tarski(X1,X2)),X3,k1_xboole_0),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_167,c_0_168]),c_0_169])).

cnf(c_0_180,plain,
    ( k3_subset_1(X1,k3_subset_1(X1,X2)) = k1_setfam_1(k2_tarski(X1,X2))
    | ~ r1_tarski(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137,c_0_170]),c_0_125])])).

cnf(c_0_181,plain,
    ( k1_setfam_1(k2_tarski(X1,k2_xboole_0(k2_xboole_0(X1,X2),X3))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_171,c_0_101]),c_0_132]),c_0_68])).

cnf(c_0_182,negated_conjecture,
    ( k3_subset_1(esk4_0,k1_setfam_1(k2_tarski(esk4_0,k1_tops_1(esk3_0,esk4_0)))) = k3_subset_1(esk4_0,k1_tops_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_158,c_0_172])).

cnf(c_0_183,negated_conjecture,
    ( k3_subset_1(esk4_0,k3_subset_1(esk4_0,k1_tops_1(esk3_0,esk4_0))) = k1_tops_1(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_172])).

cnf(c_0_184,plain,
    ( X1 = X2
    | k3_subset_1(X1,X2) != k1_xboole_0
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_137,c_0_173])).

cnf(c_0_185,negated_conjecture,
    ( k3_subset_1(k3_subset_1(u1_struct_0(esk3_0),esk4_0),k1_setfam_1(k2_tarski(u1_struct_0(esk3_0),k3_subset_1(u1_struct_0(esk3_0),esk4_0)))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_174,c_0_162]),c_0_175]),c_0_70]),c_0_176])).

cnf(c_0_186,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_177])).

fof(c_0_187,plain,(
    ! [X65,X66] :
      ( ~ l1_pre_topc(X65)
      | ~ m1_subset_1(X66,k1_zfmisc_1(u1_struct_0(X65)))
      | k2_tops_1(X65,X66) = k7_subset_1(u1_struct_0(X65),k2_pre_topc(X65,X66),k1_tops_1(X65,X66)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l78_tops_1])])])).

cnf(c_0_188,plain,
    ( k7_subset_1(X1,X2,X3) = k3_subset_1(X2,k1_setfam_1(k2_tarski(X2,X3)))
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_109,c_0_99])).

cnf(c_0_189,negated_conjecture,
    ( k7_subset_1(esk4_0,k1_setfam_1(k2_tarski(esk4_0,X1)),k2_pre_topc(esk3_0,esk4_0)) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_178,c_0_179]),c_0_169])]),c_0_77])).

cnf(c_0_190,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_137,c_0_180])).

cnf(c_0_191,plain,
    ( r1_tarski(X1,k2_xboole_0(k2_xboole_0(X1,X2),X3)) ),
    inference(spm,[status(thm)],[c_0_140,c_0_181])).

cnf(c_0_192,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk4_0,k1_tops_1(esk3_0,esk4_0))) = k1_tops_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137,c_0_182]),c_0_183]),c_0_125])])).

cnf(c_0_193,negated_conjecture,
    ( k3_subset_1(esk4_0,k1_setfam_1(k2_tarski(esk4_0,k2_pre_topc(esk3_0,esk4_0)))) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_178,c_0_168]),c_0_77])).

cnf(c_0_194,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_xboole_0(k2_xboole_0(X1,X2),X3))) ),
    inference(spm,[status(thm)],[c_0_100,c_0_181])).

cnf(c_0_195,plain,
    ( k2_xboole_0(k1_setfam_1(k2_tarski(X1,X2)),k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,X2)))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136,c_0_48]),c_0_132]),c_0_62]),c_0_93]),c_0_58])).

cnf(c_0_196,negated_conjecture,
    ( k1_setfam_1(k2_tarski(u1_struct_0(esk3_0),k3_subset_1(u1_struct_0(esk3_0),esk4_0))) = k3_subset_1(u1_struct_0(esk3_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_184,c_0_185]),c_0_140])])).

cnf(c_0_197,plain,
    ( k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X3) = k3_subset_1(k2_pre_topc(X1,X2),k1_setfam_1(k2_tarski(k2_pre_topc(X1,X2),X3)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_109,c_0_186])).

cnf(c_0_198,plain,
    ( k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_187])).

cnf(c_0_199,plain,
    ( r1_tarski(k2_pre_topc(X1,X2),u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_96,c_0_186])).

cnf(c_0_200,plain,
    ( k3_subset_1(X1,k7_subset_1(X2,X1,X3)) = k1_setfam_1(k2_tarski(X1,X3))
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137,c_0_188]),c_0_125])])).

cnf(c_0_201,negated_conjecture,
    ( k7_subset_1(esk4_0,X1,k2_pre_topc(esk3_0,esk4_0)) = k1_xboole_0
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_189,c_0_190])).

cnf(c_0_202,plain,
    ( r1_tarski(X1,k2_xboole_0(k2_xboole_0(X2,X1),X3)) ),
    inference(spm,[status(thm)],[c_0_191,c_0_150])).

cnf(c_0_203,negated_conjecture,
    ( k2_xboole_0(esk4_0,k1_tops_1(esk3_0,esk4_0)) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_121,c_0_192])).

cnf(c_0_204,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk4_0,k2_pre_topc(esk3_0,esk4_0))) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137,c_0_193]),c_0_93]),c_0_125])])).

fof(c_0_205,plain,(
    ! [X67,X68,X69] :
      ( ~ l1_pre_topc(X67)
      | ~ m1_subset_1(X68,k1_zfmisc_1(u1_struct_0(X67)))
      | ~ m1_subset_1(X69,k1_zfmisc_1(u1_struct_0(X67)))
      | ~ v3_pre_topc(X68,X67)
      | ~ r1_tarski(X68,X69)
      | r1_tarski(X68,k1_tops_1(X67,X69)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_tops_1])])])).

cnf(c_0_206,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(X1,X2)),k1_zfmisc_1(k2_xboole_0(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_194,c_0_195])).

cnf(c_0_207,negated_conjecture,
    ( k2_xboole_0(esk4_0,k3_subset_1(u1_struct_0(esk3_0),esk4_0)) = u1_struct_0(esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_195,c_0_196]),c_0_139]),c_0_58])).

cnf(c_0_208,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk3_0)
    | k2_tops_1(esk3_0,esk4_0) = k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_103])).

cnf(c_0_209,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),X1) = k3_subset_1(k2_pre_topc(esk3_0,esk4_0),k1_setfam_1(k2_tarski(k2_pre_topc(esk3_0,esk4_0),X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_197,c_0_112]),c_0_129])])).

cnf(c_0_210,plain,
    ( k3_subset_1(k2_pre_topc(X1,X2),k1_setfam_1(k2_tarski(k1_tops_1(X1,X2),k2_pre_topc(X1,X2)))) = k2_tops_1(X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_198,c_0_188]),c_0_70]),c_0_199])).

cnf(c_0_211,negated_conjecture,
    ( k1_setfam_1(k2_tarski(X1,k2_pre_topc(esk3_0,esk4_0))) = X1
    | ~ r1_tarski(X1,esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_200,c_0_201]),c_0_93])).

cnf(c_0_212,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk3_0,esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_105,c_0_159])).

cnf(c_0_213,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk3_0,esk4_0),k2_xboole_0(esk4_0,X1)) ),
    inference(spm,[status(thm)],[c_0_202,c_0_203])).

cnf(c_0_214,negated_conjecture,
    ( k2_xboole_0(esk4_0,k2_pre_topc(esk3_0,esk4_0)) = k2_pre_topc(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134,c_0_204]),c_0_58])).

cnf(c_0_215,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_xboole_0(k2_xboole_0(X2,X1),X3))) ),
    inference(spm,[status(thm)],[c_0_194,c_0_150])).

cnf(c_0_216,plain,
    ( r1_tarski(X2,k1_tops_1(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X2,X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_205])).

cnf(c_0_217,negated_conjecture,
    ( m1_subset_1(k1_setfam_1(k2_tarski(esk4_0,X1)),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_206,c_0_207])).

cnf(c_0_218,negated_conjecture,
    ( k3_subset_1(k2_pre_topc(esk3_0,esk4_0),esk4_0) = k2_tops_1(esk3_0,esk4_0)
    | v3_pre_topc(esk4_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_208,c_0_209]),c_0_70]),c_0_204])).

cnf(c_0_219,negated_conjecture,
    ( k3_subset_1(k2_pre_topc(esk3_0,esk4_0),k1_tops_1(esk3_0,esk4_0)) = k2_tops_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_210,c_0_211]),c_0_129]),c_0_112]),c_0_212])])).

cnf(c_0_220,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk3_0,esk4_0),k2_pre_topc(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_213,c_0_214])).

fof(c_0_221,plain,(
    ! [X63,X64] :
      ( ~ v2_pre_topc(X63)
      | ~ l1_pre_topc(X63)
      | ~ m1_subset_1(X64,k1_zfmisc_1(u1_struct_0(X63)))
      | v3_pre_topc(k1_tops_1(X63,X64),X63) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).

cnf(c_0_222,negated_conjecture,
    ( m1_subset_1(k1_tops_1(esk3_0,esk4_0),k1_zfmisc_1(k2_xboole_0(esk4_0,X1))) ),
    inference(spm,[status(thm)],[c_0_215,c_0_203])).

cnf(c_0_223,negated_conjecture,
    ( k2_xboole_0(esk4_0,u1_struct_0(esk3_0)) = u1_struct_0(esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134,c_0_152]),c_0_58])).

cnf(c_0_224,negated_conjecture,
    ( r1_tarski(X1,k1_tops_1(esk3_0,esk4_0))
    | ~ v3_pre_topc(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r1_tarski(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_216,c_0_112]),c_0_129])])).

cnf(c_0_225,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_217,c_0_190])).

cnf(c_0_226,negated_conjecture,
    ( k3_subset_1(k2_pre_topc(esk3_0,esk4_0),k2_tops_1(esk3_0,esk4_0)) = esk4_0
    | v3_pre_topc(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137,c_0_218]),c_0_155])])).

cnf(c_0_227,negated_conjecture,
    ( k3_subset_1(k2_pre_topc(esk3_0,esk4_0),k2_tops_1(esk3_0,esk4_0)) = k1_tops_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137,c_0_219]),c_0_220])])).

cnf(c_0_228,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_110])).

cnf(c_0_229,plain,
    ( v3_pre_topc(k1_tops_1(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_221])).

cnf(c_0_230,negated_conjecture,
    ( m1_subset_1(k1_tops_1(esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_222,c_0_223])).

cnf(c_0_231,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_103])).

cnf(c_0_232,negated_conjecture,
    ( r1_tarski(X1,k1_tops_1(esk3_0,esk4_0))
    | ~ v3_pre_topc(X1,esk3_0)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_224,c_0_225])).

cnf(c_0_233,negated_conjecture,
    ( k1_tops_1(esk3_0,esk4_0) = esk4_0
    | v3_pre_topc(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_226,c_0_227])).

cnf(c_0_234,negated_conjecture,
    ( k1_tops_1(esk3_0,esk4_0) = esk4_0
    | ~ r1_tarski(esk4_0,k1_tops_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_228,c_0_212])).

cnf(c_0_235,negated_conjecture,
    ( ~ v3_pre_topc(esk4_0,esk3_0)
    | k2_tops_1(esk3_0,esk4_0) != k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_103])).

cnf(c_0_236,negated_conjecture,
    ( v3_pre_topc(k1_tops_1(esk3_0,k1_tops_1(esk3_0,esk4_0)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_229,c_0_230]),c_0_231]),c_0_129])])).

cnf(c_0_237,negated_conjecture,
    ( k1_tops_1(esk3_0,esk4_0) = esk4_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_232,c_0_233]),c_0_133])]),c_0_234])).

cnf(c_0_238,negated_conjecture,
    ( k3_subset_1(k2_pre_topc(esk3_0,esk4_0),esk4_0) != k2_tops_1(esk3_0,esk4_0)
    | ~ v3_pre_topc(esk4_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_235,c_0_209]),c_0_70]),c_0_204])).

cnf(c_0_239,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_236,c_0_237]),c_0_237])).

cnf(c_0_240,negated_conjecture,
    ( k3_subset_1(k2_pre_topc(esk3_0,esk4_0),esk4_0) = k2_tops_1(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_219,c_0_237])).

cnf(c_0_241,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_238,c_0_239])]),c_0_240])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:04:09 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 20.11/20.31  # AutoSched0-Mode selected heuristic G_E___107_C36_F1_PI_AE_Q4_CS_SP_PS_S0Y
% 20.11/20.31  # and selection function SelectMaxLComplexAvoidPosPred.
% 20.11/20.31  #
% 20.11/20.31  # Preprocessing time       : 0.029 s
% 20.11/20.31  # Presaturation interreduction done
% 20.11/20.31  
% 20.11/20.31  # Proof found!
% 20.11/20.31  # SZS status Theorem
% 20.11/20.31  # SZS output start CNFRefutation
% 20.11/20.31  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 20.11/20.31  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 20.11/20.31  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 20.11/20.31  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 20.11/20.31  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 20.11/20.31  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 20.11/20.31  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 20.11/20.31  fof(dt_k6_subset_1, axiom, ![X1, X2]:m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 20.11/20.31  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 20.11/20.31  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 20.11/20.31  fof(t52_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 20.11/20.31  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 20.11/20.31  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 20.11/20.31  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 20.11/20.31  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 20.11/20.31  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 20.11/20.31  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 20.11/20.31  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 20.11/20.31  fof(t32_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k9_subset_1(X1,X2,k3_subset_1(X1,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_subset_1)).
% 20.11/20.31  fof(t76_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_tops_1)).
% 20.11/20.31  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 20.11/20.31  fof(t74_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k1_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 20.11/20.31  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 20.11/20.31  fof(t48_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(X2,k2_pre_topc(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_pre_topc)).
% 20.11/20.31  fof(dt_k2_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 20.11/20.31  fof(l78_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 20.11/20.31  fof(t56_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v3_pre_topc(X2,X1)&r1_tarski(X2,X3))=>r1_tarski(X2,k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tops_1)).
% 20.11/20.31  fof(fc9_tops_1, axiom, ![X1, X2]:(((v2_pre_topc(X1)&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v3_pre_topc(k1_tops_1(X1,X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 20.11/20.31  fof(c_0_28, plain, ![X19, X20]:k4_xboole_0(X19,X20)=k5_xboole_0(X19,k3_xboole_0(X19,X20)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 20.11/20.31  fof(c_0_29, plain, ![X55, X56]:k1_setfam_1(k2_tarski(X55,X56))=k3_xboole_0(X55,X56), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 20.11/20.31  fof(c_0_30, plain, ![X7, X8, X9, X10, X11, X12, X13, X14]:((((r2_hidden(X10,X7)|~r2_hidden(X10,X9)|X9!=k4_xboole_0(X7,X8))&(~r2_hidden(X10,X8)|~r2_hidden(X10,X9)|X9!=k4_xboole_0(X7,X8)))&(~r2_hidden(X11,X7)|r2_hidden(X11,X8)|r2_hidden(X11,X9)|X9!=k4_xboole_0(X7,X8)))&((~r2_hidden(esk1_3(X12,X13,X14),X14)|(~r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X13))|X14=k4_xboole_0(X12,X13))&((r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k4_xboole_0(X12,X13))&(~r2_hidden(esk1_3(X12,X13,X14),X13)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k4_xboole_0(X12,X13))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 20.11/20.31  cnf(c_0_31, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 20.11/20.31  cnf(c_0_32, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 20.11/20.31  fof(c_0_33, plain, ![X16]:k3_xboole_0(X16,X16)=X16, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 20.11/20.31  fof(c_0_34, plain, ![X24, X25]:k4_xboole_0(X24,k2_xboole_0(X24,X25))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 20.11/20.31  cnf(c_0_35, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 20.11/20.31  cnf(c_0_36, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_31, c_0_32])).
% 20.11/20.31  cnf(c_0_37, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_33])).
% 20.11/20.31  fof(c_0_38, plain, ![X23]:k4_xboole_0(X23,k1_xboole_0)=X23, inference(variable_rename,[status(thm)],[t3_boole])).
% 20.11/20.31  fof(c_0_39, plain, ![X22]:k3_xboole_0(X22,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 20.11/20.31  fof(c_0_40, plain, ![X35, X36]:m1_subset_1(k6_subset_1(X35,X36),k1_zfmisc_1(X35)), inference(variable_rename,[status(thm)],[dt_k6_subset_1])).
% 20.11/20.31  fof(c_0_41, plain, ![X45, X46]:k6_subset_1(X45,X46)=k4_xboole_0(X45,X46), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 20.11/20.31  fof(c_0_42, plain, ![X31, X32]:(~m1_subset_1(X32,k1_zfmisc_1(X31))|k3_subset_1(X31,X32)=k4_xboole_0(X31,X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 20.11/20.31  fof(c_0_43, plain, ![X26, X27, X28]:k4_xboole_0(X26,k4_xboole_0(X27,X28))=k2_xboole_0(k4_xboole_0(X26,X27),k3_xboole_0(X26,X28)), inference(variable_rename,[status(thm)],[t52_xboole_1])).
% 20.11/20.31  cnf(c_0_44, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_34])).
% 20.11/20.31  fof(c_0_45, plain, ![X21]:k2_xboole_0(X21,k1_xboole_0)=X21, inference(variable_rename,[status(thm)],[t1_boole])).
% 20.11/20.31  fof(c_0_46, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 20.11/20.31  cnf(c_0_47, plain, (X3!=k5_xboole_0(X4,k1_setfam_1(k2_tarski(X4,X2)))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_35, c_0_36])).
% 20.11/20.31  cnf(c_0_48, plain, (k1_setfam_1(k2_tarski(X1,X1))=X1), inference(rw,[status(thm)],[c_0_37, c_0_32])).
% 20.11/20.31  cnf(c_0_49, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_38])).
% 20.11/20.31  cnf(c_0_50, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_39])).
% 20.11/20.31  fof(c_0_51, plain, ![X40, X41]:(~m1_subset_1(X41,k1_zfmisc_1(X40))|k3_subset_1(X40,k3_subset_1(X40,X41))=X41), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 20.11/20.31  cnf(c_0_52, plain, (m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 20.11/20.31  cnf(c_0_53, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 20.11/20.31  cnf(c_0_54, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 20.11/20.31  cnf(c_0_55, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 20.11/20.31  cnf(c_0_56, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k2_xboole_0(X1,X2))))=k1_xboole_0), inference(rw,[status(thm)],[c_0_44, c_0_36])).
% 20.11/20.31  cnf(c_0_57, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_45])).
% 20.11/20.31  cnf(c_0_58, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 20.11/20.31  fof(c_0_59, plain, ![X29, X30]:k2_tarski(X29,X30)=k2_tarski(X30,X29), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 20.11/20.31  cnf(c_0_60, plain, (X1!=k5_xboole_0(X2,X2)|~r2_hidden(X3,X1)|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 20.11/20.31  cnf(c_0_61, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_xboole_0)))=X1), inference(rw,[status(thm)],[c_0_49, c_0_36])).
% 20.11/20.31  cnf(c_0_62, plain, (k1_setfam_1(k2_tarski(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_50, c_0_32])).
% 20.11/20.31  cnf(c_0_63, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 20.11/20.31  cnf(c_0_64, plain, (m1_subset_1(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_zfmisc_1(X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_53]), c_0_36])).
% 20.11/20.31  cnf(c_0_65, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_54, c_0_36])).
% 20.11/20.31  cnf(c_0_66, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3))))))=k2_xboole_0(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_setfam_1(k2_tarski(X1,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_32]), c_0_36]), c_0_36]), c_0_36])).
% 20.11/20.31  cnf(c_0_67, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_48])).
% 20.11/20.31  cnf(c_0_68, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 20.11/20.31  cnf(c_0_69, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 20.11/20.31  cnf(c_0_70, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 20.11/20.31  cnf(c_0_71, plain, (~r2_hidden(X1,k5_xboole_0(X2,X2))|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_60])).
% 20.11/20.31  cnf(c_0_72, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_61, c_0_62])).
% 20.11/20.31  cnf(c_0_73, plain, (k3_subset_1(X1,k3_subset_1(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))))=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 20.11/20.31  cnf(c_0_74, plain, (k3_subset_1(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))))=k1_setfam_1(k2_tarski(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_64]), c_0_66]), c_0_48]), c_0_67]), c_0_68])).
% 20.11/20.31  cnf(c_0_75, plain, (r2_hidden(X1,X2)|X3!=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X4)))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_69, c_0_36])).
% 20.11/20.31  cnf(c_0_76, plain, (k1_setfam_1(k2_tarski(k1_xboole_0,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_62, c_0_70])).
% 20.11/20.31  cnf(c_0_77, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 20.11/20.31  cnf(c_0_78, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 20.11/20.31  fof(c_0_79, plain, ![X33, X34]:(~m1_subset_1(X34,k1_zfmisc_1(X33))|m1_subset_1(k3_subset_1(X33,X34),k1_zfmisc_1(X33))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 20.11/20.31  cnf(c_0_80, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_73, c_0_74])).
% 20.11/20.31  cnf(c_0_81, plain, (X1!=k1_xboole_0|~r2_hidden(X2,X1)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_72]), c_0_77])).
% 20.11/20.31  cnf(c_0_82, plain, (X3=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_78, c_0_36])).
% 20.11/20.31  cnf(c_0_83, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_79])).
% 20.11/20.31  cnf(c_0_84, plain, (k3_subset_1(X1,k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,X2))))=k1_setfam_1(k2_tarski(X1,X2))), inference(rw,[status(thm)],[c_0_74, c_0_80])).
% 20.11/20.31  cnf(c_0_85, plain, (m1_subset_1(k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_64, c_0_80])).
% 20.11/20.31  cnf(c_0_86, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_64, c_0_56])).
% 20.11/20.31  fof(c_0_87, plain, ![X47, X48, X49]:(~m1_subset_1(X48,k1_zfmisc_1(X47))|k7_subset_1(X47,X48,X49)=k4_xboole_0(X48,X49)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 20.11/20.31  fof(c_0_88, plain, ![X57, X58]:((~m1_subset_1(X57,k1_zfmisc_1(X58))|r1_tarski(X57,X58))&(~r1_tarski(X57,X58)|m1_subset_1(X57,k1_zfmisc_1(X58)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 20.11/20.31  cnf(c_0_89, plain, (X1=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3)))|r2_hidden(esk1_3(X2,X3,X1),X2)|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 20.11/20.31  fof(c_0_90, plain, ![X50, X51, X52]:(~m1_subset_1(X51,k1_zfmisc_1(X50))|(~m1_subset_1(X52,k1_zfmisc_1(X50))|k7_subset_1(X50,X51,X52)=k9_subset_1(X50,X51,k3_subset_1(X50,X52)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_subset_1])])])).
% 20.11/20.31  cnf(c_0_91, plain, (m1_subset_1(k1_setfam_1(k2_tarski(X1,X2)),k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_85])])).
% 20.11/20.31  cnf(c_0_92, plain, (k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,k2_xboole_0(X1,X2))))=k1_xboole_0), inference(rw,[status(thm)],[c_0_56, c_0_80])).
% 20.11/20.31  cnf(c_0_93, plain, (k3_subset_1(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_86]), c_0_62]), c_0_72])).
% 20.11/20.31  cnf(c_0_94, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_87])).
% 20.11/20.31  fof(c_0_95, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2))))), inference(assume_negation,[status(cth)],[t76_tops_1])).
% 20.11/20.31  cnf(c_0_96, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_88])).
% 20.11/20.31  cnf(c_0_97, plain, (X1=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3)))|X2!=k1_xboole_0|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_81, c_0_89])).
% 20.11/20.31  cnf(c_0_98, plain, (k7_subset_1(X2,X1,X3)=k9_subset_1(X2,X1,k3_subset_1(X2,X3))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_90])).
% 20.11/20.31  cnf(c_0_99, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_88])).
% 20.11/20.31  cnf(c_0_100, plain, (m1_subset_1(k1_setfam_1(k2_tarski(X1,X2)),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_91, c_0_70])).
% 20.11/20.31  cnf(c_0_101, plain, (k1_setfam_1(k2_tarski(X1,k2_xboole_0(X1,X2)))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_92]), c_0_93])).
% 20.11/20.31  cnf(c_0_102, plain, (k7_subset_1(X2,X1,X3)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_94, c_0_36])).
% 20.11/20.31  fof(c_0_103, negated_conjecture, ((v2_pre_topc(esk3_0)&l1_pre_topc(esk3_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&((~v3_pre_topc(esk4_0,esk3_0)|k2_tops_1(esk3_0,esk4_0)!=k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0))&(v3_pre_topc(esk4_0,esk3_0)|k2_tops_1(esk3_0,esk4_0)=k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_95])])])).
% 20.11/20.31  cnf(c_0_104, plain, (r1_tarski(k3_subset_1(X1,X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_96, c_0_83])).
% 20.11/20.31  cnf(c_0_105, plain, (r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X1)), inference(spm,[status(thm)],[c_0_96, c_0_64])).
% 20.11/20.31  cnf(c_0_106, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k1_xboole_0|X1!=k1_xboole_0), inference(er,[status(thm)],[c_0_97])).
% 20.11/20.31  cnf(c_0_107, plain, (k7_subset_1(X1,X2,X3)=k9_subset_1(X1,X2,k3_subset_1(X1,X3))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X3,X1)), inference(spm,[status(thm)],[c_0_98, c_0_99])).
% 20.11/20.31  cnf(c_0_108, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_100, c_0_101])).
% 20.11/20.31  cnf(c_0_109, plain, (k7_subset_1(X1,X2,X3)=k3_subset_1(X2,k1_setfam_1(k2_tarski(X2,X3)))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_102, c_0_80])).
% 20.11/20.31  fof(c_0_110, plain, ![X17, X18]:(((r1_tarski(X17,X18)|X17!=X18)&(r1_tarski(X18,X17)|X17!=X18))&(~r1_tarski(X17,X18)|~r1_tarski(X18,X17)|X17=X18)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 20.11/20.31  cnf(c_0_111, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k2_xboole_0(X2,X1))))=k1_xboole_0), inference(spm,[status(thm)],[c_0_56, c_0_58])).
% 20.11/20.31  cnf(c_0_112, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_103])).
% 20.11/20.31  cnf(c_0_113, plain, (r1_tarski(k3_subset_1(X1,X2),X1)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_104, c_0_99])).
% 20.11/20.31  cnf(c_0_114, plain, (r1_tarski(k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,X2))),X1)), inference(rw,[status(thm)],[c_0_105, c_0_80])).
% 20.11/20.31  fof(c_0_115, plain, ![X72, X73]:(~l1_pre_topc(X72)|(~m1_subset_1(X73,k1_zfmisc_1(u1_struct_0(X72)))|k1_tops_1(X72,X73)=k7_subset_1(u1_struct_0(X72),X73,k2_tops_1(X72,X73)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_tops_1])])])).
% 20.11/20.31  cnf(c_0_116, plain, (k2_xboole_0(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_setfam_1(k2_tarski(X1,X3)))=X1|X2!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_106]), c_0_62]), c_0_72])).
% 20.11/20.31  cnf(c_0_117, plain, (k7_subset_1(k2_xboole_0(X1,X2),X1,X3)=k9_subset_1(k2_xboole_0(X1,X2),X1,k3_subset_1(k2_xboole_0(X1,X2),X3))|~r1_tarski(X3,k2_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_107, c_0_108])).
% 20.11/20.31  cnf(c_0_118, plain, (k7_subset_1(k2_xboole_0(X1,X2),X1,X3)=k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,X3)))), inference(spm,[status(thm)],[c_0_109, c_0_108])).
% 20.11/20.31  cnf(c_0_119, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_62]), c_0_72])).
% 20.11/20.31  cnf(c_0_120, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_110])).
% 20.11/20.31  cnf(c_0_121, plain, (k2_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_76]), c_0_72]), c_0_62]), c_0_72]), c_0_62]), c_0_72])).
% 20.11/20.31  cnf(c_0_122, plain, (k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,k2_xboole_0(X2,X1))))=k1_xboole_0), inference(rw,[status(thm)],[c_0_111, c_0_80])).
% 20.11/20.31  cnf(c_0_123, negated_conjecture, (k5_xboole_0(u1_struct_0(esk3_0),k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))))=k3_subset_1(u1_struct_0(esk3_0),esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_112]), c_0_70])).
% 20.11/20.31  cnf(c_0_124, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1)))=k3_subset_1(X1,k1_setfam_1(k2_tarski(X2,X1)))), inference(spm,[status(thm)],[c_0_80, c_0_70])).
% 20.11/20.31  cnf(c_0_125, plain, (r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_84]), c_0_114])])).
% 20.11/20.31  fof(c_0_126, plain, ![X42, X43, X44]:(~m1_subset_1(X43,k1_zfmisc_1(X42))|(~r2_hidden(X44,X43)|r2_hidden(X44,X42))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 20.11/20.31  fof(c_0_127, plain, ![X61, X62]:(~l1_pre_topc(X61)|(~m1_subset_1(X62,k1_zfmisc_1(u1_struct_0(X61)))|r1_tarski(X62,k2_pre_topc(X61,X62)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_pre_topc])])])).
% 20.11/20.31  cnf(c_0_128, plain, (k1_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_115])).
% 20.11/20.31  cnf(c_0_129, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_103])).
% 20.11/20.31  cnf(c_0_130, plain, (k1_setfam_1(k2_tarski(X1,X2))=X1|X1!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_48]), c_0_67]), c_0_68])).
% 20.11/20.31  cnf(c_0_131, plain, (k9_subset_1(k2_xboole_0(X1,X2),X1,k3_subset_1(k2_xboole_0(X1,X2),X3))=k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,X3)))|~r1_tarski(X3,k2_xboole_0(X1,X2))), inference(rw,[status(thm)],[c_0_117, c_0_118])).
% 20.11/20.31  cnf(c_0_132, plain, (k3_subset_1(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_119]), c_0_48]), c_0_67])).
% 20.11/20.31  cnf(c_0_133, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_120])).
% 20.11/20.31  cnf(c_0_134, plain, (k2_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1)))=X1), inference(spm,[status(thm)],[c_0_121, c_0_70])).
% 20.11/20.31  cnf(c_0_135, plain, (k1_setfam_1(k2_tarski(X1,k2_xboole_0(X2,X1)))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_122]), c_0_93])).
% 20.11/20.31  cnf(c_0_136, plain, (k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,k3_subset_1(X2,k1_setfam_1(k2_tarski(X2,X3))))))=k2_xboole_0(k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_setfam_1(k2_tarski(X1,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_80]), c_0_80]), c_0_80])).
% 20.11/20.31  cnf(c_0_137, plain, (k3_subset_1(X1,k3_subset_1(X1,X2))=X2|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_63, c_0_99])).
% 20.11/20.31  cnf(c_0_138, negated_conjecture, (k3_subset_1(u1_struct_0(esk3_0),k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0))))=k3_subset_1(u1_struct_0(esk3_0),esk4_0)), inference(rw,[status(thm)],[c_0_123, c_0_124])).
% 20.11/20.31  cnf(c_0_139, negated_conjecture, (k3_subset_1(u1_struct_0(esk3_0),k3_subset_1(u1_struct_0(esk3_0),esk4_0))=esk4_0), inference(spm,[status(thm)],[c_0_63, c_0_112])).
% 20.11/20.31  cnf(c_0_140, plain, (r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_125, c_0_70])).
% 20.11/20.31  cnf(c_0_141, plain, (r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 20.11/20.31  cnf(c_0_142, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_126])).
% 20.11/20.31  cnf(c_0_143, plain, (r1_tarski(X2,k2_pre_topc(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_127])).
% 20.11/20.31  cnf(c_0_144, negated_conjecture, (k7_subset_1(u1_struct_0(esk3_0),esk4_0,k2_tops_1(esk3_0,esk4_0))=k1_tops_1(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_112]), c_0_129])])).
% 20.11/20.31  cnf(c_0_145, negated_conjecture, (k7_subset_1(u1_struct_0(esk3_0),esk4_0,X1)=k5_xboole_0(esk4_0,k1_setfam_1(k2_tarski(esk4_0,X1)))), inference(spm,[status(thm)],[c_0_102, c_0_112])).
% 20.11/20.31  cnf(c_0_146, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=X1|X2!=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_62]), c_0_57])).
% 20.11/20.31  cnf(c_0_147, plain, (k1_setfam_1(k2_tarski(X1,X2))=X2|X2!=k1_xboole_0), inference(spm,[status(thm)],[c_0_130, c_0_70])).
% 20.11/20.31  cnf(c_0_148, plain, (m1_subset_1(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_64, c_0_70])).
% 20.11/20.31  cnf(c_0_149, plain, (k9_subset_1(k2_xboole_0(X1,X2),X1,k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131, c_0_132]), c_0_101]), c_0_132]), c_0_133])])).
% 20.11/20.31  cnf(c_0_150, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X1))=k2_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134, c_0_135]), c_0_58])).
% 20.11/20.31  cnf(c_0_151, plain, (k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,k3_subset_1(X2,k1_setfam_1(k2_tarski(X2,X1))))))=k2_xboole_0(X1,k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,X2))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136, c_0_48]), c_0_58])).
% 20.11/20.31  cnf(c_0_152, negated_conjecture, (k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk3_0)))=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137, c_0_138]), c_0_139]), c_0_140])])).
% 20.11/20.31  cnf(c_0_153, plain, (X3=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))|r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(rw,[status(thm)],[c_0_141, c_0_36])).
% 20.11/20.31  cnf(c_0_154, plain, (r2_hidden(X1,X2)|~r1_tarski(X3,X2)|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_142, c_0_99])).
% 20.11/20.31  cnf(c_0_155, negated_conjecture, (r1_tarski(esk4_0,k2_pre_topc(esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143, c_0_112]), c_0_129])])).
% 20.11/20.31  cnf(c_0_156, plain, (r2_hidden(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r2_hidden(X1,k3_subset_1(X2,X3))), inference(spm,[status(thm)],[c_0_142, c_0_83])).
% 20.11/20.31  cnf(c_0_157, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k1_xboole_0|r2_hidden(esk1_3(X1,X2,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_77, c_0_82])).
% 20.11/20.31  cnf(c_0_158, plain, (k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,X2)))=k3_subset_1(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_65, c_0_80])).
% 20.11/20.31  cnf(c_0_159, negated_conjecture, (k5_xboole_0(esk4_0,k1_setfam_1(k2_tarski(esk4_0,k2_tops_1(esk3_0,esk4_0))))=k1_tops_1(esk3_0,esk4_0)), inference(rw,[status(thm)],[c_0_144, c_0_145])).
% 20.11/20.31  cnf(c_0_160, plain, (k5_xboole_0(X1,X2)=X1|X2!=k1_xboole_0), inference(spm,[status(thm)],[c_0_146, c_0_147])).
% 20.11/20.31  cnf(c_0_161, plain, (k5_xboole_0(X1,X2)=k3_subset_1(X1,X2)|X2!=k1_xboole_0), inference(spm,[status(thm)],[c_0_80, c_0_147])).
% 20.11/20.31  cnf(c_0_162, negated_conjecture, (m1_subset_1(k3_subset_1(u1_struct_0(esk3_0),esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_148, c_0_123])).
% 20.11/20.31  cnf(c_0_163, plain, (k9_subset_1(k2_xboole_0(X1,X2),X2,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_149, c_0_150])).
% 20.11/20.31  cnf(c_0_164, negated_conjecture, (k2_xboole_0(u1_struct_0(esk3_0),k3_subset_1(u1_struct_0(esk3_0),esk4_0))=u1_struct_0(esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_151, c_0_152]), c_0_132]), c_0_62]), c_0_93]), c_0_70]), c_0_152])).
% 20.11/20.31  cnf(c_0_165, plain, (X1=k3_subset_1(X2,k1_setfam_1(k2_tarski(X2,X3)))|r2_hidden(esk1_3(X2,X3,X1),X1)|~r2_hidden(esk1_3(X2,X3,X1),X3)), inference(rw,[status(thm)],[c_0_153, c_0_80])).
% 20.11/20.31  cnf(c_0_166, negated_conjecture, (r2_hidden(X1,k2_pre_topc(esk3_0,esk4_0))|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_154, c_0_155])).
% 20.11/20.31  cnf(c_0_167, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_setfam_1(k2_tarski(X2,X3)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_156, c_0_84]), c_0_85])])).
% 20.11/20.31  cnf(c_0_168, plain, (k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,X2)))=k1_xboole_0|r2_hidden(esk1_3(X1,X2,k1_xboole_0),X1)), inference(rw,[status(thm)],[c_0_157, c_0_80])).
% 20.11/20.31  cnf(c_0_169, plain, (k3_subset_1(k1_setfam_1(k2_tarski(X1,X2)),k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X1,X2)),X3)))=k7_subset_1(X1,k1_setfam_1(k2_tarski(X1,X2)),X3)), inference(spm,[status(thm)],[c_0_109, c_0_91])).
% 20.11/20.31  cnf(c_0_170, plain, (k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,X2)))=k3_subset_1(X1,X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_158, c_0_99])).
% 20.11/20.31  cnf(c_0_171, plain, (k2_xboole_0(k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,X2))),k1_setfam_1(k2_tarski(X1,k2_xboole_0(X2,X3))))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136, c_0_101]), c_0_132]), c_0_62]), c_0_93])).
% 20.11/20.31  cnf(c_0_172, negated_conjecture, (m1_subset_1(k1_tops_1(esk3_0,esk4_0),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_64, c_0_159])).
% 20.11/20.31  cnf(c_0_173, plain, (k3_subset_1(X1,X2)=X1|X2!=k1_xboole_0), inference(spm,[status(thm)],[c_0_160, c_0_161])).
% 20.11/20.31  cnf(c_0_174, plain, (k7_subset_1(X1,X2,X1)=k9_subset_1(X1,X2,k1_xboole_0)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_119]), c_0_132])).
% 20.11/20.31  cnf(c_0_175, negated_conjecture, (k7_subset_1(u1_struct_0(esk3_0),k3_subset_1(u1_struct_0(esk3_0),esk4_0),X1)=k3_subset_1(k3_subset_1(u1_struct_0(esk3_0),esk4_0),k1_setfam_1(k2_tarski(k3_subset_1(u1_struct_0(esk3_0),esk4_0),X1)))), inference(spm,[status(thm)],[c_0_109, c_0_162])).
% 20.11/20.31  cnf(c_0_176, negated_conjecture, (k9_subset_1(u1_struct_0(esk3_0),k3_subset_1(u1_struct_0(esk3_0),esk4_0),k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_163, c_0_164])).
% 20.11/20.31  fof(c_0_177, plain, ![X59, X60]:(~l1_pre_topc(X59)|~m1_subset_1(X60,k1_zfmisc_1(u1_struct_0(X59)))|m1_subset_1(k2_pre_topc(X59,X60),k1_zfmisc_1(u1_struct_0(X59)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).
% 20.11/20.31  cnf(c_0_178, negated_conjecture, (X1=k3_subset_1(X2,k1_setfam_1(k2_tarski(X2,k2_pre_topc(esk3_0,esk4_0))))|r2_hidden(esk1_3(X2,k2_pre_topc(esk3_0,esk4_0),X1),X1)|~r2_hidden(esk1_3(X2,k2_pre_topc(esk3_0,esk4_0),X1),esk4_0)), inference(spm,[status(thm)],[c_0_165, c_0_166])).
% 20.11/20.31  cnf(c_0_179, plain, (k7_subset_1(X1,k1_setfam_1(k2_tarski(X1,X2)),X3)=k1_xboole_0|r2_hidden(esk1_3(k1_setfam_1(k2_tarski(X1,X2)),X3,k1_xboole_0),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_167, c_0_168]), c_0_169])).
% 20.11/20.31  cnf(c_0_180, plain, (k3_subset_1(X1,k3_subset_1(X1,X2))=k1_setfam_1(k2_tarski(X1,X2))|~r1_tarski(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137, c_0_170]), c_0_125])])).
% 20.11/20.31  cnf(c_0_181, plain, (k1_setfam_1(k2_tarski(X1,k2_xboole_0(k2_xboole_0(X1,X2),X3)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_171, c_0_101]), c_0_132]), c_0_68])).
% 20.11/20.31  cnf(c_0_182, negated_conjecture, (k3_subset_1(esk4_0,k1_setfam_1(k2_tarski(esk4_0,k1_tops_1(esk3_0,esk4_0))))=k3_subset_1(esk4_0,k1_tops_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_158, c_0_172])).
% 20.11/20.31  cnf(c_0_183, negated_conjecture, (k3_subset_1(esk4_0,k3_subset_1(esk4_0,k1_tops_1(esk3_0,esk4_0)))=k1_tops_1(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_63, c_0_172])).
% 20.11/20.31  cnf(c_0_184, plain, (X1=X2|k3_subset_1(X1,X2)!=k1_xboole_0|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_137, c_0_173])).
% 20.11/20.31  cnf(c_0_185, negated_conjecture, (k3_subset_1(k3_subset_1(u1_struct_0(esk3_0),esk4_0),k1_setfam_1(k2_tarski(u1_struct_0(esk3_0),k3_subset_1(u1_struct_0(esk3_0),esk4_0))))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_174, c_0_162]), c_0_175]), c_0_70]), c_0_176])).
% 20.11/20.31  cnf(c_0_186, plain, (m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_177])).
% 20.11/20.31  fof(c_0_187, plain, ![X65, X66]:(~l1_pre_topc(X65)|(~m1_subset_1(X66,k1_zfmisc_1(u1_struct_0(X65)))|k2_tops_1(X65,X66)=k7_subset_1(u1_struct_0(X65),k2_pre_topc(X65,X66),k1_tops_1(X65,X66)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l78_tops_1])])])).
% 20.11/20.31  cnf(c_0_188, plain, (k7_subset_1(X1,X2,X3)=k3_subset_1(X2,k1_setfam_1(k2_tarski(X2,X3)))|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_109, c_0_99])).
% 20.11/20.31  cnf(c_0_189, negated_conjecture, (k7_subset_1(esk4_0,k1_setfam_1(k2_tarski(esk4_0,X1)),k2_pre_topc(esk3_0,esk4_0))=k1_xboole_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_178, c_0_179]), c_0_169])]), c_0_77])).
% 20.11/20.31  cnf(c_0_190, plain, (k1_setfam_1(k2_tarski(X1,X2))=X2|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_137, c_0_180])).
% 20.11/20.31  cnf(c_0_191, plain, (r1_tarski(X1,k2_xboole_0(k2_xboole_0(X1,X2),X3))), inference(spm,[status(thm)],[c_0_140, c_0_181])).
% 20.11/20.31  cnf(c_0_192, negated_conjecture, (k1_setfam_1(k2_tarski(esk4_0,k1_tops_1(esk3_0,esk4_0)))=k1_tops_1(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137, c_0_182]), c_0_183]), c_0_125])])).
% 20.11/20.31  cnf(c_0_193, negated_conjecture, (k3_subset_1(esk4_0,k1_setfam_1(k2_tarski(esk4_0,k2_pre_topc(esk3_0,esk4_0))))=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_178, c_0_168]), c_0_77])).
% 20.11/20.31  cnf(c_0_194, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_xboole_0(k2_xboole_0(X1,X2),X3)))), inference(spm,[status(thm)],[c_0_100, c_0_181])).
% 20.11/20.31  cnf(c_0_195, plain, (k2_xboole_0(k1_setfam_1(k2_tarski(X1,X2)),k3_subset_1(X1,k1_setfam_1(k2_tarski(X1,X2))))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136, c_0_48]), c_0_132]), c_0_62]), c_0_93]), c_0_58])).
% 20.11/20.31  cnf(c_0_196, negated_conjecture, (k1_setfam_1(k2_tarski(u1_struct_0(esk3_0),k3_subset_1(u1_struct_0(esk3_0),esk4_0)))=k3_subset_1(u1_struct_0(esk3_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_184, c_0_185]), c_0_140])])).
% 20.11/20.31  cnf(c_0_197, plain, (k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X3)=k3_subset_1(k2_pre_topc(X1,X2),k1_setfam_1(k2_tarski(k2_pre_topc(X1,X2),X3)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_109, c_0_186])).
% 20.11/20.31  cnf(c_0_198, plain, (k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_187])).
% 20.11/20.31  cnf(c_0_199, plain, (r1_tarski(k2_pre_topc(X1,X2),u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_96, c_0_186])).
% 20.11/20.31  cnf(c_0_200, plain, (k3_subset_1(X1,k7_subset_1(X2,X1,X3))=k1_setfam_1(k2_tarski(X1,X3))|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137, c_0_188]), c_0_125])])).
% 20.11/20.31  cnf(c_0_201, negated_conjecture, (k7_subset_1(esk4_0,X1,k2_pre_topc(esk3_0,esk4_0))=k1_xboole_0|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_189, c_0_190])).
% 20.11/20.31  cnf(c_0_202, plain, (r1_tarski(X1,k2_xboole_0(k2_xboole_0(X2,X1),X3))), inference(spm,[status(thm)],[c_0_191, c_0_150])).
% 20.11/20.31  cnf(c_0_203, negated_conjecture, (k2_xboole_0(esk4_0,k1_tops_1(esk3_0,esk4_0))=esk4_0), inference(spm,[status(thm)],[c_0_121, c_0_192])).
% 20.11/20.31  cnf(c_0_204, negated_conjecture, (k1_setfam_1(k2_tarski(esk4_0,k2_pre_topc(esk3_0,esk4_0)))=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137, c_0_193]), c_0_93]), c_0_125])])).
% 20.11/20.31  fof(c_0_205, plain, ![X67, X68, X69]:(~l1_pre_topc(X67)|(~m1_subset_1(X68,k1_zfmisc_1(u1_struct_0(X67)))|(~m1_subset_1(X69,k1_zfmisc_1(u1_struct_0(X67)))|(~v3_pre_topc(X68,X67)|~r1_tarski(X68,X69)|r1_tarski(X68,k1_tops_1(X67,X69)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_tops_1])])])).
% 20.11/20.31  cnf(c_0_206, plain, (m1_subset_1(k1_setfam_1(k2_tarski(X1,X2)),k1_zfmisc_1(k2_xboole_0(X1,X3)))), inference(spm,[status(thm)],[c_0_194, c_0_195])).
% 20.11/20.31  cnf(c_0_207, negated_conjecture, (k2_xboole_0(esk4_0,k3_subset_1(u1_struct_0(esk3_0),esk4_0))=u1_struct_0(esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_195, c_0_196]), c_0_139]), c_0_58])).
% 20.11/20.31  cnf(c_0_208, negated_conjecture, (v3_pre_topc(esk4_0,esk3_0)|k2_tops_1(esk3_0,esk4_0)=k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_103])).
% 20.11/20.31  cnf(c_0_209, negated_conjecture, (k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),X1)=k3_subset_1(k2_pre_topc(esk3_0,esk4_0),k1_setfam_1(k2_tarski(k2_pre_topc(esk3_0,esk4_0),X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_197, c_0_112]), c_0_129])])).
% 20.11/20.31  cnf(c_0_210, plain, (k3_subset_1(k2_pre_topc(X1,X2),k1_setfam_1(k2_tarski(k1_tops_1(X1,X2),k2_pre_topc(X1,X2))))=k2_tops_1(X1,X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_198, c_0_188]), c_0_70]), c_0_199])).
% 20.11/20.31  cnf(c_0_211, negated_conjecture, (k1_setfam_1(k2_tarski(X1,k2_pre_topc(esk3_0,esk4_0)))=X1|~r1_tarski(X1,esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_200, c_0_201]), c_0_93])).
% 20.11/20.31  cnf(c_0_212, negated_conjecture, (r1_tarski(k1_tops_1(esk3_0,esk4_0),esk4_0)), inference(spm,[status(thm)],[c_0_105, c_0_159])).
% 20.11/20.31  cnf(c_0_213, negated_conjecture, (r1_tarski(k1_tops_1(esk3_0,esk4_0),k2_xboole_0(esk4_0,X1))), inference(spm,[status(thm)],[c_0_202, c_0_203])).
% 20.11/20.31  cnf(c_0_214, negated_conjecture, (k2_xboole_0(esk4_0,k2_pre_topc(esk3_0,esk4_0))=k2_pre_topc(esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134, c_0_204]), c_0_58])).
% 20.11/20.31  cnf(c_0_215, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_xboole_0(k2_xboole_0(X2,X1),X3)))), inference(spm,[status(thm)],[c_0_194, c_0_150])).
% 20.11/20.31  cnf(c_0_216, plain, (r1_tarski(X2,k1_tops_1(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v3_pre_topc(X2,X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_205])).
% 20.11/20.31  cnf(c_0_217, negated_conjecture, (m1_subset_1(k1_setfam_1(k2_tarski(esk4_0,X1)),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_206, c_0_207])).
% 20.11/20.31  cnf(c_0_218, negated_conjecture, (k3_subset_1(k2_pre_topc(esk3_0,esk4_0),esk4_0)=k2_tops_1(esk3_0,esk4_0)|v3_pre_topc(esk4_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_208, c_0_209]), c_0_70]), c_0_204])).
% 20.11/20.31  cnf(c_0_219, negated_conjecture, (k3_subset_1(k2_pre_topc(esk3_0,esk4_0),k1_tops_1(esk3_0,esk4_0))=k2_tops_1(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_210, c_0_211]), c_0_129]), c_0_112]), c_0_212])])).
% 20.11/20.31  cnf(c_0_220, negated_conjecture, (r1_tarski(k1_tops_1(esk3_0,esk4_0),k2_pre_topc(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_213, c_0_214])).
% 20.11/20.31  fof(c_0_221, plain, ![X63, X64]:(~v2_pre_topc(X63)|~l1_pre_topc(X63)|~m1_subset_1(X64,k1_zfmisc_1(u1_struct_0(X63)))|v3_pre_topc(k1_tops_1(X63,X64),X63)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).
% 20.11/20.31  cnf(c_0_222, negated_conjecture, (m1_subset_1(k1_tops_1(esk3_0,esk4_0),k1_zfmisc_1(k2_xboole_0(esk4_0,X1)))), inference(spm,[status(thm)],[c_0_215, c_0_203])).
% 20.11/20.31  cnf(c_0_223, negated_conjecture, (k2_xboole_0(esk4_0,u1_struct_0(esk3_0))=u1_struct_0(esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134, c_0_152]), c_0_58])).
% 20.11/20.31  cnf(c_0_224, negated_conjecture, (r1_tarski(X1,k1_tops_1(esk3_0,esk4_0))|~v3_pre_topc(X1,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r1_tarski(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_216, c_0_112]), c_0_129])])).
% 20.11/20.31  cnf(c_0_225, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_217, c_0_190])).
% 20.11/20.31  cnf(c_0_226, negated_conjecture, (k3_subset_1(k2_pre_topc(esk3_0,esk4_0),k2_tops_1(esk3_0,esk4_0))=esk4_0|v3_pre_topc(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137, c_0_218]), c_0_155])])).
% 20.11/20.31  cnf(c_0_227, negated_conjecture, (k3_subset_1(k2_pre_topc(esk3_0,esk4_0),k2_tops_1(esk3_0,esk4_0))=k1_tops_1(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137, c_0_219]), c_0_220])])).
% 20.11/20.31  cnf(c_0_228, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_110])).
% 20.11/20.31  cnf(c_0_229, plain, (v3_pre_topc(k1_tops_1(X1,X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_221])).
% 20.11/20.31  cnf(c_0_230, negated_conjecture, (m1_subset_1(k1_tops_1(esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_222, c_0_223])).
% 20.11/20.31  cnf(c_0_231, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_103])).
% 20.11/20.31  cnf(c_0_232, negated_conjecture, (r1_tarski(X1,k1_tops_1(esk3_0,esk4_0))|~v3_pre_topc(X1,esk3_0)|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_224, c_0_225])).
% 20.11/20.31  cnf(c_0_233, negated_conjecture, (k1_tops_1(esk3_0,esk4_0)=esk4_0|v3_pre_topc(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_226, c_0_227])).
% 20.11/20.31  cnf(c_0_234, negated_conjecture, (k1_tops_1(esk3_0,esk4_0)=esk4_0|~r1_tarski(esk4_0,k1_tops_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_228, c_0_212])).
% 20.11/20.31  cnf(c_0_235, negated_conjecture, (~v3_pre_topc(esk4_0,esk3_0)|k2_tops_1(esk3_0,esk4_0)!=k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_103])).
% 20.11/20.31  cnf(c_0_236, negated_conjecture, (v3_pre_topc(k1_tops_1(esk3_0,k1_tops_1(esk3_0,esk4_0)),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_229, c_0_230]), c_0_231]), c_0_129])])).
% 20.11/20.31  cnf(c_0_237, negated_conjecture, (k1_tops_1(esk3_0,esk4_0)=esk4_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_232, c_0_233]), c_0_133])]), c_0_234])).
% 20.11/20.31  cnf(c_0_238, negated_conjecture, (k3_subset_1(k2_pre_topc(esk3_0,esk4_0),esk4_0)!=k2_tops_1(esk3_0,esk4_0)|~v3_pre_topc(esk4_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_235, c_0_209]), c_0_70]), c_0_204])).
% 20.11/20.31  cnf(c_0_239, negated_conjecture, (v3_pre_topc(esk4_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_236, c_0_237]), c_0_237])).
% 20.11/20.31  cnf(c_0_240, negated_conjecture, (k3_subset_1(k2_pre_topc(esk3_0,esk4_0),esk4_0)=k2_tops_1(esk3_0,esk4_0)), inference(rw,[status(thm)],[c_0_219, c_0_237])).
% 20.11/20.31  cnf(c_0_241, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_238, c_0_239])]), c_0_240])]), ['proof']).
% 20.11/20.31  # SZS output end CNFRefutation
% 20.11/20.31  # Proof object total steps             : 242
% 20.11/20.31  # Proof object clause steps            : 185
% 20.11/20.31  # Proof object formula steps           : 57
% 20.11/20.31  # Proof object conjectures             : 59
% 20.11/20.31  # Proof object clause conjectures      : 56
% 20.11/20.31  # Proof object formula conjectures     : 3
% 20.11/20.31  # Proof object initial clauses used    : 37
% 20.11/20.31  # Proof object initial formulas used   : 28
% 20.11/20.31  # Proof object generating inferences   : 114
% 20.11/20.31  # Proof object simplifying inferences  : 152
% 20.11/20.31  # Training examples: 0 positive, 0 negative
% 20.11/20.31  # Parsed axioms                        : 31
% 20.11/20.31  # Removed by relevancy pruning/SinE    : 0
% 20.11/20.31  # Initial clauses                      : 44
% 20.11/20.31  # Removed in clause preprocessing      : 3
% 20.11/20.31  # Initial clauses in saturation        : 41
% 20.11/20.31  # Processed clauses                    : 98634
% 20.11/20.31  # ...of these trivial                  : 4342
% 20.11/20.31  # ...subsumed                          : 84244
% 20.11/20.31  # ...remaining for further processing  : 10047
% 20.11/20.31  # Other redundant clauses eliminated   : 2609
% 20.11/20.31  # Clauses deleted for lack of memory   : 0
% 20.11/20.31  # Backward-subsumed                    : 1063
% 20.11/20.31  # Backward-rewritten                   : 1782
% 20.11/20.31  # Generated clauses                    : 2375620
% 20.11/20.31  # ...of the previous two non-trivial   : 1915206
% 20.11/20.31  # Contextual simplify-reflections      : 205
% 20.11/20.31  # Paramodulations                      : 2372406
% 20.11/20.31  # Factorizations                       : 56
% 20.11/20.31  # Equation resolutions                 : 3113
% 20.11/20.31  # Propositional unsat checks           : 0
% 20.11/20.31  #    Propositional check models        : 0
% 20.11/20.31  #    Propositional check unsatisfiable : 0
% 20.11/20.31  #    Propositional clauses             : 0
% 20.11/20.31  #    Propositional clauses after purity: 0
% 20.11/20.31  #    Propositional unsat core size     : 0
% 20.11/20.31  #    Propositional preprocessing time  : 0.000
% 20.11/20.31  #    Propositional encoding time       : 0.000
% 20.11/20.31  #    Propositional solver time         : 0.000
% 20.11/20.31  #    Success case prop preproc time    : 0.000
% 20.11/20.31  #    Success case prop encoding time   : 0.000
% 20.11/20.31  #    Success case prop solver time     : 0.000
% 20.11/20.31  # Current number of processed clauses  : 7141
% 20.11/20.31  #    Positive orientable unit clauses  : 1034
% 20.11/20.31  #    Positive unorientable unit clauses: 25
% 20.11/20.31  #    Negative unit clauses             : 81
% 20.11/20.31  #    Non-unit-clauses                  : 6001
% 20.11/20.31  # Current number of unprocessed clauses: 1803316
% 20.11/20.31  # ...number of literals in the above   : 6771094
% 20.11/20.31  # Current number of archived formulas  : 0
% 20.11/20.31  # Current number of archived clauses   : 2892
% 20.11/20.31  # Clause-clause subsumption calls (NU) : 7208388
% 20.11/20.31  # Rec. Clause-clause subsumption calls : 4444227
% 20.11/20.31  # Non-unit clause-clause subsumptions  : 46999
% 20.11/20.31  # Unit Clause-clause subsumption calls : 125334
% 20.11/20.31  # Rewrite failures with RHS unbound    : 0
% 20.11/20.31  # BW rewrite match attempts            : 12108
% 20.11/20.31  # BW rewrite match successes           : 312
% 20.11/20.31  # Condensation attempts                : 0
% 20.11/20.31  # Condensation successes               : 0
% 20.11/20.31  # Termbank termtop insertions          : 46110468
% 20.20/20.37  
% 20.20/20.37  # -------------------------------------------------
% 20.20/20.37  # User time                : 19.295 s
% 20.20/20.37  # System time              : 0.733 s
% 20.20/20.37  # Total time               : 20.028 s
% 20.20/20.37  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------

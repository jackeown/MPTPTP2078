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
% DateTime   : Thu Dec  3 11:11:23 EST 2020

% Result     : Theorem 0.63s
% Output     : CNFRefutation 0.63s
% Verified   : 
% Statistics : Number of formulae       :  112 (2237 expanded)
%              Number of clauses        :   85 (1047 expanded)
%              Number of leaves         :   13 ( 574 expanded)
%              Depth                    :   21
%              Number of atoms          :  298 (4854 expanded)
%              Number of equality atoms :  113 (2545 expanded)
%              Maximal formula depth    :   17 (   3 average)
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

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t76_tops_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(t55_tops_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                 => ( ( v3_pre_topc(X4,X2)
                     => k1_tops_1(X2,X4) = X4 )
                    & ( k1_tops_1(X1,X3) = X3
                     => v3_pre_topc(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).

fof(t74_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k1_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(l78_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(c_0_13,plain,(
    ! [X25,X26] : k4_xboole_0(X25,X26) = k5_xboole_0(X25,k3_xboole_0(X25,X26)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_14,plain,(
    ! [X33,X34] : k1_setfam_1(k2_tarski(X33,X34)) = k3_xboole_0(X33,X34) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_15,plain,(
    ! [X16,X17,X18,X19,X20,X21,X22,X23] :
      ( ( r2_hidden(X19,X16)
        | ~ r2_hidden(X19,X18)
        | X18 != k4_xboole_0(X16,X17) )
      & ( ~ r2_hidden(X19,X17)
        | ~ r2_hidden(X19,X18)
        | X18 != k4_xboole_0(X16,X17) )
      & ( ~ r2_hidden(X20,X16)
        | r2_hidden(X20,X17)
        | r2_hidden(X20,X18)
        | X18 != k4_xboole_0(X16,X17) )
      & ( ~ r2_hidden(esk2_3(X21,X22,X23),X23)
        | ~ r2_hidden(esk2_3(X21,X22,X23),X21)
        | r2_hidden(esk2_3(X21,X22,X23),X22)
        | X23 = k4_xboole_0(X21,X22) )
      & ( r2_hidden(esk2_3(X21,X22,X23),X21)
        | r2_hidden(esk2_3(X21,X22,X23),X23)
        | X23 = k4_xboole_0(X21,X22) )
      & ( ~ r2_hidden(esk2_3(X21,X22,X23),X22)
        | r2_hidden(esk2_3(X21,X22,X23),X23)
        | X23 = k4_xboole_0(X21,X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_16,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

fof(c_0_20,plain,(
    ! [X7,X8,X9,X10,X11,X12,X13,X14] :
      ( ( r2_hidden(X10,X7)
        | ~ r2_hidden(X10,X9)
        | X9 != k3_xboole_0(X7,X8) )
      & ( r2_hidden(X10,X8)
        | ~ r2_hidden(X10,X9)
        | X9 != k3_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X11,X7)
        | ~ r2_hidden(X11,X8)
        | r2_hidden(X11,X9)
        | X9 != k3_xboole_0(X7,X8) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X12)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X13)
        | X14 = k3_xboole_0(X12,X13) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X12)
        | r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k3_xboole_0(X12,X13) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X13)
        | r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k3_xboole_0(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_21,plain,(
    ! [X27] : k3_xboole_0(X27,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_22,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_23,plain,
    ( X3 != k5_xboole_0(X4,k1_setfam_1(k2_tarski(X4,X2)))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_24,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_25,plain,(
    ! [X28,X29] : k4_xboole_0(X28,k4_xboole_0(X28,X29)) = k3_xboole_0(X28,X29) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_26,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3))))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( X3 = k1_setfam_1(k2_tarski(X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(rw,[status(thm)],[c_0_24,c_0_17])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( k1_setfam_1(k2_tarski(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_26,c_0_17])).

cnf(c_0_32,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k1_setfam_1(k2_tarski(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_17]),c_0_17])).

cnf(c_0_33,plain,
    ( X1 = k1_setfam_1(k2_tarski(X2,X3))
    | r2_hidden(esk1_3(X2,X3,X1),X1)
    | ~ r2_hidden(esk1_3(X2,X3,X1),k5_xboole_0(X4,k1_setfam_1(k2_tarski(X4,X3)))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_34,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))))) = k1_setfam_1(k2_tarski(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_17]),c_0_19]),c_0_19])).

cnf(c_0_35,plain,
    ( k1_setfam_1(k2_tarski(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_37,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_3(X2,k1_xboole_0,X1),X1)
    | ~ r2_hidden(esk1_3(X2,k1_xboole_0,X1),k5_xboole_0(X3,k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_31]),c_0_31])).

cnf(c_0_38,plain,
    ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_35])).

cnf(c_0_39,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_40,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,X2)
    | X3 != k1_setfam_1(k2_tarski(X4,X2))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_36,c_0_17])).

cnf(c_0_42,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_3(X2,k1_xboole_0,X1),X1)
    | ~ r2_hidden(esk1_3(X2,k1_xboole_0,X1),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_44,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v3_pre_topc(X2,X1)
            <=> k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t76_tops_1])).

cnf(c_0_45,plain,
    ( X3 = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2) ),
    inference(rw,[status(thm)],[c_0_39,c_0_19])).

cnf(c_0_46,plain,
    ( X3 = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | r2_hidden(esk2_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_40,c_0_19])).

fof(c_0_47,plain,(
    ! [X30,X31,X32] :
      ( ~ m1_subset_1(X31,k1_zfmisc_1(X30))
      | k7_subset_1(X30,X31,X32) = k4_xboole_0(X31,X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_setfam_1(k2_tarski(X3,X2))) ),
    inference(er,[status(thm)],[c_0_41])).

cnf(c_0_49,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_3(X2,k1_xboole_0,X1),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_29]),c_0_31])])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,X2)
    | X3 != k1_setfam_1(k2_tarski(X2,X4))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_43,c_0_17])).

fof(c_0_51,plain,(
    ! [X35,X36] :
      ( ~ l1_pre_topc(X35)
      | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))
      | m1_subset_1(k2_pre_topc(X35,X36),k1_zfmisc_1(u1_struct_0(X35))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

fof(c_0_52,negated_conjecture,
    ( v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & ( ~ v3_pre_topc(esk4_0,esk3_0)
      | k2_tops_1(esk3_0,esk4_0) != k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0) )
    & ( v3_pre_topc(esk4_0,esk3_0)
      | k2_tops_1(esk3_0,esk4_0) = k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_44])])])).

cnf(c_0_53,plain,
    ( X1 = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X2)))
    | r2_hidden(esk2_3(X2,X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_54,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_55,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k1_xboole_0
    | r2_hidden(esk1_3(X3,k1_xboole_0,k1_setfam_1(k2_tarski(X1,X2))),X2) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_56,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_setfam_1(k2_tarski(X2,X3))) ),
    inference(er,[status(thm)],[c_0_50])).

cnf(c_0_57,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_59,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_60,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_61,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X4 != k4_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_62,plain,
    ( X1 = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X2)))
    | ~ r2_hidden(esk2_3(X2,X2,X1),k5_xboole_0(X3,k1_setfam_1(k2_tarski(X3,X1)))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_53])).

cnf(c_0_63,plain,
    ( k7_subset_1(X2,X1,X3) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_54,c_0_19])).

cnf(c_0_64,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k1_xboole_0
    | ~ r2_hidden(esk1_3(X3,k1_xboole_0,k1_setfam_1(k2_tarski(X1,X2))),k5_xboole_0(X4,k1_setfam_1(k2_tarski(X4,X2)))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_55])).

cnf(c_0_65,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k1_xboole_0
    | r2_hidden(esk1_3(X3,k1_xboole_0,k1_setfam_1(k2_tarski(X1,X2))),X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_49])).

cnf(c_0_66,negated_conjecture,
    ( m1_subset_1(k2_pre_topc(esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59])])).

fof(c_0_67,plain,(
    ! [X39,X40,X41,X42] :
      ( ( ~ v3_pre_topc(X42,X40)
        | k1_tops_1(X40,X42) = X42
        | ~ m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X40)))
        | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X39)))
        | ~ l1_pre_topc(X40)
        | ~ v2_pre_topc(X39)
        | ~ l1_pre_topc(X39) )
      & ( k1_tops_1(X39,X41) != X41
        | v3_pre_topc(X41,X39)
        | ~ m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X40)))
        | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X39)))
        | ~ l1_pre_topc(X40)
        | ~ v2_pre_topc(X39)
        | ~ l1_pre_topc(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_tops_1])])])])).

cnf(c_0_68,plain,
    ( X3 = k1_setfam_1(k2_tarski(X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_60,c_0_17])).

cnf(c_0_69,plain,
    ( r2_hidden(X1,X4)
    | r2_hidden(X1,X3)
    | X4 != k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3)))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_61,c_0_19])).

cnf(c_0_70,plain,
    ( X1 = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X2)))
    | ~ r2_hidden(esk2_3(X2,X2,X1),k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_35]),c_0_38])).

cnf(c_0_71,negated_conjecture,
    ( k5_xboole_0(esk4_0,k1_setfam_1(k2_tarski(esk4_0,X1))) = k7_subset_1(u1_struct_0(esk3_0),esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_58])).

cnf(c_0_72,plain,
    ( k1_setfam_1(k2_tarski(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1))))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_32])).

cnf(c_0_73,negated_conjecture,
    ( k5_xboole_0(k2_pre_topc(esk3_0,esk4_0),k1_setfam_1(k2_tarski(k2_pre_topc(esk3_0,esk4_0),X1))) = k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_66])).

cnf(c_0_74,plain,
    ( k1_tops_1(X2,X1) = X1
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_75,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_76,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X1
    | r2_hidden(esk1_3(X1,X2,X1),X1) ),
    inference(ef,[status(thm)],[c_0_68])).

cnf(c_0_77,plain,
    ( r2_hidden(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3))))
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_69])).

cnf(c_0_78,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X2
    | r2_hidden(esk1_3(X1,X2,X2),X2) ),
    inference(ef,[status(thm)],[c_0_29])).

cnf(c_0_79,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X1))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_70,c_0_53])).

cnf(c_0_80,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk4_0,X1)) = k7_subset_1(u1_struct_0(esk3_0),esk4_0,k7_subset_1(u1_struct_0(esk3_0),esk4_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_71]),c_0_71])).

cnf(c_0_81,negated_conjecture,
    ( k1_setfam_1(k2_tarski(X1,k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),X1))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_82,negated_conjecture,
    ( k1_tops_1(X1,X2) = X2
    | ~ v3_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_58]),c_0_75]),c_0_59])])).

fof(c_0_83,plain,(
    ! [X43,X44] :
      ( ~ l1_pre_topc(X43)
      | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43)))
      | k1_tops_1(X43,X44) = k7_subset_1(u1_struct_0(X43),X44,k2_tops_1(X43,X44)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_tops_1])])])).

cnf(c_0_84,plain,
    ( X3 = k3_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_85,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X1
    | ~ r2_hidden(esk1_3(X1,X2,X1),k5_xboole_0(X3,k1_setfam_1(k2_tarski(X3,X1)))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_76])).

cnf(c_0_86,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X2
    | r2_hidden(esk1_3(X1,X2,X2),k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3))))
    | r2_hidden(esk1_3(X1,X2,X2),X3) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_87,plain,
    ( k1_setfam_1(k2_tarski(X1,X1)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_79]),c_0_31])).

cnf(c_0_88,negated_conjecture,
    ( k5_xboole_0(esk4_0,k7_subset_1(u1_struct_0(esk3_0),esk4_0,k7_subset_1(u1_struct_0(esk3_0),esk4_0,X1))) = k7_subset_1(u1_struct_0(esk3_0),esk4_0,X1) ),
    inference(rw,[status(thm)],[c_0_71,c_0_80])).

cnf(c_0_89,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk3_0),esk4_0,k7_subset_1(u1_struct_0(esk3_0),esk4_0,k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_90,negated_conjecture,
    ( k5_xboole_0(esk4_0,k1_xboole_0) = k7_subset_1(u1_struct_0(esk3_0),esk4_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_31])).

cnf(c_0_91,negated_conjecture,
    ( k1_tops_1(esk3_0,esk4_0) = esk4_0
    | ~ v3_pre_topc(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_58]),c_0_59])])).

cnf(c_0_92,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk3_0)
    | k2_tops_1(esk3_0,esk4_0) = k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_93,plain,
    ( k1_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_94,plain,
    ( X3 = k1_setfam_1(k2_tarski(X1,X2))
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_84,c_0_17])).

cnf(c_0_95,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1
    | r2_hidden(esk1_3(X1,X1,X1),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_87])).

fof(c_0_96,plain,(
    ! [X37,X38] :
      ( ~ l1_pre_topc(X37)
      | ~ m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X37)))
      | k2_tops_1(X37,X38) = k7_subset_1(u1_struct_0(X37),k2_pre_topc(X37,X38),k1_tops_1(X37,X38)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l78_tops_1])])])).

cnf(c_0_97,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk3_0),esk4_0,k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0)) = k7_subset_1(u1_struct_0(esk3_0),esk4_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_90])).

cnf(c_0_98,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0) = k2_tops_1(esk3_0,esk4_0)
    | k1_tops_1(esk3_0,esk4_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_99,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk3_0),esk4_0,k2_tops_1(esk3_0,esk4_0)) = k1_tops_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_58]),c_0_59])])).

cnf(c_0_100,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_87])]),c_0_95])).

cnf(c_0_101,plain,
    ( k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_96])).

cnf(c_0_102,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk3_0),esk4_0,k1_xboole_0) = k1_tops_1(esk3_0,esk4_0)
    | k1_tops_1(esk3_0,esk4_0) = esk4_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_99])).

cnf(c_0_103,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk3_0),esk4_0,k1_xboole_0) = esk4_0 ),
    inference(rw,[status(thm)],[c_0_90,c_0_100])).

cnf(c_0_104,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),k1_tops_1(esk3_0,esk4_0)) = k2_tops_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_58]),c_0_59])])).

cnf(c_0_105,negated_conjecture,
    ( k1_tops_1(esk3_0,esk4_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_102,c_0_103])).

cnf(c_0_106,negated_conjecture,
    ( ~ v3_pre_topc(esk4_0,esk3_0)
    | k2_tops_1(esk3_0,esk4_0) != k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_107,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0) = k2_tops_1(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_104,c_0_105])).

cnf(c_0_108,plain,
    ( v3_pre_topc(X2,X1)
    | k1_tops_1(X1,X2) != X2
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X4)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_109,negated_conjecture,
    ( ~ v3_pre_topc(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_106,c_0_107])])).

cnf(c_0_110,negated_conjecture,
    ( ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_105]),c_0_75]),c_0_59]),c_0_58])]),c_0_109])).

cnf(c_0_111,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_58]),c_0_59])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:13:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.63/0.87  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S2mI
% 0.63/0.87  # and selection function SelectCQArNTNpEqFirst.
% 0.63/0.87  #
% 0.63/0.87  # Preprocessing time       : 0.028 s
% 0.63/0.87  # Presaturation interreduction done
% 0.63/0.87  
% 0.63/0.87  # Proof found!
% 0.63/0.87  # SZS status Theorem
% 0.63/0.87  # SZS output start CNFRefutation
% 0.63/0.87  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.63/0.87  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.63/0.87  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.63/0.87  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.63/0.87  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 0.63/0.87  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.63/0.87  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.63/0.87  fof(t76_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_tops_1)).
% 0.63/0.87  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 0.63/0.87  fof(dt_k2_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 0.63/0.87  fof(t55_tops_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(l1_pre_topc(X2)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>((v3_pre_topc(X4,X2)=>k1_tops_1(X2,X4)=X4)&(k1_tops_1(X1,X3)=X3=>v3_pre_topc(X3,X1))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_tops_1)).
% 0.63/0.87  fof(t74_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k1_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 0.63/0.87  fof(l78_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 0.63/0.87  fof(c_0_13, plain, ![X25, X26]:k4_xboole_0(X25,X26)=k5_xboole_0(X25,k3_xboole_0(X25,X26)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.63/0.87  fof(c_0_14, plain, ![X33, X34]:k1_setfam_1(k2_tarski(X33,X34))=k3_xboole_0(X33,X34), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.63/0.87  fof(c_0_15, plain, ![X16, X17, X18, X19, X20, X21, X22, X23]:((((r2_hidden(X19,X16)|~r2_hidden(X19,X18)|X18!=k4_xboole_0(X16,X17))&(~r2_hidden(X19,X17)|~r2_hidden(X19,X18)|X18!=k4_xboole_0(X16,X17)))&(~r2_hidden(X20,X16)|r2_hidden(X20,X17)|r2_hidden(X20,X18)|X18!=k4_xboole_0(X16,X17)))&((~r2_hidden(esk2_3(X21,X22,X23),X23)|(~r2_hidden(esk2_3(X21,X22,X23),X21)|r2_hidden(esk2_3(X21,X22,X23),X22))|X23=k4_xboole_0(X21,X22))&((r2_hidden(esk2_3(X21,X22,X23),X21)|r2_hidden(esk2_3(X21,X22,X23),X23)|X23=k4_xboole_0(X21,X22))&(~r2_hidden(esk2_3(X21,X22,X23),X22)|r2_hidden(esk2_3(X21,X22,X23),X23)|X23=k4_xboole_0(X21,X22))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.63/0.87  cnf(c_0_16, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.63/0.87  cnf(c_0_17, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.63/0.87  cnf(c_0_18, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.63/0.87  cnf(c_0_19, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 0.63/0.87  fof(c_0_20, plain, ![X7, X8, X9, X10, X11, X12, X13, X14]:((((r2_hidden(X10,X7)|~r2_hidden(X10,X9)|X9!=k3_xboole_0(X7,X8))&(r2_hidden(X10,X8)|~r2_hidden(X10,X9)|X9!=k3_xboole_0(X7,X8)))&(~r2_hidden(X11,X7)|~r2_hidden(X11,X8)|r2_hidden(X11,X9)|X9!=k3_xboole_0(X7,X8)))&((~r2_hidden(esk1_3(X12,X13,X14),X14)|(~r2_hidden(esk1_3(X12,X13,X14),X12)|~r2_hidden(esk1_3(X12,X13,X14),X13))|X14=k3_xboole_0(X12,X13))&((r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k3_xboole_0(X12,X13))&(r2_hidden(esk1_3(X12,X13,X14),X13)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k3_xboole_0(X12,X13))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.63/0.87  fof(c_0_21, plain, ![X27]:k3_xboole_0(X27,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.63/0.87  fof(c_0_22, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.63/0.87  cnf(c_0_23, plain, (X3!=k5_xboole_0(X4,k1_setfam_1(k2_tarski(X4,X2)))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 0.63/0.87  cnf(c_0_24, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.63/0.87  fof(c_0_25, plain, ![X28, X29]:k4_xboole_0(X28,k4_xboole_0(X28,X29))=k3_xboole_0(X28,X29), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.63/0.87  cnf(c_0_26, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.63/0.87  cnf(c_0_27, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.63/0.87  cnf(c_0_28, plain, (~r2_hidden(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3))))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_23])).
% 0.63/0.87  cnf(c_0_29, plain, (X3=k1_setfam_1(k2_tarski(X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X2)), inference(rw,[status(thm)],[c_0_24, c_0_17])).
% 0.63/0.87  cnf(c_0_30, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.63/0.87  cnf(c_0_31, plain, (k1_setfam_1(k2_tarski(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_26, c_0_17])).
% 0.63/0.87  cnf(c_0_32, plain, (k1_setfam_1(k2_tarski(X1,X2))=k1_setfam_1(k2_tarski(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_17]), c_0_17])).
% 0.63/0.87  cnf(c_0_33, plain, (X1=k1_setfam_1(k2_tarski(X2,X3))|r2_hidden(esk1_3(X2,X3,X1),X1)|~r2_hidden(esk1_3(X2,X3,X1),k5_xboole_0(X4,k1_setfam_1(k2_tarski(X4,X3))))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.63/0.87  cnf(c_0_34, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))))))=k1_setfam_1(k2_tarski(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_17]), c_0_19]), c_0_19])).
% 0.63/0.87  cnf(c_0_35, plain, (k1_setfam_1(k2_tarski(k1_xboole_0,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.63/0.87  cnf(c_0_36, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.63/0.87  cnf(c_0_37, plain, (X1=k1_xboole_0|r2_hidden(esk1_3(X2,k1_xboole_0,X1),X1)|~r2_hidden(esk1_3(X2,k1_xboole_0,X1),k5_xboole_0(X3,k1_xboole_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_31]), c_0_31])).
% 0.63/0.87  cnf(c_0_38, plain, (k5_xboole_0(k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_35])).
% 0.63/0.87  cnf(c_0_39, plain, (r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.63/0.87  cnf(c_0_40, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.63/0.87  cnf(c_0_41, plain, (r2_hidden(X1,X2)|X3!=k1_setfam_1(k2_tarski(X4,X2))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_36, c_0_17])).
% 0.63/0.87  cnf(c_0_42, plain, (X1=k1_xboole_0|r2_hidden(esk1_3(X2,k1_xboole_0,X1),X1)|~r2_hidden(esk1_3(X2,k1_xboole_0,X1),k1_xboole_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.63/0.87  cnf(c_0_43, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.63/0.87  fof(c_0_44, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2))))), inference(assume_negation,[status(cth)],[t76_tops_1])).
% 0.63/0.87  cnf(c_0_45, plain, (X3=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))|r2_hidden(esk2_3(X1,X2,X3),X3)|~r2_hidden(esk2_3(X1,X2,X3),X2)), inference(rw,[status(thm)],[c_0_39, c_0_19])).
% 0.63/0.87  cnf(c_0_46, plain, (X3=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))|r2_hidden(esk2_3(X1,X2,X3),X3)|r2_hidden(esk2_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_40, c_0_19])).
% 0.63/0.87  fof(c_0_47, plain, ![X30, X31, X32]:(~m1_subset_1(X31,k1_zfmisc_1(X30))|k7_subset_1(X30,X31,X32)=k4_xboole_0(X31,X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 0.63/0.87  cnf(c_0_48, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_setfam_1(k2_tarski(X3,X2)))), inference(er,[status(thm)],[c_0_41])).
% 0.63/0.87  cnf(c_0_49, plain, (X1=k1_xboole_0|r2_hidden(esk1_3(X2,k1_xboole_0,X1),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_29]), c_0_31])])).
% 0.63/0.87  cnf(c_0_50, plain, (r2_hidden(X1,X2)|X3!=k1_setfam_1(k2_tarski(X2,X4))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_43, c_0_17])).
% 0.63/0.87  fof(c_0_51, plain, ![X35, X36]:(~l1_pre_topc(X35)|~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))|m1_subset_1(k2_pre_topc(X35,X36),k1_zfmisc_1(u1_struct_0(X35)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).
% 0.63/0.87  fof(c_0_52, negated_conjecture, ((v2_pre_topc(esk3_0)&l1_pre_topc(esk3_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&((~v3_pre_topc(esk4_0,esk3_0)|k2_tops_1(esk3_0,esk4_0)!=k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0))&(v3_pre_topc(esk4_0,esk3_0)|k2_tops_1(esk3_0,esk4_0)=k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_44])])])).
% 0.63/0.87  cnf(c_0_53, plain, (X1=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X2)))|r2_hidden(esk2_3(X2,X2,X1),X1)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.63/0.87  cnf(c_0_54, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.63/0.87  cnf(c_0_55, plain, (k1_setfam_1(k2_tarski(X1,X2))=k1_xboole_0|r2_hidden(esk1_3(X3,k1_xboole_0,k1_setfam_1(k2_tarski(X1,X2))),X2)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.63/0.87  cnf(c_0_56, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_setfam_1(k2_tarski(X2,X3)))), inference(er,[status(thm)],[c_0_50])).
% 0.63/0.87  cnf(c_0_57, plain, (m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.63/0.87  cnf(c_0_58, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.63/0.87  cnf(c_0_59, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.63/0.87  cnf(c_0_60, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.63/0.87  cnf(c_0_61, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X4!=k4_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.63/0.87  cnf(c_0_62, plain, (X1=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X2)))|~r2_hidden(esk2_3(X2,X2,X1),k5_xboole_0(X3,k1_setfam_1(k2_tarski(X3,X1))))), inference(spm,[status(thm)],[c_0_28, c_0_53])).
% 0.63/0.87  cnf(c_0_63, plain, (k7_subset_1(X2,X1,X3)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_54, c_0_19])).
% 0.63/0.87  cnf(c_0_64, plain, (k1_setfam_1(k2_tarski(X1,X2))=k1_xboole_0|~r2_hidden(esk1_3(X3,k1_xboole_0,k1_setfam_1(k2_tarski(X1,X2))),k5_xboole_0(X4,k1_setfam_1(k2_tarski(X4,X2))))), inference(spm,[status(thm)],[c_0_28, c_0_55])).
% 0.63/0.87  cnf(c_0_65, plain, (k1_setfam_1(k2_tarski(X1,X2))=k1_xboole_0|r2_hidden(esk1_3(X3,k1_xboole_0,k1_setfam_1(k2_tarski(X1,X2))),X1)), inference(spm,[status(thm)],[c_0_56, c_0_49])).
% 0.63/0.87  cnf(c_0_66, negated_conjecture, (m1_subset_1(k2_pre_topc(esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59])])).
% 0.63/0.87  fof(c_0_67, plain, ![X39, X40, X41, X42]:((~v3_pre_topc(X42,X40)|k1_tops_1(X40,X42)=X42|~m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X40)))|~m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X39)))|~l1_pre_topc(X40)|(~v2_pre_topc(X39)|~l1_pre_topc(X39)))&(k1_tops_1(X39,X41)!=X41|v3_pre_topc(X41,X39)|~m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X40)))|~m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X39)))|~l1_pre_topc(X40)|(~v2_pre_topc(X39)|~l1_pre_topc(X39)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_tops_1])])])])).
% 0.63/0.87  cnf(c_0_68, plain, (X3=k1_setfam_1(k2_tarski(X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_60, c_0_17])).
% 0.63/0.87  cnf(c_0_69, plain, (r2_hidden(X1,X4)|r2_hidden(X1,X3)|X4!=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3)))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_61, c_0_19])).
% 0.63/0.87  cnf(c_0_70, plain, (X1=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X2)))|~r2_hidden(esk2_3(X2,X2,X1),k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_35]), c_0_38])).
% 0.63/0.87  cnf(c_0_71, negated_conjecture, (k5_xboole_0(esk4_0,k1_setfam_1(k2_tarski(esk4_0,X1)))=k7_subset_1(u1_struct_0(esk3_0),esk4_0,X1)), inference(spm,[status(thm)],[c_0_63, c_0_58])).
% 0.63/0.87  cnf(c_0_72, plain, (k1_setfam_1(k2_tarski(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_32])).
% 0.63/0.87  cnf(c_0_73, negated_conjecture, (k5_xboole_0(k2_pre_topc(esk3_0,esk4_0),k1_setfam_1(k2_tarski(k2_pre_topc(esk3_0,esk4_0),X1)))=k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),X1)), inference(spm,[status(thm)],[c_0_63, c_0_66])).
% 0.63/0.87  cnf(c_0_74, plain, (k1_tops_1(X2,X1)=X1|~v3_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))|~l1_pre_topc(X2)|~v2_pre_topc(X4)|~l1_pre_topc(X4)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.63/0.87  cnf(c_0_75, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.63/0.87  cnf(c_0_76, plain, (k1_setfam_1(k2_tarski(X1,X2))=X1|r2_hidden(esk1_3(X1,X2,X1),X1)), inference(ef,[status(thm)],[c_0_68])).
% 0.63/0.87  cnf(c_0_77, plain, (r2_hidden(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3))))|r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_69])).
% 0.63/0.87  cnf(c_0_78, plain, (k1_setfam_1(k2_tarski(X1,X2))=X2|r2_hidden(esk1_3(X1,X2,X2),X2)), inference(ef,[status(thm)],[c_0_29])).
% 0.63/0.87  cnf(c_0_79, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X1)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_70, c_0_53])).
% 0.63/0.87  cnf(c_0_80, negated_conjecture, (k1_setfam_1(k2_tarski(esk4_0,X1))=k7_subset_1(u1_struct_0(esk3_0),esk4_0,k7_subset_1(u1_struct_0(esk3_0),esk4_0,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_71]), c_0_71])).
% 0.63/0.87  cnf(c_0_81, negated_conjecture, (k1_setfam_1(k2_tarski(X1,k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),X1)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.63/0.87  cnf(c_0_82, negated_conjecture, (k1_tops_1(X1,X2)=X2|~v3_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_58]), c_0_75]), c_0_59])])).
% 0.63/0.87  fof(c_0_83, plain, ![X43, X44]:(~l1_pre_topc(X43)|(~m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43)))|k1_tops_1(X43,X44)=k7_subset_1(u1_struct_0(X43),X44,k2_tops_1(X43,X44)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_tops_1])])])).
% 0.63/0.87  cnf(c_0_84, plain, (X3=k3_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.63/0.87  cnf(c_0_85, plain, (k1_setfam_1(k2_tarski(X1,X2))=X1|~r2_hidden(esk1_3(X1,X2,X1),k5_xboole_0(X3,k1_setfam_1(k2_tarski(X3,X1))))), inference(spm,[status(thm)],[c_0_28, c_0_76])).
% 0.63/0.87  cnf(c_0_86, plain, (k1_setfam_1(k2_tarski(X1,X2))=X2|r2_hidden(esk1_3(X1,X2,X2),k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3))))|r2_hidden(esk1_3(X1,X2,X2),X3)), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 0.63/0.87  cnf(c_0_87, plain, (k1_setfam_1(k2_tarski(X1,X1))=k5_xboole_0(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_79]), c_0_31])).
% 0.63/0.87  cnf(c_0_88, negated_conjecture, (k5_xboole_0(esk4_0,k7_subset_1(u1_struct_0(esk3_0),esk4_0,k7_subset_1(u1_struct_0(esk3_0),esk4_0,X1)))=k7_subset_1(u1_struct_0(esk3_0),esk4_0,X1)), inference(rw,[status(thm)],[c_0_71, c_0_80])).
% 0.63/0.87  cnf(c_0_89, negated_conjecture, (k7_subset_1(u1_struct_0(esk3_0),esk4_0,k7_subset_1(u1_struct_0(esk3_0),esk4_0,k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 0.63/0.87  cnf(c_0_90, negated_conjecture, (k5_xboole_0(esk4_0,k1_xboole_0)=k7_subset_1(u1_struct_0(esk3_0),esk4_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_71, c_0_31])).
% 0.63/0.87  cnf(c_0_91, negated_conjecture, (k1_tops_1(esk3_0,esk4_0)=esk4_0|~v3_pre_topc(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_58]), c_0_59])])).
% 0.63/0.87  cnf(c_0_92, negated_conjecture, (v3_pre_topc(esk4_0,esk3_0)|k2_tops_1(esk3_0,esk4_0)=k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.63/0.87  cnf(c_0_93, plain, (k1_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_83])).
% 0.63/0.87  cnf(c_0_94, plain, (X3=k1_setfam_1(k2_tarski(X1,X2))|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X2)|~r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_84, c_0_17])).
% 0.63/0.87  cnf(c_0_95, plain, (k5_xboole_0(X1,k1_xboole_0)=X1|r2_hidden(esk1_3(X1,X1,X1),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_87])).
% 0.63/0.87  fof(c_0_96, plain, ![X37, X38]:(~l1_pre_topc(X37)|(~m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X37)))|k2_tops_1(X37,X38)=k7_subset_1(u1_struct_0(X37),k2_pre_topc(X37,X38),k1_tops_1(X37,X38)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l78_tops_1])])])).
% 0.63/0.87  cnf(c_0_97, negated_conjecture, (k7_subset_1(u1_struct_0(esk3_0),esk4_0,k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0))=k7_subset_1(u1_struct_0(esk3_0),esk4_0,k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_90])).
% 0.63/0.87  cnf(c_0_98, negated_conjecture, (k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0)=k2_tops_1(esk3_0,esk4_0)|k1_tops_1(esk3_0,esk4_0)=esk4_0), inference(spm,[status(thm)],[c_0_91, c_0_92])).
% 0.63/0.87  cnf(c_0_99, negated_conjecture, (k7_subset_1(u1_struct_0(esk3_0),esk4_0,k2_tops_1(esk3_0,esk4_0))=k1_tops_1(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_58]), c_0_59])])).
% 0.63/0.87  cnf(c_0_100, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_87])]), c_0_95])).
% 0.63/0.87  cnf(c_0_101, plain, (k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_96])).
% 0.63/0.87  cnf(c_0_102, negated_conjecture, (k7_subset_1(u1_struct_0(esk3_0),esk4_0,k1_xboole_0)=k1_tops_1(esk3_0,esk4_0)|k1_tops_1(esk3_0,esk4_0)=esk4_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_98]), c_0_99])).
% 0.63/0.87  cnf(c_0_103, negated_conjecture, (k7_subset_1(u1_struct_0(esk3_0),esk4_0,k1_xboole_0)=esk4_0), inference(rw,[status(thm)],[c_0_90, c_0_100])).
% 0.63/0.87  cnf(c_0_104, negated_conjecture, (k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),k1_tops_1(esk3_0,esk4_0))=k2_tops_1(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_58]), c_0_59])])).
% 0.63/0.87  cnf(c_0_105, negated_conjecture, (k1_tops_1(esk3_0,esk4_0)=esk4_0), inference(spm,[status(thm)],[c_0_102, c_0_103])).
% 0.63/0.87  cnf(c_0_106, negated_conjecture, (~v3_pre_topc(esk4_0,esk3_0)|k2_tops_1(esk3_0,esk4_0)!=k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.63/0.87  cnf(c_0_107, negated_conjecture, (k7_subset_1(u1_struct_0(esk3_0),k2_pre_topc(esk3_0,esk4_0),esk4_0)=k2_tops_1(esk3_0,esk4_0)), inference(rw,[status(thm)],[c_0_104, c_0_105])).
% 0.63/0.87  cnf(c_0_108, plain, (v3_pre_topc(X2,X1)|k1_tops_1(X1,X2)!=X2|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X4)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.63/0.87  cnf(c_0_109, negated_conjecture, (~v3_pre_topc(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_106, c_0_107])])).
% 0.63/0.87  cnf(c_0_110, negated_conjecture, (~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_105]), c_0_75]), c_0_59]), c_0_58])]), c_0_109])).
% 0.63/0.87  cnf(c_0_111, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_58]), c_0_59])]), ['proof']).
% 0.63/0.87  # SZS output end CNFRefutation
% 0.63/0.87  # Proof object total steps             : 112
% 0.63/0.87  # Proof object clause steps            : 85
% 0.63/0.87  # Proof object formula steps           : 27
% 0.63/0.87  # Proof object conjectures             : 29
% 0.63/0.87  # Proof object clause conjectures      : 26
% 0.63/0.87  # Proof object formula conjectures     : 3
% 0.63/0.87  # Proof object initial clauses used    : 25
% 0.63/0.87  # Proof object initial formulas used   : 13
% 0.63/0.87  # Proof object generating inferences   : 38
% 0.63/0.87  # Proof object simplifying inferences  : 58
% 0.63/0.87  # Training examples: 0 positive, 0 negative
% 0.63/0.87  # Parsed axioms                        : 13
% 0.63/0.87  # Removed by relevancy pruning/SinE    : 0
% 0.63/0.87  # Initial clauses                      : 28
% 0.63/0.87  # Removed in clause preprocessing      : 2
% 0.63/0.87  # Initial clauses in saturation        : 26
% 0.63/0.87  # Processed clauses                    : 3127
% 0.63/0.87  # ...of these trivial                  : 49
% 0.63/0.87  # ...subsumed                          : 1881
% 0.63/0.87  # ...remaining for further processing  : 1197
% 0.63/0.87  # Other redundant clauses eliminated   : 6
% 0.63/0.87  # Clauses deleted for lack of memory   : 0
% 0.63/0.87  # Backward-subsumed                    : 101
% 0.63/0.87  # Backward-rewritten                   : 571
% 0.63/0.87  # Generated clauses                    : 33147
% 0.63/0.87  # ...of the previous two non-trivial   : 31796
% 0.63/0.87  # Contextual simplify-reflections      : 5
% 0.63/0.87  # Paramodulations                      : 33007
% 0.63/0.87  # Factorizations                       : 134
% 0.63/0.87  # Equation resolutions                 : 6
% 0.63/0.87  # Propositional unsat checks           : 0
% 0.63/0.87  #    Propositional check models        : 0
% 0.63/0.87  #    Propositional check unsatisfiable : 0
% 0.63/0.87  #    Propositional clauses             : 0
% 0.63/0.87  #    Propositional clauses after purity: 0
% 0.63/0.87  #    Propositional unsat core size     : 0
% 0.63/0.87  #    Propositional preprocessing time  : 0.000
% 0.63/0.87  #    Propositional encoding time       : 0.000
% 0.63/0.87  #    Propositional solver time         : 0.000
% 0.63/0.87  #    Success case prop preproc time    : 0.000
% 0.63/0.87  #    Success case prop encoding time   : 0.000
% 0.63/0.87  #    Success case prop solver time     : 0.000
% 0.63/0.87  # Current number of processed clauses  : 493
% 0.63/0.87  #    Positive orientable unit clauses  : 200
% 0.63/0.87  #    Positive unorientable unit clauses: 1
% 0.63/0.87  #    Negative unit clauses             : 1
% 0.63/0.87  #    Non-unit-clauses                  : 291
% 0.63/0.87  # Current number of unprocessed clauses: 28508
% 0.63/0.87  # ...number of literals in the above   : 72411
% 0.63/0.87  # Current number of archived formulas  : 0
% 0.63/0.87  # Current number of archived clauses   : 700
% 0.63/0.87  # Clause-clause subsumption calls (NU) : 90412
% 0.63/0.87  # Rec. Clause-clause subsumption calls : 85387
% 0.63/0.87  # Non-unit clause-clause subsumptions  : 1986
% 0.63/0.87  # Unit Clause-clause subsumption calls : 1397
% 0.63/0.87  # Rewrite failures with RHS unbound    : 0
% 0.63/0.87  # BW rewrite match attempts            : 10465
% 0.63/0.87  # BW rewrite match successes           : 110
% 0.63/0.87  # Condensation attempts                : 0
% 0.63/0.87  # Condensation successes               : 0
% 0.63/0.87  # Termbank termtop insertions          : 1179052
% 0.63/0.87  
% 0.63/0.87  # -------------------------------------------------
% 0.63/0.87  # User time                : 0.507 s
% 0.63/0.87  # System time              : 0.024 s
% 0.63/0.87  # Total time               : 0.531 s
% 0.63/0.87  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------

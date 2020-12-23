%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:11:26 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 563 expanded)
%              Number of clauses        :   48 ( 233 expanded)
%              Number of leaves         :   17 ( 138 expanded)
%              Depth                    :   14
%              Number of atoms          :  195 (1642 expanded)
%              Number of equality atoms :   59 ( 427 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t76_tops_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t48_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(X2,k2_pre_topc(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(idempotence_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(t32_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => k7_subset_1(X1,X2,X3) = k9_subset_1(X1,X2,k3_subset_1(X1,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

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

fof(t74_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k1_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(fc9_tops_1,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => v3_pre_topc(k1_tops_1(X1,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

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

fof(l78_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v3_pre_topc(X2,X1)
            <=> k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t76_tops_1])).

fof(c_0_18,plain,(
    ! [X5,X6] : k4_xboole_0(X5,X6) = k5_xboole_0(X5,k3_xboole_0(X5,X6)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_19,plain,(
    ! [X24,X25] : k1_setfam_1(k2_tarski(X24,X25)) = k3_xboole_0(X24,X25) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_20,plain,(
    ! [X30,X31] :
      ( ~ l1_pre_topc(X30)
      | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
      | r1_tarski(X31,k2_pre_topc(X30,X31)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_pre_topc])])])).

fof(c_0_21,negated_conjecture,
    ( v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & ( ~ v3_pre_topc(esk3_0,esk2_0)
      | k2_tops_1(esk2_0,esk3_0) != k7_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),esk3_0) )
    & ( v3_pre_topc(esk3_0,esk2_0)
      | k2_tops_1(esk2_0,esk3_0) = k7_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

fof(c_0_22,plain,(
    ! [X18,X19,X20] :
      ( ~ m1_subset_1(X19,k1_zfmisc_1(X18))
      | k7_subset_1(X18,X19,X20) = k4_xboole_0(X19,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_25,plain,(
    ! [X7,X8] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(X7))
      | k3_subset_1(X7,X8) = k4_xboole_0(X7,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_26,plain,(
    ! [X26,X27] :
      ( ( ~ m1_subset_1(X26,k1_zfmisc_1(X27))
        | r1_tarski(X26,X27) )
      & ( ~ r1_tarski(X26,X27)
        | m1_subset_1(X26,k1_zfmisc_1(X27)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_27,plain,
    ( r1_tarski(X2,k2_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_30,plain,(
    ! [X28,X29] :
      ( ~ l1_pre_topc(X28)
      | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
      | m1_subset_1(k2_pre_topc(X28,X29),k1_zfmisc_1(u1_struct_0(X28))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

fof(c_0_31,plain,(
    ! [X13,X14,X15] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(X13))
      | k9_subset_1(X13,X14,X14) = X14 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[idempotence_k9_subset_1])])).

fof(c_0_32,plain,(
    ! [X11] : m1_subset_1(esk1_1(X11),X11) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

cnf(c_0_33,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_35,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(esk3_0,k2_pre_topc(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])])).

cnf(c_0_38,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_39,plain,(
    ! [X21,X22,X23] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(X21))
      | ~ m1_subset_1(X23,k1_zfmisc_1(X21))
      | k7_subset_1(X21,X22,X23) = k9_subset_1(X21,X22,k3_subset_1(X21,X23)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_subset_1])])])).

cnf(c_0_40,plain,
    ( k9_subset_1(X2,X3,X3) = X3
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,plain,
    ( m1_subset_1(esk1_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_42,plain,(
    ! [X9,X10] :
      ( ~ m1_subset_1(X10,k1_zfmisc_1(X9))
      | m1_subset_1(k3_subset_1(X9,X10),k1_zfmisc_1(X9)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

fof(c_0_43,plain,(
    ! [X16,X17] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(X16))
      | k3_subset_1(X16,k3_subset_1(X16,X17)) = X17 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

cnf(c_0_44,plain,
    ( k7_subset_1(X2,X1,X3) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_45,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_35,c_0_34])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_pre_topc(esk2_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(k2_pre_topc(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_28]),c_0_29])])).

cnf(c_0_48,plain,
    ( k7_subset_1(X2,X1,X3) = k9_subset_1(X2,X1,k3_subset_1(X2,X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_49,plain,
    ( k9_subset_1(X1,X2,X2) = X2 ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_50,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_51,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_52,negated_conjecture,
    ( k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X1))) = k7_subset_1(u1_struct_0(esk2_0),esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_28])).

cnf(c_0_53,negated_conjecture,
    ( k5_xboole_0(k2_pre_topc(esk2_0,esk3_0),k1_setfam_1(k2_tarski(k2_pre_topc(esk2_0,esk3_0),esk3_0))) = k3_subset_1(k2_pre_topc(esk2_0,esk3_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_54,negated_conjecture,
    ( k5_xboole_0(k2_pre_topc(esk2_0,esk3_0),k1_setfam_1(k2_tarski(k2_pre_topc(esk2_0,esk3_0),X1))) = k7_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_47])).

fof(c_0_55,plain,(
    ! [X40,X41] :
      ( ~ l1_pre_topc(X40)
      | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))
      | k1_tops_1(X40,X41) = k7_subset_1(u1_struct_0(X40),X41,k2_tops_1(X40,X41)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_tops_1])])])).

cnf(c_0_56,plain,
    ( k7_subset_1(X1,k3_subset_1(X1,X2),X2) = k3_subset_1(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(k3_subset_1(k2_pre_topc(esk2_0,esk3_0),esk3_0),k1_zfmisc_1(k2_pre_topc(esk2_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_46])).

cnf(c_0_58,negated_conjecture,
    ( k3_subset_1(k2_pre_topc(esk2_0,esk3_0),k3_subset_1(k2_pre_topc(esk2_0,esk3_0),esk3_0)) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_51,c_0_46])).

cnf(c_0_59,negated_conjecture,
    ( k7_subset_1(k2_pre_topc(esk2_0,esk3_0),esk3_0,X1) = k7_subset_1(u1_struct_0(esk2_0),esk3_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_46]),c_0_52])).

cnf(c_0_60,negated_conjecture,
    ( v3_pre_topc(esk3_0,esk2_0)
    | k2_tops_1(esk2_0,esk3_0) = k7_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_61,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),esk3_0) = k3_subset_1(k2_pre_topc(esk2_0,esk3_0),esk3_0) ),
    inference(rw,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_62,plain,
    ( k1_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

fof(c_0_63,plain,(
    ! [X32,X33] :
      ( ~ v2_pre_topc(X32)
      | ~ l1_pre_topc(X32)
      | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))
      | v3_pre_topc(k1_tops_1(X32,X33),X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).

cnf(c_0_64,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk2_0),esk3_0,k3_subset_1(k2_pre_topc(esk2_0,esk3_0),esk3_0)) = esk3_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58]),c_0_59]),c_0_58])).

cnf(c_0_65,negated_conjecture,
    ( k3_subset_1(k2_pre_topc(esk2_0,esk3_0),esk3_0) = k2_tops_1(esk2_0,esk3_0)
    | v3_pre_topc(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_66,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk2_0),esk3_0,k2_tops_1(esk2_0,esk3_0)) = k1_tops_1(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_28]),c_0_29])])).

fof(c_0_67,plain,(
    ! [X36,X37,X38,X39] :
      ( ( ~ v3_pre_topc(X39,X37)
        | k1_tops_1(X37,X39) = X39
        | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X37)))
        | ~ m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X36)))
        | ~ l1_pre_topc(X37)
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36) )
      & ( k1_tops_1(X36,X38) != X38
        | v3_pre_topc(X38,X36)
        | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X37)))
        | ~ m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X36)))
        | ~ l1_pre_topc(X37)
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_tops_1])])])])).

cnf(c_0_68,plain,
    ( v3_pre_topc(k1_tops_1(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_69,negated_conjecture,
    ( k1_tops_1(esk2_0,esk3_0) = esk3_0
    | v3_pre_topc(esk3_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_66])).

cnf(c_0_70,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_71,plain,
    ( k1_tops_1(X2,X1) = X1
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_72,negated_conjecture,
    ( v3_pre_topc(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70]),c_0_29]),c_0_28])])).

fof(c_0_73,plain,(
    ! [X34,X35] :
      ( ~ l1_pre_topc(X34)
      | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))
      | k2_tops_1(X34,X35) = k7_subset_1(u1_struct_0(X34),k2_pre_topc(X34,X35),k1_tops_1(X34,X35)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l78_tops_1])])])).

cnf(c_0_74,negated_conjecture,
    ( k1_tops_1(esk2_0,esk3_0) = esk3_0
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_29]),c_0_28])])).

cnf(c_0_75,negated_conjecture,
    ( ~ v3_pre_topc(esk3_0,esk2_0)
    | k2_tops_1(esk2_0,esk3_0) != k7_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_76,plain,
    ( k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_77,negated_conjecture,
    ( k1_tops_1(esk2_0,esk3_0) = esk3_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_70]),c_0_29])])).

cnf(c_0_78,negated_conjecture,
    ( k3_subset_1(k2_pre_topc(esk2_0,esk3_0),esk3_0) != k2_tops_1(esk2_0,esk3_0)
    | ~ v3_pre_topc(esk3_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_75,c_0_61])).

cnf(c_0_79,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),k1_tops_1(esk2_0,esk3_0)) = k2_tops_1(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_28]),c_0_29])])).

cnf(c_0_80,negated_conjecture,
    ( k1_tops_1(esk2_0,esk3_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_77,c_0_28])).

cnf(c_0_81,negated_conjecture,
    ( k3_subset_1(k2_pre_topc(esk2_0,esk3_0),esk3_0) != k2_tops_1(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_72])])).

cnf(c_0_82,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_80]),c_0_61]),c_0_81]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:58:34 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.18/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S049N
% 0.18/0.39  # and selection function PSelectComplexPreferEQ.
% 0.18/0.39  #
% 0.18/0.39  # Preprocessing time       : 0.029 s
% 0.18/0.39  # Presaturation interreduction done
% 0.18/0.39  
% 0.18/0.39  # Proof found!
% 0.18/0.39  # SZS status Theorem
% 0.18/0.39  # SZS output start CNFRefutation
% 0.18/0.39  fof(t76_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_tops_1)).
% 0.18/0.39  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.18/0.39  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.18/0.39  fof(t48_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(X2,k2_pre_topc(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_pre_topc)).
% 0.18/0.39  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 0.18/0.39  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 0.18/0.39  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.18/0.39  fof(dt_k2_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 0.18/0.39  fof(idempotence_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k9_subset_1)).
% 0.18/0.39  fof(existence_m1_subset_1, axiom, ![X1]:?[X2]:m1_subset_1(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 0.18/0.39  fof(t32_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k9_subset_1(X1,X2,k3_subset_1(X1,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_subset_1)).
% 0.18/0.39  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 0.18/0.39  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 0.18/0.39  fof(t74_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k1_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 0.18/0.39  fof(fc9_tops_1, axiom, ![X1, X2]:(((v2_pre_topc(X1)&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v3_pre_topc(k1_tops_1(X1,X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 0.18/0.39  fof(t55_tops_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(l1_pre_topc(X2)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>((v3_pre_topc(X4,X2)=>k1_tops_1(X2,X4)=X4)&(k1_tops_1(X1,X3)=X3=>v3_pre_topc(X3,X1))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_tops_1)).
% 0.18/0.39  fof(l78_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 0.18/0.39  fof(c_0_17, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2))))), inference(assume_negation,[status(cth)],[t76_tops_1])).
% 0.18/0.39  fof(c_0_18, plain, ![X5, X6]:k4_xboole_0(X5,X6)=k5_xboole_0(X5,k3_xboole_0(X5,X6)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.18/0.39  fof(c_0_19, plain, ![X24, X25]:k1_setfam_1(k2_tarski(X24,X25))=k3_xboole_0(X24,X25), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.18/0.39  fof(c_0_20, plain, ![X30, X31]:(~l1_pre_topc(X30)|(~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))|r1_tarski(X31,k2_pre_topc(X30,X31)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_pre_topc])])])).
% 0.18/0.39  fof(c_0_21, negated_conjecture, ((v2_pre_topc(esk2_0)&l1_pre_topc(esk2_0))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&((~v3_pre_topc(esk3_0,esk2_0)|k2_tops_1(esk2_0,esk3_0)!=k7_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),esk3_0))&(v3_pre_topc(esk3_0,esk2_0)|k2_tops_1(esk2_0,esk3_0)=k7_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 0.18/0.39  fof(c_0_22, plain, ![X18, X19, X20]:(~m1_subset_1(X19,k1_zfmisc_1(X18))|k7_subset_1(X18,X19,X20)=k4_xboole_0(X19,X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 0.18/0.39  cnf(c_0_23, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.18/0.39  cnf(c_0_24, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.18/0.39  fof(c_0_25, plain, ![X7, X8]:(~m1_subset_1(X8,k1_zfmisc_1(X7))|k3_subset_1(X7,X8)=k4_xboole_0(X7,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.18/0.39  fof(c_0_26, plain, ![X26, X27]:((~m1_subset_1(X26,k1_zfmisc_1(X27))|r1_tarski(X26,X27))&(~r1_tarski(X26,X27)|m1_subset_1(X26,k1_zfmisc_1(X27)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.18/0.39  cnf(c_0_27, plain, (r1_tarski(X2,k2_pre_topc(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.39  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.18/0.39  cnf(c_0_29, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.18/0.39  fof(c_0_30, plain, ![X28, X29]:(~l1_pre_topc(X28)|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))|m1_subset_1(k2_pre_topc(X28,X29),k1_zfmisc_1(u1_struct_0(X28)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).
% 0.18/0.39  fof(c_0_31, plain, ![X13, X14, X15]:(~m1_subset_1(X15,k1_zfmisc_1(X13))|k9_subset_1(X13,X14,X14)=X14), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[idempotence_k9_subset_1])])).
% 0.18/0.39  fof(c_0_32, plain, ![X11]:m1_subset_1(esk1_1(X11),X11), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).
% 0.18/0.39  cnf(c_0_33, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.18/0.39  cnf(c_0_34, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 0.18/0.39  cnf(c_0_35, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.18/0.39  cnf(c_0_36, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.18/0.39  cnf(c_0_37, negated_conjecture, (r1_tarski(esk3_0,k2_pre_topc(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29])])).
% 0.18/0.39  cnf(c_0_38, plain, (m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.18/0.39  fof(c_0_39, plain, ![X21, X22, X23]:(~m1_subset_1(X22,k1_zfmisc_1(X21))|(~m1_subset_1(X23,k1_zfmisc_1(X21))|k7_subset_1(X21,X22,X23)=k9_subset_1(X21,X22,k3_subset_1(X21,X23)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_subset_1])])])).
% 0.18/0.39  cnf(c_0_40, plain, (k9_subset_1(X2,X3,X3)=X3|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.18/0.39  cnf(c_0_41, plain, (m1_subset_1(esk1_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.18/0.39  fof(c_0_42, plain, ![X9, X10]:(~m1_subset_1(X10,k1_zfmisc_1(X9))|m1_subset_1(k3_subset_1(X9,X10),k1_zfmisc_1(X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 0.18/0.39  fof(c_0_43, plain, ![X16, X17]:(~m1_subset_1(X17,k1_zfmisc_1(X16))|k3_subset_1(X16,k3_subset_1(X16,X17))=X17), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 0.18/0.39  cnf(c_0_44, plain, (k7_subset_1(X2,X1,X3)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X3)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_33, c_0_34])).
% 0.18/0.39  cnf(c_0_45, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_35, c_0_34])).
% 0.18/0.39  cnf(c_0_46, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_pre_topc(esk2_0,esk3_0)))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.18/0.39  cnf(c_0_47, negated_conjecture, (m1_subset_1(k2_pre_topc(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_28]), c_0_29])])).
% 0.18/0.39  cnf(c_0_48, plain, (k7_subset_1(X2,X1,X3)=k9_subset_1(X2,X1,k3_subset_1(X2,X3))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.18/0.39  cnf(c_0_49, plain, (k9_subset_1(X1,X2,X2)=X2), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.18/0.39  cnf(c_0_50, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.18/0.39  cnf(c_0_51, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.18/0.39  cnf(c_0_52, negated_conjecture, (k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,X1)))=k7_subset_1(u1_struct_0(esk2_0),esk3_0,X1)), inference(spm,[status(thm)],[c_0_44, c_0_28])).
% 0.18/0.39  cnf(c_0_53, negated_conjecture, (k5_xboole_0(k2_pre_topc(esk2_0,esk3_0),k1_setfam_1(k2_tarski(k2_pre_topc(esk2_0,esk3_0),esk3_0)))=k3_subset_1(k2_pre_topc(esk2_0,esk3_0),esk3_0)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.18/0.39  cnf(c_0_54, negated_conjecture, (k5_xboole_0(k2_pre_topc(esk2_0,esk3_0),k1_setfam_1(k2_tarski(k2_pre_topc(esk2_0,esk3_0),X1)))=k7_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),X1)), inference(spm,[status(thm)],[c_0_44, c_0_47])).
% 0.18/0.39  fof(c_0_55, plain, ![X40, X41]:(~l1_pre_topc(X40)|(~m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))|k1_tops_1(X40,X41)=k7_subset_1(u1_struct_0(X40),X41,k2_tops_1(X40,X41)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_tops_1])])])).
% 0.18/0.39  cnf(c_0_56, plain, (k7_subset_1(X1,k3_subset_1(X1,X2),X2)=k3_subset_1(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50])).
% 0.18/0.39  cnf(c_0_57, negated_conjecture, (m1_subset_1(k3_subset_1(k2_pre_topc(esk2_0,esk3_0),esk3_0),k1_zfmisc_1(k2_pre_topc(esk2_0,esk3_0)))), inference(spm,[status(thm)],[c_0_50, c_0_46])).
% 0.18/0.39  cnf(c_0_58, negated_conjecture, (k3_subset_1(k2_pre_topc(esk2_0,esk3_0),k3_subset_1(k2_pre_topc(esk2_0,esk3_0),esk3_0))=esk3_0), inference(spm,[status(thm)],[c_0_51, c_0_46])).
% 0.18/0.39  cnf(c_0_59, negated_conjecture, (k7_subset_1(k2_pre_topc(esk2_0,esk3_0),esk3_0,X1)=k7_subset_1(u1_struct_0(esk2_0),esk3_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_46]), c_0_52])).
% 0.18/0.39  cnf(c_0_60, negated_conjecture, (v3_pre_topc(esk3_0,esk2_0)|k2_tops_1(esk2_0,esk3_0)=k7_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.18/0.39  cnf(c_0_61, negated_conjecture, (k7_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),esk3_0)=k3_subset_1(k2_pre_topc(esk2_0,esk3_0),esk3_0)), inference(rw,[status(thm)],[c_0_53, c_0_54])).
% 0.18/0.39  cnf(c_0_62, plain, (k1_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.18/0.39  fof(c_0_63, plain, ![X32, X33]:(~v2_pre_topc(X32)|~l1_pre_topc(X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))|v3_pre_topc(k1_tops_1(X32,X33),X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).
% 0.18/0.39  cnf(c_0_64, negated_conjecture, (k7_subset_1(u1_struct_0(esk2_0),esk3_0,k3_subset_1(k2_pre_topc(esk2_0,esk3_0),esk3_0))=esk3_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58]), c_0_59]), c_0_58])).
% 0.18/0.39  cnf(c_0_65, negated_conjecture, (k3_subset_1(k2_pre_topc(esk2_0,esk3_0),esk3_0)=k2_tops_1(esk2_0,esk3_0)|v3_pre_topc(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.18/0.39  cnf(c_0_66, negated_conjecture, (k7_subset_1(u1_struct_0(esk2_0),esk3_0,k2_tops_1(esk2_0,esk3_0))=k1_tops_1(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_28]), c_0_29])])).
% 0.18/0.39  fof(c_0_67, plain, ![X36, X37, X38, X39]:((~v3_pre_topc(X39,X37)|k1_tops_1(X37,X39)=X39|~m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X37)))|~m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X36)))|~l1_pre_topc(X37)|(~v2_pre_topc(X36)|~l1_pre_topc(X36)))&(k1_tops_1(X36,X38)!=X38|v3_pre_topc(X38,X36)|~m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X37)))|~m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X36)))|~l1_pre_topc(X37)|(~v2_pre_topc(X36)|~l1_pre_topc(X36)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_tops_1])])])])).
% 0.18/0.39  cnf(c_0_68, plain, (v3_pre_topc(k1_tops_1(X1,X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.18/0.39  cnf(c_0_69, negated_conjecture, (k1_tops_1(esk2_0,esk3_0)=esk3_0|v3_pre_topc(esk3_0,esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_66])).
% 0.18/0.39  cnf(c_0_70, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.18/0.39  cnf(c_0_71, plain, (k1_tops_1(X2,X1)=X1|~v3_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))|~l1_pre_topc(X2)|~v2_pre_topc(X4)|~l1_pre_topc(X4)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.18/0.39  cnf(c_0_72, negated_conjecture, (v3_pre_topc(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_70]), c_0_29]), c_0_28])])).
% 0.18/0.39  fof(c_0_73, plain, ![X34, X35]:(~l1_pre_topc(X34)|(~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))|k2_tops_1(X34,X35)=k7_subset_1(u1_struct_0(X34),k2_pre_topc(X34,X35),k1_tops_1(X34,X35)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l78_tops_1])])])).
% 0.18/0.39  cnf(c_0_74, negated_conjecture, (k1_tops_1(esk2_0,esk3_0)=esk3_0|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_29]), c_0_28])])).
% 0.18/0.39  cnf(c_0_75, negated_conjecture, (~v3_pre_topc(esk3_0,esk2_0)|k2_tops_1(esk2_0,esk3_0)!=k7_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.18/0.39  cnf(c_0_76, plain, (k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.18/0.39  cnf(c_0_77, negated_conjecture, (k1_tops_1(esk2_0,esk3_0)=esk3_0|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_70]), c_0_29])])).
% 0.18/0.39  cnf(c_0_78, negated_conjecture, (k3_subset_1(k2_pre_topc(esk2_0,esk3_0),esk3_0)!=k2_tops_1(esk2_0,esk3_0)|~v3_pre_topc(esk3_0,esk2_0)), inference(rw,[status(thm)],[c_0_75, c_0_61])).
% 0.18/0.39  cnf(c_0_79, negated_conjecture, (k7_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,esk3_0),k1_tops_1(esk2_0,esk3_0))=k2_tops_1(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_28]), c_0_29])])).
% 0.18/0.39  cnf(c_0_80, negated_conjecture, (k1_tops_1(esk2_0,esk3_0)=esk3_0), inference(spm,[status(thm)],[c_0_77, c_0_28])).
% 0.18/0.39  cnf(c_0_81, negated_conjecture, (k3_subset_1(k2_pre_topc(esk2_0,esk3_0),esk3_0)!=k2_tops_1(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_78, c_0_72])])).
% 0.18/0.39  cnf(c_0_82, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_80]), c_0_61]), c_0_81]), ['proof']).
% 0.18/0.39  # SZS output end CNFRefutation
% 0.18/0.39  # Proof object total steps             : 83
% 0.18/0.39  # Proof object clause steps            : 48
% 0.18/0.39  # Proof object formula steps           : 35
% 0.18/0.39  # Proof object conjectures             : 30
% 0.18/0.39  # Proof object clause conjectures      : 27
% 0.18/0.39  # Proof object formula conjectures     : 3
% 0.18/0.39  # Proof object initial clauses used    : 21
% 0.18/0.39  # Proof object initial formulas used   : 17
% 0.18/0.39  # Proof object generating inferences   : 20
% 0.18/0.39  # Proof object simplifying inferences  : 33
% 0.18/0.39  # Training examples: 0 positive, 0 negative
% 0.18/0.39  # Parsed axioms                        : 17
% 0.18/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.39  # Initial clauses                      : 23
% 0.18/0.39  # Removed in clause preprocessing      : 2
% 0.18/0.39  # Initial clauses in saturation        : 21
% 0.18/0.39  # Processed clauses                    : 232
% 0.18/0.39  # ...of these trivial                  : 9
% 0.18/0.39  # ...subsumed                          : 1
% 0.18/0.39  # ...remaining for further processing  : 222
% 0.18/0.39  # Other redundant clauses eliminated   : 0
% 0.18/0.39  # Clauses deleted for lack of memory   : 0
% 0.18/0.39  # Backward-subsumed                    : 3
% 0.18/0.39  # Backward-rewritten                   : 13
% 0.18/0.39  # Generated clauses                    : 1214
% 0.18/0.39  # ...of the previous two non-trivial   : 1153
% 0.18/0.39  # Contextual simplify-reflections      : 1
% 0.18/0.39  # Paramodulations                      : 1214
% 0.18/0.39  # Factorizations                       : 0
% 0.18/0.39  # Equation resolutions                 : 0
% 0.18/0.39  # Propositional unsat checks           : 0
% 0.18/0.39  #    Propositional check models        : 0
% 0.18/0.39  #    Propositional check unsatisfiable : 0
% 0.18/0.39  #    Propositional clauses             : 0
% 0.18/0.39  #    Propositional clauses after purity: 0
% 0.18/0.39  #    Propositional unsat core size     : 0
% 0.18/0.39  #    Propositional preprocessing time  : 0.000
% 0.18/0.39  #    Propositional encoding time       : 0.000
% 0.18/0.39  #    Propositional solver time         : 0.000
% 0.18/0.39  #    Success case prop preproc time    : 0.000
% 0.18/0.39  #    Success case prop encoding time   : 0.000
% 0.18/0.39  #    Success case prop solver time     : 0.000
% 0.18/0.39  # Current number of processed clauses  : 185
% 0.18/0.39  #    Positive orientable unit clauses  : 147
% 0.18/0.39  #    Positive unorientable unit clauses: 0
% 0.18/0.39  #    Negative unit clauses             : 1
% 0.18/0.39  #    Non-unit-clauses                  : 37
% 0.18/0.39  # Current number of unprocessed clauses: 955
% 0.18/0.39  # ...number of literals in the above   : 1135
% 0.18/0.39  # Current number of archived formulas  : 0
% 0.18/0.39  # Current number of archived clauses   : 39
% 0.18/0.39  # Clause-clause subsumption calls (NU) : 275
% 0.18/0.39  # Rec. Clause-clause subsumption calls : 175
% 0.18/0.39  # Non-unit clause-clause subsumptions  : 2
% 0.18/0.39  # Unit Clause-clause subsumption calls : 25
% 0.18/0.39  # Rewrite failures with RHS unbound    : 0
% 0.18/0.39  # BW rewrite match attempts            : 570
% 0.18/0.39  # BW rewrite match successes           : 6
% 0.18/0.39  # Condensation attempts                : 0
% 0.18/0.39  # Condensation successes               : 0
% 0.18/0.39  # Termbank termtop insertions          : 43643
% 0.18/0.39  
% 0.18/0.39  # -------------------------------------------------
% 0.18/0.39  # User time                : 0.055 s
% 0.18/0.39  # System time              : 0.004 s
% 0.18/0.39  # Total time               : 0.059 s
% 0.18/0.39  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------

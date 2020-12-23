%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:11:58 EST 2020

% Result     : Theorem 3.29s
% Output     : CNFRefutation 3.29s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 549 expanded)
%              Number of clauses        :   55 ( 240 expanded)
%              Number of leaves         :   13 ( 139 expanded)
%              Depth                    :   15
%              Number of atoms          :  240 (1749 expanded)
%              Number of equality atoms :   54 ( 310 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(dt_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(d3_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v1_tops_1(X2,X1)
          <=> k2_pre_topc(X1,X2) = k2_struct_0(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

fof(commutativity_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k9_subset_1(X1,X3,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t82_tops_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( v1_tops_1(X2,X1)
                  & v1_tops_1(X3,X1)
                  & v3_pre_topc(X3,X1) )
               => v1_tops_1(k9_subset_1(u1_struct_0(X1),X2,X3),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_tops_1)).

fof(t41_tops_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( v3_pre_topc(X2,X1)
               => k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) = k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X2,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tops_1)).

fof(c_0_13,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(X4,X5)
      | k3_xboole_0(X4,X5) = X4 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_14,plain,(
    ! [X17,X18] : k1_setfam_1(k2_tarski(X17,X18)) = k3_xboole_0(X17,X18) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_15,plain,(
    ! [X14,X15,X16] :
      ( ~ m1_subset_1(X16,k1_zfmisc_1(X14))
      | k9_subset_1(X14,X15,X16) = k3_xboole_0(X15,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

cnf(c_0_16,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,plain,(
    ! [X11,X12,X13] :
      ( ~ m1_subset_1(X13,k1_zfmisc_1(X11))
      | m1_subset_1(k9_subset_1(X11,X12,X13),k1_zfmisc_1(X11)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).

cnf(c_0_20,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,plain,
    ( k9_subset_1(X2,X3,X1) = k1_setfam_1(k2_tarski(X3,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_18,c_0_17])).

cnf(c_0_22,plain,
    ( m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,plain,
    ( k9_subset_1(X1,X2,X3) = X2
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_24,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(X1,X2)),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_21])).

fof(c_0_25,plain,(
    ! [X10] : m1_subset_1(k2_subset_1(X10),k1_zfmisc_1(X10)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_26,plain,(
    ! [X9] : k2_subset_1(X9) = X9 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_27,plain,(
    ! [X21] :
      ( ~ l1_struct_0(X21)
      | k2_struct_0(X21) = u1_struct_0(X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_28,plain,(
    ! [X22] :
      ( ~ l1_pre_topc(X22)
      | l1_struct_0(X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_29,plain,
    ( k9_subset_1(X1,X2,k1_setfam_1(k2_tarski(X3,X4))) = X2
    | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,k1_setfam_1(k2_tarski(X3,X4))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_30,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_34,plain,(
    ! [X23,X24] :
      ( ( ~ v1_tops_1(X24,X23)
        | k2_pre_topc(X23,X24) = k2_struct_0(X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ l1_pre_topc(X23) )
      & ( k2_pre_topc(X23,X24) != k2_struct_0(X23)
        | v1_tops_1(X24,X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ l1_pre_topc(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tops_1])])])])).

fof(c_0_35,plain,(
    ! [X6,X7,X8] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(X6))
      | k9_subset_1(X6,X7,X8) = k9_subset_1(X6,X8,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k9_subset_1])])).

cnf(c_0_36,plain,
    ( k9_subset_1(X1,X2,X3) = X2
    | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X3)
    | ~ r1_tarski(X3,X4) ),
    inference(spm,[status(thm)],[c_0_29,c_0_20])).

cnf(c_0_37,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_30,c_0_31])).

fof(c_0_38,plain,(
    ! [X19,X20] :
      ( ( ~ m1_subset_1(X19,k1_zfmisc_1(X20))
        | r1_tarski(X19,X20) )
      & ( ~ r1_tarski(X19,X20)
        | m1_subset_1(X19,k1_zfmisc_1(X20)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_39,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( ( v1_tops_1(X2,X1)
                    & v1_tops_1(X3,X1)
                    & v3_pre_topc(X3,X1) )
                 => v1_tops_1(k9_subset_1(u1_struct_0(X1),X2,X3),X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t82_tops_1])).

fof(c_0_40,plain,(
    ! [X25,X26,X27] :
      ( ~ v2_pre_topc(X25)
      | ~ l1_pre_topc(X25)
      | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
      | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X25)))
      | ~ v3_pre_topc(X26,X25)
      | k2_pre_topc(X25,k9_subset_1(u1_struct_0(X25),X26,k2_pre_topc(X25,X27))) = k2_pre_topc(X25,k9_subset_1(u1_struct_0(X25),X26,X27)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t41_tops_1])])])).

cnf(c_0_41,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_42,plain,
    ( k2_pre_topc(X2,X1) = k2_struct_0(X2)
    | ~ v1_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_43,plain,
    ( k9_subset_1(X2,X3,X1) = k9_subset_1(X2,X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,plain,
    ( k9_subset_1(X1,X2,X3) = X2
    | ~ r1_tarski(X2,X3)
    | ~ r1_tarski(X3,X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_46,negated_conjecture,
    ( v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & v1_tops_1(esk2_0,esk1_0)
    & v1_tops_1(esk3_0,esk1_0)
    & v3_pre_topc(esk3_0,esk1_0)
    & ~ v1_tops_1(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_39])])])).

cnf(c_0_47,plain,
    ( v1_tops_1(X2,X1)
    | k2_pre_topc(X1,X2) != k2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_48,plain,
    ( k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) = k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X2,X3))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_49,plain,
    ( k2_pre_topc(X1,X2) = u1_struct_0(X1)
    | ~ v1_tops_1(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_50,plain,
    ( m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_43])).

cnf(c_0_51,plain,
    ( k9_subset_1(X1,X2,X3) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ r1_tarski(X3,X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_53,plain,
    ( v1_tops_1(X1,X2)
    | k2_pre_topc(X2,X1) != u1_struct_0(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(spm,[status(thm)],[c_0_47,c_0_41])).

cnf(c_0_54,plain,
    ( k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X2,X3)) = u1_struct_0(X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_tops_1(k9_subset_1(u1_struct_0(X1),X2,k2_pre_topc(X1,X3)),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50])).

cnf(c_0_55,negated_conjecture,
    ( k9_subset_1(X1,esk3_0,u1_struct_0(esk1_0)) = esk3_0
    | ~ r1_tarski(u1_struct_0(esk1_0),X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_56,plain,
    ( k9_subset_1(X1,X2,k9_subset_1(X1,X3,X4)) = X2
    | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,k9_subset_1(X1,X3,X4)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_22])).

cnf(c_0_57,plain,
    ( k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X2,X3)) = k2_struct_0(X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_tops_1(k9_subset_1(u1_struct_0(X1),X2,k2_pre_topc(X1,X3)),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_48]),c_0_50])).

cnf(c_0_58,plain,
    ( v1_tops_1(k9_subset_1(u1_struct_0(X1),X2,k2_pre_topc(X1,X3)),X1)
    | k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X2,X3)) != u1_struct_0(X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_48]),c_0_50])).

cnf(c_0_59,plain,
    ( k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X2,X3)) = u1_struct_0(X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_tops_1(k9_subset_1(u1_struct_0(X1),X2,u1_struct_0(X1)),X1)
    | ~ v1_tops_1(X3,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_54,c_0_49])).

cnf(c_0_60,negated_conjecture,
    ( k9_subset_1(X1,esk3_0,u1_struct_0(esk1_0)) = esk3_0
    | ~ m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_45])).

cnf(c_0_61,negated_conjecture,
    ( v3_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_62,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_63,negated_conjecture,
    ( v1_tops_1(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_64,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_65,plain,
    ( k9_subset_1(X1,X2,k9_subset_1(X1,X3,X4)) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(k9_subset_1(X1,X3,X4)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_45])).

cnf(c_0_66,plain,
    ( k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X2,X3)) = k2_struct_0(X1)
    | k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X2,X3)) != u1_struct_0(X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_67,negated_conjecture,
    ( k2_pre_topc(esk1_0,k9_subset_1(u1_struct_0(esk1_0),esk3_0,X1)) = u1_struct_0(esk1_0)
    | ~ v1_tops_1(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61]),c_0_62]),c_0_63]),c_0_64]),c_0_52]),c_0_37])])).

cnf(c_0_68,negated_conjecture,
    ( ~ v1_tops_1(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_69,plain,
    ( k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X2,u1_struct_0(X1))) = k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X2,X3))
    | ~ v3_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_tops_1(X3,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_70,negated_conjecture,
    ( k9_subset_1(X1,X2,esk3_0) = X2
    | ~ m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_60])).

cnf(c_0_71,negated_conjecture,
    ( k2_struct_0(esk1_0) = u1_struct_0(esk1_0)
    | ~ v1_tops_1(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_61]),c_0_62]),c_0_64]),c_0_52])])).

cnf(c_0_72,negated_conjecture,
    ( ~ v1_tops_1(k9_subset_1(u1_struct_0(esk1_0),esk3_0,esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_43]),c_0_52])])).

cnf(c_0_73,plain,
    ( k9_subset_1(X1,X2,X3) = k9_subset_1(X4,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_21])).

cnf(c_0_74,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_75,plain,
    ( v1_tops_1(k9_subset_1(u1_struct_0(X1),X2,X3),X1)
    | k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X2,u1_struct_0(X1))) != k2_struct_0(X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_tops_1(X3,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_69]),c_0_50])).

cnf(c_0_76,negated_conjecture,
    ( k2_pre_topc(esk1_0,esk3_0) = u1_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_70]),c_0_63]),c_0_52]),c_0_37]),c_0_37])])).

cnf(c_0_77,negated_conjecture,
    ( k2_struct_0(esk1_0) = u1_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_52]),c_0_63])])).

cnf(c_0_78,negated_conjecture,
    ( ~ v1_tops_1(k9_subset_1(X1,esk3_0,esk2_0),esk1_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_74])])).

cnf(c_0_79,negated_conjecture,
    ( v1_tops_1(k9_subset_1(u1_struct_0(esk1_0),esk3_0,X1),esk1_0)
    | ~ v1_tops_1(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_60]),c_0_76]),c_0_77]),c_0_61]),c_0_62]),c_0_64]),c_0_52]),c_0_37])])).

cnf(c_0_80,negated_conjecture,
    ( v1_tops_1(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_81,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_74]),c_0_80])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.33  % Computer   : n003.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 21:02:12 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  # Version: 2.5pre002
% 0.19/0.34  # No SInE strategy applied
% 0.19/0.34  # Trying AutoSched0 for 299 seconds
% 3.29/3.50  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 3.29/3.50  # and selection function SelectComplexExceptUniqMaxHorn.
% 3.29/3.50  #
% 3.29/3.50  # Preprocessing time       : 0.028 s
% 3.29/3.50  # Presaturation interreduction done
% 3.29/3.50  
% 3.29/3.50  # Proof found!
% 3.29/3.50  # SZS status Theorem
% 3.29/3.50  # SZS output start CNFRefutation
% 3.29/3.50  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.29/3.50  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.29/3.50  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 3.29/3.50  fof(dt_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 3.29/3.50  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.29/3.50  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 3.29/3.50  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.29/3.50  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.29/3.50  fof(d3_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v1_tops_1(X2,X1)<=>k2_pre_topc(X1,X2)=k2_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tops_1)).
% 3.29/3.50  fof(commutativity_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k9_subset_1(X1,X3,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 3.29/3.50  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.29/3.50  fof(t82_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(((v1_tops_1(X2,X1)&v1_tops_1(X3,X1))&v3_pre_topc(X3,X1))=>v1_tops_1(k9_subset_1(u1_struct_0(X1),X2,X3),X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_tops_1)).
% 3.29/3.50  fof(t41_tops_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)=>k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))=k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X2,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_tops_1)).
% 3.29/3.50  fof(c_0_13, plain, ![X4, X5]:(~r1_tarski(X4,X5)|k3_xboole_0(X4,X5)=X4), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 3.29/3.50  fof(c_0_14, plain, ![X17, X18]:k1_setfam_1(k2_tarski(X17,X18))=k3_xboole_0(X17,X18), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 3.29/3.50  fof(c_0_15, plain, ![X14, X15, X16]:(~m1_subset_1(X16,k1_zfmisc_1(X14))|k9_subset_1(X14,X15,X16)=k3_xboole_0(X15,X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 3.29/3.50  cnf(c_0_16, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 3.29/3.50  cnf(c_0_17, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 3.29/3.50  cnf(c_0_18, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 3.29/3.50  fof(c_0_19, plain, ![X11, X12, X13]:(~m1_subset_1(X13,k1_zfmisc_1(X11))|m1_subset_1(k9_subset_1(X11,X12,X13),k1_zfmisc_1(X11))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).
% 3.29/3.50  cnf(c_0_20, plain, (k1_setfam_1(k2_tarski(X1,X2))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 3.29/3.50  cnf(c_0_21, plain, (k9_subset_1(X2,X3,X1)=k1_setfam_1(k2_tarski(X3,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_18, c_0_17])).
% 3.29/3.50  cnf(c_0_22, plain, (m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 3.29/3.50  cnf(c_0_23, plain, (k9_subset_1(X1,X2,X3)=X2|~m1_subset_1(X3,k1_zfmisc_1(X1))|~r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 3.29/3.50  cnf(c_0_24, plain, (m1_subset_1(k1_setfam_1(k2_tarski(X1,X2)),k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_22, c_0_21])).
% 3.29/3.50  fof(c_0_25, plain, ![X10]:m1_subset_1(k2_subset_1(X10),k1_zfmisc_1(X10)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 3.29/3.50  fof(c_0_26, plain, ![X9]:k2_subset_1(X9)=X9, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 3.29/3.50  fof(c_0_27, plain, ![X21]:(~l1_struct_0(X21)|k2_struct_0(X21)=u1_struct_0(X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 3.29/3.50  fof(c_0_28, plain, ![X22]:(~l1_pre_topc(X22)|l1_struct_0(X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 3.29/3.50  cnf(c_0_29, plain, (k9_subset_1(X1,X2,k1_setfam_1(k2_tarski(X3,X4)))=X2|~m1_subset_1(X4,k1_zfmisc_1(X1))|~r1_tarski(X2,k1_setfam_1(k2_tarski(X3,X4)))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 3.29/3.50  cnf(c_0_30, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 3.29/3.50  cnf(c_0_31, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_26])).
% 3.29/3.50  cnf(c_0_32, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 3.29/3.50  cnf(c_0_33, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 3.29/3.50  fof(c_0_34, plain, ![X23, X24]:((~v1_tops_1(X24,X23)|k2_pre_topc(X23,X24)=k2_struct_0(X23)|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))|~l1_pre_topc(X23))&(k2_pre_topc(X23,X24)!=k2_struct_0(X23)|v1_tops_1(X24,X23)|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))|~l1_pre_topc(X23))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tops_1])])])])).
% 3.29/3.50  fof(c_0_35, plain, ![X6, X7, X8]:(~m1_subset_1(X8,k1_zfmisc_1(X6))|k9_subset_1(X6,X7,X8)=k9_subset_1(X6,X8,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k9_subset_1])])).
% 3.29/3.50  cnf(c_0_36, plain, (k9_subset_1(X1,X2,X3)=X2|~m1_subset_1(X4,k1_zfmisc_1(X1))|~r1_tarski(X2,X3)|~r1_tarski(X3,X4)), inference(spm,[status(thm)],[c_0_29, c_0_20])).
% 3.29/3.50  cnf(c_0_37, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_30, c_0_31])).
% 3.29/3.50  fof(c_0_38, plain, ![X19, X20]:((~m1_subset_1(X19,k1_zfmisc_1(X20))|r1_tarski(X19,X20))&(~r1_tarski(X19,X20)|m1_subset_1(X19,k1_zfmisc_1(X20)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 3.29/3.50  fof(c_0_39, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(((v1_tops_1(X2,X1)&v1_tops_1(X3,X1))&v3_pre_topc(X3,X1))=>v1_tops_1(k9_subset_1(u1_struct_0(X1),X2,X3),X1)))))), inference(assume_negation,[status(cth)],[t82_tops_1])).
% 3.29/3.50  fof(c_0_40, plain, ![X25, X26, X27]:(~v2_pre_topc(X25)|~l1_pre_topc(X25)|(~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))|(~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X25)))|(~v3_pre_topc(X26,X25)|k2_pre_topc(X25,k9_subset_1(u1_struct_0(X25),X26,k2_pre_topc(X25,X27)))=k2_pre_topc(X25,k9_subset_1(u1_struct_0(X25),X26,X27)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t41_tops_1])])])).
% 3.29/3.50  cnf(c_0_41, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 3.29/3.50  cnf(c_0_42, plain, (k2_pre_topc(X2,X1)=k2_struct_0(X2)|~v1_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 3.29/3.50  cnf(c_0_43, plain, (k9_subset_1(X2,X3,X1)=k9_subset_1(X2,X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 3.29/3.50  cnf(c_0_44, plain, (k9_subset_1(X1,X2,X3)=X2|~r1_tarski(X2,X3)|~r1_tarski(X3,X1)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 3.29/3.50  cnf(c_0_45, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 3.29/3.50  fof(c_0_46, negated_conjecture, ((v2_pre_topc(esk1_0)&l1_pre_topc(esk1_0))&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(((v1_tops_1(esk2_0,esk1_0)&v1_tops_1(esk3_0,esk1_0))&v3_pre_topc(esk3_0,esk1_0))&~v1_tops_1(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),esk1_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_39])])])).
% 3.29/3.50  cnf(c_0_47, plain, (v1_tops_1(X2,X1)|k2_pre_topc(X1,X2)!=k2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 3.29/3.50  cnf(c_0_48, plain, (k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))=k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X2,X3))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v3_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 3.29/3.50  cnf(c_0_49, plain, (k2_pre_topc(X1,X2)=u1_struct_0(X1)|~v1_tops_1(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 3.29/3.50  cnf(c_0_50, plain, (m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_22, c_0_43])).
% 3.29/3.50  cnf(c_0_51, plain, (k9_subset_1(X1,X2,X3)=X2|~m1_subset_1(X2,k1_zfmisc_1(X3))|~r1_tarski(X3,X1)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 3.29/3.50  cnf(c_0_52, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 3.29/3.50  cnf(c_0_53, plain, (v1_tops_1(X1,X2)|k2_pre_topc(X2,X1)!=u1_struct_0(X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(spm,[status(thm)],[c_0_47, c_0_41])).
% 3.29/3.50  cnf(c_0_54, plain, (k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X2,X3))=u1_struct_0(X1)|~v3_pre_topc(X2,X1)|~v2_pre_topc(X1)|~v1_tops_1(k9_subset_1(u1_struct_0(X1),X2,k2_pre_topc(X1,X3)),X1)|~l1_pre_topc(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50])).
% 3.29/3.50  cnf(c_0_55, negated_conjecture, (k9_subset_1(X1,esk3_0,u1_struct_0(esk1_0))=esk3_0|~r1_tarski(u1_struct_0(esk1_0),X1)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 3.29/3.50  cnf(c_0_56, plain, (k9_subset_1(X1,X2,k9_subset_1(X1,X3,X4))=X2|~m1_subset_1(X4,k1_zfmisc_1(X1))|~r1_tarski(X2,k9_subset_1(X1,X3,X4))), inference(spm,[status(thm)],[c_0_23, c_0_22])).
% 3.29/3.50  cnf(c_0_57, plain, (k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X2,X3))=k2_struct_0(X1)|~v3_pre_topc(X2,X1)|~v2_pre_topc(X1)|~v1_tops_1(k9_subset_1(u1_struct_0(X1),X2,k2_pre_topc(X1,X3)),X1)|~l1_pre_topc(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_48]), c_0_50])).
% 3.29/3.50  cnf(c_0_58, plain, (v1_tops_1(k9_subset_1(u1_struct_0(X1),X2,k2_pre_topc(X1,X3)),X1)|k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X2,X3))!=u1_struct_0(X1)|~v3_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_48]), c_0_50])).
% 3.29/3.50  cnf(c_0_59, plain, (k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X2,X3))=u1_struct_0(X1)|~v3_pre_topc(X2,X1)|~v2_pre_topc(X1)|~v1_tops_1(k9_subset_1(u1_struct_0(X1),X2,u1_struct_0(X1)),X1)|~v1_tops_1(X3,X1)|~l1_pre_topc(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_54, c_0_49])).
% 3.29/3.50  cnf(c_0_60, negated_conjecture, (k9_subset_1(X1,esk3_0,u1_struct_0(esk1_0))=esk3_0|~m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_55, c_0_45])).
% 3.29/3.50  cnf(c_0_61, negated_conjecture, (v3_pre_topc(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 3.29/3.50  cnf(c_0_62, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 3.29/3.50  cnf(c_0_63, negated_conjecture, (v1_tops_1(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 3.29/3.50  cnf(c_0_64, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 3.29/3.50  cnf(c_0_65, plain, (k9_subset_1(X1,X2,k9_subset_1(X1,X3,X4))=X2|~m1_subset_1(X2,k1_zfmisc_1(k9_subset_1(X1,X3,X4)))|~m1_subset_1(X4,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_56, c_0_45])).
% 3.29/3.50  cnf(c_0_66, plain, (k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X2,X3))=k2_struct_0(X1)|k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X2,X3))!=u1_struct_0(X1)|~v3_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 3.29/3.50  cnf(c_0_67, negated_conjecture, (k2_pre_topc(esk1_0,k9_subset_1(u1_struct_0(esk1_0),esk3_0,X1))=u1_struct_0(esk1_0)|~v1_tops_1(X1,esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61]), c_0_62]), c_0_63]), c_0_64]), c_0_52]), c_0_37])])).
% 3.29/3.50  cnf(c_0_68, negated_conjecture, (~v1_tops_1(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),esk1_0)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 3.29/3.50  cnf(c_0_69, plain, (k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X2,u1_struct_0(X1)))=k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X2,X3))|~v3_pre_topc(X2,X1)|~v2_pre_topc(X1)|~v1_tops_1(X3,X1)|~l1_pre_topc(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 3.29/3.50  cnf(c_0_70, negated_conjecture, (k9_subset_1(X1,X2,esk3_0)=X2|~m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(esk3_0))), inference(spm,[status(thm)],[c_0_65, c_0_60])).
% 3.29/3.50  cnf(c_0_71, negated_conjecture, (k2_struct_0(esk1_0)=u1_struct_0(esk1_0)|~v1_tops_1(X1,esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_61]), c_0_62]), c_0_64]), c_0_52])])).
% 3.29/3.50  cnf(c_0_72, negated_conjecture, (~v1_tops_1(k9_subset_1(u1_struct_0(esk1_0),esk3_0,esk2_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_43]), c_0_52])])).
% 3.29/3.50  cnf(c_0_73, plain, (k9_subset_1(X1,X2,X3)=k9_subset_1(X4,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X4))), inference(spm,[status(thm)],[c_0_21, c_0_21])).
% 3.29/3.50  cnf(c_0_74, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 3.29/3.50  cnf(c_0_75, plain, (v1_tops_1(k9_subset_1(u1_struct_0(X1),X2,X3),X1)|k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X2,u1_struct_0(X1)))!=k2_struct_0(X1)|~v3_pre_topc(X2,X1)|~v2_pre_topc(X1)|~v1_tops_1(X3,X1)|~l1_pre_topc(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_69]), c_0_50])).
% 3.29/3.50  cnf(c_0_76, negated_conjecture, (k2_pre_topc(esk1_0,esk3_0)=u1_struct_0(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_70]), c_0_63]), c_0_52]), c_0_37]), c_0_37])])).
% 3.29/3.50  cnf(c_0_77, negated_conjecture, (k2_struct_0(esk1_0)=u1_struct_0(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_52]), c_0_63])])).
% 3.29/3.50  cnf(c_0_78, negated_conjecture, (~v1_tops_1(k9_subset_1(X1,esk3_0,esk2_0),esk1_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_74])])).
% 3.29/3.50  cnf(c_0_79, negated_conjecture, (v1_tops_1(k9_subset_1(u1_struct_0(esk1_0),esk3_0,X1),esk1_0)|~v1_tops_1(X1,esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_60]), c_0_76]), c_0_77]), c_0_61]), c_0_62]), c_0_64]), c_0_52]), c_0_37])])).
% 3.29/3.50  cnf(c_0_80, negated_conjecture, (v1_tops_1(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 3.29/3.50  cnf(c_0_81, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_74]), c_0_80])]), ['proof']).
% 3.29/3.50  # SZS output end CNFRefutation
% 3.29/3.50  # Proof object total steps             : 82
% 3.29/3.50  # Proof object clause steps            : 55
% 3.29/3.50  # Proof object formula steps           : 27
% 3.29/3.50  # Proof object conjectures             : 22
% 3.29/3.50  # Proof object clause conjectures      : 19
% 3.29/3.50  # Proof object formula conjectures     : 3
% 3.29/3.50  # Proof object initial clauses used    : 21
% 3.29/3.50  # Proof object initial formulas used   : 13
% 3.29/3.50  # Proof object generating inferences   : 31
% 3.29/3.50  # Proof object simplifying inferences  : 41
% 3.29/3.50  # Training examples: 0 positive, 0 negative
% 3.29/3.50  # Parsed axioms                        : 13
% 3.29/3.50  # Removed by relevancy pruning/SinE    : 0
% 3.29/3.50  # Initial clauses                      : 22
% 3.29/3.50  # Removed in clause preprocessing      : 2
% 3.29/3.50  # Initial clauses in saturation        : 20
% 3.29/3.50  # Processed clauses                    : 8873
% 3.29/3.50  # ...of these trivial                  : 18
% 3.29/3.50  # ...subsumed                          : 7175
% 3.29/3.50  # ...remaining for further processing  : 1680
% 3.29/3.50  # Other redundant clauses eliminated   : 0
% 3.29/3.50  # Clauses deleted for lack of memory   : 0
% 3.29/3.50  # Backward-subsumed                    : 119
% 3.29/3.50  # Backward-rewritten                   : 144
% 3.29/3.50  # Generated clauses                    : 181710
% 3.29/3.50  # ...of the previous two non-trivial   : 179655
% 3.29/3.50  # Contextual simplify-reflections      : 283
% 3.29/3.50  # Paramodulations                      : 181696
% 3.29/3.50  # Factorizations                       : 0
% 3.29/3.50  # Equation resolutions                 : 14
% 3.29/3.50  # Propositional unsat checks           : 0
% 3.29/3.50  #    Propositional check models        : 0
% 3.29/3.50  #    Propositional check unsatisfiable : 0
% 3.29/3.50  #    Propositional clauses             : 0
% 3.29/3.50  #    Propositional clauses after purity: 0
% 3.29/3.50  #    Propositional unsat core size     : 0
% 3.29/3.50  #    Propositional preprocessing time  : 0.000
% 3.29/3.50  #    Propositional encoding time       : 0.000
% 3.29/3.50  #    Propositional solver time         : 0.000
% 3.29/3.50  #    Success case prop preproc time    : 0.000
% 3.29/3.50  #    Success case prop encoding time   : 0.000
% 3.29/3.50  #    Success case prop solver time     : 0.000
% 3.29/3.50  # Current number of processed clauses  : 1397
% 3.29/3.50  #    Positive orientable unit clauses  : 18
% 3.29/3.50  #    Positive unorientable unit clauses: 0
% 3.29/3.50  #    Negative unit clauses             : 6
% 3.29/3.50  #    Non-unit-clauses                  : 1373
% 3.29/3.50  # Current number of unprocessed clauses: 170219
% 3.29/3.50  # ...number of literals in the above   : 1993973
% 3.29/3.50  # Current number of archived formulas  : 0
% 3.29/3.50  # Current number of archived clauses   : 285
% 3.29/3.50  # Clause-clause subsumption calls (NU) : 1135905
% 3.29/3.50  # Rec. Clause-clause subsumption calls : 235947
% 3.29/3.50  # Non-unit clause-clause subsumptions  : 5829
% 3.29/3.50  # Unit Clause-clause subsumption calls : 1938
% 3.29/3.50  # Rewrite failures with RHS unbound    : 0
% 3.29/3.50  # BW rewrite match attempts            : 31
% 3.29/3.50  # BW rewrite match successes           : 10
% 3.29/3.50  # Condensation attempts                : 0
% 3.29/3.50  # Condensation successes               : 0
% 3.29/3.50  # Termbank termtop insertions          : 9382131
% 3.29/3.51  
% 3.29/3.51  # -------------------------------------------------
% 3.29/3.51  # User time                : 3.068 s
% 3.29/3.51  # System time              : 0.107 s
% 3.29/3.51  # Total time               : 3.175 s
% 3.29/3.51  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:09:14 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 154 expanded)
%              Number of clauses        :   33 (  66 expanded)
%              Number of leaves         :   12 (  39 expanded)
%              Depth                    :   14
%              Number of atoms          :  132 ( 341 expanded)
%              Number of equality atoms :   14 (  64 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t19_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(t51_pre_topc,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => r1_tarski(k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X2,X3)),k9_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k2_pre_topc(X1,X3))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_pre_topc)).

fof(t49_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( r1_tarski(X2,X3)
               => r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_pre_topc)).

fof(dt_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(t108_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k3_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(c_0_12,plain,(
    ! [X20,X21] : k1_setfam_1(k2_tarski(X20,X21)) = k3_xboole_0(X20,X21) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_13,plain,(
    ! [X10,X11] : k1_enumset1(X10,X10,X11) = k2_tarski(X10,X11) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_14,plain,(
    ! [X7,X8,X9] :
      ( ~ r1_tarski(X7,X8)
      | ~ r1_tarski(X7,X9)
      | r1_tarski(X7,k3_xboole_0(X8,X9)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).

cnf(c_0_15,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_17,plain,(
    ! [X17,X18,X19] :
      ( ~ m1_subset_1(X19,k1_zfmisc_1(X17))
      | k9_subset_1(X17,X18,X19) = k3_xboole_0(X18,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => r1_tarski(k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X2,X3)),k9_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k2_pre_topc(X1,X3))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t51_pre_topc])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_22,negated_conjecture,
    ( l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & ~ r1_tarski(k2_pre_topc(esk1_0,k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)),k9_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),k2_pre_topc(esk1_0,esk3_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,k1_setfam_1(k1_enumset1(X2,X2,X3)))
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_24,plain,
    ( k9_subset_1(X2,X3,X1) = k1_setfam_1(k1_enumset1(X3,X3,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_21,c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( ~ r1_tarski(k2_pre_topc(esk1_0,k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)),k9_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),k2_pre_topc(esk1_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,k9_subset_1(X2,X3,X4))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X4)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

fof(c_0_27,plain,(
    ! [X26,X27,X28] :
      ( ~ l1_pre_topc(X26)
      | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
      | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))
      | ~ r1_tarski(X27,X28)
      | r1_tarski(k2_pre_topc(X26,X27),k2_pre_topc(X26,X28)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t49_pre_topc])])])).

cnf(c_0_28,negated_conjecture,
    ( ~ m1_subset_1(k2_pre_topc(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(k2_pre_topc(esk1_0,k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)),k2_pre_topc(esk1_0,esk3_0))
    | ~ r1_tarski(k2_pre_topc(esk1_0,k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)),k2_pre_topc(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_29,plain,
    ( r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_30,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,negated_conjecture,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k2_pre_topc(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(k2_pre_topc(esk1_0,k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)),k2_pre_topc(esk1_0,esk2_0))
    | ~ r1_tarski(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30]),c_0_31])])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_34,plain,(
    ! [X14,X15,X16] :
      ( ~ m1_subset_1(X16,k1_zfmisc_1(X14))
      | m1_subset_1(k9_subset_1(X14,X15,X16),k1_zfmisc_1(X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).

fof(c_0_35,plain,(
    ! [X4,X5,X6] :
      ( ~ r1_tarski(X4,X5)
      | r1_tarski(k3_xboole_0(X4,X6),X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t108_xboole_1])])).

cnf(c_0_36,negated_conjecture,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k2_pre_topc(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),esk3_0)
    | ~ r1_tarski(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_29]),c_0_30]),c_0_33])])).

cnf(c_0_37,plain,
    ( m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_38,plain,(
    ! [X22,X23] :
      ( ( ~ m1_subset_1(X22,k1_zfmisc_1(X23))
        | r1_tarski(X22,X23) )
      & ( ~ r1_tarski(X22,X23)
        | m1_subset_1(X22,k1_zfmisc_1(X23)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_39,plain,
    ( r1_tarski(k3_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_40,negated_conjecture,
    ( ~ m1_subset_1(k2_pre_topc(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),esk3_0)
    | ~ r1_tarski(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_31])])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_42,plain,
    ( r1_tarski(k1_setfam_1(k1_enumset1(X1,X1,X3)),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_39,c_0_20])).

fof(c_0_43,plain,(
    ! [X13] : m1_subset_1(k2_subset_1(X13),k1_zfmisc_1(X13)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_44,plain,(
    ! [X12] : k2_subset_1(X12) = X12 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_45,negated_conjecture,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),k1_zfmisc_1(esk3_0))
    | ~ m1_subset_1(k2_pre_topc(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_46,plain,
    ( r1_tarski(k9_subset_1(X1,X2,X3),X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X4) ),
    inference(spm,[status(thm)],[c_0_42,c_0_24])).

cnf(c_0_47,plain,
    ( m1_subset_1(k1_setfam_1(k1_enumset1(X1,X1,X2)),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_24])).

cnf(c_0_48,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_49,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_50,negated_conjecture,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),k1_zfmisc_1(esk3_0))
    | ~ m1_subset_1(k2_pre_topc(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(esk2_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_31])])).

cnf(c_0_51,plain,
    ( m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_24])).

cnf(c_0_52,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_48,c_0_49])).

fof(c_0_53,plain,(
    ! [X24,X25] :
      ( ~ l1_pre_topc(X24)
      | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
      | m1_subset_1(k2_pre_topc(X24,X25),k1_zfmisc_1(u1_struct_0(X24))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

cnf(c_0_54,negated_conjecture,
    ( ~ m1_subset_1(k2_pre_topc(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(esk2_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52]),c_0_31])])).

cnf(c_0_55,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_56,negated_conjecture,
    ( ~ r1_tarski(esk2_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_30]),c_0_31])])).

cnf(c_0_57,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_41]),c_0_52])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:14:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.36  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.36  #
% 0.13/0.36  # Preprocessing time       : 0.017 s
% 0.13/0.36  # Presaturation interreduction done
% 0.13/0.36  
% 0.13/0.36  # Proof found!
% 0.13/0.36  # SZS status Theorem
% 0.13/0.36  # SZS output start CNFRefutation
% 0.13/0.36  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.13/0.36  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.36  fof(t19_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(X1,k3_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 0.13/0.36  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 0.13/0.36  fof(t51_pre_topc, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X2,X3)),k9_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k2_pre_topc(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_pre_topc)).
% 0.13/0.36  fof(t49_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X2,X3)=>r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_pre_topc)).
% 0.13/0.36  fof(dt_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 0.13/0.36  fof(t108_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(k3_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_xboole_1)).
% 0.13/0.36  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.13/0.36  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.13/0.36  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 0.13/0.36  fof(dt_k2_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 0.13/0.36  fof(c_0_12, plain, ![X20, X21]:k1_setfam_1(k2_tarski(X20,X21))=k3_xboole_0(X20,X21), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.13/0.36  fof(c_0_13, plain, ![X10, X11]:k1_enumset1(X10,X10,X11)=k2_tarski(X10,X11), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.36  fof(c_0_14, plain, ![X7, X8, X9]:(~r1_tarski(X7,X8)|~r1_tarski(X7,X9)|r1_tarski(X7,k3_xboole_0(X8,X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).
% 0.13/0.36  cnf(c_0_15, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.36  cnf(c_0_16, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.36  fof(c_0_17, plain, ![X17, X18, X19]:(~m1_subset_1(X19,k1_zfmisc_1(X17))|k9_subset_1(X17,X18,X19)=k3_xboole_0(X18,X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 0.13/0.36  fof(c_0_18, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X2,X3)),k9_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k2_pre_topc(X1,X3))))))), inference(assume_negation,[status(cth)],[t51_pre_topc])).
% 0.13/0.36  cnf(c_0_19, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.36  cnf(c_0_20, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 0.13/0.36  cnf(c_0_21, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.36  fof(c_0_22, negated_conjecture, (l1_pre_topc(esk1_0)&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&~r1_tarski(k2_pre_topc(esk1_0,k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)),k9_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),k2_pre_topc(esk1_0,esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 0.13/0.36  cnf(c_0_23, plain, (r1_tarski(X1,k1_setfam_1(k1_enumset1(X2,X2,X3)))|~r1_tarski(X1,X3)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 0.13/0.36  cnf(c_0_24, plain, (k9_subset_1(X2,X3,X1)=k1_setfam_1(k1_enumset1(X3,X3,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_21, c_0_20])).
% 0.13/0.36  cnf(c_0_25, negated_conjecture, (~r1_tarski(k2_pre_topc(esk1_0,k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)),k9_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),k2_pre_topc(esk1_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.36  cnf(c_0_26, plain, (r1_tarski(X1,k9_subset_1(X2,X3,X4))|~m1_subset_1(X4,k1_zfmisc_1(X2))|~r1_tarski(X1,X4)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.13/0.36  fof(c_0_27, plain, ![X26, X27, X28]:(~l1_pre_topc(X26)|(~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|(~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))|(~r1_tarski(X27,X28)|r1_tarski(k2_pre_topc(X26,X27),k2_pre_topc(X26,X28)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t49_pre_topc])])])).
% 0.13/0.36  cnf(c_0_28, negated_conjecture, (~m1_subset_1(k2_pre_topc(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(k2_pre_topc(esk1_0,k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)),k2_pre_topc(esk1_0,esk3_0))|~r1_tarski(k2_pre_topc(esk1_0,k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)),k2_pre_topc(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.13/0.36  cnf(c_0_29, plain, (r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.36  cnf(c_0_30, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.36  cnf(c_0_31, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.36  cnf(c_0_32, negated_conjecture, (~m1_subset_1(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(k2_pre_topc(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(k2_pre_topc(esk1_0,k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)),k2_pre_topc(esk1_0,esk2_0))|~r1_tarski(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30]), c_0_31])])).
% 0.13/0.36  cnf(c_0_33, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.36  fof(c_0_34, plain, ![X14, X15, X16]:(~m1_subset_1(X16,k1_zfmisc_1(X14))|m1_subset_1(k9_subset_1(X14,X15,X16),k1_zfmisc_1(X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).
% 0.13/0.36  fof(c_0_35, plain, ![X4, X5, X6]:(~r1_tarski(X4,X5)|r1_tarski(k3_xboole_0(X4,X6),X5)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t108_xboole_1])])).
% 0.13/0.36  cnf(c_0_36, negated_conjecture, (~m1_subset_1(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(k2_pre_topc(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),esk3_0)|~r1_tarski(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_29]), c_0_30]), c_0_33])])).
% 0.13/0.36  cnf(c_0_37, plain, (m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.36  fof(c_0_38, plain, ![X22, X23]:((~m1_subset_1(X22,k1_zfmisc_1(X23))|r1_tarski(X22,X23))&(~r1_tarski(X22,X23)|m1_subset_1(X22,k1_zfmisc_1(X23)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.13/0.36  cnf(c_0_39, plain, (r1_tarski(k3_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.36  cnf(c_0_40, negated_conjecture, (~m1_subset_1(k2_pre_topc(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),esk3_0)|~r1_tarski(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_31])])).
% 0.13/0.36  cnf(c_0_41, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.13/0.36  cnf(c_0_42, plain, (r1_tarski(k1_setfam_1(k1_enumset1(X1,X1,X3)),X2)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_39, c_0_20])).
% 0.13/0.36  fof(c_0_43, plain, ![X13]:m1_subset_1(k2_subset_1(X13),k1_zfmisc_1(X13)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.13/0.36  fof(c_0_44, plain, ![X12]:k2_subset_1(X12)=X12, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.13/0.36  cnf(c_0_45, negated_conjecture, (~m1_subset_1(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),k1_zfmisc_1(esk3_0))|~m1_subset_1(k2_pre_topc(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),esk2_0)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.13/0.36  cnf(c_0_46, plain, (r1_tarski(k9_subset_1(X1,X2,X3),X4)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~r1_tarski(X2,X4)), inference(spm,[status(thm)],[c_0_42, c_0_24])).
% 0.13/0.36  cnf(c_0_47, plain, (m1_subset_1(k1_setfam_1(k1_enumset1(X1,X1,X2)),k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_37, c_0_24])).
% 0.13/0.36  cnf(c_0_48, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.13/0.36  cnf(c_0_49, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.13/0.36  cnf(c_0_50, negated_conjecture, (~m1_subset_1(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),k1_zfmisc_1(esk3_0))|~m1_subset_1(k2_pre_topc(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(esk2_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_31])])).
% 0.13/0.36  cnf(c_0_51, plain, (m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X4))|~m1_subset_1(X3,k1_zfmisc_1(X4))|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_47, c_0_24])).
% 0.13/0.36  cnf(c_0_52, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_48, c_0_49])).
% 0.13/0.36  fof(c_0_53, plain, ![X24, X25]:(~l1_pre_topc(X24)|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))|m1_subset_1(k2_pre_topc(X24,X25),k1_zfmisc_1(u1_struct_0(X24)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).
% 0.13/0.36  cnf(c_0_54, negated_conjecture, (~m1_subset_1(k2_pre_topc(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(esk2_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52]), c_0_31])])).
% 0.13/0.36  cnf(c_0_55, plain, (m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.13/0.36  cnf(c_0_56, negated_conjecture, (~r1_tarski(esk2_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_30]), c_0_31])])).
% 0.13/0.36  cnf(c_0_57, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_41]), c_0_52])]), ['proof']).
% 0.13/0.36  # SZS output end CNFRefutation
% 0.13/0.36  # Proof object total steps             : 58
% 0.13/0.36  # Proof object clause steps            : 33
% 0.13/0.36  # Proof object formula steps           : 25
% 0.13/0.36  # Proof object conjectures             : 16
% 0.13/0.36  # Proof object clause conjectures      : 13
% 0.13/0.36  # Proof object formula conjectures     : 3
% 0.13/0.36  # Proof object initial clauses used    : 15
% 0.13/0.36  # Proof object initial formulas used   : 12
% 0.13/0.36  # Proof object generating inferences   : 13
% 0.13/0.36  # Proof object simplifying inferences  : 23
% 0.13/0.36  # Training examples: 0 positive, 0 negative
% 0.13/0.36  # Parsed axioms                        : 12
% 0.13/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.36  # Initial clauses                      : 16
% 0.13/0.36  # Removed in clause preprocessing      : 3
% 0.13/0.36  # Initial clauses in saturation        : 13
% 0.13/0.36  # Processed clauses                    : 64
% 0.13/0.36  # ...of these trivial                  : 0
% 0.13/0.36  # ...subsumed                          : 9
% 0.13/0.36  # ...remaining for further processing  : 55
% 0.13/0.36  # Other redundant clauses eliminated   : 0
% 0.13/0.36  # Clauses deleted for lack of memory   : 0
% 0.13/0.36  # Backward-subsumed                    : 3
% 0.13/0.36  # Backward-rewritten                   : 0
% 0.13/0.36  # Generated clauses                    : 94
% 0.13/0.36  # ...of the previous two non-trivial   : 92
% 0.13/0.36  # Contextual simplify-reflections      : 0
% 0.13/0.36  # Paramodulations                      : 94
% 0.13/0.36  # Factorizations                       : 0
% 0.13/0.36  # Equation resolutions                 : 0
% 0.13/0.36  # Propositional unsat checks           : 0
% 0.13/0.36  #    Propositional check models        : 0
% 0.13/0.36  #    Propositional check unsatisfiable : 0
% 0.13/0.36  #    Propositional clauses             : 0
% 0.13/0.36  #    Propositional clauses after purity: 0
% 0.13/0.36  #    Propositional unsat core size     : 0
% 0.13/0.36  #    Propositional preprocessing time  : 0.000
% 0.13/0.36  #    Propositional encoding time       : 0.000
% 0.13/0.36  #    Propositional solver time         : 0.000
% 0.13/0.36  #    Success case prop preproc time    : 0.000
% 0.13/0.36  #    Success case prop encoding time   : 0.000
% 0.13/0.36  #    Success case prop solver time     : 0.000
% 0.13/0.36  # Current number of processed clauses  : 39
% 0.13/0.36  #    Positive orientable unit clauses  : 4
% 0.13/0.36  #    Positive unorientable unit clauses: 0
% 0.13/0.36  #    Negative unit clauses             : 4
% 0.13/0.36  #    Non-unit-clauses                  : 31
% 0.13/0.36  # Current number of unprocessed clauses: 54
% 0.13/0.36  # ...number of literals in the above   : 204
% 0.13/0.36  # Current number of archived formulas  : 0
% 0.13/0.36  # Current number of archived clauses   : 19
% 0.13/0.36  # Clause-clause subsumption calls (NU) : 463
% 0.13/0.36  # Rec. Clause-clause subsumption calls : 257
% 0.13/0.36  # Non-unit clause-clause subsumptions  : 12
% 0.13/0.36  # Unit Clause-clause subsumption calls : 21
% 0.13/0.36  # Rewrite failures with RHS unbound    : 0
% 0.13/0.36  # BW rewrite match attempts            : 4
% 0.13/0.36  # BW rewrite match successes           : 0
% 0.13/0.36  # Condensation attempts                : 0
% 0.13/0.36  # Condensation successes               : 0
% 0.13/0.36  # Termbank termtop insertions          : 3153
% 0.13/0.36  
% 0.13/0.36  # -------------------------------------------------
% 0.13/0.36  # User time                : 0.018 s
% 0.13/0.36  # System time              : 0.004 s
% 0.13/0.36  # Total time               : 0.023 s
% 0.13/0.36  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------

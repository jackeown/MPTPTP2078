%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:10:49 EST 2020

% Result     : Theorem 0.42s
% Output     : CNFRefutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 524 expanded)
%              Number of clauses        :   44 ( 203 expanded)
%              Number of leaves         :   11 ( 125 expanded)
%              Depth                    :   11
%              Number of atoms          :  155 (1541 expanded)
%              Number of equality atoms :   21 ( 102 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t49_tops_1,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => r1_tarski(k4_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2),k1_tops_1(X1,X3)),k1_tops_1(X1,k4_subset_1(u1_struct_0(X1),X2,X3))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tops_1)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(t36_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r1_tarski(k3_subset_1(X1,X2),X3)
           => r1_tarski(k3_subset_1(X1,X3),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_subset_1)).

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

fof(dt_k1_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(t48_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( r1_tarski(X2,X3)
               => r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

fof(t41_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => r1_tarski(k3_subset_1(X1,k4_subset_1(X1,X2,X3)),k3_subset_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_subset_1)).

fof(dt_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => r1_tarski(k4_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2),k1_tops_1(X1,X3)),k1_tops_1(X1,k4_subset_1(u1_struct_0(X1),X2,X3))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t49_tops_1])).

fof(c_0_12,plain,(
    ! [X13,X14,X15] :
      ( ~ m1_subset_1(X14,k1_zfmisc_1(X13))
      | ~ m1_subset_1(X15,k1_zfmisc_1(X13))
      | k4_subset_1(X13,X14,X15) = k2_xboole_0(X14,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

fof(c_0_13,negated_conjecture,
    ( l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & ~ r1_tarski(k4_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)),k1_tops_1(esk1_0,k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

fof(c_0_14,plain,(
    ! [X16,X17,X18] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(X16))
      | ~ m1_subset_1(X18,k1_zfmisc_1(X16))
      | ~ r1_tarski(k3_subset_1(X16,X17),X18)
      | r1_tarski(k3_subset_1(X16,X18),X17) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t36_subset_1])])])).

fof(c_0_15,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(X6))
      | m1_subset_1(k3_subset_1(X6,X7),k1_zfmisc_1(X6)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

fof(c_0_16,plain,(
    ! [X11,X12] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(X11))
      | k3_subset_1(X11,k3_subset_1(X11,X12)) = X12 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

cnf(c_0_17,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_19,plain,(
    ! [X24,X25] :
      ( ~ l1_pre_topc(X24)
      | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
      | m1_subset_1(k1_tops_1(X24,X25),k1_zfmisc_1(u1_struct_0(X24))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_1])])).

fof(c_0_20,plain,(
    ! [X26,X27,X28] :
      ( ~ l1_pre_topc(X26)
      | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
      | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))
      | ~ r1_tarski(X27,X28)
      | r1_tarski(k1_tops_1(X26,X27),k1_tops_1(X26,X28)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).

cnf(c_0_21,plain,
    ( r1_tarski(k3_subset_1(X2,X3),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_tarski(k3_subset_1(X2,X1),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_25,plain,(
    ! [X19,X20,X21] :
      ( ~ m1_subset_1(X20,k1_zfmisc_1(X19))
      | ~ m1_subset_1(X21,k1_zfmisc_1(X19))
      | r1_tarski(k3_subset_1(X19,k4_subset_1(X19,X20,X21)),k3_subset_1(X19,X20)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t41_subset_1])])])).

cnf(c_0_26,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),X1,esk3_0) = k2_xboole_0(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

fof(c_0_27,plain,(
    ! [X8,X9,X10] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(X8))
      | ~ m1_subset_1(X10,k1_zfmisc_1(X8))
      | m1_subset_1(k4_subset_1(X8,X9,X10),k1_zfmisc_1(X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_subset_1])])).

fof(c_0_28,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_29,plain,
    ( m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_31,plain,(
    ! [X22,X23] :
      ( ( ~ m1_subset_1(X22,k1_zfmisc_1(X23))
        | r1_tarski(X22,X23) )
      & ( ~ r1_tarski(X22,X23)
        | m1_subset_1(X22,k1_zfmisc_1(X23)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_32,plain,
    ( r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_33,plain,
    ( r1_tarski(k3_subset_1(X1,k3_subset_1(X1,X2)),X3)
    | ~ r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_34,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_35,plain,
    ( r1_tarski(k3_subset_1(X2,k4_subset_1(X2,X1,X3)),k3_subset_1(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0) = k2_xboole_0(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_24])).

cnf(c_0_37,plain,
    ( m1_subset_1(k4_subset_1(X2,X1,X3),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_38,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),X1,esk2_0) = k2_xboole_0(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_17,c_0_24])).

cnf(c_0_39,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(k1_tops_1(esk1_0,X1),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_41,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,X1),k1_tops_1(esk1_0,X2))
    | ~ r1_tarski(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_30])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(esk2_0,X1)
    | ~ r1_tarski(k3_subset_1(u1_struct_0(esk1_0),X1),k3_subset_1(u1_struct_0(esk1_0),esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_24])])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(k3_subset_1(u1_struct_0(esk1_0),k2_xboole_0(esk2_0,esk3_0)),k3_subset_1(u1_struct_0(esk1_0),esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_18]),c_0_24])])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(k2_xboole_0(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_36]),c_0_18]),c_0_24])])).

cnf(c_0_46,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk3_0)) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_18])).

cnf(c_0_47,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),esk3_0,esk2_0) = k2_xboole_0(esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_18]),c_0_39])).

cnf(c_0_48,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),X1,k1_tops_1(esk1_0,X2)) = k2_xboole_0(X1,k1_tops_1(esk1_0,X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_17,c_0_40])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(k1_tops_1(esk1_0,X1),k1_zfmisc_1(k1_tops_1(esk1_0,X2)))
    | ~ r1_tarski(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(esk2_0,k2_xboole_0(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(esk3_0,X1)
    | ~ r1_tarski(k3_subset_1(u1_struct_0(esk1_0),X1),k3_subset_1(u1_struct_0(esk1_0),esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_46]),c_0_18])])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(k3_subset_1(u1_struct_0(esk1_0),k2_xboole_0(esk2_0,esk3_0)),k3_subset_1(u1_struct_0(esk1_0),esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_47]),c_0_24]),c_0_18])])).

cnf(c_0_53,negated_conjecture,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)),k1_tops_1(esk1_0,k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_54,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_55,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,X1),k1_tops_1(esk1_0,X2)) = k2_xboole_0(k1_tops_1(esk1_0,X1),k1_tops_1(esk1_0,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_48,c_0_40])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(k1_tops_1(esk1_0,k2_xboole_0(esk2_0,esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_45]),c_0_24])])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(esk3_0,k2_xboole_0(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_45])])).

cnf(c_0_58,negated_conjecture,
    ( ~ m1_subset_1(k4_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)),k1_zfmisc_1(k1_tops_1(esk1_0,k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_59,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,X1),k1_tops_1(esk1_0,esk3_0)) = k2_xboole_0(k1_tops_1(esk1_0,X1),k1_tops_1(esk1_0,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_18])).

cnf(c_0_60,negated_conjecture,
    ( k4_subset_1(k1_tops_1(esk1_0,k2_xboole_0(esk2_0,esk3_0)),X1,k1_tops_1(esk1_0,esk2_0)) = k2_xboole_0(X1,k1_tops_1(esk1_0,esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_tops_1(esk1_0,k2_xboole_0(esk2_0,esk3_0)))) ),
    inference(spm,[status(thm)],[c_0_17,c_0_56])).

cnf(c_0_61,negated_conjecture,
    ( m1_subset_1(k1_tops_1(esk1_0,esk3_0),k1_zfmisc_1(k1_tops_1(esk1_0,k2_xboole_0(esk2_0,esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_57]),c_0_45]),c_0_18])])).

cnf(c_0_62,negated_conjecture,
    ( ~ m1_subset_1(k4_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)),k1_zfmisc_1(k1_tops_1(esk1_0,k2_xboole_0(esk2_0,esk3_0)))) ),
    inference(rw,[status(thm)],[c_0_58,c_0_36])).

cnf(c_0_63,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)) = k2_xboole_0(k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_24])).

cnf(c_0_64,negated_conjecture,
    ( k4_subset_1(k1_tops_1(esk1_0,k2_xboole_0(esk2_0,esk3_0)),k1_tops_1(esk1_0,esk3_0),k1_tops_1(esk1_0,esk2_0)) = k2_xboole_0(k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_39])).

cnf(c_0_65,negated_conjecture,
    ( ~ m1_subset_1(k2_xboole_0(k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)),k1_zfmisc_1(k1_tops_1(esk1_0,k2_xboole_0(esk2_0,esk3_0)))) ),
    inference(rw,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_66,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_64]),c_0_56]),c_0_61])]),c_0_65]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:13:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.34  # Version: 2.5pre002
% 0.20/0.34  # No SInE strategy applied
% 0.20/0.34  # Trying AutoSched0 for 299 seconds
% 0.42/0.58  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S050I
% 0.42/0.58  # and selection function PSelectNewComplexExceptUniqMaxHorn.
% 0.42/0.58  #
% 0.42/0.58  # Preprocessing time       : 0.027 s
% 0.42/0.58  # Presaturation interreduction done
% 0.42/0.58  
% 0.42/0.58  # Proof found!
% 0.42/0.58  # SZS status Theorem
% 0.42/0.58  # SZS output start CNFRefutation
% 0.42/0.58  fof(t49_tops_1, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k4_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2),k1_tops_1(X1,X3)),k1_tops_1(X1,k4_subset_1(u1_struct_0(X1),X2,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_tops_1)).
% 0.42/0.58  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 0.42/0.58  fof(t36_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_tarski(k3_subset_1(X1,X2),X3)=>r1_tarski(k3_subset_1(X1,X3),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_subset_1)).
% 0.42/0.58  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 0.42/0.58  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 0.42/0.58  fof(dt_k1_tops_1, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 0.42/0.58  fof(t48_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X2,X3)=>r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tops_1)).
% 0.42/0.58  fof(t41_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>r1_tarski(k3_subset_1(X1,k4_subset_1(X1,X2,X3)),k3_subset_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_subset_1)).
% 0.42/0.58  fof(dt_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 0.42/0.58  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.42/0.58  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.42/0.58  fof(c_0_11, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k4_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2),k1_tops_1(X1,X3)),k1_tops_1(X1,k4_subset_1(u1_struct_0(X1),X2,X3))))))), inference(assume_negation,[status(cth)],[t49_tops_1])).
% 0.42/0.58  fof(c_0_12, plain, ![X13, X14, X15]:(~m1_subset_1(X14,k1_zfmisc_1(X13))|~m1_subset_1(X15,k1_zfmisc_1(X13))|k4_subset_1(X13,X14,X15)=k2_xboole_0(X14,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 0.42/0.58  fof(c_0_13, negated_conjecture, (l1_pre_topc(esk1_0)&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&~r1_tarski(k4_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)),k1_tops_1(esk1_0,k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 0.42/0.58  fof(c_0_14, plain, ![X16, X17, X18]:(~m1_subset_1(X17,k1_zfmisc_1(X16))|(~m1_subset_1(X18,k1_zfmisc_1(X16))|(~r1_tarski(k3_subset_1(X16,X17),X18)|r1_tarski(k3_subset_1(X16,X18),X17)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t36_subset_1])])])).
% 0.42/0.58  fof(c_0_15, plain, ![X6, X7]:(~m1_subset_1(X7,k1_zfmisc_1(X6))|m1_subset_1(k3_subset_1(X6,X7),k1_zfmisc_1(X6))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 0.42/0.58  fof(c_0_16, plain, ![X11, X12]:(~m1_subset_1(X12,k1_zfmisc_1(X11))|k3_subset_1(X11,k3_subset_1(X11,X12))=X12), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 0.42/0.58  cnf(c_0_17, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.42/0.58  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.42/0.58  fof(c_0_19, plain, ![X24, X25]:(~l1_pre_topc(X24)|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))|m1_subset_1(k1_tops_1(X24,X25),k1_zfmisc_1(u1_struct_0(X24)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_1])])).
% 0.42/0.58  fof(c_0_20, plain, ![X26, X27, X28]:(~l1_pre_topc(X26)|(~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|(~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))|(~r1_tarski(X27,X28)|r1_tarski(k1_tops_1(X26,X27),k1_tops_1(X26,X28)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).
% 0.42/0.58  cnf(c_0_21, plain, (r1_tarski(k3_subset_1(X2,X3),X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_tarski(k3_subset_1(X2,X1),X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.42/0.58  cnf(c_0_22, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.42/0.58  cnf(c_0_23, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.42/0.58  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.42/0.58  fof(c_0_25, plain, ![X19, X20, X21]:(~m1_subset_1(X20,k1_zfmisc_1(X19))|(~m1_subset_1(X21,k1_zfmisc_1(X19))|r1_tarski(k3_subset_1(X19,k4_subset_1(X19,X20,X21)),k3_subset_1(X19,X20)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t41_subset_1])])])).
% 0.42/0.58  cnf(c_0_26, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),X1,esk3_0)=k2_xboole_0(X1,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.42/0.58  fof(c_0_27, plain, ![X8, X9, X10]:(~m1_subset_1(X9,k1_zfmisc_1(X8))|~m1_subset_1(X10,k1_zfmisc_1(X8))|m1_subset_1(k4_subset_1(X8,X9,X10),k1_zfmisc_1(X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_subset_1])])).
% 0.42/0.58  fof(c_0_28, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.42/0.58  cnf(c_0_29, plain, (m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.42/0.58  cnf(c_0_30, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.42/0.58  fof(c_0_31, plain, ![X22, X23]:((~m1_subset_1(X22,k1_zfmisc_1(X23))|r1_tarski(X22,X23))&(~r1_tarski(X22,X23)|m1_subset_1(X22,k1_zfmisc_1(X23)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.42/0.58  cnf(c_0_32, plain, (r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.42/0.58  cnf(c_0_33, plain, (r1_tarski(k3_subset_1(X1,k3_subset_1(X1,X2)),X3)|~r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.42/0.58  cnf(c_0_34, negated_conjecture, (k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))=esk2_0), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.42/0.58  cnf(c_0_35, plain, (r1_tarski(k3_subset_1(X2,k4_subset_1(X2,X1,X3)),k3_subset_1(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.42/0.58  cnf(c_0_36, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)=k2_xboole_0(esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_26, c_0_24])).
% 0.42/0.58  cnf(c_0_37, plain, (m1_subset_1(k4_subset_1(X2,X1,X3),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.42/0.58  cnf(c_0_38, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),X1,esk2_0)=k2_xboole_0(X1,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_17, c_0_24])).
% 0.42/0.58  cnf(c_0_39, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.42/0.58  cnf(c_0_40, negated_conjecture, (m1_subset_1(k1_tops_1(esk1_0,X1),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.42/0.58  cnf(c_0_41, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.42/0.58  cnf(c_0_42, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,X1),k1_tops_1(esk1_0,X2))|~r1_tarski(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_32, c_0_30])).
% 0.42/0.58  cnf(c_0_43, negated_conjecture, (r1_tarski(esk2_0,X1)|~r1_tarski(k3_subset_1(u1_struct_0(esk1_0),X1),k3_subset_1(u1_struct_0(esk1_0),esk2_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_24])])).
% 0.42/0.58  cnf(c_0_44, negated_conjecture, (r1_tarski(k3_subset_1(u1_struct_0(esk1_0),k2_xboole_0(esk2_0,esk3_0)),k3_subset_1(u1_struct_0(esk1_0),esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_18]), c_0_24])])).
% 0.42/0.58  cnf(c_0_45, negated_conjecture, (m1_subset_1(k2_xboole_0(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_36]), c_0_18]), c_0_24])])).
% 0.42/0.58  cnf(c_0_46, negated_conjecture, (k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk3_0))=esk3_0), inference(spm,[status(thm)],[c_0_23, c_0_18])).
% 0.42/0.58  cnf(c_0_47, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),esk3_0,esk2_0)=k2_xboole_0(esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_18]), c_0_39])).
% 0.42/0.58  cnf(c_0_48, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),X1,k1_tops_1(esk1_0,X2))=k2_xboole_0(X1,k1_tops_1(esk1_0,X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_17, c_0_40])).
% 0.42/0.58  cnf(c_0_49, negated_conjecture, (m1_subset_1(k1_tops_1(esk1_0,X1),k1_zfmisc_1(k1_tops_1(esk1_0,X2)))|~r1_tarski(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.42/0.58  cnf(c_0_50, negated_conjecture, (r1_tarski(esk2_0,k2_xboole_0(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45])])).
% 0.42/0.58  cnf(c_0_51, negated_conjecture, (r1_tarski(esk3_0,X1)|~r1_tarski(k3_subset_1(u1_struct_0(esk1_0),X1),k3_subset_1(u1_struct_0(esk1_0),esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_46]), c_0_18])])).
% 0.42/0.58  cnf(c_0_52, negated_conjecture, (r1_tarski(k3_subset_1(u1_struct_0(esk1_0),k2_xboole_0(esk2_0,esk3_0)),k3_subset_1(u1_struct_0(esk1_0),esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_47]), c_0_24]), c_0_18])])).
% 0.42/0.58  cnf(c_0_53, negated_conjecture, (~r1_tarski(k4_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)),k1_tops_1(esk1_0,k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.42/0.58  cnf(c_0_54, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.42/0.58  cnf(c_0_55, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,X1),k1_tops_1(esk1_0,X2))=k2_xboole_0(k1_tops_1(esk1_0,X1),k1_tops_1(esk1_0,X2))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_48, c_0_40])).
% 0.42/0.58  cnf(c_0_56, negated_conjecture, (m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(k1_tops_1(esk1_0,k2_xboole_0(esk2_0,esk3_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_45]), c_0_24])])).
% 0.42/0.58  cnf(c_0_57, negated_conjecture, (r1_tarski(esk3_0,k2_xboole_0(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_45])])).
% 0.42/0.58  cnf(c_0_58, negated_conjecture, (~m1_subset_1(k4_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)),k1_zfmisc_1(k1_tops_1(esk1_0,k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0))))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.42/0.58  cnf(c_0_59, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,X1),k1_tops_1(esk1_0,esk3_0))=k2_xboole_0(k1_tops_1(esk1_0,X1),k1_tops_1(esk1_0,esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_55, c_0_18])).
% 0.42/0.58  cnf(c_0_60, negated_conjecture, (k4_subset_1(k1_tops_1(esk1_0,k2_xboole_0(esk2_0,esk3_0)),X1,k1_tops_1(esk1_0,esk2_0))=k2_xboole_0(X1,k1_tops_1(esk1_0,esk2_0))|~m1_subset_1(X1,k1_zfmisc_1(k1_tops_1(esk1_0,k2_xboole_0(esk2_0,esk3_0))))), inference(spm,[status(thm)],[c_0_17, c_0_56])).
% 0.42/0.58  cnf(c_0_61, negated_conjecture, (m1_subset_1(k1_tops_1(esk1_0,esk3_0),k1_zfmisc_1(k1_tops_1(esk1_0,k2_xboole_0(esk2_0,esk3_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_57]), c_0_45]), c_0_18])])).
% 0.42/0.58  cnf(c_0_62, negated_conjecture, (~m1_subset_1(k4_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)),k1_zfmisc_1(k1_tops_1(esk1_0,k2_xboole_0(esk2_0,esk3_0))))), inference(rw,[status(thm)],[c_0_58, c_0_36])).
% 0.42/0.58  cnf(c_0_63, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0))=k2_xboole_0(k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0))), inference(spm,[status(thm)],[c_0_59, c_0_24])).
% 0.42/0.58  cnf(c_0_64, negated_conjecture, (k4_subset_1(k1_tops_1(esk1_0,k2_xboole_0(esk2_0,esk3_0)),k1_tops_1(esk1_0,esk3_0),k1_tops_1(esk1_0,esk2_0))=k2_xboole_0(k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_39])).
% 0.42/0.58  cnf(c_0_65, negated_conjecture, (~m1_subset_1(k2_xboole_0(k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)),k1_zfmisc_1(k1_tops_1(esk1_0,k2_xboole_0(esk2_0,esk3_0))))), inference(rw,[status(thm)],[c_0_62, c_0_63])).
% 0.42/0.58  cnf(c_0_66, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_64]), c_0_56]), c_0_61])]), c_0_65]), ['proof']).
% 0.42/0.58  # SZS output end CNFRefutation
% 0.42/0.58  # Proof object total steps             : 67
% 0.42/0.58  # Proof object clause steps            : 44
% 0.42/0.58  # Proof object formula steps           : 23
% 0.42/0.58  # Proof object conjectures             : 35
% 0.42/0.58  # Proof object clause conjectures      : 32
% 0.42/0.58  # Proof object formula conjectures     : 3
% 0.42/0.58  # Proof object initial clauses used    : 15
% 0.42/0.58  # Proof object initial formulas used   : 11
% 0.42/0.58  # Proof object generating inferences   : 27
% 0.42/0.58  # Proof object simplifying inferences  : 31
% 0.42/0.58  # Training examples: 0 positive, 0 negative
% 0.42/0.58  # Parsed axioms                        : 11
% 0.42/0.58  # Removed by relevancy pruning/SinE    : 0
% 0.42/0.58  # Initial clauses                      : 15
% 0.42/0.58  # Removed in clause preprocessing      : 0
% 0.42/0.58  # Initial clauses in saturation        : 15
% 0.42/0.58  # Processed clauses                    : 1379
% 0.42/0.58  # ...of these trivial                  : 45
% 0.42/0.58  # ...subsumed                          : 323
% 0.42/0.58  # ...remaining for further processing  : 1011
% 0.42/0.58  # Other redundant clauses eliminated   : 0
% 0.42/0.58  # Clauses deleted for lack of memory   : 0
% 0.42/0.58  # Backward-subsumed                    : 12
% 0.42/0.58  # Backward-rewritten                   : 57
% 0.42/0.58  # Generated clauses                    : 11829
% 0.42/0.58  # ...of the previous two non-trivial   : 11158
% 0.42/0.58  # Contextual simplify-reflections      : 8
% 0.42/0.58  # Paramodulations                      : 11829
% 0.42/0.58  # Factorizations                       : 0
% 0.42/0.58  # Equation resolutions                 : 0
% 0.42/0.58  # Propositional unsat checks           : 0
% 0.42/0.58  #    Propositional check models        : 0
% 0.42/0.58  #    Propositional check unsatisfiable : 0
% 0.42/0.58  #    Propositional clauses             : 0
% 0.42/0.58  #    Propositional clauses after purity: 0
% 0.42/0.58  #    Propositional unsat core size     : 0
% 0.42/0.58  #    Propositional preprocessing time  : 0.000
% 0.42/0.58  #    Propositional encoding time       : 0.000
% 0.42/0.58  #    Propositional solver time         : 0.000
% 0.42/0.58  #    Success case prop preproc time    : 0.000
% 0.42/0.58  #    Success case prop encoding time   : 0.000
% 0.42/0.58  #    Success case prop solver time     : 0.000
% 0.42/0.58  # Current number of processed clauses  : 927
% 0.42/0.58  #    Positive orientable unit clauses  : 337
% 0.42/0.58  #    Positive unorientable unit clauses: 1
% 0.42/0.58  #    Negative unit clauses             : 2
% 0.42/0.58  #    Non-unit-clauses                  : 587
% 0.42/0.58  # Current number of unprocessed clauses: 9801
% 0.42/0.58  # ...number of literals in the above   : 19178
% 0.42/0.58  # Current number of archived formulas  : 0
% 0.42/0.58  # Current number of archived clauses   : 84
% 0.42/0.58  # Clause-clause subsumption calls (NU) : 27429
% 0.42/0.58  # Rec. Clause-clause subsumption calls : 26000
% 0.42/0.58  # Non-unit clause-clause subsumptions  : 341
% 0.42/0.58  # Unit Clause-clause subsumption calls : 14457
% 0.42/0.58  # Rewrite failures with RHS unbound    : 0
% 0.42/0.58  # BW rewrite match attempts            : 4440
% 0.42/0.58  # BW rewrite match successes           : 47
% 0.42/0.58  # Condensation attempts                : 0
% 0.42/0.58  # Condensation successes               : 0
% 0.42/0.58  # Termbank termtop insertions          : 380223
% 0.42/0.58  
% 0.42/0.58  # -------------------------------------------------
% 0.42/0.58  # User time                : 0.222 s
% 0.42/0.58  # System time              : 0.013 s
% 0.42/0.58  # Total time               : 0.235 s
% 0.42/0.58  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------

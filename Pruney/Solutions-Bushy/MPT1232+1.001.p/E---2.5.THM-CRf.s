%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1232+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:57 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 356 expanded)
%              Number of clauses        :   56 ( 161 expanded)
%              Number of leaves         :   12 (  87 expanded)
%              Depth                    :   16
%              Number of atoms          :  221 (1117 expanded)
%              Number of equality atoms :   43 ( 280 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t26_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k3_xboole_0(X1,X3),k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_xboole_1)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t41_tops_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( v3_pre_topc(X2,X1)
               => k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) = k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X2,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tops_1)).

fof(commutativity_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k9_subset_1(X1,X3,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(dt_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(t49_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( r1_tarski(X2,X3)
               => r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_pre_topc)).

fof(projectivity_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => k2_pre_topc(X1,k2_pre_topc(X1,X2)) = k2_pre_topc(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(t40_tops_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( v3_pre_topc(X2,X1)
               => r1_tarski(k9_subset_1(u1_struct_0(X1),X2,k2_pre_topc(X1,X3)),k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X2,X3))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_tops_1)).

fof(t48_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(X2,k2_pre_topc(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

fof(c_0_12,plain,(
    ! [X9,X10] :
      ( ( r1_tarski(X9,X10)
        | X9 != X10 )
      & ( r1_tarski(X10,X9)
        | X9 != X10 )
      & ( ~ r1_tarski(X9,X10)
        | ~ r1_tarski(X10,X9)
        | X9 = X10 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_13,plain,(
    ! [X21,X22,X23] :
      ( ~ r1_tarski(X21,X22)
      | r1_tarski(k3_xboole_0(X21,X23),k3_xboole_0(X22,X23)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_xboole_1])])).

cnf(c_0_14,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_15,plain,
    ( r1_tarski(k3_xboole_0(X1,X3),k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_16,plain,(
    ! [X18,X19,X20] :
      ( ~ m1_subset_1(X20,k1_zfmisc_1(X18))
      | k9_subset_1(X18,X19,X20) = k3_xboole_0(X19,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

fof(c_0_17,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_18,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X3,X2)
    | ~ r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2))
    | ~ r1_tarski(X3,X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_19,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( v3_pre_topc(X2,X1)
                 => k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) = k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X2,X3)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t41_tops_1])).

fof(c_0_21,plain,(
    ! [X6,X7,X8] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(X6))
      | k9_subset_1(X6,X7,X8) = k9_subset_1(X6,X8,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k9_subset_1])])).

cnf(c_0_22,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( k3_xboole_0(X1,X2) = k9_subset_1(X3,X4,X2)
    | ~ r1_tarski(k3_xboole_0(X1,X2),k9_subset_1(X3,X4,X2))
    | ~ r1_tarski(X4,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_24,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),k9_subset_1(X3,X4,X2))
    | ~ r1_tarski(X1,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_19])).

fof(c_0_25,negated_conjecture,
    ( v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & v3_pre_topc(esk2_0,esk1_0)
    & k2_pre_topc(esk1_0,k9_subset_1(u1_struct_0(esk1_0),esk2_0,k2_pre_topc(esk1_0,esk3_0))) != k2_pre_topc(esk1_0,k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).

cnf(c_0_26,plain,
    ( k9_subset_1(X2,X3,X1) = k9_subset_1(X2,X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( k9_subset_1(X1,X2,X3) = k3_xboole_0(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_19])).

cnf(c_0_28,plain,
    ( k3_xboole_0(X1,X2) = k9_subset_1(X3,X4,X2)
    | ~ r1_tarski(X4,X1)
    | ~ r1_tarski(X1,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_33,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X3,X1))
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_15,c_0_22])).

cnf(c_0_34,plain,
    ( k9_subset_1(X1,X2,X3) = k3_xboole_0(X3,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_26])).

cnf(c_0_35,negated_conjecture,
    ( k3_xboole_0(X1,esk3_0) = k9_subset_1(u1_struct_0(esk1_0),X2,esk3_0)
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( k3_xboole_0(X1,esk2_0) = k9_subset_1(u1_struct_0(esk1_0),X2,esk2_0)
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_31])).

cnf(c_0_38,plain,
    ( k9_subset_1(X1,X2,X3) = k3_xboole_0(X4,X3)
    | ~ r1_tarski(k9_subset_1(X1,X2,X3),k3_xboole_0(X4,X3))
    | ~ r1_tarski(X4,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_32])).

cnf(c_0_39,plain,
    ( r1_tarski(k9_subset_1(X1,X2,X3),k3_xboole_0(X4,X3))
    | ~ r1_tarski(X2,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

fof(c_0_40,plain,(
    ! [X13,X14,X15] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(X13))
      | m1_subset_1(k9_subset_1(X13,X14,X15),k1_zfmisc_1(X13)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).

cnf(c_0_41,negated_conjecture,
    ( k3_xboole_0(X1,esk3_0) = k9_subset_1(u1_struct_0(esk1_0),X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_36])])).

fof(c_0_42,plain,(
    ! [X29,X30,X31] :
      ( ~ l1_pre_topc(X29)
      | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
      | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X29)))
      | ~ r1_tarski(X30,X31)
      | r1_tarski(k2_pre_topc(X29,X30),k2_pre_topc(X29,X31)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t49_pre_topc])])])).

fof(c_0_43,plain,(
    ! [X16,X17] :
      ( ~ l1_pre_topc(X16)
      | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
      | k2_pre_topc(X16,k2_pre_topc(X16,X17)) = k2_pre_topc(X16,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[projectivity_k2_pre_topc])])).

fof(c_0_44,plain,(
    ! [X11,X12] :
      ( ~ l1_pre_topc(X11)
      | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))
      | m1_subset_1(k2_pre_topc(X11,X12),k1_zfmisc_1(u1_struct_0(X11))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

fof(c_0_45,plain,(
    ! [X24,X25,X26] :
      ( ~ v2_pre_topc(X24)
      | ~ l1_pre_topc(X24)
      | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
      | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X24)))
      | ~ v3_pre_topc(X25,X24)
      | r1_tarski(k9_subset_1(u1_struct_0(X24),X25,k2_pre_topc(X24,X26)),k2_pre_topc(X24,k9_subset_1(u1_struct_0(X24),X25,X26))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t40_tops_1])])])).

cnf(c_0_46,negated_conjecture,
    ( k3_xboole_0(X1,esk2_0) = k9_subset_1(u1_struct_0(esk1_0),X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_36]),c_0_36])])).

cnf(c_0_47,plain,
    ( k9_subset_1(X1,X2,X3) = k3_xboole_0(X4,X3)
    | ~ r1_tarski(X4,X2)
    | ~ r1_tarski(X2,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_48,plain,
    ( m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_49,negated_conjecture,
    ( k9_subset_1(X1,X2,esk3_0) = k9_subset_1(u1_struct_0(esk1_0),X2,esk3_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_41])).

cnf(c_0_50,plain,
    ( r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_51,plain,
    ( k2_pre_topc(X1,k2_pre_topc(X1,X2)) = k2_pre_topc(X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_52,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_53,plain,
    ( r1_tarski(k9_subset_1(u1_struct_0(X1),X2,k2_pre_topc(X1,X3)),k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X2,X3)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_54,negated_conjecture,
    ( k3_xboole_0(esk3_0,X1) = k9_subset_1(u1_struct_0(esk1_0),X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_41])).

cnf(c_0_55,negated_conjecture,
    ( k3_xboole_0(esk2_0,X1) = k9_subset_1(u1_struct_0(esk1_0),X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_46])).

cnf(c_0_56,negated_conjecture,
    ( k3_xboole_0(X1,X2) = k9_subset_1(u1_struct_0(esk1_0),esk2_0,X2)
    | ~ r1_tarski(X1,esk2_0)
    | ~ r1_tarski(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_31])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(k9_subset_1(X1,X2,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_29])])).

cnf(c_0_58,plain,
    ( k2_pre_topc(X1,X2) = k2_pre_topc(X1,X3)
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3))
    | ~ r1_tarski(X3,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_14,c_0_50])).

cnf(c_0_59,plain,
    ( r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(X2,k2_pre_topc(X1,X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])).

cnf(c_0_60,plain,
    ( r1_tarski(k9_subset_1(u1_struct_0(X1),X2,k2_pre_topc(X1,X3)),k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X3,X2)))
    | ~ v3_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_26])).

cnf(c_0_61,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk1_0),esk3_0,esk2_0) = k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_46])).

cnf(c_0_62,negated_conjecture,
    ( v3_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_63,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_64,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_65,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk1_0),esk2_0,X1) = k9_subset_1(u1_struct_0(esk1_0),X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_36])])).

cnf(c_0_66,negated_conjecture,
    ( m1_subset_1(k9_subset_1(u1_struct_0(esk1_0),X1,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_19]),c_0_41])).

cnf(c_0_67,plain,
    ( k2_pre_topc(X1,X2) = k2_pre_topc(X1,X3)
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(X2,k2_pre_topc(X1,X3))
    | ~ r1_tarski(X3,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_68,negated_conjecture,
    ( r1_tarski(k9_subset_1(u1_struct_0(esk1_0),esk2_0,k2_pre_topc(esk1_0,esk3_0)),k2_pre_topc(esk1_0,k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62]),c_0_63]),c_0_64]),c_0_29]),c_0_31])])).

cnf(c_0_69,negated_conjecture,
    ( m1_subset_1(k9_subset_1(u1_struct_0(esk1_0),esk2_0,X1),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_65]),c_0_31])])).

cnf(c_0_70,negated_conjecture,
    ( m1_subset_1(k9_subset_1(u1_struct_0(esk1_0),X1,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_66,c_0_29])).

cnf(c_0_71,negated_conjecture,
    ( k2_pre_topc(esk1_0,k9_subset_1(u1_struct_0(esk1_0),esk2_0,k2_pre_topc(esk1_0,esk3_0))) != k2_pre_topc(esk1_0,k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_72,negated_conjecture,
    ( ~ r1_tarski(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),k9_subset_1(u1_struct_0(esk1_0),esk2_0,k2_pre_topc(esk1_0,esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_64]),c_0_69]),c_0_70])]),c_0_71])).

cnf(c_0_73,plain,
    ( k9_subset_1(X1,X2,X3) = k9_subset_1(X4,X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_34])).

cnf(c_0_74,negated_conjecture,
    ( ~ r1_tarski(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),k9_subset_1(X1,k2_pre_topc(esk1_0,esk3_0),esk2_0))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_31])])).

cnf(c_0_75,plain,
    ( r1_tarski(k9_subset_1(X1,X2,X3),k9_subset_1(X4,X5,X2))
    | ~ r1_tarski(X3,X5)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_27])).

fof(c_0_76,plain,(
    ! [X27,X28] :
      ( ~ l1_pre_topc(X27)
      | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))
      | r1_tarski(X28,k2_pre_topc(X27,X28)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_pre_topc])])])).

cnf(c_0_77,negated_conjecture,
    ( ~ r1_tarski(esk3_0,k2_pre_topc(esk1_0,esk3_0))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_29])])).

cnf(c_0_78,plain,
    ( r1_tarski(X2,k2_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_79,negated_conjecture,
    ( ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_64]),c_0_29])])).

cnf(c_0_80,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_31,c_0_79]),
    [proof]).

%------------------------------------------------------------------------------

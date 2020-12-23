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
% DateTime   : Thu Dec  3 11:11:00 EST 2020

% Result     : Theorem 0.42s
% Output     : CNFRefutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 667 expanded)
%              Number of clauses        :   60 ( 251 expanded)
%              Number of leaves         :   15 ( 162 expanded)
%              Depth                    :   16
%              Number of atoms          :  289 (3959 expanded)
%              Number of equality atoms :   22 (  62 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t11_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X1,X2),X3)
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t54_tops_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2,X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
         => ( r2_hidden(X2,k1_tops_1(X1,X3))
          <=> ? [X4] :
                ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                & v3_pre_topc(X4,X1)
                & r1_tarski(X4,X3)
                & r2_hidden(X2,X4) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_tops_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(d1_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k1_tops_1(X1,X2) = k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

fof(t52_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ( v4_pre_topc(X2,X1)
             => k2_pre_topc(X1,X2) = X2 )
            & ( ( v2_pre_topc(X1)
                & k2_pre_topc(X1,X2) = X2 )
             => v4_pre_topc(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(dt_k1_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(fc9_tops_1,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => v3_pre_topc(k1_tops_1(X1,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(t30_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tops_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(t44_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(k1_tops_1(X1,X2),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(t48_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( r1_tarski(X2,X3)
               => r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(c_0_15,plain,(
    ! [X5,X6,X7] :
      ( ~ r1_tarski(k2_xboole_0(X5,X6),X7)
      | r1_tarski(X5,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

fof(c_0_16,plain,(
    ! [X8,X9] :
      ( ~ r1_tarski(X8,X9)
      | k2_xboole_0(X8,X9) = X9 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_18,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_19,plain,(
    ! [X18,X19] :
      ( ( ~ m1_subset_1(X18,k1_zfmisc_1(X19))
        | r1_tarski(X18,X19) )
      & ( ~ r1_tarski(X18,X19)
        | m1_subset_1(X18,k1_zfmisc_1(X19)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2,X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
           => ( r2_hidden(X2,k1_tops_1(X1,X3))
            <=> ? [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                  & v3_pre_topc(X4,X1)
                  & r1_tarski(X4,X3)
                  & r2_hidden(X2,X4) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t54_tops_1])).

fof(c_0_21,plain,(
    ! [X10,X11] : r1_tarski(k4_xboole_0(X10,X11),X10) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_24,negated_conjecture,(
    ! [X38] :
      ( v2_pre_topc(esk1_0)
      & l1_pre_topc(esk1_0)
      & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
      & ( ~ r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0))
        | ~ m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(esk1_0)))
        | ~ v3_pre_topc(X38,esk1_0)
        | ~ r1_tarski(X38,esk3_0)
        | ~ r2_hidden(esk2_0,X38) )
      & ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
        | r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0)) )
      & ( v3_pre_topc(esk4_0,esk1_0)
        | r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0)) )
      & ( r1_tarski(esk4_0,esk3_0)
        | r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0)) )
      & ( r2_hidden(esk2_0,esk4_0)
        | r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])])])).

cnf(c_0_25,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_27,plain,(
    ! [X14,X15] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(X14))
      | k3_subset_1(X14,X15) = k4_xboole_0(X14,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_30,plain,(
    ! [X22,X23] :
      ( ~ l1_pre_topc(X22)
      | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
      | k1_tops_1(X22,X23) = k3_subset_1(u1_struct_0(X22),k2_pre_topc(X22,k3_subset_1(u1_struct_0(X22),X23))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tops_1])])])).

fof(c_0_31,plain,(
    ! [X20,X21] :
      ( ( ~ v4_pre_topc(X21,X20)
        | k2_pre_topc(X20,X21) = X21
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))
        | ~ l1_pre_topc(X20) )
      & ( ~ v2_pre_topc(X20)
        | k2_pre_topc(X20,X21) != X21
        | v4_pre_topc(X21,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))
        | ~ l1_pre_topc(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).

cnf(c_0_32,plain,
    ( m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_33,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( ~ r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ v3_pre_topc(X1,esk1_0)
    | ~ r1_tarski(X1,esk3_0)
    | ~ r2_hidden(esk2_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk1_0)
    | r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_36,plain,(
    ! [X24,X25] :
      ( ~ l1_pre_topc(X24)
      | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
      | m1_subset_1(k1_tops_1(X24,X25),k1_zfmisc_1(u1_struct_0(X24))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_1])])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_38,plain,(
    ! [X26,X27] :
      ( ~ v2_pre_topc(X26)
      | ~ l1_pre_topc(X26)
      | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
      | v3_pre_topc(k1_tops_1(X26,X27),X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_40,plain,
    ( k1_tops_1(X1,X2) = k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_41,plain,
    ( k2_pre_topc(X2,X1) = X1
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_42,plain,
    ( m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

fof(c_0_43,plain,(
    ! [X28,X29] :
      ( ( ~ v3_pre_topc(X29,X28)
        | v4_pre_topc(k3_subset_1(u1_struct_0(X28),X29),X28)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
        | ~ l1_pre_topc(X28) )
      & ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(X28),X29),X28)
        | v3_pre_topc(X29,X28)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
        | ~ l1_pre_topc(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_tops_1])])])])).

cnf(c_0_44,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk1_0)
    | ~ v3_pre_topc(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r2_hidden(esk2_0,X1)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_45,plain,
    ( m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_46,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ v3_pre_topc(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r2_hidden(esk2_0,X1)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_37])).

cnf(c_0_48,plain,
    ( v3_pre_topc(k1_tops_1(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_49,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_39])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(esk4_0,esk3_0)
    | r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_52,plain,(
    ! [X16,X17] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(X16))
      | k3_subset_1(X16,k3_subset_1(X16,X17)) = X17 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

cnf(c_0_53,plain,
    ( k3_subset_1(u1_struct_0(X1),k3_subset_1(u1_struct_0(X1),X2)) = k1_tops_1(X1,X2)
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])).

cnf(c_0_54,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(X2),X1),X2)
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_55,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk1_0)
    | ~ v3_pre_topc(k1_tops_1(esk1_0,X1),esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r2_hidden(esk2_0,k1_tops_1(esk1_0,X1))
    | ~ r1_tarski(k1_tops_1(esk1_0,X1),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46])])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r2_hidden(esk2_0,k1_tops_1(esk1_0,X1))
    | ~ r1_tarski(k1_tops_1(esk1_0,X1),esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49]),c_0_46])]),c_0_50])).

fof(c_0_57,plain,(
    ! [X30,X31] :
      ( ~ l1_pre_topc(X30)
      | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
      | r1_tarski(k1_tops_1(X30,X31),X31) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(esk4_0,esk3_0)
    | ~ v3_pre_topc(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r2_hidden(esk2_0,X1)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_51])).

fof(c_0_59,plain,(
    ! [X32,X33,X34] :
      ( ~ l1_pre_topc(X32)
      | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))
      | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X32)))
      | ~ r1_tarski(X33,X34)
      | r1_tarski(k1_tops_1(X32,X33),k1_tops_1(X32,X34)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).

cnf(c_0_60,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_61,plain,
    ( k3_subset_1(u1_struct_0(X1),k3_subset_1(u1_struct_0(X1),X2)) = k1_tops_1(X1,X2)
    | ~ v3_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_62,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r2_hidden(esk2_0,k1_tops_1(esk1_0,X1))
    | ~ r1_tarski(k1_tops_1(esk1_0,X1),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_48]),c_0_49]),c_0_46])])).

cnf(c_0_63,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_37]),c_0_29])])).

cnf(c_0_64,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(esk4_0,esk3_0)
    | ~ m1_subset_1(k1_tops_1(esk1_0,X1),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r2_hidden(esk2_0,k1_tops_1(esk1_0,X1))
    | ~ r1_tarski(k1_tops_1(esk1_0,X1),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_48]),c_0_49]),c_0_46])])).

cnf(c_0_66,plain,
    ( r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_67,plain,
    ( k1_tops_1(X1,X2) = X2
    | ~ v3_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_68,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk1_0)
    | ~ r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_35]),c_0_29])])).

cnf(c_0_69,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_46]),c_0_29])])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(esk4_0,esk3_0)
    | ~ m1_subset_1(k1_tops_1(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_51]),c_0_29])])).

cnf(c_0_71,plain,
    ( r1_tarski(X1,k1_tops_1(X2,X3))
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(X1,k1_tops_1(X2,X4))
    | ~ r1_tarski(X4,X3) ),
    inference(spm,[status(thm)],[c_0_22,c_0_66])).

cnf(c_0_72,negated_conjecture,
    ( k1_tops_1(esk1_0,esk4_0) = esk4_0
    | ~ r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_46]),c_0_69])])).

cnf(c_0_73,negated_conjecture,
    ( r1_tarski(esk4_0,esk3_0)
    | ~ r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_45]),c_0_46]),c_0_29])])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(esk2_0,esk4_0)
    | r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_75,plain,(
    ! [X12,X13] :
      ( ( ~ r1_tarski(k1_tarski(X12),X13)
        | r2_hidden(X12,X13) )
      & ( ~ r2_hidden(X12,X13)
        | r1_tarski(k1_tarski(X12),X13) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

cnf(c_0_76,negated_conjecture,
    ( r1_tarski(X1,k1_tops_1(esk1_0,esk3_0))
    | ~ r1_tarski(X1,k1_tops_1(esk1_0,X2))
    | ~ r1_tarski(X2,esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_29]),c_0_46])]),c_0_50])).

cnf(c_0_77,negated_conjecture,
    ( k1_tops_1(esk1_0,esk4_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_64]),c_0_46]),c_0_29])])).

cnf(c_0_78,negated_conjecture,
    ( r1_tarski(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_64]),c_0_46]),c_0_29])])).

cnf(c_0_79,negated_conjecture,
    ( r2_hidden(esk2_0,esk4_0)
    | ~ v3_pre_topc(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r2_hidden(esk2_0,X1)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_74])).

cnf(c_0_80,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_81,negated_conjecture,
    ( r1_tarski(X1,k1_tops_1(esk1_0,esk3_0))
    | ~ r1_tarski(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_78])])).

cnf(c_0_82,negated_conjecture,
    ( r2_hidden(esk2_0,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r2_hidden(esk2_0,k1_tops_1(esk1_0,X1))
    | ~ r1_tarski(k1_tops_1(esk1_0,X1),esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_48]),c_0_49]),c_0_46])]),c_0_50])).

cnf(c_0_83,negated_conjecture,
    ( r2_hidden(X1,k1_tops_1(esk1_0,esk3_0))
    | ~ r1_tarski(k1_tarski(X1),esk4_0) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_84,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_85,negated_conjecture,
    ( r2_hidden(esk2_0,esk4_0)
    | ~ r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_74]),c_0_29])])).

cnf(c_0_86,negated_conjecture,
    ( r2_hidden(X1,k1_tops_1(esk1_0,esk3_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_87,negated_conjecture,
    ( r2_hidden(esk2_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_64]),c_0_46]),c_0_29])])).

cnf(c_0_88,negated_conjecture,
    ( ~ v3_pre_topc(X1,esk1_0)
    | ~ r2_hidden(esk2_0,X1)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_86]),c_0_87])]),c_0_50])).

cnf(c_0_89,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_77]),c_0_49]),c_0_46]),c_0_69])])).

cnf(c_0_90,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_87]),c_0_78])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:47:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.42/0.58  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SOS_SP_PS_S5PRR_RG_S04AN
% 0.42/0.58  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.42/0.58  #
% 0.42/0.58  # Preprocessing time       : 0.028 s
% 0.42/0.58  # Presaturation interreduction done
% 0.42/0.58  
% 0.42/0.58  # Proof found!
% 0.42/0.58  # SZS status Theorem
% 0.42/0.58  # SZS output start CNFRefutation
% 0.42/0.58  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 0.42/0.58  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.42/0.58  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.42/0.58  fof(t54_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X2,k1_tops_1(X1,X3))<=>?[X4]:(((m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))&v3_pre_topc(X4,X1))&r1_tarski(X4,X3))&r2_hidden(X2,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_tops_1)).
% 0.42/0.58  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.42/0.58  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 0.42/0.58  fof(d1_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k1_tops_1(X1,X2)=k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tops_1)).
% 0.42/0.58  fof(t52_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v4_pre_topc(X2,X1)=>k2_pre_topc(X1,X2)=X2)&((v2_pre_topc(X1)&k2_pre_topc(X1,X2)=X2)=>v4_pre_topc(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 0.42/0.58  fof(dt_k1_tops_1, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 0.42/0.58  fof(fc9_tops_1, axiom, ![X1, X2]:(((v2_pre_topc(X1)&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v3_pre_topc(k1_tops_1(X1,X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 0.42/0.58  fof(t30_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>v4_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_tops_1)).
% 0.42/0.58  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 0.42/0.58  fof(t44_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,X2),X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 0.42/0.58  fof(t48_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X2,X3)=>r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tops_1)).
% 0.42/0.58  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 0.42/0.58  fof(c_0_15, plain, ![X5, X6, X7]:(~r1_tarski(k2_xboole_0(X5,X6),X7)|r1_tarski(X5,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 0.42/0.58  fof(c_0_16, plain, ![X8, X9]:(~r1_tarski(X8,X9)|k2_xboole_0(X8,X9)=X9), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.42/0.58  cnf(c_0_17, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.42/0.58  cnf(c_0_18, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.42/0.58  fof(c_0_19, plain, ![X18, X19]:((~m1_subset_1(X18,k1_zfmisc_1(X19))|r1_tarski(X18,X19))&(~r1_tarski(X18,X19)|m1_subset_1(X18,k1_zfmisc_1(X19)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.42/0.58  fof(c_0_20, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X2,k1_tops_1(X1,X3))<=>?[X4]:(((m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))&v3_pre_topc(X4,X1))&r1_tarski(X4,X3))&r2_hidden(X2,X4)))))), inference(assume_negation,[status(cth)],[t54_tops_1])).
% 0.42/0.58  fof(c_0_21, plain, ![X10, X11]:r1_tarski(k4_xboole_0(X10,X11),X10), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.42/0.58  cnf(c_0_22, plain, (r1_tarski(X1,X2)|~r1_tarski(X3,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.42/0.58  cnf(c_0_23, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.42/0.58  fof(c_0_24, negated_conjecture, ![X38]:((v2_pre_topc(esk1_0)&l1_pre_topc(esk1_0))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&((~r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0))|(~m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(esk1_0)))|~v3_pre_topc(X38,esk1_0)|~r1_tarski(X38,esk3_0)|~r2_hidden(esk2_0,X38)))&((((m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0)))|r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0)))&(v3_pre_topc(esk4_0,esk1_0)|r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0))))&(r1_tarski(esk4_0,esk3_0)|r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0))))&(r2_hidden(esk2_0,esk4_0)|r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])])])).
% 0.42/0.58  cnf(c_0_25, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.42/0.58  cnf(c_0_26, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.42/0.58  fof(c_0_27, plain, ![X14, X15]:(~m1_subset_1(X15,k1_zfmisc_1(X14))|k3_subset_1(X14,X15)=k4_xboole_0(X14,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.42/0.58  cnf(c_0_28, plain, (r1_tarski(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.42/0.58  cnf(c_0_29, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.42/0.58  fof(c_0_30, plain, ![X22, X23]:(~l1_pre_topc(X22)|(~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|k1_tops_1(X22,X23)=k3_subset_1(u1_struct_0(X22),k2_pre_topc(X22,k3_subset_1(u1_struct_0(X22),X23))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tops_1])])])).
% 0.42/0.58  fof(c_0_31, plain, ![X20, X21]:((~v4_pre_topc(X21,X20)|k2_pre_topc(X20,X21)=X21|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))|~l1_pre_topc(X20))&(~v2_pre_topc(X20)|k2_pre_topc(X20,X21)!=X21|v4_pre_topc(X21,X20)|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))|~l1_pre_topc(X20))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).
% 0.42/0.58  cnf(c_0_32, plain, (m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.42/0.58  cnf(c_0_33, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.42/0.58  cnf(c_0_34, negated_conjecture, (~r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~v3_pre_topc(X1,esk1_0)|~r1_tarski(X1,esk3_0)|~r2_hidden(esk2_0,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.42/0.58  cnf(c_0_35, negated_conjecture, (v3_pre_topc(esk4_0,esk1_0)|r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.42/0.58  fof(c_0_36, plain, ![X24, X25]:(~l1_pre_topc(X24)|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))|m1_subset_1(k1_tops_1(X24,X25),k1_zfmisc_1(u1_struct_0(X24)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_1])])).
% 0.42/0.58  cnf(c_0_37, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0)))|r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.42/0.58  fof(c_0_38, plain, ![X26, X27]:(~v2_pre_topc(X26)|~l1_pre_topc(X26)|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|v3_pre_topc(k1_tops_1(X26,X27),X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).
% 0.42/0.58  cnf(c_0_39, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.42/0.58  cnf(c_0_40, plain, (k1_tops_1(X1,X2)=k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.42/0.58  cnf(c_0_41, plain, (k2_pre_topc(X2,X1)=X1|~v4_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.42/0.58  cnf(c_0_42, plain, (m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.42/0.58  fof(c_0_43, plain, ![X28, X29]:((~v3_pre_topc(X29,X28)|v4_pre_topc(k3_subset_1(u1_struct_0(X28),X29),X28)|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))|~l1_pre_topc(X28))&(~v4_pre_topc(k3_subset_1(u1_struct_0(X28),X29),X28)|v3_pre_topc(X29,X28)|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))|~l1_pre_topc(X28))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_tops_1])])])])).
% 0.42/0.58  cnf(c_0_44, negated_conjecture, (v3_pre_topc(esk4_0,esk1_0)|~v3_pre_topc(X1,esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r2_hidden(esk2_0,X1)|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.42/0.58  cnf(c_0_45, plain, (m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.42/0.58  cnf(c_0_46, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.42/0.58  cnf(c_0_47, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0)))|~v3_pre_topc(X1,esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r2_hidden(esk2_0,X1)|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_34, c_0_37])).
% 0.42/0.58  cnf(c_0_48, plain, (v3_pre_topc(k1_tops_1(X1,X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.42/0.58  cnf(c_0_49, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.42/0.58  cnf(c_0_50, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_25, c_0_39])).
% 0.42/0.58  cnf(c_0_51, negated_conjecture, (r1_tarski(esk4_0,esk3_0)|r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.42/0.58  fof(c_0_52, plain, ![X16, X17]:(~m1_subset_1(X17,k1_zfmisc_1(X16))|k3_subset_1(X16,k3_subset_1(X16,X17))=X17), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 0.42/0.58  cnf(c_0_53, plain, (k3_subset_1(u1_struct_0(X1),k3_subset_1(u1_struct_0(X1),X2))=k1_tops_1(X1,X2)|~v4_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])).
% 0.42/0.58  cnf(c_0_54, plain, (v4_pre_topc(k3_subset_1(u1_struct_0(X2),X1),X2)|~v3_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.42/0.58  cnf(c_0_55, negated_conjecture, (v3_pre_topc(esk4_0,esk1_0)|~v3_pre_topc(k1_tops_1(esk1_0,X1),esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r2_hidden(esk2_0,k1_tops_1(esk1_0,X1))|~r1_tarski(k1_tops_1(esk1_0,X1),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46])])).
% 0.42/0.58  cnf(c_0_56, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r2_hidden(esk2_0,k1_tops_1(esk1_0,X1))|~r1_tarski(k1_tops_1(esk1_0,X1),esk3_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49]), c_0_46])]), c_0_50])).
% 0.42/0.58  fof(c_0_57, plain, ![X30, X31]:(~l1_pre_topc(X30)|(~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))|r1_tarski(k1_tops_1(X30,X31),X31))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).
% 0.42/0.58  cnf(c_0_58, negated_conjecture, (r1_tarski(esk4_0,esk3_0)|~v3_pre_topc(X1,esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r2_hidden(esk2_0,X1)|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_34, c_0_51])).
% 0.42/0.58  fof(c_0_59, plain, ![X32, X33, X34]:(~l1_pre_topc(X32)|(~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))|(~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X32)))|(~r1_tarski(X33,X34)|r1_tarski(k1_tops_1(X32,X33),k1_tops_1(X32,X34)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).
% 0.42/0.58  cnf(c_0_60, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.42/0.58  cnf(c_0_61, plain, (k3_subset_1(u1_struct_0(X1),k3_subset_1(u1_struct_0(X1),X2))=k1_tops_1(X1,X2)|~v3_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.42/0.58  cnf(c_0_62, negated_conjecture, (v3_pre_topc(esk4_0,esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r2_hidden(esk2_0,k1_tops_1(esk1_0,X1))|~r1_tarski(k1_tops_1(esk1_0,X1),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_48]), c_0_49]), c_0_46])])).
% 0.42/0.58  cnf(c_0_63, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_37]), c_0_29])])).
% 0.42/0.58  cnf(c_0_64, plain, (r1_tarski(k1_tops_1(X1,X2),X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.42/0.58  cnf(c_0_65, negated_conjecture, (r1_tarski(esk4_0,esk3_0)|~m1_subset_1(k1_tops_1(esk1_0,X1),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r2_hidden(esk2_0,k1_tops_1(esk1_0,X1))|~r1_tarski(k1_tops_1(esk1_0,X1),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_48]), c_0_49]), c_0_46])])).
% 0.42/0.58  cnf(c_0_66, plain, (r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.42/0.58  cnf(c_0_67, plain, (k1_tops_1(X1,X2)=X2|~v3_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.42/0.58  cnf(c_0_68, negated_conjecture, (v3_pre_topc(esk4_0,esk1_0)|~r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_35]), c_0_29])])).
% 0.42/0.58  cnf(c_0_69, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_46]), c_0_29])])).
% 0.42/0.58  cnf(c_0_70, negated_conjecture, (r1_tarski(esk4_0,esk3_0)|~m1_subset_1(k1_tops_1(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_51]), c_0_29])])).
% 0.42/0.58  cnf(c_0_71, plain, (r1_tarski(X1,k1_tops_1(X2,X3))|~l1_pre_topc(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(X1,k1_tops_1(X2,X4))|~r1_tarski(X4,X3)), inference(spm,[status(thm)],[c_0_22, c_0_66])).
% 0.42/0.58  cnf(c_0_72, negated_conjecture, (k1_tops_1(esk1_0,esk4_0)=esk4_0|~r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_46]), c_0_69])])).
% 0.42/0.58  cnf(c_0_73, negated_conjecture, (r1_tarski(esk4_0,esk3_0)|~r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_45]), c_0_46]), c_0_29])])).
% 0.42/0.58  cnf(c_0_74, negated_conjecture, (r2_hidden(esk2_0,esk4_0)|r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.42/0.58  fof(c_0_75, plain, ![X12, X13]:((~r1_tarski(k1_tarski(X12),X13)|r2_hidden(X12,X13))&(~r2_hidden(X12,X13)|r1_tarski(k1_tarski(X12),X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 0.42/0.58  cnf(c_0_76, negated_conjecture, (r1_tarski(X1,k1_tops_1(esk1_0,esk3_0))|~r1_tarski(X1,k1_tops_1(esk1_0,X2))|~r1_tarski(X2,esk3_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_29]), c_0_46])]), c_0_50])).
% 0.42/0.58  cnf(c_0_77, negated_conjecture, (k1_tops_1(esk1_0,esk4_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_64]), c_0_46]), c_0_29])])).
% 0.42/0.58  cnf(c_0_78, negated_conjecture, (r1_tarski(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_64]), c_0_46]), c_0_29])])).
% 0.42/0.58  cnf(c_0_79, negated_conjecture, (r2_hidden(esk2_0,esk4_0)|~v3_pre_topc(X1,esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r2_hidden(esk2_0,X1)|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_34, c_0_74])).
% 0.42/0.58  cnf(c_0_80, plain, (r2_hidden(X1,X2)|~r1_tarski(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.42/0.58  cnf(c_0_81, negated_conjecture, (r1_tarski(X1,k1_tops_1(esk1_0,esk3_0))|~r1_tarski(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_78])])).
% 0.42/0.58  cnf(c_0_82, negated_conjecture, (r2_hidden(esk2_0,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r2_hidden(esk2_0,k1_tops_1(esk1_0,X1))|~r1_tarski(k1_tops_1(esk1_0,X1),esk3_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_48]), c_0_49]), c_0_46])]), c_0_50])).
% 0.42/0.58  cnf(c_0_83, negated_conjecture, (r2_hidden(X1,k1_tops_1(esk1_0,esk3_0))|~r1_tarski(k1_tarski(X1),esk4_0)), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 0.42/0.58  cnf(c_0_84, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.42/0.58  cnf(c_0_85, negated_conjecture, (r2_hidden(esk2_0,esk4_0)|~r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_74]), c_0_29])])).
% 0.42/0.58  cnf(c_0_86, negated_conjecture, (r2_hidden(X1,k1_tops_1(esk1_0,esk3_0))|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 0.42/0.58  cnf(c_0_87, negated_conjecture, (r2_hidden(esk2_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_64]), c_0_46]), c_0_29])])).
% 0.42/0.58  cnf(c_0_88, negated_conjecture, (~v3_pre_topc(X1,esk1_0)|~r2_hidden(esk2_0,X1)|~r1_tarski(X1,esk3_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_86]), c_0_87])]), c_0_50])).
% 0.42/0.58  cnf(c_0_89, negated_conjecture, (v3_pre_topc(esk4_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_77]), c_0_49]), c_0_46]), c_0_69])])).
% 0.42/0.58  cnf(c_0_90, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_87]), c_0_78])]), ['proof']).
% 0.42/0.58  # SZS output end CNFRefutation
% 0.42/0.58  # Proof object total steps             : 91
% 0.42/0.58  # Proof object clause steps            : 60
% 0.42/0.58  # Proof object formula steps           : 31
% 0.42/0.58  # Proof object conjectures             : 39
% 0.42/0.58  # Proof object clause conjectures      : 36
% 0.42/0.58  # Proof object formula conjectures     : 3
% 0.42/0.58  # Proof object initial clauses used    : 24
% 0.42/0.58  # Proof object initial formulas used   : 15
% 0.42/0.58  # Proof object generating inferences   : 36
% 0.42/0.58  # Proof object simplifying inferences  : 58
% 0.42/0.58  # Training examples: 0 positive, 0 negative
% 0.42/0.58  # Parsed axioms                        : 15
% 0.42/0.58  # Removed by relevancy pruning/SinE    : 0
% 0.42/0.58  # Initial clauses                      : 26
% 0.42/0.58  # Removed in clause preprocessing      : 0
% 0.42/0.58  # Initial clauses in saturation        : 26
% 0.42/0.58  # Processed clauses                    : 2176
% 0.42/0.58  # ...of these trivial                  : 34
% 0.42/0.58  # ...subsumed                          : 1376
% 0.42/0.58  # ...remaining for further processing  : 766
% 0.42/0.58  # Other redundant clauses eliminated   : 0
% 0.42/0.58  # Clauses deleted for lack of memory   : 0
% 0.42/0.58  # Backward-subsumed                    : 19
% 0.42/0.58  # Backward-rewritten                   : 160
% 0.42/0.58  # Generated clauses                    : 9174
% 0.42/0.58  # ...of the previous two non-trivial   : 8926
% 0.42/0.58  # Contextual simplify-reflections      : 27
% 0.42/0.58  # Paramodulations                      : 9174
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
% 0.42/0.58  # Current number of processed clauses  : 561
% 0.42/0.58  #    Positive orientable unit clauses  : 35
% 0.42/0.58  #    Positive unorientable unit clauses: 0
% 0.42/0.58  #    Negative unit clauses             : 0
% 0.42/0.58  #    Non-unit-clauses                  : 526
% 0.42/0.58  # Current number of unprocessed clauses: 6773
% 0.42/0.58  # ...number of literals in the above   : 26575
% 0.42/0.58  # Current number of archived formulas  : 0
% 0.42/0.58  # Current number of archived clauses   : 205
% 0.42/0.58  # Clause-clause subsumption calls (NU) : 111978
% 0.42/0.58  # Rec. Clause-clause subsumption calls : 81246
% 0.42/0.58  # Non-unit clause-clause subsumptions  : 1410
% 0.42/0.58  # Unit Clause-clause subsumption calls : 1428
% 0.42/0.58  # Rewrite failures with RHS unbound    : 0
% 0.42/0.58  # BW rewrite match attempts            : 51
% 0.42/0.58  # BW rewrite match successes           : 9
% 0.42/0.58  # Condensation attempts                : 0
% 0.42/0.58  # Condensation successes               : 0
% 0.42/0.58  # Termbank termtop insertions          : 166028
% 0.42/0.58  
% 0.42/0.58  # -------------------------------------------------
% 0.42/0.58  # User time                : 0.223 s
% 0.42/0.58  # System time              : 0.008 s
% 0.42/0.58  # Total time               : 0.231 s
% 0.42/0.58  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------

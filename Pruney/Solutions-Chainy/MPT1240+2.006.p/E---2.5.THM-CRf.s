%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:10:59 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 604 expanded)
%              Number of clauses        :   60 ( 212 expanded)
%              Number of leaves         :   14 ( 145 expanded)
%              Depth                    :   15
%              Number of atoms          :  299 (4069 expanded)
%              Number of equality atoms :   24 (  27 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_tops_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t11_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X1,X2),X3)
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(fc9_tops_1,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => v3_pre_topc(k1_tops_1(X1,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(t38_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_tarski(X1,X2),X3)
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(dt_k1_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(t44_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(k1_tops_1(X1,X2),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(d1_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k1_tops_1(X1,X2) = k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(t30_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tops_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

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

fof(c_0_14,negated_conjecture,(
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

fof(c_0_15,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_16,negated_conjecture,(
    ! [X37] :
      ( v2_pre_topc(esk1_0)
      & l1_pre_topc(esk1_0)
      & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
      & ( ~ r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0))
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(esk1_0)))
        | ~ v3_pre_topc(X37,esk1_0)
        | ~ r1_tarski(X37,esk3_0)
        | ~ r2_hidden(esk2_0,X37) )
      & ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
        | r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0)) )
      & ( v3_pre_topc(esk4_0,esk1_0)
        | r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0)) )
      & ( r1_tarski(esk4_0,esk3_0)
        | r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0)) )
      & ( r2_hidden(esk2_0,esk4_0)
        | r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])])])).

fof(c_0_17,plain,(
    ! [X7,X8,X9] :
      ( ~ r1_tarski(k2_xboole_0(X7,X8),X9)
      | r1_tarski(X7,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

fof(c_0_18,plain,(
    ! [X10,X11] :
      ( ~ r1_tarski(X10,X11)
      | k2_xboole_0(X10,X11) = X11 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( ~ r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ v3_pre_topc(X1,esk1_0)
    | ~ r1_tarski(X1,esk3_0)
    | ~ r2_hidden(esk2_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(esk2_0,esk4_0)
    | r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_22,plain,(
    ! [X25,X26] :
      ( ~ v2_pre_topc(X25)
      | ~ l1_pre_topc(X25)
      | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
      | v3_pre_topc(k1_tops_1(X25,X26),X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk2_0,esk4_0)
    | ~ v3_pre_topc(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r2_hidden(esk2_0,X1)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_27,plain,
    ( v3_pre_topc(k1_tops_1(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_29,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_30,plain,(
    ! [X12,X13,X14] :
      ( ( r2_hidden(X12,X14)
        | ~ r1_tarski(k2_tarski(X12,X13),X14) )
      & ( r2_hidden(X13,X14)
        | ~ r1_tarski(k2_tarski(X12,X13),X14) )
      & ( ~ r2_hidden(X12,X14)
        | ~ r2_hidden(X13,X14)
        | r1_tarski(k2_tarski(X12,X13),X14) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk2_0,esk4_0)
    | ~ m1_subset_1(k1_tops_1(esk1_0,X1),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r2_hidden(esk2_0,k1_tops_1(esk1_0,X1))
    | ~ r1_tarski(k1_tops_1(esk1_0,X1),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29])])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_35,plain,(
    ! [X23,X24] :
      ( ~ l1_pre_topc(X23)
      | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
      | m1_subset_1(k1_tops_1(X23,X24),k1_zfmisc_1(u1_struct_0(X23))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_1])])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_tarski(X1,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk2_0,esk4_0)
    | ~ m1_subset_1(k1_tops_1(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_21]),c_0_34])])).

cnf(c_0_39,plain,
    ( m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_40,plain,(
    ! [X29,X30] :
      ( ~ l1_pre_topc(X29)
      | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
      | r1_tarski(k1_tops_1(X29,X30),X30) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k2_tarski(X1,X4),X2) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_43,plain,
    ( r1_tarski(k2_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk2_0,esk4_0)
    | ~ r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_29]),c_0_34])])).

cnf(c_0_45,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(esk4_0,esk3_0)
    | r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_47,plain,(
    ! [X21,X22] :
      ( ~ l1_pre_topc(X21)
      | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
      | k1_tops_1(X21,X22) = k3_subset_1(u1_struct_0(X21),k2_pre_topc(X21,k3_subset_1(u1_struct_0(X21),X22))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tops_1])])])).

fof(c_0_48,plain,(
    ! [X19,X20] :
      ( ( ~ v4_pre_topc(X20,X19)
        | k2_pre_topc(X19,X20) = X20
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ l1_pre_topc(X19) )
      & ( ~ v2_pre_topc(X19)
        | k2_pre_topc(X19,X20) != X20
        | v4_pre_topc(X20,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ l1_pre_topc(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).

fof(c_0_49,plain,(
    ! [X15,X16] :
      ( ~ m1_subset_1(X16,k1_zfmisc_1(X15))
      | m1_subset_1(k3_subset_1(X15,X16),k1_zfmisc_1(X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

cnf(c_0_50,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk1_0)
    | r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ v3_pre_topc(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r2_hidden(esk2_0,X1)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_41])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X4,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk2_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_29]),c_0_34])])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(esk4_0,esk3_0)
    | ~ v3_pre_topc(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r2_hidden(esk2_0,X1)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_46])).

cnf(c_0_55,plain,
    ( k1_tops_1(X1,X2) = k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_56,plain,
    ( k2_pre_topc(X2,X1) = X1
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_57,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_58,plain,(
    ! [X27,X28] :
      ( ( ~ v3_pre_topc(X28,X27)
        | v4_pre_topc(k3_subset_1(u1_struct_0(X27),X28),X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ l1_pre_topc(X27) )
      & ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(X27),X28),X27)
        | v3_pre_topc(X28,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ l1_pre_topc(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_tops_1])])])])).

cnf(c_0_59,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk1_0)
    | ~ v3_pre_topc(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r2_hidden(esk2_0,X1)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_50])).

cnf(c_0_60,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k1_tops_1(esk1_0,X1),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r2_hidden(esk2_0,k1_tops_1(esk1_0,X1))
    | ~ r1_tarski(k1_tops_1(esk1_0,X1),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_27]),c_0_28]),c_0_29])])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(X1,k2_xboole_0(esk4_0,X2))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(esk4_0,esk3_0)
    | ~ m1_subset_1(k1_tops_1(esk1_0,X1),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r2_hidden(esk2_0,k1_tops_1(esk1_0,X1))
    | ~ r1_tarski(k1_tops_1(esk1_0,X1),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_27]),c_0_28]),c_0_29])])).

fof(c_0_63,plain,(
    ! [X17,X18] :
      ( ~ m1_subset_1(X18,k1_zfmisc_1(X17))
      | k3_subset_1(X17,k3_subset_1(X17,X18)) = X18 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

cnf(c_0_64,plain,
    ( k3_subset_1(u1_struct_0(X1),k3_subset_1(u1_struct_0(X1),X2)) = k1_tops_1(X1,X2)
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57])).

cnf(c_0_65,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(X2),X1),X2)
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_66,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk1_0)
    | ~ v3_pre_topc(k1_tops_1(esk1_0,X1),esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r2_hidden(esk2_0,k1_tops_1(esk1_0,X1))
    | ~ r1_tarski(k1_tops_1(esk1_0,X1),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_39]),c_0_29])])).

cnf(c_0_67,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k1_tops_1(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_41]),c_0_34])])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,esk4_0)
    | ~ r1_tarski(esk4_0,X2) ),
    inference(spm,[status(thm)],[c_0_61,c_0_24])).

cnf(c_0_69,negated_conjecture,
    ( r1_tarski(esk4_0,esk3_0)
    | ~ m1_subset_1(k1_tops_1(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_46]),c_0_34])])).

cnf(c_0_70,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_71,plain,
    ( k3_subset_1(u1_struct_0(X1),k3_subset_1(u1_struct_0(X1),X2)) = k1_tops_1(X1,X2)
    | ~ v3_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_72,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r2_hidden(esk2_0,k1_tops_1(esk1_0,X1))
    | ~ r1_tarski(k1_tops_1(esk1_0,X1),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_27]),c_0_28]),c_0_29])])).

cnf(c_0_73,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_39]),c_0_29]),c_0_34])])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(esk2_0,X1)
    | ~ r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_68,c_0_53])).

cnf(c_0_75,negated_conjecture,
    ( r1_tarski(esk4_0,esk3_0)
    | ~ r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_39]),c_0_29]),c_0_34])])).

cnf(c_0_76,plain,
    ( k1_tops_1(X1,X2) = X2
    | ~ v3_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_77,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk1_0)
    | ~ r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_50]),c_0_34])])).

cnf(c_0_78,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_45]),c_0_29]),c_0_34])])).

cnf(c_0_79,negated_conjecture,
    ( ~ v3_pre_topc(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r2_hidden(esk2_0,X1)
    | ~ r1_tarski(esk4_0,k1_tops_1(esk1_0,esk3_0))
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_74])).

cnf(c_0_80,negated_conjecture,
    ( r1_tarski(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_45]),c_0_29]),c_0_34])])).

fof(c_0_81,plain,(
    ! [X31,X32,X33] :
      ( ~ l1_pre_topc(X31)
      | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
      | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X31)))
      | ~ r1_tarski(X32,X33)
      | r1_tarski(k1_tops_1(X31,X32),k1_tops_1(X31,X33)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).

cnf(c_0_82,negated_conjecture,
    ( k1_tops_1(esk1_0,esk4_0) = esk4_0
    | ~ r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_29]),c_0_78])])).

cnf(c_0_83,negated_conjecture,
    ( ~ r1_tarski(esk4_0,k1_tops_1(esk1_0,esk3_0))
    | ~ r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_77]),c_0_78]),c_0_53]),c_0_80])])).

cnf(c_0_84,plain,
    ( r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_85,negated_conjecture,
    ( k1_tops_1(esk1_0,esk4_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_45]),c_0_29]),c_0_34])])).

cnf(c_0_86,negated_conjecture,
    ( ~ r1_tarski(esk4_0,k1_tops_1(esk1_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_45]),c_0_29]),c_0_34])])).

cnf(c_0_87,negated_conjecture,
    ( r1_tarski(esk4_0,k1_tops_1(esk1_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_29]),c_0_78])])).

cnf(c_0_88,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_34]),c_0_80])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:34:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.54  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SOS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.54  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.54  #
% 0.19/0.54  # Preprocessing time       : 0.028 s
% 0.19/0.54  # Presaturation interreduction done
% 0.19/0.54  
% 0.19/0.54  # Proof found!
% 0.19/0.54  # SZS status Theorem
% 0.19/0.54  # SZS output start CNFRefutation
% 0.19/0.54  fof(t54_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X2,k1_tops_1(X1,X3))<=>?[X4]:(((m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))&v3_pre_topc(X4,X1))&r1_tarski(X4,X3))&r2_hidden(X2,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_tops_1)).
% 0.19/0.54  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.54  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 0.19/0.54  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.19/0.54  fof(fc9_tops_1, axiom, ![X1, X2]:(((v2_pre_topc(X1)&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v3_pre_topc(k1_tops_1(X1,X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 0.19/0.54  fof(t38_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),X3)<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 0.19/0.54  fof(dt_k1_tops_1, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 0.19/0.54  fof(t44_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,X2),X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 0.19/0.54  fof(d1_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k1_tops_1(X1,X2)=k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_1)).
% 0.19/0.54  fof(t52_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v4_pre_topc(X2,X1)=>k2_pre_topc(X1,X2)=X2)&((v2_pre_topc(X1)&k2_pre_topc(X1,X2)=X2)=>v4_pre_topc(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 0.19/0.54  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 0.19/0.54  fof(t30_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>v4_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_tops_1)).
% 0.19/0.54  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 0.19/0.54  fof(t48_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X2,X3)=>r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tops_1)).
% 0.19/0.54  fof(c_0_14, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X2,k1_tops_1(X1,X3))<=>?[X4]:(((m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))&v3_pre_topc(X4,X1))&r1_tarski(X4,X3))&r2_hidden(X2,X4)))))), inference(assume_negation,[status(cth)],[t54_tops_1])).
% 0.19/0.54  fof(c_0_15, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.54  fof(c_0_16, negated_conjecture, ![X37]:((v2_pre_topc(esk1_0)&l1_pre_topc(esk1_0))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&((~r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0))|(~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(esk1_0)))|~v3_pre_topc(X37,esk1_0)|~r1_tarski(X37,esk3_0)|~r2_hidden(esk2_0,X37)))&((((m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0)))|r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0)))&(v3_pre_topc(esk4_0,esk1_0)|r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0))))&(r1_tarski(esk4_0,esk3_0)|r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0))))&(r2_hidden(esk2_0,esk4_0)|r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])])])).
% 0.19/0.54  fof(c_0_17, plain, ![X7, X8, X9]:(~r1_tarski(k2_xboole_0(X7,X8),X9)|r1_tarski(X7,X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 0.19/0.54  fof(c_0_18, plain, ![X10, X11]:(~r1_tarski(X10,X11)|k2_xboole_0(X10,X11)=X11), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.19/0.54  cnf(c_0_19, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.54  cnf(c_0_20, negated_conjecture, (~r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~v3_pre_topc(X1,esk1_0)|~r1_tarski(X1,esk3_0)|~r2_hidden(esk2_0,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.54  cnf(c_0_21, negated_conjecture, (r2_hidden(esk2_0,esk4_0)|r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.54  fof(c_0_22, plain, ![X25, X26]:(~v2_pre_topc(X25)|~l1_pre_topc(X25)|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))|v3_pre_topc(k1_tops_1(X25,X26),X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).
% 0.19/0.54  cnf(c_0_23, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.54  cnf(c_0_24, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.54  cnf(c_0_25, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_19])).
% 0.19/0.54  cnf(c_0_26, negated_conjecture, (r2_hidden(esk2_0,esk4_0)|~v3_pre_topc(X1,esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r2_hidden(esk2_0,X1)|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.54  cnf(c_0_27, plain, (v3_pre_topc(k1_tops_1(X1,X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.54  cnf(c_0_28, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.54  cnf(c_0_29, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.54  fof(c_0_30, plain, ![X12, X13, X14]:(((r2_hidden(X12,X14)|~r1_tarski(k2_tarski(X12,X13),X14))&(r2_hidden(X13,X14)|~r1_tarski(k2_tarski(X12,X13),X14)))&(~r2_hidden(X12,X14)|~r2_hidden(X13,X14)|r1_tarski(k2_tarski(X12,X13),X14))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).
% 0.19/0.54  cnf(c_0_31, plain, (r1_tarski(X1,X2)|~r1_tarski(X3,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.54  cnf(c_0_32, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_23, c_0_25])).
% 0.19/0.54  cnf(c_0_33, negated_conjecture, (r2_hidden(esk2_0,esk4_0)|~m1_subset_1(k1_tops_1(esk1_0,X1),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r2_hidden(esk2_0,k1_tops_1(esk1_0,X1))|~r1_tarski(k1_tops_1(esk1_0,X1),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29])])).
% 0.19/0.54  cnf(c_0_34, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.54  fof(c_0_35, plain, ![X23, X24]:(~l1_pre_topc(X23)|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))|m1_subset_1(k1_tops_1(X23,X24),k1_zfmisc_1(u1_struct_0(X23)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_1])])).
% 0.19/0.54  cnf(c_0_36, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_tarski(X1,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.54  cnf(c_0_37, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.19/0.54  cnf(c_0_38, negated_conjecture, (r2_hidden(esk2_0,esk4_0)|~m1_subset_1(k1_tops_1(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_21]), c_0_34])])).
% 0.19/0.54  cnf(c_0_39, plain, (m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.54  fof(c_0_40, plain, ![X29, X30]:(~l1_pre_topc(X29)|(~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))|r1_tarski(k1_tops_1(X29,X30),X30))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).
% 0.19/0.54  cnf(c_0_41, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0)))|r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.54  cnf(c_0_42, plain, (r2_hidden(X1,k2_xboole_0(X2,X3))|~r1_tarski(k2_tarski(X1,X4),X2)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.19/0.54  cnf(c_0_43, plain, (r1_tarski(k2_tarski(X1,X3),X2)|~r2_hidden(X1,X2)|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.54  cnf(c_0_44, negated_conjecture, (r2_hidden(esk2_0,esk4_0)|~r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_29]), c_0_34])])).
% 0.19/0.54  cnf(c_0_45, plain, (r1_tarski(k1_tops_1(X1,X2),X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.54  cnf(c_0_46, negated_conjecture, (r1_tarski(esk4_0,esk3_0)|r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.54  fof(c_0_47, plain, ![X21, X22]:(~l1_pre_topc(X21)|(~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|k1_tops_1(X21,X22)=k3_subset_1(u1_struct_0(X21),k2_pre_topc(X21,k3_subset_1(u1_struct_0(X21),X22))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tops_1])])])).
% 0.19/0.54  fof(c_0_48, plain, ![X19, X20]:((~v4_pre_topc(X20,X19)|k2_pre_topc(X19,X20)=X20|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|~l1_pre_topc(X19))&(~v2_pre_topc(X19)|k2_pre_topc(X19,X20)!=X20|v4_pre_topc(X20,X19)|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|~l1_pre_topc(X19))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).
% 0.19/0.54  fof(c_0_49, plain, ![X15, X16]:(~m1_subset_1(X16,k1_zfmisc_1(X15))|m1_subset_1(k3_subset_1(X15,X16),k1_zfmisc_1(X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 0.19/0.54  cnf(c_0_50, negated_conjecture, (v3_pre_topc(esk4_0,esk1_0)|r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.54  cnf(c_0_51, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0)))|~v3_pre_topc(X1,esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r2_hidden(esk2_0,X1)|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_20, c_0_41])).
% 0.19/0.54  cnf(c_0_52, plain, (r2_hidden(X1,k2_xboole_0(X2,X3))|~r2_hidden(X4,X2)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.19/0.54  cnf(c_0_53, negated_conjecture, (r2_hidden(esk2_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_29]), c_0_34])])).
% 0.19/0.54  cnf(c_0_54, negated_conjecture, (r1_tarski(esk4_0,esk3_0)|~v3_pre_topc(X1,esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r2_hidden(esk2_0,X1)|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_20, c_0_46])).
% 0.19/0.54  cnf(c_0_55, plain, (k1_tops_1(X1,X2)=k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.54  cnf(c_0_56, plain, (k2_pre_topc(X2,X1)=X1|~v4_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.54  cnf(c_0_57, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.19/0.54  fof(c_0_58, plain, ![X27, X28]:((~v3_pre_topc(X28,X27)|v4_pre_topc(k3_subset_1(u1_struct_0(X27),X28),X27)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))|~l1_pre_topc(X27))&(~v4_pre_topc(k3_subset_1(u1_struct_0(X27),X28),X27)|v3_pre_topc(X28,X27)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))|~l1_pre_topc(X27))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_tops_1])])])])).
% 0.19/0.54  cnf(c_0_59, negated_conjecture, (v3_pre_topc(esk4_0,esk1_0)|~v3_pre_topc(X1,esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r2_hidden(esk2_0,X1)|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_20, c_0_50])).
% 0.19/0.54  cnf(c_0_60, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(k1_tops_1(esk1_0,X1),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r2_hidden(esk2_0,k1_tops_1(esk1_0,X1))|~r1_tarski(k1_tops_1(esk1_0,X1),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_27]), c_0_28]), c_0_29])])).
% 0.19/0.54  cnf(c_0_61, negated_conjecture, (r2_hidden(X1,k2_xboole_0(esk4_0,X2))|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.19/0.54  cnf(c_0_62, negated_conjecture, (r1_tarski(esk4_0,esk3_0)|~m1_subset_1(k1_tops_1(esk1_0,X1),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r2_hidden(esk2_0,k1_tops_1(esk1_0,X1))|~r1_tarski(k1_tops_1(esk1_0,X1),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_27]), c_0_28]), c_0_29])])).
% 0.19/0.54  fof(c_0_63, plain, ![X17, X18]:(~m1_subset_1(X18,k1_zfmisc_1(X17))|k3_subset_1(X17,k3_subset_1(X17,X18))=X18), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 0.19/0.54  cnf(c_0_64, plain, (k3_subset_1(u1_struct_0(X1),k3_subset_1(u1_struct_0(X1),X2))=k1_tops_1(X1,X2)|~v4_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57])).
% 0.19/0.54  cnf(c_0_65, plain, (v4_pre_topc(k3_subset_1(u1_struct_0(X2),X1),X2)|~v3_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.19/0.54  cnf(c_0_66, negated_conjecture, (v3_pre_topc(esk4_0,esk1_0)|~v3_pre_topc(k1_tops_1(esk1_0,X1),esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r2_hidden(esk2_0,k1_tops_1(esk1_0,X1))|~r1_tarski(k1_tops_1(esk1_0,X1),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_39]), c_0_29])])).
% 0.19/0.54  cnf(c_0_67, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(k1_tops_1(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_41]), c_0_34])])).
% 0.19/0.54  cnf(c_0_68, negated_conjecture, (r2_hidden(X1,X2)|~r2_hidden(X1,esk4_0)|~r1_tarski(esk4_0,X2)), inference(spm,[status(thm)],[c_0_61, c_0_24])).
% 0.19/0.54  cnf(c_0_69, negated_conjecture, (r1_tarski(esk4_0,esk3_0)|~m1_subset_1(k1_tops_1(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_46]), c_0_34])])).
% 0.19/0.54  cnf(c_0_70, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.19/0.54  cnf(c_0_71, plain, (k3_subset_1(u1_struct_0(X1),k3_subset_1(u1_struct_0(X1),X2))=k1_tops_1(X1,X2)|~v3_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.19/0.54  cnf(c_0_72, negated_conjecture, (v3_pre_topc(esk4_0,esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r2_hidden(esk2_0,k1_tops_1(esk1_0,X1))|~r1_tarski(k1_tops_1(esk1_0,X1),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_27]), c_0_28]), c_0_29])])).
% 0.19/0.54  cnf(c_0_73, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_39]), c_0_29]), c_0_34])])).
% 0.19/0.54  cnf(c_0_74, negated_conjecture, (r2_hidden(esk2_0,X1)|~r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_68, c_0_53])).
% 0.19/0.54  cnf(c_0_75, negated_conjecture, (r1_tarski(esk4_0,esk3_0)|~r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_39]), c_0_29]), c_0_34])])).
% 0.19/0.54  cnf(c_0_76, plain, (k1_tops_1(X1,X2)=X2|~v3_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.19/0.54  cnf(c_0_77, negated_conjecture, (v3_pre_topc(esk4_0,esk1_0)|~r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_50]), c_0_34])])).
% 0.19/0.54  cnf(c_0_78, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_45]), c_0_29]), c_0_34])])).
% 0.19/0.54  cnf(c_0_79, negated_conjecture, (~v3_pre_topc(X1,esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r2_hidden(esk2_0,X1)|~r1_tarski(esk4_0,k1_tops_1(esk1_0,esk3_0))|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_20, c_0_74])).
% 0.19/0.54  cnf(c_0_80, negated_conjecture, (r1_tarski(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_45]), c_0_29]), c_0_34])])).
% 0.19/0.54  fof(c_0_81, plain, ![X31, X32, X33]:(~l1_pre_topc(X31)|(~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))|(~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X31)))|(~r1_tarski(X32,X33)|r1_tarski(k1_tops_1(X31,X32),k1_tops_1(X31,X33)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).
% 0.19/0.54  cnf(c_0_82, negated_conjecture, (k1_tops_1(esk1_0,esk4_0)=esk4_0|~r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_29]), c_0_78])])).
% 0.19/0.54  cnf(c_0_83, negated_conjecture, (~r1_tarski(esk4_0,k1_tops_1(esk1_0,esk3_0))|~r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_77]), c_0_78]), c_0_53]), c_0_80])])).
% 0.19/0.54  cnf(c_0_84, plain, (r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.19/0.54  cnf(c_0_85, negated_conjecture, (k1_tops_1(esk1_0,esk4_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_45]), c_0_29]), c_0_34])])).
% 0.19/0.54  cnf(c_0_86, negated_conjecture, (~r1_tarski(esk4_0,k1_tops_1(esk1_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_45]), c_0_29]), c_0_34])])).
% 0.19/0.54  cnf(c_0_87, negated_conjecture, (r1_tarski(esk4_0,k1_tops_1(esk1_0,X1))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_29]), c_0_78])])).
% 0.19/0.54  cnf(c_0_88, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_34]), c_0_80])]), ['proof']).
% 0.19/0.54  # SZS output end CNFRefutation
% 0.19/0.54  # Proof object total steps             : 89
% 0.19/0.54  # Proof object clause steps            : 60
% 0.19/0.54  # Proof object formula steps           : 29
% 0.19/0.54  # Proof object conjectures             : 40
% 0.19/0.54  # Proof object clause conjectures      : 37
% 0.19/0.54  # Proof object formula conjectures     : 3
% 0.19/0.54  # Proof object initial clauses used    : 22
% 0.19/0.54  # Proof object initial formulas used   : 14
% 0.19/0.54  # Proof object generating inferences   : 37
% 0.19/0.54  # Proof object simplifying inferences  : 61
% 0.19/0.54  # Training examples: 0 positive, 0 negative
% 0.19/0.54  # Parsed axioms                        : 14
% 0.19/0.54  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.54  # Initial clauses                      : 27
% 0.19/0.54  # Removed in clause preprocessing      : 0
% 0.19/0.54  # Initial clauses in saturation        : 27
% 0.19/0.54  # Processed clauses                    : 1937
% 0.19/0.54  # ...of these trivial                  : 19
% 0.19/0.54  # ...subsumed                          : 1208
% 0.19/0.54  # ...remaining for further processing  : 710
% 0.19/0.54  # Other redundant clauses eliminated   : 2
% 0.19/0.54  # Clauses deleted for lack of memory   : 0
% 0.19/0.54  # Backward-subsumed                    : 54
% 0.19/0.54  # Backward-rewritten                   : 145
% 0.19/0.54  # Generated clauses                    : 6040
% 0.19/0.54  # ...of the previous two non-trivial   : 5808
% 0.19/0.54  # Contextual simplify-reflections      : 31
% 0.19/0.54  # Paramodulations                      : 6038
% 0.19/0.54  # Factorizations                       : 0
% 0.19/0.54  # Equation resolutions                 : 2
% 0.19/0.54  # Propositional unsat checks           : 0
% 0.19/0.54  #    Propositional check models        : 0
% 0.19/0.54  #    Propositional check unsatisfiable : 0
% 0.19/0.54  #    Propositional clauses             : 0
% 0.19/0.54  #    Propositional clauses after purity: 0
% 0.19/0.54  #    Propositional unsat core size     : 0
% 0.19/0.54  #    Propositional preprocessing time  : 0.000
% 0.19/0.54  #    Propositional encoding time       : 0.000
% 0.19/0.54  #    Propositional solver time         : 0.000
% 0.19/0.54  #    Success case prop preproc time    : 0.000
% 0.19/0.54  #    Success case prop encoding time   : 0.000
% 0.19/0.54  #    Success case prop solver time     : 0.000
% 0.19/0.54  # Current number of processed clauses  : 483
% 0.19/0.54  #    Positive orientable unit clauses  : 32
% 0.19/0.54  #    Positive unorientable unit clauses: 0
% 0.19/0.54  #    Negative unit clauses             : 3
% 0.19/0.54  #    Non-unit-clauses                  : 448
% 0.19/0.54  # Current number of unprocessed clauses: 3840
% 0.19/0.54  # ...number of literals in the above   : 16630
% 0.19/0.54  # Current number of archived formulas  : 0
% 0.19/0.54  # Current number of archived clauses   : 225
% 0.19/0.54  # Clause-clause subsumption calls (NU) : 77601
% 0.19/0.54  # Rec. Clause-clause subsumption calls : 37189
% 0.19/0.54  # Non-unit clause-clause subsumptions  : 1001
% 0.19/0.54  # Unit Clause-clause subsumption calls : 440
% 0.19/0.54  # Rewrite failures with RHS unbound    : 0
% 0.19/0.54  # BW rewrite match attempts            : 47
% 0.19/0.54  # BW rewrite match successes           : 8
% 0.19/0.54  # Condensation attempts                : 0
% 0.19/0.54  # Condensation successes               : 0
% 0.19/0.54  # Termbank termtop insertions          : 110244
% 0.19/0.54  
% 0.19/0.54  # -------------------------------------------------
% 0.19/0.54  # User time                : 0.196 s
% 0.19/0.54  # System time              : 0.004 s
% 0.19/0.54  # Total time               : 0.200 s
% 0.19/0.54  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------

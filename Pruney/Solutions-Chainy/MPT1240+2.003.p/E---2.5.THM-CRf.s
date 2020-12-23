%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:10:58 EST 2020

% Result     : Theorem 0.42s
% Output     : CNFRefutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 841 expanded)
%              Number of clauses        :   84 ( 331 expanded)
%              Number of leaves         :   18 ( 203 expanded)
%              Depth                    :   17
%              Number of atoms          :  408 (4811 expanded)
%              Number of equality atoms :   27 (  42 expanded)
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

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(fc9_tops_1,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => v3_pre_topc(k1_tops_1(X1,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(t44_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(k1_tops_1(X1,X2),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(dt_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k7_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_subset_1)).

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

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(t31_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r1_tarski(X2,X3)
          <=> r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

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

fof(t29_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v4_pre_topc(X2,X1)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

fof(c_0_18,negated_conjecture,(
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

fof(c_0_19,negated_conjecture,(
    ! [X55] :
      ( v2_pre_topc(esk2_0)
      & l1_pre_topc(esk2_0)
      & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
      & ( ~ r2_hidden(esk3_0,k1_tops_1(esk2_0,esk4_0))
        | ~ m1_subset_1(X55,k1_zfmisc_1(u1_struct_0(esk2_0)))
        | ~ v3_pre_topc(X55,esk2_0)
        | ~ r1_tarski(X55,esk4_0)
        | ~ r2_hidden(esk3_0,X55) )
      & ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
        | r2_hidden(esk3_0,k1_tops_1(esk2_0,esk4_0)) )
      & ( v3_pre_topc(esk5_0,esk2_0)
        | r2_hidden(esk3_0,k1_tops_1(esk2_0,esk4_0)) )
      & ( r1_tarski(esk5_0,esk4_0)
        | r2_hidden(esk3_0,k1_tops_1(esk2_0,esk4_0)) )
      & ( r2_hidden(esk3_0,esk5_0)
        | r2_hidden(esk3_0,k1_tops_1(esk2_0,esk4_0)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])])])).

fof(c_0_20,plain,(
    ! [X13,X14,X15] :
      ( ~ r1_tarski(X13,X14)
      | ~ r1_tarski(X14,X15)
      | r1_tarski(X13,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_21,plain,(
    ! [X37,X38] :
      ( ( ~ m1_subset_1(X37,k1_zfmisc_1(X38))
        | r1_tarski(X37,X38) )
      & ( ~ r1_tarski(X37,X38)
        | m1_subset_1(X37,k1_zfmisc_1(X38)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_22,negated_conjecture,
    ( ~ r2_hidden(esk3_0,k1_tops_1(esk2_0,esk4_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v3_pre_topc(X1,esk2_0)
    | ~ r1_tarski(X1,esk4_0)
    | ~ r2_hidden(esk3_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | r2_hidden(esk3_0,k1_tops_1(esk2_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_24,plain,(
    ! [X43,X44] :
      ( ~ v2_pre_topc(X43)
      | ~ l1_pre_topc(X43)
      | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43)))
      | v3_pre_topc(k1_tops_1(X43,X44),X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v3_pre_topc(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r2_hidden(esk3_0,X1)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,plain,
    ( v3_pre_topc(k1_tops_1(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(k1_tops_1(esk2_0,X1),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r2_hidden(esk3_0,k1_tops_1(esk2_0,X1))
    | ~ r1_tarski(k1_tops_1(esk2_0,X1),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29]),c_0_30])])).

cnf(c_0_34,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk2_0))
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0)
    | r2_hidden(esk3_0,k1_tops_1(esk2_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(k1_tops_1(esk2_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_tarski(k1_tops_1(esk2_0,esk4_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_23]),c_0_32])])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

fof(c_0_39,plain,(
    ! [X47,X48] :
      ( ~ l1_pre_topc(X47)
      | ~ m1_subset_1(X48,k1_zfmisc_1(u1_struct_0(X47)))
      | r1_tarski(k1_tops_1(X47,X48),X48) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).

fof(c_0_40,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(esk5_0,esk4_0)
    | r2_hidden(esk3_0,k1_tops_1(esk2_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0)
    | ~ v3_pre_topc(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r2_hidden(esk3_0,X1)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_36])).

fof(c_0_43,plain,(
    ! [X25,X26,X27] :
      ( ~ m1_subset_1(X26,k1_zfmisc_1(X25))
      | ~ r2_hidden(X27,X26)
      | r2_hidden(X27,X25) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_tarski(k1_tops_1(esk2_0,esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_45,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_47,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(esk5_0,esk4_0)
    | ~ v3_pre_topc(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r2_hidden(esk3_0,X1)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_41])).

cnf(c_0_49,negated_conjecture,
    ( v3_pre_topc(esk5_0,esk2_0)
    | r2_hidden(esk3_0,k1_tops_1(esk2_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_50,plain,(
    ! [X20,X21,X22] :
      ( ~ m1_subset_1(X21,k1_zfmisc_1(X20))
      | m1_subset_1(k7_subset_1(X20,X21,X22),k1_zfmisc_1(X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_subset_1])])).

fof(c_0_51,plain,(
    ! [X49,X50,X51] :
      ( ~ l1_pre_topc(X49)
      | ~ m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X49)))
      | ~ m1_subset_1(X51,k1_zfmisc_1(u1_struct_0(X49)))
      | ~ r1_tarski(X50,X51)
      | r1_tarski(k1_tops_1(X49,X50),k1_tops_1(X49,X51)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0)
    | ~ m1_subset_1(k1_tops_1(esk2_0,X1),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r2_hidden(esk3_0,k1_tops_1(esk2_0,X1))
    | ~ r1_tarski(k1_tops_1(esk2_0,X1),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_28]),c_0_29]),c_0_30])])).

cnf(c_0_53,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_30]),c_0_32])])).

cnf(c_0_55,plain,
    ( r2_hidden(esk1_2(X1,X2),X3)
    | r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(esk5_0,esk4_0)
    | ~ m1_subset_1(k1_tops_1(esk2_0,X1),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r2_hidden(esk3_0,k1_tops_1(esk2_0,X1))
    | ~ r1_tarski(k1_tops_1(esk2_0,X1),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_28]),c_0_29]),c_0_30])])).

cnf(c_0_57,negated_conjecture,
    ( v3_pre_topc(esk5_0,esk2_0)
    | ~ v3_pre_topc(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r2_hidden(esk3_0,X1)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_49])).

cnf(c_0_58,plain,
    ( m1_subset_1(k7_subset_1(X2,X1,X3),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

fof(c_0_59,plain,(
    ! [X28,X29,X30] :
      ( ~ m1_subset_1(X29,k1_zfmisc_1(X28))
      | k7_subset_1(X28,X29,X30) = k4_xboole_0(X29,X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

cnf(c_0_60,plain,
    ( r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0)
    | ~ m1_subset_1(k1_tops_1(esk2_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_tarski(k1_tops_1(esk2_0,esk4_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_36]),c_0_32])])).

fof(c_0_62,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_63,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_65,plain,
    ( r2_hidden(esk1_2(k1_tops_1(X1,X2),X3),X2)
    | r1_tarski(k1_tops_1(X1,X2),X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_45])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(esk5_0,esk4_0)
    | ~ m1_subset_1(k1_tops_1(esk2_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_tarski(k1_tops_1(esk2_0,esk4_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_41]),c_0_32])])).

cnf(c_0_67,negated_conjecture,
    ( v3_pre_topc(esk5_0,esk2_0)
    | ~ v3_pre_topc(k7_subset_1(u1_struct_0(esk2_0),X1,X2),esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r2_hidden(esk3_0,k7_subset_1(u1_struct_0(esk2_0),X1,X2))
    | ~ r1_tarski(k7_subset_1(u1_struct_0(esk2_0),X1,X2),esk4_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_68,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

fof(c_0_69,plain,(
    ! [X16,X17] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(X16))
      | k3_subset_1(X16,X17) = k4_xboole_0(X16,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_70,plain,
    ( m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(k1_tops_1(X1,X3)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_34,c_0_60])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0)
    | ~ r1_tarski(k1_tops_1(esk2_0,esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_38])).

cnf(c_0_72,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_73,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(esk1_2(X1,u1_struct_0(esk2_0)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(esk1_2(k1_tops_1(esk2_0,esk5_0),X1),esk5_0)
    | r1_tarski(k1_tops_1(esk2_0,esk5_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_54]),c_0_30])])).

cnf(c_0_75,negated_conjecture,
    ( r1_tarski(esk5_0,esk4_0)
    | ~ r1_tarski(k1_tops_1(esk2_0,esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_38])).

cnf(c_0_76,negated_conjecture,
    ( v3_pre_topc(esk5_0,esk2_0)
    | ~ v3_pre_topc(k4_xboole_0(X1,X2),esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r2_hidden(esk3_0,k4_xboole_0(X1,X2))
    | ~ r1_tarski(k4_xboole_0(X1,X2),esk4_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_77,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

fof(c_0_78,plain,(
    ! [X23,X24] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(X23))
      | k3_subset_1(X23,k3_subset_1(X23,X24)) = X24 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

fof(c_0_79,plain,(
    ! [X18,X19] :
      ( ~ m1_subset_1(X19,k1_zfmisc_1(X18))
      | m1_subset_1(k3_subset_1(X18,X19),k1_zfmisc_1(X18)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

cnf(c_0_80,plain,
    ( r2_hidden(X1,k1_tops_1(X2,X3))
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X1,k1_tops_1(X2,X4))
    | ~ r1_tarski(X4,X3) ),
    inference(spm,[status(thm)],[c_0_53,c_0_70])).

cnf(c_0_81,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_45]),c_0_30]),c_0_32])])).

cnf(c_0_82,plain,
    ( k1_tops_1(X1,X2) = X2
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,k1_tops_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_45])).

cnf(c_0_83,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk2_0,esk5_0),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_84,negated_conjecture,
    ( r1_tarski(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_45]),c_0_30]),c_0_32])])).

cnf(c_0_85,negated_conjecture,
    ( v3_pre_topc(esk5_0,esk2_0)
    | ~ v3_pre_topc(k3_subset_1(X1,X2),esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(esk3_0,k3_subset_1(X1,X2))
    | ~ r1_tarski(k3_subset_1(X1,X2),esk4_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_86,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_87,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

fof(c_0_88,plain,(
    ! [X31,X32,X33] :
      ( ( ~ r1_tarski(X32,X33)
        | r1_tarski(k3_subset_1(X31,X33),k3_subset_1(X31,X32))
        | ~ m1_subset_1(X33,k1_zfmisc_1(X31))
        | ~ m1_subset_1(X32,k1_zfmisc_1(X31)) )
      & ( ~ r1_tarski(k3_subset_1(X31,X33),k3_subset_1(X31,X32))
        | r1_tarski(X32,X33)
        | ~ m1_subset_1(X33,k1_zfmisc_1(X31))
        | ~ m1_subset_1(X32,k1_zfmisc_1(X31)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_subset_1])])])])).

fof(c_0_89,plain,(
    ! [X41,X42] :
      ( ~ l1_pre_topc(X41)
      | ~ m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))
      | k1_tops_1(X41,X42) = k3_subset_1(u1_struct_0(X41),k2_pre_topc(X41,k3_subset_1(u1_struct_0(X41),X42))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tops_1])])])).

fof(c_0_90,plain,(
    ! [X39,X40] :
      ( ( ~ v4_pre_topc(X40,X39)
        | k2_pre_topc(X39,X40) = X40
        | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))
        | ~ l1_pre_topc(X39) )
      & ( ~ v2_pre_topc(X39)
        | k2_pre_topc(X39,X40) != X40
        | v4_pre_topc(X40,X39)
        | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))
        | ~ l1_pre_topc(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).

fof(c_0_91,plain,(
    ! [X45,X46] :
      ( ( ~ v4_pre_topc(X46,X45)
        | v3_pre_topc(k3_subset_1(u1_struct_0(X45),X46),X45)
        | ~ m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))
        | ~ l1_pre_topc(X45) )
      & ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X45),X46),X45)
        | v4_pre_topc(X46,X45)
        | ~ m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))
        | ~ l1_pre_topc(X45) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_tops_1])])])])).

cnf(c_0_92,negated_conjecture,
    ( r2_hidden(X1,k1_tops_1(esk2_0,esk4_0))
    | ~ r2_hidden(X1,k1_tops_1(esk2_0,X2))
    | ~ r1_tarski(X2,esk4_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_32]),c_0_30])]),c_0_38])).

cnf(c_0_93,negated_conjecture,
    ( r2_hidden(esk3_0,X1)
    | ~ r1_tarski(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_81])).

cnf(c_0_94,plain,
    ( k1_tops_1(X1,k1_tops_1(X1,X2)) = k1_tops_1(X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,k1_tops_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_82,c_0_60])).

cnf(c_0_95,negated_conjecture,
    ( m1_subset_1(k1_tops_1(esk2_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_83])).

cnf(c_0_96,negated_conjecture,
    ( r1_tarski(X1,esk4_0)
    | ~ r1_tarski(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_84])).

cnf(c_0_97,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk2_0,esk5_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_74])).

cnf(c_0_98,negated_conjecture,
    ( v3_pre_topc(esk5_0,esk2_0)
    | ~ v3_pre_topc(X1,esk2_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(esk3_0,X1)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_87])).

cnf(c_0_99,plain,
    ( r1_tarski(X3,X2)
    | ~ r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

cnf(c_0_100,plain,
    ( k1_tops_1(X1,X2) = k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_89])).

cnf(c_0_101,plain,
    ( k2_pre_topc(X2,X1) = X1
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_102,plain,
    ( v4_pre_topc(X2,X1)
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_91])).

cnf(c_0_103,negated_conjecture,
    ( r2_hidden(esk3_0,k1_tops_1(esk2_0,esk4_0))
    | ~ r1_tarski(esk5_0,k1_tops_1(esk2_0,X1))
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_104,negated_conjecture,
    ( k1_tops_1(esk2_0,k1_tops_1(esk2_0,esk5_0)) = k1_tops_1(esk2_0,esk5_0)
    | ~ r1_tarski(esk5_0,k1_tops_1(esk2_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_30]),c_0_54])])).

cnf(c_0_105,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk2_0,esk5_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_96,c_0_97])).

cnf(c_0_106,negated_conjecture,
    ( v3_pre_topc(esk5_0,esk2_0)
    | ~ v3_pre_topc(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk4_0))
    | ~ r2_hidden(esk3_0,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_32]),c_0_26])).

cnf(c_0_107,plain,
    ( m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_45])).

cnf(c_0_108,plain,
    ( r1_tarski(X1,k3_subset_1(X2,X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_tarski(X3,k3_subset_1(X2,X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_86]),c_0_87])).

cnf(c_0_109,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_47])).

cnf(c_0_110,plain,
    ( k3_subset_1(u1_struct_0(X1),k3_subset_1(u1_struct_0(X1),X2)) = k1_tops_1(X1,X2)
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_87])).

cnf(c_0_111,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_86]),c_0_87])).

cnf(c_0_112,negated_conjecture,
    ( r2_hidden(esk3_0,k1_tops_1(esk2_0,esk4_0))
    | ~ r1_tarski(esk5_0,k1_tops_1(esk2_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_104]),c_0_105])])).

cnf(c_0_113,negated_conjecture,
    ( v3_pre_topc(esk5_0,esk2_0)
    | ~ v3_pre_topc(k1_tops_1(X1,esk4_0),esk2_0)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(esk3_0,k1_tops_1(X1,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_106,c_0_107])).

cnf(c_0_114,plain,
    ( r1_tarski(X1,k3_subset_1(X2,k3_subset_1(X2,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_109]),c_0_87])).

cnf(c_0_115,plain,
    ( k3_subset_1(u1_struct_0(X1),k3_subset_1(u1_struct_0(X1),X2)) = k1_tops_1(X1,X2)
    | ~ v3_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_110,c_0_111])).

cnf(c_0_116,negated_conjecture,
    ( ~ v3_pre_topc(X1,esk2_0)
    | ~ r2_hidden(esk3_0,X1)
    | ~ r1_tarski(esk5_0,k1_tops_1(esk2_0,esk5_0))
    | ~ r1_tarski(X1,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_112]),c_0_38])).

cnf(c_0_117,negated_conjecture,
    ( v3_pre_topc(esk5_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_28]),c_0_30]),c_0_32]),c_0_29])]),c_0_49])).

cnf(c_0_118,plain,
    ( r1_tarski(X1,k1_tops_1(X2,X1))
    | ~ v3_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(spm,[status(thm)],[c_0_114,c_0_115])).

cnf(c_0_119,negated_conjecture,
    ( ~ r1_tarski(esk5_0,k1_tops_1(esk2_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_117]),c_0_81]),c_0_84])])).

cnf(c_0_120,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_54]),c_0_117]),c_0_30])]),c_0_119]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n015.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:28:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.42/0.61  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 0.42/0.61  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.42/0.61  #
% 0.42/0.61  # Preprocessing time       : 0.029 s
% 0.42/0.61  
% 0.42/0.61  # Proof found!
% 0.42/0.61  # SZS status Theorem
% 0.42/0.61  # SZS output start CNFRefutation
% 0.42/0.61  fof(t54_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X2,k1_tops_1(X1,X3))<=>?[X4]:(((m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))&v3_pre_topc(X4,X1))&r1_tarski(X4,X3))&r2_hidden(X2,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_tops_1)).
% 0.42/0.61  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.42/0.61  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.42/0.61  fof(fc9_tops_1, axiom, ![X1, X2]:(((v2_pre_topc(X1)&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v3_pre_topc(k1_tops_1(X1,X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 0.42/0.61  fof(t44_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,X2),X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 0.42/0.61  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.42/0.61  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 0.42/0.61  fof(dt_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k7_subset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_subset_1)).
% 0.42/0.61  fof(t48_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X2,X3)=>r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tops_1)).
% 0.42/0.61  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 0.42/0.61  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.42/0.61  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 0.42/0.61  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 0.42/0.61  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 0.42/0.61  fof(t31_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_tarski(X2,X3)<=>r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 0.42/0.61  fof(d1_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k1_tops_1(X1,X2)=k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_1)).
% 0.42/0.61  fof(t52_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v4_pre_topc(X2,X1)=>k2_pre_topc(X1,X2)=X2)&((v2_pre_topc(X1)&k2_pre_topc(X1,X2)=X2)=>v4_pre_topc(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 0.42/0.61  fof(t29_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)<=>v3_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_tops_1)).
% 0.42/0.61  fof(c_0_18, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X2,k1_tops_1(X1,X3))<=>?[X4]:(((m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))&v3_pre_topc(X4,X1))&r1_tarski(X4,X3))&r2_hidden(X2,X4)))))), inference(assume_negation,[status(cth)],[t54_tops_1])).
% 0.42/0.61  fof(c_0_19, negated_conjecture, ![X55]:((v2_pre_topc(esk2_0)&l1_pre_topc(esk2_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&((~r2_hidden(esk3_0,k1_tops_1(esk2_0,esk4_0))|(~m1_subset_1(X55,k1_zfmisc_1(u1_struct_0(esk2_0)))|~v3_pre_topc(X55,esk2_0)|~r1_tarski(X55,esk4_0)|~r2_hidden(esk3_0,X55)))&((((m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0)))|r2_hidden(esk3_0,k1_tops_1(esk2_0,esk4_0)))&(v3_pre_topc(esk5_0,esk2_0)|r2_hidden(esk3_0,k1_tops_1(esk2_0,esk4_0))))&(r1_tarski(esk5_0,esk4_0)|r2_hidden(esk3_0,k1_tops_1(esk2_0,esk4_0))))&(r2_hidden(esk3_0,esk5_0)|r2_hidden(esk3_0,k1_tops_1(esk2_0,esk4_0))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])])])).
% 0.42/0.61  fof(c_0_20, plain, ![X13, X14, X15]:(~r1_tarski(X13,X14)|~r1_tarski(X14,X15)|r1_tarski(X13,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.42/0.61  fof(c_0_21, plain, ![X37, X38]:((~m1_subset_1(X37,k1_zfmisc_1(X38))|r1_tarski(X37,X38))&(~r1_tarski(X37,X38)|m1_subset_1(X37,k1_zfmisc_1(X38)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.42/0.61  cnf(c_0_22, negated_conjecture, (~r2_hidden(esk3_0,k1_tops_1(esk2_0,esk4_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~v3_pre_topc(X1,esk2_0)|~r1_tarski(X1,esk4_0)|~r2_hidden(esk3_0,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.42/0.61  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0)))|r2_hidden(esk3_0,k1_tops_1(esk2_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.42/0.61  fof(c_0_24, plain, ![X43, X44]:(~v2_pre_topc(X43)|~l1_pre_topc(X43)|~m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43)))|v3_pre_topc(k1_tops_1(X43,X44),X43)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).
% 0.42/0.61  cnf(c_0_25, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.42/0.61  cnf(c_0_26, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.42/0.61  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0)))|~v3_pre_topc(X1,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r2_hidden(esk3_0,X1)|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.42/0.61  cnf(c_0_28, plain, (v3_pre_topc(k1_tops_1(X1,X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.42/0.61  cnf(c_0_29, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.42/0.61  cnf(c_0_30, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.42/0.61  cnf(c_0_31, plain, (r1_tarski(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.42/0.61  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.42/0.61  cnf(c_0_33, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(k1_tops_1(esk2_0,X1),k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r2_hidden(esk3_0,k1_tops_1(esk2_0,X1))|~r1_tarski(k1_tops_1(esk2_0,X1),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29]), c_0_30])])).
% 0.42/0.61  cnf(c_0_34, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.42/0.61  cnf(c_0_35, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk2_0))|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.42/0.61  cnf(c_0_36, negated_conjecture, (r2_hidden(esk3_0,esk5_0)|r2_hidden(esk3_0,k1_tops_1(esk2_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.42/0.61  cnf(c_0_37, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(k1_tops_1(esk2_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0)))|~r1_tarski(k1_tops_1(esk2_0,esk4_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_23]), c_0_32])])).
% 0.42/0.61  cnf(c_0_38, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.42/0.61  fof(c_0_39, plain, ![X47, X48]:(~l1_pre_topc(X47)|(~m1_subset_1(X48,k1_zfmisc_1(u1_struct_0(X47)))|r1_tarski(k1_tops_1(X47,X48),X48))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).
% 0.42/0.61  fof(c_0_40, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.42/0.61  cnf(c_0_41, negated_conjecture, (r1_tarski(esk5_0,esk4_0)|r2_hidden(esk3_0,k1_tops_1(esk2_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.42/0.61  cnf(c_0_42, negated_conjecture, (r2_hidden(esk3_0,esk5_0)|~v3_pre_topc(X1,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r2_hidden(esk3_0,X1)|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_22, c_0_36])).
% 0.42/0.61  fof(c_0_43, plain, ![X25, X26, X27]:(~m1_subset_1(X26,k1_zfmisc_1(X25))|(~r2_hidden(X27,X26)|r2_hidden(X27,X25))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.42/0.61  cnf(c_0_44, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r1_tarski(k1_tops_1(esk2_0,esk4_0),esk4_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.42/0.61  cnf(c_0_45, plain, (r1_tarski(k1_tops_1(X1,X2),X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.42/0.61  cnf(c_0_46, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.42/0.61  cnf(c_0_47, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.42/0.61  cnf(c_0_48, negated_conjecture, (r1_tarski(esk5_0,esk4_0)|~v3_pre_topc(X1,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r2_hidden(esk3_0,X1)|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_22, c_0_41])).
% 0.42/0.61  cnf(c_0_49, negated_conjecture, (v3_pre_topc(esk5_0,esk2_0)|r2_hidden(esk3_0,k1_tops_1(esk2_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.42/0.61  fof(c_0_50, plain, ![X20, X21, X22]:(~m1_subset_1(X21,k1_zfmisc_1(X20))|m1_subset_1(k7_subset_1(X20,X21,X22),k1_zfmisc_1(X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_subset_1])])).
% 0.42/0.61  fof(c_0_51, plain, ![X49, X50, X51]:(~l1_pre_topc(X49)|(~m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X49)))|(~m1_subset_1(X51,k1_zfmisc_1(u1_struct_0(X49)))|(~r1_tarski(X50,X51)|r1_tarski(k1_tops_1(X49,X50),k1_tops_1(X49,X51)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).
% 0.42/0.61  cnf(c_0_52, negated_conjecture, (r2_hidden(esk3_0,esk5_0)|~m1_subset_1(k1_tops_1(esk2_0,X1),k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r2_hidden(esk3_0,k1_tops_1(esk2_0,X1))|~r1_tarski(k1_tops_1(esk2_0,X1),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_28]), c_0_29]), c_0_30])])).
% 0.42/0.61  cnf(c_0_53, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.42/0.61  cnf(c_0_54, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_30]), c_0_32])])).
% 0.42/0.61  cnf(c_0_55, plain, (r2_hidden(esk1_2(X1,X2),X3)|r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.42/0.61  cnf(c_0_56, negated_conjecture, (r1_tarski(esk5_0,esk4_0)|~m1_subset_1(k1_tops_1(esk2_0,X1),k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r2_hidden(esk3_0,k1_tops_1(esk2_0,X1))|~r1_tarski(k1_tops_1(esk2_0,X1),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_28]), c_0_29]), c_0_30])])).
% 0.42/0.61  cnf(c_0_57, negated_conjecture, (v3_pre_topc(esk5_0,esk2_0)|~v3_pre_topc(X1,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r2_hidden(esk3_0,X1)|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_22, c_0_49])).
% 0.42/0.61  cnf(c_0_58, plain, (m1_subset_1(k7_subset_1(X2,X1,X3),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.42/0.61  fof(c_0_59, plain, ![X28, X29, X30]:(~m1_subset_1(X29,k1_zfmisc_1(X28))|k7_subset_1(X28,X29,X30)=k4_xboole_0(X29,X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 0.42/0.61  cnf(c_0_60, plain, (r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.42/0.61  cnf(c_0_61, negated_conjecture, (r2_hidden(esk3_0,esk5_0)|~m1_subset_1(k1_tops_1(esk2_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0)))|~r1_tarski(k1_tops_1(esk2_0,esk4_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_36]), c_0_32])])).
% 0.42/0.61  fof(c_0_62, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.42/0.61  cnf(c_0_63, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.42/0.61  cnf(c_0_64, negated_conjecture, (r2_hidden(X1,u1_struct_0(esk2_0))|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.42/0.61  cnf(c_0_65, plain, (r2_hidden(esk1_2(k1_tops_1(X1,X2),X3),X2)|r1_tarski(k1_tops_1(X1,X2),X3)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_55, c_0_45])).
% 0.42/0.61  cnf(c_0_66, negated_conjecture, (r1_tarski(esk5_0,esk4_0)|~m1_subset_1(k1_tops_1(esk2_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0)))|~r1_tarski(k1_tops_1(esk2_0,esk4_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_41]), c_0_32])])).
% 0.42/0.61  cnf(c_0_67, negated_conjecture, (v3_pre_topc(esk5_0,esk2_0)|~v3_pre_topc(k7_subset_1(u1_struct_0(esk2_0),X1,X2),esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r2_hidden(esk3_0,k7_subset_1(u1_struct_0(esk2_0),X1,X2))|~r1_tarski(k7_subset_1(u1_struct_0(esk2_0),X1,X2),esk4_0)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.42/0.61  cnf(c_0_68, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.42/0.61  fof(c_0_69, plain, ![X16, X17]:(~m1_subset_1(X17,k1_zfmisc_1(X16))|k3_subset_1(X16,X17)=k4_xboole_0(X16,X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.42/0.61  cnf(c_0_70, plain, (m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(k1_tops_1(X1,X3)))|~l1_pre_topc(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_34, c_0_60])).
% 0.42/0.61  cnf(c_0_71, negated_conjecture, (r2_hidden(esk3_0,esk5_0)|~r1_tarski(k1_tops_1(esk2_0,esk4_0),esk4_0)), inference(spm,[status(thm)],[c_0_61, c_0_38])).
% 0.42/0.61  cnf(c_0_72, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.42/0.61  cnf(c_0_73, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk2_0))|~r2_hidden(esk1_2(X1,u1_struct_0(esk2_0)),esk5_0)), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.42/0.61  cnf(c_0_74, negated_conjecture, (r2_hidden(esk1_2(k1_tops_1(esk2_0,esk5_0),X1),esk5_0)|r1_tarski(k1_tops_1(esk2_0,esk5_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_54]), c_0_30])])).
% 0.42/0.61  cnf(c_0_75, negated_conjecture, (r1_tarski(esk5_0,esk4_0)|~r1_tarski(k1_tops_1(esk2_0,esk4_0),esk4_0)), inference(spm,[status(thm)],[c_0_66, c_0_38])).
% 0.42/0.61  cnf(c_0_76, negated_conjecture, (v3_pre_topc(esk5_0,esk2_0)|~v3_pre_topc(k4_xboole_0(X1,X2),esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r2_hidden(esk3_0,k4_xboole_0(X1,X2))|~r1_tarski(k4_xboole_0(X1,X2),esk4_0)), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.42/0.61  cnf(c_0_77, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.42/0.61  fof(c_0_78, plain, ![X23, X24]:(~m1_subset_1(X24,k1_zfmisc_1(X23))|k3_subset_1(X23,k3_subset_1(X23,X24))=X24), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 0.42/0.61  fof(c_0_79, plain, ![X18, X19]:(~m1_subset_1(X19,k1_zfmisc_1(X18))|m1_subset_1(k3_subset_1(X18,X19),k1_zfmisc_1(X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 0.42/0.61  cnf(c_0_80, plain, (r2_hidden(X1,k1_tops_1(X2,X3))|~l1_pre_topc(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|~r2_hidden(X1,k1_tops_1(X2,X4))|~r1_tarski(X4,X3)), inference(spm,[status(thm)],[c_0_53, c_0_70])).
% 0.42/0.61  cnf(c_0_81, negated_conjecture, (r2_hidden(esk3_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_45]), c_0_30]), c_0_32])])).
% 0.42/0.61  cnf(c_0_82, plain, (k1_tops_1(X1,X2)=X2|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X2,k1_tops_1(X1,X2))), inference(spm,[status(thm)],[c_0_72, c_0_45])).
% 0.42/0.61  cnf(c_0_83, negated_conjecture, (r1_tarski(k1_tops_1(esk2_0,esk5_0),u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.42/0.61  cnf(c_0_84, negated_conjecture, (r1_tarski(esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_45]), c_0_30]), c_0_32])])).
% 0.42/0.61  cnf(c_0_85, negated_conjecture, (v3_pre_topc(esk5_0,esk2_0)|~v3_pre_topc(k3_subset_1(X1,X2),esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r2_hidden(esk3_0,k3_subset_1(X1,X2))|~r1_tarski(k3_subset_1(X1,X2),esk4_0)), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.42/0.61  cnf(c_0_86, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.42/0.61  cnf(c_0_87, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.42/0.61  fof(c_0_88, plain, ![X31, X32, X33]:((~r1_tarski(X32,X33)|r1_tarski(k3_subset_1(X31,X33),k3_subset_1(X31,X32))|~m1_subset_1(X33,k1_zfmisc_1(X31))|~m1_subset_1(X32,k1_zfmisc_1(X31)))&(~r1_tarski(k3_subset_1(X31,X33),k3_subset_1(X31,X32))|r1_tarski(X32,X33)|~m1_subset_1(X33,k1_zfmisc_1(X31))|~m1_subset_1(X32,k1_zfmisc_1(X31)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_subset_1])])])])).
% 0.42/0.61  fof(c_0_89, plain, ![X41, X42]:(~l1_pre_topc(X41)|(~m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))|k1_tops_1(X41,X42)=k3_subset_1(u1_struct_0(X41),k2_pre_topc(X41,k3_subset_1(u1_struct_0(X41),X42))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tops_1])])])).
% 0.42/0.61  fof(c_0_90, plain, ![X39, X40]:((~v4_pre_topc(X40,X39)|k2_pre_topc(X39,X40)=X40|~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))|~l1_pre_topc(X39))&(~v2_pre_topc(X39)|k2_pre_topc(X39,X40)!=X40|v4_pre_topc(X40,X39)|~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))|~l1_pre_topc(X39))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).
% 0.42/0.61  fof(c_0_91, plain, ![X45, X46]:((~v4_pre_topc(X46,X45)|v3_pre_topc(k3_subset_1(u1_struct_0(X45),X46),X45)|~m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))|~l1_pre_topc(X45))&(~v3_pre_topc(k3_subset_1(u1_struct_0(X45),X46),X45)|v4_pre_topc(X46,X45)|~m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))|~l1_pre_topc(X45))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_tops_1])])])])).
% 0.42/0.61  cnf(c_0_92, negated_conjecture, (r2_hidden(X1,k1_tops_1(esk2_0,esk4_0))|~r2_hidden(X1,k1_tops_1(esk2_0,X2))|~r1_tarski(X2,esk4_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_32]), c_0_30])]), c_0_38])).
% 0.42/0.61  cnf(c_0_93, negated_conjecture, (r2_hidden(esk3_0,X1)|~r1_tarski(esk5_0,X1)), inference(spm,[status(thm)],[c_0_46, c_0_81])).
% 0.42/0.61  cnf(c_0_94, plain, (k1_tops_1(X1,k1_tops_1(X1,X2))=k1_tops_1(X1,X2)|~l1_pre_topc(X1)|~m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X2,k1_tops_1(X1,X2))), inference(spm,[status(thm)],[c_0_82, c_0_60])).
% 0.42/0.61  cnf(c_0_95, negated_conjecture, (m1_subset_1(k1_tops_1(esk2_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_34, c_0_83])).
% 0.42/0.61  cnf(c_0_96, negated_conjecture, (r1_tarski(X1,esk4_0)|~r1_tarski(X1,esk5_0)), inference(spm,[status(thm)],[c_0_25, c_0_84])).
% 0.42/0.61  cnf(c_0_97, negated_conjecture, (r1_tarski(k1_tops_1(esk2_0,esk5_0),esk5_0)), inference(spm,[status(thm)],[c_0_63, c_0_74])).
% 0.42/0.61  cnf(c_0_98, negated_conjecture, (v3_pre_topc(esk5_0,esk2_0)|~v3_pre_topc(X1,esk2_0)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(esk3_0,X1)|~r1_tarski(X1,esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_87])).
% 0.42/0.61  cnf(c_0_99, plain, (r1_tarski(X3,X2)|~r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X3))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_88])).
% 0.42/0.61  cnf(c_0_100, plain, (k1_tops_1(X1,X2)=k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_89])).
% 0.42/0.61  cnf(c_0_101, plain, (k2_pre_topc(X2,X1)=X1|~v4_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_90])).
% 0.42/0.61  cnf(c_0_102, plain, (v4_pre_topc(X2,X1)|~v3_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_91])).
% 0.42/0.61  cnf(c_0_103, negated_conjecture, (r2_hidden(esk3_0,k1_tops_1(esk2_0,esk4_0))|~r1_tarski(esk5_0,k1_tops_1(esk2_0,X1))|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_92, c_0_93])).
% 0.42/0.61  cnf(c_0_104, negated_conjecture, (k1_tops_1(esk2_0,k1_tops_1(esk2_0,esk5_0))=k1_tops_1(esk2_0,esk5_0)|~r1_tarski(esk5_0,k1_tops_1(esk2_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_30]), c_0_54])])).
% 0.42/0.61  cnf(c_0_105, negated_conjecture, (r1_tarski(k1_tops_1(esk2_0,esk5_0),esk4_0)), inference(spm,[status(thm)],[c_0_96, c_0_97])).
% 0.42/0.61  cnf(c_0_106, negated_conjecture, (v3_pre_topc(esk5_0,esk2_0)|~v3_pre_topc(X1,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(esk4_0))|~r2_hidden(esk3_0,X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_32]), c_0_26])).
% 0.42/0.61  cnf(c_0_107, plain, (m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_34, c_0_45])).
% 0.42/0.61  cnf(c_0_108, plain, (r1_tarski(X1,k3_subset_1(X2,X3))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_tarski(X3,k3_subset_1(X2,X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_86]), c_0_87])).
% 0.42/0.61  cnf(c_0_109, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_63, c_0_47])).
% 0.42/0.61  cnf(c_0_110, plain, (k3_subset_1(u1_struct_0(X1),k3_subset_1(u1_struct_0(X1),X2))=k1_tops_1(X1,X2)|~v4_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_101]), c_0_87])).
% 0.42/0.61  cnf(c_0_111, plain, (v4_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1)|~v3_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_86]), c_0_87])).
% 0.42/0.61  cnf(c_0_112, negated_conjecture, (r2_hidden(esk3_0,k1_tops_1(esk2_0,esk4_0))|~r1_tarski(esk5_0,k1_tops_1(esk2_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_104]), c_0_105])])).
% 0.42/0.61  cnf(c_0_113, negated_conjecture, (v3_pre_topc(esk5_0,esk2_0)|~v3_pre_topc(k1_tops_1(X1,esk4_0),esk2_0)|~l1_pre_topc(X1)|~m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(esk3_0,k1_tops_1(X1,esk4_0))), inference(spm,[status(thm)],[c_0_106, c_0_107])).
% 0.42/0.61  cnf(c_0_114, plain, (r1_tarski(X1,k3_subset_1(X2,k3_subset_1(X2,X1)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_109]), c_0_87])).
% 0.42/0.61  cnf(c_0_115, plain, (k3_subset_1(u1_struct_0(X1),k3_subset_1(u1_struct_0(X1),X2))=k1_tops_1(X1,X2)|~v3_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_110, c_0_111])).
% 0.42/0.61  cnf(c_0_116, negated_conjecture, (~v3_pre_topc(X1,esk2_0)|~r2_hidden(esk3_0,X1)|~r1_tarski(esk5_0,k1_tops_1(esk2_0,esk5_0))|~r1_tarski(X1,esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_112]), c_0_38])).
% 0.42/0.61  cnf(c_0_117, negated_conjecture, (v3_pre_topc(esk5_0,esk2_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_28]), c_0_30]), c_0_32]), c_0_29])]), c_0_49])).
% 0.42/0.61  cnf(c_0_118, plain, (r1_tarski(X1,k1_tops_1(X2,X1))|~v3_pre_topc(X1,X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(spm,[status(thm)],[c_0_114, c_0_115])).
% 0.42/0.61  cnf(c_0_119, negated_conjecture, (~r1_tarski(esk5_0,k1_tops_1(esk2_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_117]), c_0_81]), c_0_84])])).
% 0.42/0.61  cnf(c_0_120, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118, c_0_54]), c_0_117]), c_0_30])]), c_0_119]), ['proof']).
% 0.42/0.61  # SZS output end CNFRefutation
% 0.42/0.61  # Proof object total steps             : 121
% 0.42/0.61  # Proof object clause steps            : 84
% 0.42/0.61  # Proof object formula steps           : 37
% 0.42/0.61  # Proof object conjectures             : 52
% 0.42/0.61  # Proof object clause conjectures      : 49
% 0.42/0.61  # Proof object formula conjectures     : 3
% 0.42/0.61  # Proof object initial clauses used    : 28
% 0.42/0.61  # Proof object initial formulas used   : 18
% 0.42/0.61  # Proof object generating inferences   : 56
% 0.42/0.61  # Proof object simplifying inferences  : 53
% 0.42/0.61  # Training examples: 0 positive, 0 negative
% 0.42/0.61  # Parsed axioms                        : 19
% 0.42/0.61  # Removed by relevancy pruning/SinE    : 0
% 0.42/0.61  # Initial clauses                      : 34
% 0.42/0.61  # Removed in clause preprocessing      : 0
% 0.42/0.61  # Initial clauses in saturation        : 34
% 0.42/0.61  # Processed clauses                    : 1490
% 0.42/0.61  # ...of these trivial                  : 14
% 0.42/0.61  # ...subsumed                          : 801
% 0.42/0.61  # ...remaining for further processing  : 675
% 0.42/0.61  # Other redundant clauses eliminated   : 2
% 0.42/0.61  # Clauses deleted for lack of memory   : 0
% 0.42/0.61  # Backward-subsumed                    : 44
% 0.42/0.61  # Backward-rewritten                   : 110
% 0.42/0.61  # Generated clauses                    : 9288
% 0.42/0.61  # ...of the previous two non-trivial   : 8852
% 0.42/0.61  # Contextual simplify-reflections      : 79
% 0.42/0.61  # Paramodulations                      : 9272
% 0.42/0.61  # Factorizations                       : 14
% 0.42/0.61  # Equation resolutions                 : 2
% 0.42/0.61  # Propositional unsat checks           : 0
% 0.42/0.61  #    Propositional check models        : 0
% 0.42/0.61  #    Propositional check unsatisfiable : 0
% 0.42/0.61  #    Propositional clauses             : 0
% 0.42/0.61  #    Propositional clauses after purity: 0
% 0.42/0.61  #    Propositional unsat core size     : 0
% 0.42/0.61  #    Propositional preprocessing time  : 0.000
% 0.42/0.61  #    Propositional encoding time       : 0.000
% 0.42/0.61  #    Propositional solver time         : 0.000
% 0.42/0.61  #    Success case prop preproc time    : 0.000
% 0.42/0.61  #    Success case prop encoding time   : 0.000
% 0.42/0.61  #    Success case prop solver time     : 0.000
% 0.42/0.61  # Current number of processed clauses  : 519
% 0.42/0.61  #    Positive orientable unit clauses  : 35
% 0.42/0.61  #    Positive unorientable unit clauses: 0
% 0.42/0.61  #    Negative unit clauses             : 6
% 0.42/0.61  #    Non-unit-clauses                  : 478
% 0.42/0.61  # Current number of unprocessed clauses: 7256
% 0.42/0.61  # ...number of literals in the above   : 43587
% 0.42/0.61  # Current number of archived formulas  : 0
% 0.42/0.61  # Current number of archived clauses   : 154
% 0.42/0.61  # Clause-clause subsumption calls (NU) : 55667
% 0.42/0.61  # Rec. Clause-clause subsumption calls : 14675
% 0.42/0.61  # Non-unit clause-clause subsumptions  : 706
% 0.42/0.61  # Unit Clause-clause subsumption calls : 349
% 0.42/0.61  # Rewrite failures with RHS unbound    : 0
% 0.42/0.61  # BW rewrite match attempts            : 36
% 0.42/0.61  # BW rewrite match successes           : 7
% 0.42/0.61  # Condensation attempts                : 0
% 0.42/0.61  # Condensation successes               : 0
% 0.42/0.61  # Termbank termtop insertions          : 262539
% 0.42/0.61  
% 0.42/0.61  # -------------------------------------------------
% 0.42/0.61  # User time                : 0.267 s
% 0.42/0.61  # System time              : 0.005 s
% 0.42/0.61  # Total time               : 0.272 s
% 0.42/0.61  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------

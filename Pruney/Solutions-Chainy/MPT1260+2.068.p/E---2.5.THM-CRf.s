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
% DateTime   : Thu Dec  3 11:11:24 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 559 expanded)
%              Number of clauses        :   55 ( 214 expanded)
%              Number of leaves         :   17 ( 135 expanded)
%              Depth                    :   26
%              Number of atoms          :  245 (2163 expanded)
%              Number of equality atoms :   57 ( 525 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    4 (   2 average)

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t74_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k1_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

fof(t44_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(k1_tops_1(X1,X2),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(fc9_tops_1,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => v3_pre_topc(k1_tops_1(X1,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(l78_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(idempotence_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k4_subset_1)).

fof(t33_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => k3_subset_1(X1,k7_subset_1(X1,X2,X3)) = k4_subset_1(X1,k3_subset_1(X1,X2),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_subset_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(dt_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k7_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_subset_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(t48_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(X2,k2_pre_topc(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

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
    ! [X38,X39,X40] :
      ( ~ l1_pre_topc(X38)
      | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))
      | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X38)))
      | ~ v3_pre_topc(X39,X38)
      | ~ r1_tarski(X39,X40)
      | r1_tarski(X39,k1_tops_1(X38,X40)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_tops_1])])])).

fof(c_0_19,negated_conjecture,
    ( v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & ( ~ v3_pre_topc(esk2_0,esk1_0)
      | k2_tops_1(esk1_0,esk2_0) != k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0) )
    & ( v3_pre_topc(esk2_0,esk1_0)
      | k2_tops_1(esk1_0,esk2_0) = k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

fof(c_0_20,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_21,plain,
    ( r1_tarski(X2,k1_tops_1(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X2,X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( v3_pre_topc(esk2_0,esk1_0)
    | k2_tops_1(esk1_0,esk2_0) = k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_26,plain,(
    ! [X41,X42] :
      ( ~ l1_pre_topc(X41)
      | ~ m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))
      | k1_tops_1(X41,X42) = k7_subset_1(u1_struct_0(X41),X42,k2_tops_1(X41,X42)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_tops_1])])])).

cnf(c_0_27,negated_conjecture,
    ( k2_tops_1(esk1_0,esk2_0) = k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0)
    | r1_tarski(esk2_0,k1_tops_1(esk1_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(esk2_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23]),c_0_24])])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_29,plain,
    ( k1_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( k2_tops_1(esk1_0,esk2_0) = k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0)
    | r1_tarski(esk2_0,k1_tops_1(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_24]),c_0_28])])).

cnf(c_0_31,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_32,negated_conjecture,
    ( k1_tops_1(esk1_0,esk2_0) = k7_subset_1(u1_struct_0(esk1_0),esk2_0,k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0))
    | r1_tarski(esk2_0,k1_tops_1(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_23]),c_0_24])])).

fof(c_0_33,plain,(
    ! [X36,X37] :
      ( ~ l1_pre_topc(X36)
      | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))
      | r1_tarski(k1_tops_1(X36,X37),X37) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).

fof(c_0_34,plain,(
    ! [X32,X33] :
      ( ~ v2_pre_topc(X32)
      | ~ l1_pre_topc(X32)
      | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))
      | v3_pre_topc(k1_tops_1(X32,X33),X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).

cnf(c_0_35,negated_conjecture,
    ( k1_tops_1(esk1_0,esk2_0) = k7_subset_1(u1_struct_0(esk1_0),esk2_0,k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0))
    | k1_tops_1(esk1_0,esk2_0) = esk2_0
    | ~ r1_tarski(k1_tops_1(esk1_0,esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_36,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_37,plain,
    ( v3_pre_topc(k1_tops_1(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_38,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_39,negated_conjecture,
    ( k1_tops_1(esk1_0,esk2_0) = k7_subset_1(u1_struct_0(esk1_0),esk2_0,k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0))
    | k1_tops_1(esk1_0,esk2_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_23]),c_0_24])])).

cnf(c_0_40,negated_conjecture,
    ( v3_pre_topc(k1_tops_1(esk1_0,X1),esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_23])])).

cnf(c_0_41,negated_conjecture,
    ( k1_tops_1(esk1_0,esk2_0) = esk2_0
    | k7_subset_1(u1_struct_0(esk1_0),esk2_0,k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0)) != esk2_0 ),
    inference(ef,[status(thm)],[c_0_39])).

cnf(c_0_42,negated_conjecture,
    ( ~ v3_pre_topc(esk2_0,esk1_0)
    | k2_tops_1(esk1_0,esk2_0) != k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_43,negated_conjecture,
    ( v3_pre_topc(esk2_0,esk1_0)
    | k7_subset_1(u1_struct_0(esk1_0),esk2_0,k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0)) != esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_24])])).

fof(c_0_44,plain,(
    ! [X34,X35] :
      ( ~ l1_pre_topc(X34)
      | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))
      | k2_tops_1(X34,X35) = k7_subset_1(u1_struct_0(X34),k2_pre_topc(X34,X35),k1_tops_1(X34,X35)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l78_tops_1])])])).

cnf(c_0_45,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk2_0,k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0)) != esk2_0
    | k2_tops_1(esk1_0,esk2_0) != k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_46,plain,
    ( k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_47,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),k1_tops_1(esk1_0,esk2_0)) != k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0)
    | k7_subset_1(u1_struct_0(esk1_0),esk2_0,k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0)) != esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_23]),c_0_24])])).

cnf(c_0_48,plain,
    ( k1_tops_1(X1,X2) = X2
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,k1_tops_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_36])).

cnf(c_0_49,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk2_0,k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0)) != esk2_0 ),
    inference(spm,[status(thm)],[c_0_47,c_0_41])).

cnf(c_0_50,negated_conjecture,
    ( k1_tops_1(esk1_0,esk2_0) = esk2_0
    | ~ r1_tarski(esk2_0,k7_subset_1(u1_struct_0(esk1_0),esk2_0,k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_39]),c_0_23]),c_0_24])]),c_0_49])).

cnf(c_0_51,negated_conjecture,
    ( v3_pre_topc(esk2_0,esk1_0)
    | ~ r1_tarski(esk2_0,k7_subset_1(u1_struct_0(esk1_0),esk2_0,k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_50]),c_0_24])])).

cnf(c_0_52,negated_conjecture,
    ( k2_tops_1(esk1_0,esk2_0) != k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0)
    | ~ r1_tarski(esk2_0,k7_subset_1(u1_struct_0(esk1_0),esk2_0,k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_51])).

fof(c_0_53,plain,(
    ! [X20,X21,X22] :
      ( ~ m1_subset_1(X21,k1_zfmisc_1(X20))
      | k7_subset_1(X20,X21,X22) = k4_xboole_0(X21,X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

fof(c_0_54,plain,(
    ! [X26,X27] :
      ( ( ~ m1_subset_1(X26,k1_zfmisc_1(X27))
        | r1_tarski(X26,X27) )
      & ( ~ r1_tarski(X26,X27)
        | m1_subset_1(X26,k1_zfmisc_1(X27)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_55,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),k1_tops_1(esk1_0,esk2_0)) != k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0)
    | ~ r1_tarski(esk2_0,k7_subset_1(u1_struct_0(esk1_0),esk2_0,k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_46]),c_0_23]),c_0_24])])).

cnf(c_0_56,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

fof(c_0_57,plain,(
    ! [X15,X16,X17] :
      ( ~ m1_subset_1(X16,k1_zfmisc_1(X15))
      | ~ m1_subset_1(X17,k1_zfmisc_1(X15))
      | k4_subset_1(X15,X16,X16) = X16 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[idempotence_k4_subset_1])])).

cnf(c_0_58,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_59,negated_conjecture,
    ( ~ r1_tarski(esk2_0,k7_subset_1(u1_struct_0(esk1_0),esk2_0,k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_50])).

cnf(c_0_60,plain,
    ( k7_subset_1(X1,X2,X3) = k7_subset_1(X4,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_56])).

fof(c_0_61,plain,(
    ! [X23,X24,X25] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(X23))
      | ~ m1_subset_1(X25,k1_zfmisc_1(X23))
      | k3_subset_1(X23,k7_subset_1(X23,X24,X25)) = k4_subset_1(X23,k3_subset_1(X23,X24),X25) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_subset_1])])])).

cnf(c_0_62,plain,
    ( k4_subset_1(X2,X1,X1) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_63,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_28])).

fof(c_0_64,plain,(
    ! [X10,X11] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(X10))
      | m1_subset_1(k3_subset_1(X10,X11),k1_zfmisc_1(X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

cnf(c_0_65,negated_conjecture,
    ( ~ m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(X1))
    | ~ r1_tarski(esk2_0,k7_subset_1(u1_struct_0(esk1_0),esk2_0,k7_subset_1(X1,k2_pre_topc(esk1_0,esk2_0),esk2_0))) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

fof(c_0_66,plain,(
    ! [X18,X19] :
      ( ~ m1_subset_1(X19,k1_zfmisc_1(X18))
      | k3_subset_1(X18,k3_subset_1(X18,X19)) = X19 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

cnf(c_0_67,plain,
    ( k3_subset_1(X2,k7_subset_1(X2,X1,X3)) = k4_subset_1(X2,k3_subset_1(X2,X1),X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_68,plain,
    ( k4_subset_1(X1,X2,X2) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_69,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

fof(c_0_70,plain,(
    ! [X12,X13,X14] :
      ( ~ m1_subset_1(X13,k1_zfmisc_1(X12))
      | m1_subset_1(k7_subset_1(X12,X13,X14),k1_zfmisc_1(X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_subset_1])])).

cnf(c_0_71,negated_conjecture,
    ( ~ m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(X1))
    | ~ r1_tarski(esk2_0,k7_subset_1(u1_struct_0(esk1_0),esk2_0,k4_xboole_0(k2_pre_topc(esk1_0,esk2_0),esk2_0))) ),
    inference(spm,[status(thm)],[c_0_65,c_0_56])).

fof(c_0_72,plain,(
    ! [X8,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(X8))
      | k3_subset_1(X8,X9) = k4_xboole_0(X8,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_73,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_74,plain,
    ( k3_subset_1(X1,k7_subset_1(X1,X2,k3_subset_1(X1,X2))) = k3_subset_1(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_69])).

cnf(c_0_75,plain,
    ( m1_subset_1(k7_subset_1(X2,X1,X3),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_76,negated_conjecture,
    ( ~ m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X2))
    | ~ r1_tarski(esk2_0,k7_subset_1(X2,esk2_0,k4_xboole_0(k2_pre_topc(esk1_0,esk2_0),esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_60]),c_0_24])])).

cnf(c_0_77,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_78,plain,
    ( k3_subset_1(X1,k3_subset_1(X1,X2)) = k7_subset_1(X1,X2,k3_subset_1(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_75])).

cnf(c_0_79,negated_conjecture,
    ( ~ m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(k2_pre_topc(esk1_0,esk2_0)))
    | ~ m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X2))
    | ~ r1_tarski(esk2_0,k7_subset_1(X2,esk2_0,k3_subset_1(k2_pre_topc(esk1_0,esk2_0),esk2_0))) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_80,plain,
    ( k7_subset_1(X1,X2,k3_subset_1(X1,X2)) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_78])).

fof(c_0_81,plain,(
    ! [X28,X29] :
      ( ~ l1_pre_topc(X28)
      | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
      | m1_subset_1(k2_pre_topc(X28,X29),k1_zfmisc_1(u1_struct_0(X28))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

cnf(c_0_82,negated_conjecture,
    ( ~ m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(k2_pre_topc(esk1_0,esk2_0)))
    | ~ m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_28])])).

cnf(c_0_83,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

fof(c_0_84,plain,(
    ! [X30,X31] :
      ( ~ l1_pre_topc(X30)
      | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
      | r1_tarski(X31,k2_pre_topc(X30,X31)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_pre_topc])])])).

cnf(c_0_85,negated_conjecture,
    ( ~ m1_subset_1(esk2_0,k1_zfmisc_1(k2_pre_topc(esk1_0,esk2_0)))
    | ~ m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_23]),c_0_24])])).

cnf(c_0_86,plain,
    ( r1_tarski(X2,k2_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_87,negated_conjecture,
    ( ~ m1_subset_1(esk2_0,k1_zfmisc_1(k2_pre_topc(esk1_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_85,c_0_63])).

cnf(c_0_88,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_pre_topc(X2,X1)))
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(spm,[status(thm)],[c_0_58,c_0_86])).

cnf(c_0_89,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_23]),c_0_24])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.33  % Computer   : n022.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 18:31:40 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.54  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.20/0.54  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.54  #
% 0.20/0.54  # Preprocessing time       : 0.028 s
% 0.20/0.54  # Presaturation interreduction done
% 0.20/0.54  
% 0.20/0.54  # Proof found!
% 0.20/0.54  # SZS status Theorem
% 0.20/0.54  # SZS output start CNFRefutation
% 0.20/0.54  fof(t76_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_tops_1)).
% 0.20/0.54  fof(t56_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v3_pre_topc(X2,X1)&r1_tarski(X2,X3))=>r1_tarski(X2,k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tops_1)).
% 0.20/0.54  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.54  fof(t74_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k1_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tops_1)).
% 0.20/0.54  fof(t44_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,X2),X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 0.20/0.54  fof(fc9_tops_1, axiom, ![X1, X2]:(((v2_pre_topc(X1)&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v3_pre_topc(k1_tops_1(X1,X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 0.20/0.54  fof(l78_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 0.20/0.54  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 0.20/0.54  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.54  fof(idempotence_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k4_subset_1)).
% 0.20/0.54  fof(t33_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k3_subset_1(X1,k7_subset_1(X1,X2,X3))=k4_subset_1(X1,k3_subset_1(X1,X2),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_subset_1)).
% 0.20/0.54  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 0.20/0.54  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 0.20/0.54  fof(dt_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k7_subset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_subset_1)).
% 0.20/0.54  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 0.20/0.54  fof(dt_k2_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 0.20/0.54  fof(t48_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(X2,k2_pre_topc(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_pre_topc)).
% 0.20/0.54  fof(c_0_17, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2))))), inference(assume_negation,[status(cth)],[t76_tops_1])).
% 0.20/0.54  fof(c_0_18, plain, ![X38, X39, X40]:(~l1_pre_topc(X38)|(~m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))|(~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X38)))|(~v3_pre_topc(X39,X38)|~r1_tarski(X39,X40)|r1_tarski(X39,k1_tops_1(X38,X40)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_tops_1])])])).
% 0.20/0.54  fof(c_0_19, negated_conjecture, ((v2_pre_topc(esk1_0)&l1_pre_topc(esk1_0))&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&((~v3_pre_topc(esk2_0,esk1_0)|k2_tops_1(esk1_0,esk2_0)!=k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0))&(v3_pre_topc(esk2_0,esk1_0)|k2_tops_1(esk1_0,esk2_0)=k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 0.20/0.54  fof(c_0_20, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.54  cnf(c_0_21, plain, (r1_tarski(X2,k1_tops_1(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v3_pre_topc(X2,X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.54  cnf(c_0_22, negated_conjecture, (v3_pre_topc(esk2_0,esk1_0)|k2_tops_1(esk1_0,esk2_0)=k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.54  cnf(c_0_23, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.54  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.54  cnf(c_0_25, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.54  fof(c_0_26, plain, ![X41, X42]:(~l1_pre_topc(X41)|(~m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))|k1_tops_1(X41,X42)=k7_subset_1(u1_struct_0(X41),X42,k2_tops_1(X41,X42)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_tops_1])])])).
% 0.20/0.54  cnf(c_0_27, negated_conjecture, (k2_tops_1(esk1_0,esk2_0)=k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0)|r1_tarski(esk2_0,k1_tops_1(esk1_0,X1))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(esk2_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23]), c_0_24])])).
% 0.20/0.54  cnf(c_0_28, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_25])).
% 0.20/0.54  cnf(c_0_29, plain, (k1_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.54  cnf(c_0_30, negated_conjecture, (k2_tops_1(esk1_0,esk2_0)=k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0)|r1_tarski(esk2_0,k1_tops_1(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_24]), c_0_28])])).
% 0.20/0.54  cnf(c_0_31, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.54  cnf(c_0_32, negated_conjecture, (k1_tops_1(esk1_0,esk2_0)=k7_subset_1(u1_struct_0(esk1_0),esk2_0,k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0))|r1_tarski(esk2_0,k1_tops_1(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_23]), c_0_24])])).
% 0.20/0.54  fof(c_0_33, plain, ![X36, X37]:(~l1_pre_topc(X36)|(~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))|r1_tarski(k1_tops_1(X36,X37),X37))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).
% 0.20/0.54  fof(c_0_34, plain, ![X32, X33]:(~v2_pre_topc(X32)|~l1_pre_topc(X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))|v3_pre_topc(k1_tops_1(X32,X33),X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).
% 0.20/0.54  cnf(c_0_35, negated_conjecture, (k1_tops_1(esk1_0,esk2_0)=k7_subset_1(u1_struct_0(esk1_0),esk2_0,k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0))|k1_tops_1(esk1_0,esk2_0)=esk2_0|~r1_tarski(k1_tops_1(esk1_0,esk2_0),esk2_0)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.20/0.54  cnf(c_0_36, plain, (r1_tarski(k1_tops_1(X1,X2),X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.54  cnf(c_0_37, plain, (v3_pre_topc(k1_tops_1(X1,X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.54  cnf(c_0_38, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.54  cnf(c_0_39, negated_conjecture, (k1_tops_1(esk1_0,esk2_0)=k7_subset_1(u1_struct_0(esk1_0),esk2_0,k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0))|k1_tops_1(esk1_0,esk2_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_23]), c_0_24])])).
% 0.20/0.54  cnf(c_0_40, negated_conjecture, (v3_pre_topc(k1_tops_1(esk1_0,X1),esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_23])])).
% 0.20/0.54  cnf(c_0_41, negated_conjecture, (k1_tops_1(esk1_0,esk2_0)=esk2_0|k7_subset_1(u1_struct_0(esk1_0),esk2_0,k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0))!=esk2_0), inference(ef,[status(thm)],[c_0_39])).
% 0.20/0.54  cnf(c_0_42, negated_conjecture, (~v3_pre_topc(esk2_0,esk1_0)|k2_tops_1(esk1_0,esk2_0)!=k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.54  cnf(c_0_43, negated_conjecture, (v3_pre_topc(esk2_0,esk1_0)|k7_subset_1(u1_struct_0(esk1_0),esk2_0,k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0))!=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_24])])).
% 0.20/0.54  fof(c_0_44, plain, ![X34, X35]:(~l1_pre_topc(X34)|(~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))|k2_tops_1(X34,X35)=k7_subset_1(u1_struct_0(X34),k2_pre_topc(X34,X35),k1_tops_1(X34,X35)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l78_tops_1])])])).
% 0.20/0.54  cnf(c_0_45, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk2_0,k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0))!=esk2_0|k2_tops_1(esk1_0,esk2_0)!=k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.20/0.54  cnf(c_0_46, plain, (k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.54  cnf(c_0_47, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),k1_tops_1(esk1_0,esk2_0))!=k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0)|k7_subset_1(u1_struct_0(esk1_0),esk2_0,k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0))!=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_23]), c_0_24])])).
% 0.20/0.54  cnf(c_0_48, plain, (k1_tops_1(X1,X2)=X2|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X2,k1_tops_1(X1,X2))), inference(spm,[status(thm)],[c_0_31, c_0_36])).
% 0.20/0.54  cnf(c_0_49, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk2_0,k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0))!=esk2_0), inference(spm,[status(thm)],[c_0_47, c_0_41])).
% 0.20/0.54  cnf(c_0_50, negated_conjecture, (k1_tops_1(esk1_0,esk2_0)=esk2_0|~r1_tarski(esk2_0,k7_subset_1(u1_struct_0(esk1_0),esk2_0,k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_39]), c_0_23]), c_0_24])]), c_0_49])).
% 0.20/0.54  cnf(c_0_51, negated_conjecture, (v3_pre_topc(esk2_0,esk1_0)|~r1_tarski(esk2_0,k7_subset_1(u1_struct_0(esk1_0),esk2_0,k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_50]), c_0_24])])).
% 0.20/0.54  cnf(c_0_52, negated_conjecture, (k2_tops_1(esk1_0,esk2_0)!=k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0)|~r1_tarski(esk2_0,k7_subset_1(u1_struct_0(esk1_0),esk2_0,k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0)))), inference(spm,[status(thm)],[c_0_42, c_0_51])).
% 0.20/0.54  fof(c_0_53, plain, ![X20, X21, X22]:(~m1_subset_1(X21,k1_zfmisc_1(X20))|k7_subset_1(X20,X21,X22)=k4_xboole_0(X21,X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 0.20/0.54  fof(c_0_54, plain, ![X26, X27]:((~m1_subset_1(X26,k1_zfmisc_1(X27))|r1_tarski(X26,X27))&(~r1_tarski(X26,X27)|m1_subset_1(X26,k1_zfmisc_1(X27)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.54  cnf(c_0_55, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),k1_tops_1(esk1_0,esk2_0))!=k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0)|~r1_tarski(esk2_0,k7_subset_1(u1_struct_0(esk1_0),esk2_0,k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_46]), c_0_23]), c_0_24])])).
% 0.20/0.54  cnf(c_0_56, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.20/0.54  fof(c_0_57, plain, ![X15, X16, X17]:(~m1_subset_1(X16,k1_zfmisc_1(X15))|~m1_subset_1(X17,k1_zfmisc_1(X15))|k4_subset_1(X15,X16,X16)=X16), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[idempotence_k4_subset_1])])).
% 0.20/0.54  cnf(c_0_58, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.20/0.54  cnf(c_0_59, negated_conjecture, (~r1_tarski(esk2_0,k7_subset_1(u1_struct_0(esk1_0),esk2_0,k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0)))), inference(spm,[status(thm)],[c_0_55, c_0_50])).
% 0.20/0.54  cnf(c_0_60, plain, (k7_subset_1(X1,X2,X3)=k7_subset_1(X4,X2,X3)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X4))), inference(spm,[status(thm)],[c_0_56, c_0_56])).
% 0.20/0.54  fof(c_0_61, plain, ![X23, X24, X25]:(~m1_subset_1(X24,k1_zfmisc_1(X23))|(~m1_subset_1(X25,k1_zfmisc_1(X23))|k3_subset_1(X23,k7_subset_1(X23,X24,X25))=k4_subset_1(X23,k3_subset_1(X23,X24),X25))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_subset_1])])])).
% 0.20/0.54  cnf(c_0_62, plain, (k4_subset_1(X2,X1,X1)=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.20/0.54  cnf(c_0_63, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_58, c_0_28])).
% 0.20/0.54  fof(c_0_64, plain, ![X10, X11]:(~m1_subset_1(X11,k1_zfmisc_1(X10))|m1_subset_1(k3_subset_1(X10,X11),k1_zfmisc_1(X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 0.20/0.54  cnf(c_0_65, negated_conjecture, (~m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(X1))|~r1_tarski(esk2_0,k7_subset_1(u1_struct_0(esk1_0),esk2_0,k7_subset_1(X1,k2_pre_topc(esk1_0,esk2_0),esk2_0)))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.20/0.54  fof(c_0_66, plain, ![X18, X19]:(~m1_subset_1(X19,k1_zfmisc_1(X18))|k3_subset_1(X18,k3_subset_1(X18,X19))=X19), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 0.20/0.54  cnf(c_0_67, plain, (k3_subset_1(X2,k7_subset_1(X2,X1,X3))=k4_subset_1(X2,k3_subset_1(X2,X1),X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.20/0.54  cnf(c_0_68, plain, (k4_subset_1(X1,X2,X2)=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.20/0.54  cnf(c_0_69, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.20/0.54  fof(c_0_70, plain, ![X12, X13, X14]:(~m1_subset_1(X13,k1_zfmisc_1(X12))|m1_subset_1(k7_subset_1(X12,X13,X14),k1_zfmisc_1(X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_subset_1])])).
% 0.20/0.54  cnf(c_0_71, negated_conjecture, (~m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(X1))|~r1_tarski(esk2_0,k7_subset_1(u1_struct_0(esk1_0),esk2_0,k4_xboole_0(k2_pre_topc(esk1_0,esk2_0),esk2_0)))), inference(spm,[status(thm)],[c_0_65, c_0_56])).
% 0.20/0.54  fof(c_0_72, plain, ![X8, X9]:(~m1_subset_1(X9,k1_zfmisc_1(X8))|k3_subset_1(X8,X9)=k4_xboole_0(X8,X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.20/0.54  cnf(c_0_73, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.20/0.54  cnf(c_0_74, plain, (k3_subset_1(X1,k7_subset_1(X1,X2,k3_subset_1(X1,X2)))=k3_subset_1(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_69])).
% 0.20/0.54  cnf(c_0_75, plain, (m1_subset_1(k7_subset_1(X2,X1,X3),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.20/0.54  cnf(c_0_76, negated_conjecture, (~m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(X1))|~m1_subset_1(esk2_0,k1_zfmisc_1(X2))|~r1_tarski(esk2_0,k7_subset_1(X2,esk2_0,k4_xboole_0(k2_pre_topc(esk1_0,esk2_0),esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_60]), c_0_24])])).
% 0.20/0.54  cnf(c_0_77, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.20/0.54  cnf(c_0_78, plain, (k3_subset_1(X1,k3_subset_1(X1,X2))=k7_subset_1(X1,X2,k3_subset_1(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_75])).
% 0.20/0.54  cnf(c_0_79, negated_conjecture, (~m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(esk2_0,k1_zfmisc_1(k2_pre_topc(esk1_0,esk2_0)))|~m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(X1))|~m1_subset_1(esk2_0,k1_zfmisc_1(X2))|~r1_tarski(esk2_0,k7_subset_1(X2,esk2_0,k3_subset_1(k2_pre_topc(esk1_0,esk2_0),esk2_0)))), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.20/0.54  cnf(c_0_80, plain, (k7_subset_1(X1,X2,k3_subset_1(X1,X2))=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_73, c_0_78])).
% 0.20/0.54  fof(c_0_81, plain, ![X28, X29]:(~l1_pre_topc(X28)|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))|m1_subset_1(k2_pre_topc(X28,X29),k1_zfmisc_1(u1_struct_0(X28)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).
% 0.20/0.54  cnf(c_0_82, negated_conjecture, (~m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(esk2_0,k1_zfmisc_1(k2_pre_topc(esk1_0,esk2_0)))|~m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_28])])).
% 0.20/0.54  cnf(c_0_83, plain, (m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.20/0.54  fof(c_0_84, plain, ![X30, X31]:(~l1_pre_topc(X30)|(~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))|r1_tarski(X31,k2_pre_topc(X30,X31)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_pre_topc])])])).
% 0.20/0.54  cnf(c_0_85, negated_conjecture, (~m1_subset_1(esk2_0,k1_zfmisc_1(k2_pre_topc(esk1_0,esk2_0)))|~m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_23]), c_0_24])])).
% 0.20/0.54  cnf(c_0_86, plain, (r1_tarski(X2,k2_pre_topc(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_84])).
% 0.20/0.54  cnf(c_0_87, negated_conjecture, (~m1_subset_1(esk2_0,k1_zfmisc_1(k2_pre_topc(esk1_0,esk2_0)))), inference(spm,[status(thm)],[c_0_85, c_0_63])).
% 0.20/0.54  cnf(c_0_88, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_pre_topc(X2,X1)))|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(spm,[status(thm)],[c_0_58, c_0_86])).
% 0.20/0.54  cnf(c_0_89, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_23]), c_0_24])]), ['proof']).
% 0.20/0.54  # SZS output end CNFRefutation
% 0.20/0.54  # Proof object total steps             : 90
% 0.20/0.54  # Proof object clause steps            : 55
% 0.20/0.54  # Proof object formula steps           : 35
% 0.20/0.54  # Proof object conjectures             : 32
% 0.20/0.54  # Proof object clause conjectures      : 29
% 0.20/0.54  # Proof object formula conjectures     : 3
% 0.20/0.54  # Proof object initial clauses used    : 22
% 0.20/0.54  # Proof object initial formulas used   : 17
% 0.20/0.54  # Proof object generating inferences   : 32
% 0.20/0.54  # Proof object simplifying inferences  : 40
% 0.20/0.54  # Training examples: 0 positive, 0 negative
% 0.20/0.54  # Parsed axioms                        : 18
% 0.20/0.54  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.54  # Initial clauses                      : 25
% 0.20/0.54  # Removed in clause preprocessing      : 0
% 0.20/0.54  # Initial clauses in saturation        : 25
% 0.20/0.54  # Processed clauses                    : 1946
% 0.20/0.54  # ...of these trivial                  : 18
% 0.20/0.54  # ...subsumed                          : 1326
% 0.20/0.54  # ...remaining for further processing  : 602
% 0.20/0.54  # Other redundant clauses eliminated   : 2
% 0.20/0.54  # Clauses deleted for lack of memory   : 0
% 0.20/0.54  # Backward-subsumed                    : 65
% 0.20/0.54  # Backward-rewritten                   : 62
% 0.20/0.54  # Generated clauses                    : 7123
% 0.20/0.54  # ...of the previous two non-trivial   : 6667
% 0.20/0.54  # Contextual simplify-reflections      : 12
% 0.20/0.54  # Paramodulations                      : 7119
% 0.20/0.54  # Factorizations                       : 2
% 0.20/0.54  # Equation resolutions                 : 2
% 0.20/0.54  # Propositional unsat checks           : 0
% 0.20/0.54  #    Propositional check models        : 0
% 0.20/0.54  #    Propositional check unsatisfiable : 0
% 0.20/0.54  #    Propositional clauses             : 0
% 0.20/0.54  #    Propositional clauses after purity: 0
% 0.20/0.54  #    Propositional unsat core size     : 0
% 0.20/0.54  #    Propositional preprocessing time  : 0.000
% 0.20/0.54  #    Propositional encoding time       : 0.000
% 0.20/0.54  #    Propositional solver time         : 0.000
% 0.20/0.54  #    Success case prop preproc time    : 0.000
% 0.20/0.54  #    Success case prop encoding time   : 0.000
% 0.20/0.54  #    Success case prop solver time     : 0.000
% 0.20/0.54  # Current number of processed clauses  : 449
% 0.20/0.54  #    Positive orientable unit clauses  : 21
% 0.20/0.54  #    Positive unorientable unit clauses: 0
% 0.20/0.54  #    Negative unit clauses             : 8
% 0.20/0.54  #    Non-unit-clauses                  : 420
% 0.20/0.54  # Current number of unprocessed clauses: 4604
% 0.20/0.54  # ...number of literals in the above   : 16460
% 0.20/0.54  # Current number of archived formulas  : 0
% 0.20/0.54  # Current number of archived clauses   : 151
% 0.20/0.54  # Clause-clause subsumption calls (NU) : 41708
% 0.20/0.54  # Rec. Clause-clause subsumption calls : 22405
% 0.20/0.54  # Non-unit clause-clause subsumptions  : 1213
% 0.20/0.54  # Unit Clause-clause subsumption calls : 360
% 0.20/0.54  # Rewrite failures with RHS unbound    : 0
% 0.20/0.54  # BW rewrite match attempts            : 55
% 0.20/0.54  # BW rewrite match successes           : 15
% 0.20/0.54  # Condensation attempts                : 0
% 0.20/0.54  # Condensation successes               : 0
% 0.20/0.54  # Termbank termtop insertions          : 186595
% 0.20/0.54  
% 0.20/0.54  # -------------------------------------------------
% 0.20/0.54  # User time                : 0.203 s
% 0.20/0.54  # System time              : 0.003 s
% 0.20/0.54  # Total time               : 0.207 s
% 0.20/0.54  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------

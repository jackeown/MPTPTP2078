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
% DateTime   : Thu Dec  3 11:11:25 EST 2020

% Result     : Theorem 0.41s
% Output     : CNFRefutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :  106 (1126 expanded)
%              Number of clauses        :   71 ( 459 expanded)
%              Number of leaves         :   17 ( 276 expanded)
%              Depth                    :   20
%              Number of atoms          :  222 (3563 expanded)
%              Number of equality atoms :   54 ( 811 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    7 (   2 average)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t44_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(k1_tops_1(X1,X2),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(t48_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(X2,k2_pre_topc(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

fof(t74_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k1_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(fc9_tops_1,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => v3_pre_topc(k1_tops_1(X1,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

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

fof(l78_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

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
    ! [X24,X25] :
      ( ( ~ m1_subset_1(X24,k1_zfmisc_1(X25))
        | r1_tarski(X24,X25) )
      & ( ~ r1_tarski(X24,X25)
        | m1_subset_1(X24,k1_zfmisc_1(X25)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

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
    ! [X7,X8,X9] :
      ( ~ r1_tarski(X7,X8)
      | ~ r1_tarski(X8,X9)
      | r1_tarski(X7,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( r1_tarski(esk2_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_25,plain,(
    ! [X10,X11] : r1_tarski(k4_xboole_0(X10,X11),X10) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_26,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_27,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_28,plain,(
    ! [X34,X35] :
      ( ~ l1_pre_topc(X34)
      | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))
      | r1_tarski(k1_tops_1(X34,X35),X35) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).

cnf(c_0_29,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk2_0,X1),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

fof(c_0_31,plain,(
    ! [X12,X13,X14] : k4_xboole_0(k4_xboole_0(X12,X13),X14) = k4_xboole_0(X12,k2_xboole_0(X13,X14)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_32,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(k4_xboole_0(esk2_0,X1),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_35,plain,(
    ! [X15,X16] :
      ( ~ m1_subset_1(X16,k1_zfmisc_1(X15))
      | k3_subset_1(X15,X16) = k4_xboole_0(X15,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_36,plain,
    ( m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_27])).

cnf(c_0_37,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_27])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(esk2_0,X1)),k4_xboole_0(esk2_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])])).

fof(c_0_40,plain,(
    ! [X19,X20] :
      ( ~ m1_subset_1(X20,k1_zfmisc_1(X19))
      | k3_subset_1(X19,k3_subset_1(X19,X20)) = X20 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

cnf(c_0_41,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_42,plain,
    ( m1_subset_1(k4_xboole_0(k4_xboole_0(X1,X2),X3),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

fof(c_0_43,plain,(
    ! [X21,X22,X23] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(X21))
      | k7_subset_1(X21,X22,X23) = k4_xboole_0(X22,X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

fof(c_0_44,plain,(
    ! [X28,X29] :
      ( ~ l1_pre_topc(X28)
      | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
      | r1_tarski(X29,k2_pre_topc(X28,X29)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_pre_topc])])])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(esk2_0,X1)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_46,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_47,plain,
    ( k3_subset_1(X1,k4_xboole_0(k4_xboole_0(X1,X2),X3)) = k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,X2),X3)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_48,plain,
    ( k3_subset_1(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_36])).

fof(c_0_49,plain,(
    ! [X39,X40] :
      ( ~ l1_pre_topc(X39)
      | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))
      | k1_tops_1(X39,X40) = k7_subset_1(u1_struct_0(X39),X40,k2_tops_1(X39,X40)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_tops_1])])])).

cnf(c_0_50,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk2_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_22]),c_0_34])])).

cnf(c_0_52,plain,
    ( r1_tarski(X2,k2_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_53,plain,(
    ! [X26,X27] :
      ( ~ l1_pre_topc(X26)
      | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
      | m1_subset_1(k2_pre_topc(X26,X27),k1_zfmisc_1(u1_struct_0(X26))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(X1,esk2_0)
    | ~ r1_tarski(X1,k1_tops_1(esk1_0,k4_xboole_0(esk2_0,X2))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_45])).

cnf(c_0_55,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,X2),X3))) = k4_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_42]),c_0_47]),c_0_48])).

cnf(c_0_56,plain,
    ( k1_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_57,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1) = k4_xboole_0(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_22])).

fof(c_0_58,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_51])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(esk2_0,k2_pre_topc(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_22]),c_0_34])])).

cnf(c_0_61,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(X1,esk2_0)
    | ~ r1_tarski(X1,k1_tops_1(esk1_0,k4_xboole_0(k4_xboole_0(esk2_0,X2),X3))) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_63,negated_conjecture,
    ( k4_xboole_0(esk2_0,k2_tops_1(esk1_0,esk2_0)) = k1_tops_1(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_22]),c_0_57]),c_0_34])])).

cnf(c_0_64,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_65,negated_conjecture,
    ( m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_59])).

cnf(c_0_66,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k2_pre_topc(esk1_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_60])).

cnf(c_0_67,negated_conjecture,
    ( m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_22]),c_0_34])])).

cnf(c_0_68,negated_conjecture,
    ( r1_tarski(X1,esk2_0)
    | ~ r1_tarski(X1,k1_tops_1(esk1_0,k4_xboole_0(k1_tops_1(esk1_0,esk2_0),X2))) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_69,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_64])).

cnf(c_0_70,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),X1) = k4_xboole_0(k1_tops_1(esk1_0,esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_65])).

fof(c_0_71,plain,(
    ! [X4] : k2_xboole_0(X4,X4) = X4 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

cnf(c_0_72,negated_conjecture,
    ( k3_subset_1(k2_pre_topc(esk1_0,esk2_0),esk2_0) = k4_xboole_0(k2_pre_topc(esk1_0,esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_66])).

cnf(c_0_73,negated_conjecture,
    ( v3_pre_topc(esk2_0,esk1_0)
    | k2_tops_1(esk1_0,esk2_0) = k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_74,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),X1) = k4_xboole_0(k2_pre_topc(esk1_0,esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_67])).

cnf(c_0_75,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(k1_tops_1(esk1_0,esk2_0),X1)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_76,negated_conjecture,
    ( k4_xboole_0(k1_tops_1(esk1_0,esk2_0),k2_tops_1(esk1_0,k1_tops_1(esk1_0,esk2_0))) = k1_tops_1(esk1_0,k1_tops_1(esk1_0,esk2_0)) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_65]),c_0_34])]),c_0_70])).

cnf(c_0_77,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_78,negated_conjecture,
    ( k4_xboole_0(k2_pre_topc(esk1_0,esk2_0),k4_xboole_0(k2_pre_topc(esk1_0,esk2_0),esk2_0)) = esk2_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_66]),c_0_72]),c_0_48])).

cnf(c_0_79,negated_conjecture,
    ( k4_xboole_0(k2_pre_topc(esk1_0,esk2_0),esk2_0) = k2_tops_1(esk1_0,esk2_0)
    | v3_pre_topc(esk2_0,esk1_0) ),
    inference(rw,[status(thm)],[c_0_73,c_0_74])).

fof(c_0_80,plain,(
    ! [X30,X31] :
      ( ~ v2_pre_topc(X30)
      | ~ l1_pre_topc(X30)
      | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
      | v3_pre_topc(k1_tops_1(X30,X31),X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).

cnf(c_0_81,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,k1_tops_1(esk1_0,k1_tops_1(esk1_0,esk2_0))),esk2_0) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

fof(c_0_82,plain,(
    ! [X36,X37,X38] :
      ( ~ l1_pre_topc(X36)
      | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))
      | ~ m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X36)))
      | ~ v3_pre_topc(X37,X36)
      | ~ r1_tarski(X37,X38)
      | r1_tarski(X37,k1_tops_1(X36,X38)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_tops_1])])])).

cnf(c_0_83,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_77])).

cnf(c_0_84,negated_conjecture,
    ( k4_xboole_0(k2_pre_topc(esk1_0,esk2_0),k2_tops_1(esk1_0,esk2_0)) = esk2_0
    | v3_pre_topc(esk2_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_85,plain,
    ( v3_pre_topc(k1_tops_1(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_86,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_87,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,k1_tops_1(esk1_0,k1_tops_1(esk1_0,esk2_0))),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_81])).

cnf(c_0_88,plain,
    ( r1_tarski(X2,k1_tops_1(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X2,X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_89,negated_conjecture,
    ( k1_tops_1(esk1_0,esk2_0) = esk2_0
    | v3_pre_topc(esk2_0,esk1_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_63])).

cnf(c_0_90,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_91,negated_conjecture,
    ( v3_pre_topc(k1_tops_1(esk1_0,X1),esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_34])])).

cnf(c_0_92,negated_conjecture,
    ( m1_subset_1(k1_tops_1(esk1_0,k1_tops_1(esk1_0,k1_tops_1(esk1_0,esk2_0))),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_87])).

cnf(c_0_93,negated_conjecture,
    ( k1_tops_1(esk1_0,esk2_0) = esk2_0
    | r1_tarski(esk2_0,k1_tops_1(esk1_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(esk2_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_34]),c_0_22])])).

cnf(c_0_94,negated_conjecture,
    ( k1_tops_1(esk1_0,esk2_0) = esk2_0
    | ~ r1_tarski(esk2_0,k1_tops_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_90,c_0_51])).

fof(c_0_95,plain,(
    ! [X32,X33] :
      ( ~ l1_pre_topc(X32)
      | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))
      | k2_tops_1(X32,X33) = k7_subset_1(u1_struct_0(X32),k2_pre_topc(X32,X33),k1_tops_1(X32,X33)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l78_tops_1])])])).

cnf(c_0_96,negated_conjecture,
    ( ~ v3_pre_topc(esk2_0,esk1_0)
    | k2_tops_1(esk1_0,esk2_0) != k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_97,negated_conjecture,
    ( v3_pre_topc(k1_tops_1(esk1_0,k1_tops_1(esk1_0,k1_tops_1(esk1_0,k1_tops_1(esk1_0,esk2_0)))),esk1_0) ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_98,negated_conjecture,
    ( k1_tops_1(esk1_0,esk2_0) = esk2_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_22]),c_0_69])]),c_0_94])).

cnf(c_0_99,plain,
    ( k2_tops_1(X1,X2) = k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_95])).

cnf(c_0_100,negated_conjecture,
    ( k4_xboole_0(k2_pre_topc(esk1_0,esk2_0),esk2_0) != k2_tops_1(esk1_0,esk2_0)
    | ~ v3_pre_topc(esk2_0,esk1_0) ),
    inference(rw,[status(thm)],[c_0_96,c_0_74])).

cnf(c_0_101,negated_conjecture,
    ( v3_pre_topc(esk2_0,esk1_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_97,c_0_98]),c_0_98]),c_0_98]),c_0_98])).

cnf(c_0_102,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,k4_xboole_0(esk2_0,X1)),k1_tops_1(esk1_0,k4_xboole_0(esk2_0,X1))) = k2_tops_1(esk1_0,k4_xboole_0(esk2_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_33]),c_0_34])])).

cnf(c_0_103,negated_conjecture,
    ( k4_xboole_0(esk2_0,k2_tops_1(esk1_0,esk2_0)) = esk2_0 ),
    inference(rw,[status(thm)],[c_0_63,c_0_98])).

cnf(c_0_104,negated_conjecture,
    ( k4_xboole_0(k2_pre_topc(esk1_0,esk2_0),esk2_0) != k2_tops_1(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_100,c_0_101])])).

cnf(c_0_105,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_103]),c_0_74]),c_0_98]),c_0_104]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n015.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 18:40:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.41/0.58  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S049N
% 0.41/0.58  # and selection function PSelectComplexPreferEQ.
% 0.41/0.58  #
% 0.41/0.58  # Preprocessing time       : 0.028 s
% 0.41/0.58  # Presaturation interreduction done
% 0.41/0.58  
% 0.41/0.58  # Proof found!
% 0.41/0.58  # SZS status Theorem
% 0.41/0.58  # SZS output start CNFRefutation
% 0.41/0.58  fof(t76_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_tops_1)).
% 0.41/0.58  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.41/0.58  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.41/0.58  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.41/0.58  fof(t44_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,X2),X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 0.41/0.58  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.41/0.58  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 0.41/0.58  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 0.41/0.58  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 0.41/0.58  fof(t48_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(X2,k2_pre_topc(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_pre_topc)).
% 0.41/0.58  fof(t74_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k1_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tops_1)).
% 0.41/0.58  fof(dt_k2_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 0.41/0.58  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.41/0.58  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 0.41/0.58  fof(fc9_tops_1, axiom, ![X1, X2]:(((v2_pre_topc(X1)&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v3_pre_topc(k1_tops_1(X1,X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 0.41/0.58  fof(t56_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v3_pre_topc(X2,X1)&r1_tarski(X2,X3))=>r1_tarski(X2,k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tops_1)).
% 0.41/0.58  fof(l78_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 0.41/0.58  fof(c_0_17, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X2))))), inference(assume_negation,[status(cth)],[t76_tops_1])).
% 0.41/0.58  fof(c_0_18, plain, ![X24, X25]:((~m1_subset_1(X24,k1_zfmisc_1(X25))|r1_tarski(X24,X25))&(~r1_tarski(X24,X25)|m1_subset_1(X24,k1_zfmisc_1(X25)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.41/0.58  fof(c_0_19, negated_conjecture, ((v2_pre_topc(esk1_0)&l1_pre_topc(esk1_0))&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&((~v3_pre_topc(esk2_0,esk1_0)|k2_tops_1(esk1_0,esk2_0)!=k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0))&(v3_pre_topc(esk2_0,esk1_0)|k2_tops_1(esk1_0,esk2_0)=k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 0.41/0.58  fof(c_0_20, plain, ![X7, X8, X9]:(~r1_tarski(X7,X8)|~r1_tarski(X8,X9)|r1_tarski(X7,X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.41/0.58  cnf(c_0_21, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.41/0.58  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.41/0.58  cnf(c_0_23, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.41/0.58  cnf(c_0_24, negated_conjecture, (r1_tarski(esk2_0,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.41/0.58  fof(c_0_25, plain, ![X10, X11]:r1_tarski(k4_xboole_0(X10,X11),X10), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.41/0.58  cnf(c_0_26, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.41/0.58  cnf(c_0_27, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.41/0.58  fof(c_0_28, plain, ![X34, X35]:(~l1_pre_topc(X34)|(~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))|r1_tarski(k1_tops_1(X34,X35),X35))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).
% 0.41/0.58  cnf(c_0_29, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.41/0.58  cnf(c_0_30, negated_conjecture, (r1_tarski(k4_xboole_0(esk2_0,X1),u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.41/0.58  fof(c_0_31, plain, ![X12, X13, X14]:k4_xboole_0(k4_xboole_0(X12,X13),X14)=k4_xboole_0(X12,k2_xboole_0(X13,X14)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.41/0.58  cnf(c_0_32, plain, (r1_tarski(k1_tops_1(X1,X2),X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.41/0.58  cnf(c_0_33, negated_conjecture, (m1_subset_1(k4_xboole_0(esk2_0,X1),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.41/0.58  cnf(c_0_34, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.41/0.58  fof(c_0_35, plain, ![X15, X16]:(~m1_subset_1(X16,k1_zfmisc_1(X15))|k3_subset_1(X15,X16)=k4_xboole_0(X15,X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.41/0.58  cnf(c_0_36, plain, (m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_29, c_0_27])).
% 0.41/0.58  cnf(c_0_37, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.41/0.58  cnf(c_0_38, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_23, c_0_27])).
% 0.41/0.58  cnf(c_0_39, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(esk2_0,X1)),k4_xboole_0(esk2_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34])])).
% 0.41/0.58  fof(c_0_40, plain, ![X19, X20]:(~m1_subset_1(X20,k1_zfmisc_1(X19))|k3_subset_1(X19,k3_subset_1(X19,X20))=X20), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 0.41/0.58  cnf(c_0_41, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.41/0.58  cnf(c_0_42, plain, (m1_subset_1(k4_xboole_0(k4_xboole_0(X1,X2),X3),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.41/0.58  fof(c_0_43, plain, ![X21, X22, X23]:(~m1_subset_1(X22,k1_zfmisc_1(X21))|k7_subset_1(X21,X22,X23)=k4_xboole_0(X22,X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 0.41/0.58  fof(c_0_44, plain, ![X28, X29]:(~l1_pre_topc(X28)|(~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))|r1_tarski(X29,k2_pre_topc(X28,X29)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_pre_topc])])])).
% 0.41/0.58  cnf(c_0_45, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(esk2_0,X1)),esk2_0)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.41/0.58  cnf(c_0_46, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.41/0.58  cnf(c_0_47, plain, (k3_subset_1(X1,k4_xboole_0(k4_xboole_0(X1,X2),X3))=k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,X2),X3))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.41/0.58  cnf(c_0_48, plain, (k3_subset_1(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X1,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_41, c_0_36])).
% 0.41/0.58  fof(c_0_49, plain, ![X39, X40]:(~l1_pre_topc(X39)|(~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))|k1_tops_1(X39,X40)=k7_subset_1(u1_struct_0(X39),X40,k2_tops_1(X39,X40)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_tops_1])])])).
% 0.41/0.58  cnf(c_0_50, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.41/0.58  cnf(c_0_51, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,esk2_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_22]), c_0_34])])).
% 0.41/0.58  cnf(c_0_52, plain, (r1_tarski(X2,k2_pre_topc(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.41/0.58  fof(c_0_53, plain, ![X26, X27]:(~l1_pre_topc(X26)|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|m1_subset_1(k2_pre_topc(X26,X27),k1_zfmisc_1(u1_struct_0(X26)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).
% 0.41/0.58  cnf(c_0_54, negated_conjecture, (r1_tarski(X1,esk2_0)|~r1_tarski(X1,k1_tops_1(esk1_0,k4_xboole_0(esk2_0,X2)))), inference(spm,[status(thm)],[c_0_23, c_0_45])).
% 0.41/0.58  cnf(c_0_55, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,X2),X3)))=k4_xboole_0(k4_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_42]), c_0_47]), c_0_48])).
% 0.41/0.58  cnf(c_0_56, plain, (k1_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.41/0.58  cnf(c_0_57, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)=k4_xboole_0(esk2_0,X1)), inference(spm,[status(thm)],[c_0_50, c_0_22])).
% 0.41/0.58  fof(c_0_58, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.41/0.58  cnf(c_0_59, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,esk2_0),u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_26, c_0_51])).
% 0.41/0.58  cnf(c_0_60, negated_conjecture, (r1_tarski(esk2_0,k2_pre_topc(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_22]), c_0_34])])).
% 0.41/0.58  cnf(c_0_61, plain, (m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.41/0.58  cnf(c_0_62, negated_conjecture, (r1_tarski(X1,esk2_0)|~r1_tarski(X1,k1_tops_1(esk1_0,k4_xboole_0(k4_xboole_0(esk2_0,X2),X3)))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.41/0.58  cnf(c_0_63, negated_conjecture, (k4_xboole_0(esk2_0,k2_tops_1(esk1_0,esk2_0))=k1_tops_1(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_22]), c_0_57]), c_0_34])])).
% 0.41/0.58  cnf(c_0_64, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.41/0.58  cnf(c_0_65, negated_conjecture, (m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_29, c_0_59])).
% 0.41/0.58  cnf(c_0_66, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(k2_pre_topc(esk1_0,esk2_0)))), inference(spm,[status(thm)],[c_0_29, c_0_60])).
% 0.41/0.58  cnf(c_0_67, negated_conjecture, (m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_22]), c_0_34])])).
% 0.41/0.58  cnf(c_0_68, negated_conjecture, (r1_tarski(X1,esk2_0)|~r1_tarski(X1,k1_tops_1(esk1_0,k4_xboole_0(k1_tops_1(esk1_0,esk2_0),X2)))), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.41/0.58  cnf(c_0_69, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_64])).
% 0.41/0.58  cnf(c_0_70, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),X1)=k4_xboole_0(k1_tops_1(esk1_0,esk2_0),X1)), inference(spm,[status(thm)],[c_0_50, c_0_65])).
% 0.41/0.58  fof(c_0_71, plain, ![X4]:k2_xboole_0(X4,X4)=X4, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 0.41/0.58  cnf(c_0_72, negated_conjecture, (k3_subset_1(k2_pre_topc(esk1_0,esk2_0),esk2_0)=k4_xboole_0(k2_pre_topc(esk1_0,esk2_0),esk2_0)), inference(spm,[status(thm)],[c_0_41, c_0_66])).
% 0.41/0.58  cnf(c_0_73, negated_conjecture, (v3_pre_topc(esk2_0,esk1_0)|k2_tops_1(esk1_0,esk2_0)=k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.41/0.58  cnf(c_0_74, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),X1)=k4_xboole_0(k2_pre_topc(esk1_0,esk2_0),X1)), inference(spm,[status(thm)],[c_0_50, c_0_67])).
% 0.41/0.58  cnf(c_0_75, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(k1_tops_1(esk1_0,esk2_0),X1)),esk2_0)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.41/0.58  cnf(c_0_76, negated_conjecture, (k4_xboole_0(k1_tops_1(esk1_0,esk2_0),k2_tops_1(esk1_0,k1_tops_1(esk1_0,esk2_0)))=k1_tops_1(esk1_0,k1_tops_1(esk1_0,esk2_0))), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_65]), c_0_34])]), c_0_70])).
% 0.41/0.58  cnf(c_0_77, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.41/0.58  cnf(c_0_78, negated_conjecture, (k4_xboole_0(k2_pre_topc(esk1_0,esk2_0),k4_xboole_0(k2_pre_topc(esk1_0,esk2_0),esk2_0))=esk2_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_66]), c_0_72]), c_0_48])).
% 0.41/0.58  cnf(c_0_79, negated_conjecture, (k4_xboole_0(k2_pre_topc(esk1_0,esk2_0),esk2_0)=k2_tops_1(esk1_0,esk2_0)|v3_pre_topc(esk2_0,esk1_0)), inference(rw,[status(thm)],[c_0_73, c_0_74])).
% 0.41/0.58  fof(c_0_80, plain, ![X30, X31]:(~v2_pre_topc(X30)|~l1_pre_topc(X30)|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))|v3_pre_topc(k1_tops_1(X30,X31),X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).
% 0.41/0.58  cnf(c_0_81, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,k1_tops_1(esk1_0,k1_tops_1(esk1_0,esk2_0))),esk2_0)), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.41/0.58  fof(c_0_82, plain, ![X36, X37, X38]:(~l1_pre_topc(X36)|(~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))|(~m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X36)))|(~v3_pre_topc(X37,X36)|~r1_tarski(X37,X38)|r1_tarski(X37,k1_tops_1(X36,X38)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_tops_1])])])).
% 0.41/0.58  cnf(c_0_83, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_37, c_0_77])).
% 0.41/0.58  cnf(c_0_84, negated_conjecture, (k4_xboole_0(k2_pre_topc(esk1_0,esk2_0),k2_tops_1(esk1_0,esk2_0))=esk2_0|v3_pre_topc(esk2_0,esk1_0)), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 0.41/0.58  cnf(c_0_85, plain, (v3_pre_topc(k1_tops_1(X1,X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.41/0.58  cnf(c_0_86, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.41/0.58  cnf(c_0_87, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,k1_tops_1(esk1_0,k1_tops_1(esk1_0,esk2_0))),u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_26, c_0_81])).
% 0.41/0.58  cnf(c_0_88, plain, (r1_tarski(X2,k1_tops_1(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v3_pre_topc(X2,X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_82])).
% 0.41/0.58  cnf(c_0_89, negated_conjecture, (k1_tops_1(esk1_0,esk2_0)=esk2_0|v3_pre_topc(esk2_0,esk1_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_63])).
% 0.41/0.58  cnf(c_0_90, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.41/0.58  cnf(c_0_91, negated_conjecture, (v3_pre_topc(k1_tops_1(esk1_0,X1),esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_34])])).
% 0.41/0.58  cnf(c_0_92, negated_conjecture, (m1_subset_1(k1_tops_1(esk1_0,k1_tops_1(esk1_0,k1_tops_1(esk1_0,esk2_0))),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_29, c_0_87])).
% 0.41/0.58  cnf(c_0_93, negated_conjecture, (k1_tops_1(esk1_0,esk2_0)=esk2_0|r1_tarski(esk2_0,k1_tops_1(esk1_0,X1))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(esk2_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_34]), c_0_22])])).
% 0.41/0.58  cnf(c_0_94, negated_conjecture, (k1_tops_1(esk1_0,esk2_0)=esk2_0|~r1_tarski(esk2_0,k1_tops_1(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_90, c_0_51])).
% 0.41/0.58  fof(c_0_95, plain, ![X32, X33]:(~l1_pre_topc(X32)|(~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))|k2_tops_1(X32,X33)=k7_subset_1(u1_struct_0(X32),k2_pre_topc(X32,X33),k1_tops_1(X32,X33)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l78_tops_1])])])).
% 0.41/0.58  cnf(c_0_96, negated_conjecture, (~v3_pre_topc(esk2_0,esk1_0)|k2_tops_1(esk1_0,esk2_0)!=k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.41/0.58  cnf(c_0_97, negated_conjecture, (v3_pre_topc(k1_tops_1(esk1_0,k1_tops_1(esk1_0,k1_tops_1(esk1_0,k1_tops_1(esk1_0,esk2_0)))),esk1_0)), inference(spm,[status(thm)],[c_0_91, c_0_92])).
% 0.41/0.58  cnf(c_0_98, negated_conjecture, (k1_tops_1(esk1_0,esk2_0)=esk2_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_22]), c_0_69])]), c_0_94])).
% 0.41/0.58  cnf(c_0_99, plain, (k2_tops_1(X1,X2)=k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k1_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_95])).
% 0.41/0.58  cnf(c_0_100, negated_conjecture, (k4_xboole_0(k2_pre_topc(esk1_0,esk2_0),esk2_0)!=k2_tops_1(esk1_0,esk2_0)|~v3_pre_topc(esk2_0,esk1_0)), inference(rw,[status(thm)],[c_0_96, c_0_74])).
% 0.41/0.58  cnf(c_0_101, negated_conjecture, (v3_pre_topc(esk2_0,esk1_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_97, c_0_98]), c_0_98]), c_0_98]), c_0_98])).
% 0.41/0.58  cnf(c_0_102, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,k4_xboole_0(esk2_0,X1)),k1_tops_1(esk1_0,k4_xboole_0(esk2_0,X1)))=k2_tops_1(esk1_0,k4_xboole_0(esk2_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_33]), c_0_34])])).
% 0.41/0.58  cnf(c_0_103, negated_conjecture, (k4_xboole_0(esk2_0,k2_tops_1(esk1_0,esk2_0))=esk2_0), inference(rw,[status(thm)],[c_0_63, c_0_98])).
% 0.41/0.58  cnf(c_0_104, negated_conjecture, (k4_xboole_0(k2_pre_topc(esk1_0,esk2_0),esk2_0)!=k2_tops_1(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_100, c_0_101])])).
% 0.41/0.58  cnf(c_0_105, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_103]), c_0_74]), c_0_98]), c_0_104]), ['proof']).
% 0.41/0.58  # SZS output end CNFRefutation
% 0.41/0.58  # Proof object total steps             : 106
% 0.41/0.58  # Proof object clause steps            : 71
% 0.41/0.58  # Proof object formula steps           : 35
% 0.41/0.58  # Proof object conjectures             : 48
% 0.41/0.58  # Proof object clause conjectures      : 45
% 0.41/0.58  # Proof object formula conjectures     : 3
% 0.41/0.58  # Proof object initial clauses used    : 23
% 0.41/0.58  # Proof object initial formulas used   : 17
% 0.41/0.58  # Proof object generating inferences   : 42
% 0.41/0.58  # Proof object simplifying inferences  : 42
% 0.41/0.58  # Training examples: 0 positive, 0 negative
% 0.41/0.58  # Parsed axioms                        : 18
% 0.41/0.58  # Removed by relevancy pruning/SinE    : 0
% 0.41/0.58  # Initial clauses                      : 25
% 0.41/0.58  # Removed in clause preprocessing      : 0
% 0.41/0.58  # Initial clauses in saturation        : 25
% 0.41/0.58  # Processed clauses                    : 2908
% 0.41/0.58  # ...of these trivial                  : 244
% 0.41/0.59  # ...subsumed                          : 964
% 0.41/0.59  # ...remaining for further processing  : 1700
% 0.41/0.59  # Other redundant clauses eliminated   : 2
% 0.41/0.59  # Clauses deleted for lack of memory   : 0
% 0.41/0.59  # Backward-subsumed                    : 0
% 0.41/0.59  # Backward-rewritten                   : 395
% 0.41/0.59  # Generated clauses                    : 17277
% 0.41/0.59  # ...of the previous two non-trivial   : 13412
% 0.41/0.59  # Contextual simplify-reflections      : 1
% 0.41/0.59  # Paramodulations                      : 17275
% 0.41/0.59  # Factorizations                       : 0
% 0.41/0.59  # Equation resolutions                 : 2
% 0.41/0.59  # Propositional unsat checks           : 0
% 0.41/0.59  #    Propositional check models        : 0
% 0.41/0.59  #    Propositional check unsatisfiable : 0
% 0.41/0.59  #    Propositional clauses             : 0
% 0.41/0.59  #    Propositional clauses after purity: 0
% 0.41/0.59  #    Propositional unsat core size     : 0
% 0.41/0.59  #    Propositional preprocessing time  : 0.000
% 0.41/0.59  #    Propositional encoding time       : 0.000
% 0.41/0.59  #    Propositional solver time         : 0.000
% 0.41/0.59  #    Success case prop preproc time    : 0.000
% 0.41/0.59  #    Success case prop encoding time   : 0.000
% 0.41/0.59  #    Success case prop solver time     : 0.000
% 0.41/0.59  # Current number of processed clauses  : 1279
% 0.41/0.59  #    Positive orientable unit clauses  : 1076
% 0.41/0.59  #    Positive unorientable unit clauses: 0
% 0.41/0.59  #    Negative unit clauses             : 1
% 0.41/0.59  #    Non-unit-clauses                  : 202
% 0.41/0.59  # Current number of unprocessed clauses: 10249
% 0.41/0.59  # ...number of literals in the above   : 13319
% 0.41/0.59  # Current number of archived formulas  : 0
% 0.41/0.59  # Current number of archived clauses   : 419
% 0.41/0.59  # Clause-clause subsumption calls (NU) : 19384
% 0.41/0.59  # Rec. Clause-clause subsumption calls : 14629
% 0.41/0.59  # Non-unit clause-clause subsumptions  : 965
% 0.41/0.59  # Unit Clause-clause subsumption calls : 49
% 0.41/0.59  # Rewrite failures with RHS unbound    : 0
% 0.41/0.59  # BW rewrite match attempts            : 45721
% 0.41/0.59  # BW rewrite match successes           : 99
% 0.41/0.59  # Condensation attempts                : 0
% 0.41/0.59  # Condensation successes               : 0
% 0.41/0.59  # Termbank termtop insertions          : 398568
% 0.41/0.59  
% 0.41/0.59  # -------------------------------------------------
% 0.41/0.59  # User time                : 0.240 s
% 0.41/0.59  # System time              : 0.012 s
% 0.41/0.59  # Total time               : 0.251 s
% 0.41/0.59  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------

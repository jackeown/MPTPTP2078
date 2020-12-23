%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : setfam_1__t59_setfam_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:19 EDT 2019

% Result     : Theorem 264.83s
% Output     : CNFRefutation 264.83s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 196 expanded)
%              Number of clauses        :   31 (  83 expanded)
%              Number of leaves         :    7 (  47 expanded)
%              Depth                    :   10
%              Number of atoms          :  131 ( 615 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t59_setfam_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
         => ( r1_tarski(X2,X3)
           => r1_tarski(k8_setfam_1(X1,X3),k8_setfam_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t59_setfam_1.p',t59_setfam_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t59_setfam_1.p',t5_subset)).

fof(dt_k8_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => m1_subset_1(k8_setfam_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t59_setfam_1.p',dt_k8_setfam_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t59_setfam_1.p',d3_tarski)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t59_setfam_1.p',t4_subset)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t59_setfam_1.p',t2_subset)).

fof(t58_setfam_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( r2_hidden(X2,X1)
       => ( r2_hidden(X2,k8_setfam_1(X1,X3))
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
             => r2_hidden(X2,X4) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t59_setfam_1.p',t58_setfam_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
           => ( r1_tarski(X2,X3)
             => r1_tarski(k8_setfam_1(X1,X3),k8_setfam_1(X1,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t59_setfam_1])).

fof(c_0_8,plain,(
    ! [X34,X35,X36] :
      ( ~ r2_hidden(X34,X35)
      | ~ m1_subset_1(X35,k1_zfmisc_1(X36))
      | ~ v1_xboole_0(X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_9,plain,(
    ! [X16,X17] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(X16)))
      | m1_subset_1(k8_setfam_1(X16,X17),k1_zfmisc_1(X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_setfam_1])])).

fof(c_0_10,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0)))
    & m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0)))
    & r1_tarski(esk2_0,esk3_0)
    & ~ r1_tarski(k8_setfam_1(esk1_0,esk3_0),k8_setfam_1(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_11,plain,(
    ! [X10,X11,X12,X13,X14] :
      ( ( ~ r1_tarski(X10,X11)
        | ~ r2_hidden(X12,X10)
        | r2_hidden(X12,X11) )
      & ( r2_hidden(esk4_2(X13,X14),X13)
        | r1_tarski(X13,X14) )
      & ( ~ r2_hidden(esk4_2(X13,X14),X14)
        | r1_tarski(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_12,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( m1_subset_1(k8_setfam_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( ~ r1_tarski(k8_setfam_1(esk1_0,esk3_0),k8_setfam_1(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( r2_hidden(esk4_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_16,plain,(
    ! [X26,X27,X28] :
      ( ~ r2_hidden(X26,X27)
      | ~ m1_subset_1(X27,k1_zfmisc_1(X28))
      | m1_subset_1(X26,X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_17,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,k8_setfam_1(X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(esk4_2(k8_setfam_1(esk1_0,esk3_0),k8_setfam_1(esk1_0,esk2_0)),k8_setfam_1(esk1_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_20,plain,(
    ! [X22,X23] :
      ( ~ m1_subset_1(X22,X23)
      | v1_xboole_0(X23)
      | r2_hidden(X22,X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_21,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_22,plain,(
    ! [X29,X30,X31,X32] :
      ( ( ~ r2_hidden(X30,k8_setfam_1(X29,X31))
        | ~ r2_hidden(X32,X31)
        | r2_hidden(X30,X32)
        | ~ r2_hidden(X30,X29)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k1_zfmisc_1(X29))) )
      & ( r2_hidden(esk6_3(X29,X30,X31),X31)
        | r2_hidden(X30,k8_setfam_1(X29,X31))
        | ~ r2_hidden(X30,X29)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k1_zfmisc_1(X29))) )
      & ( ~ r2_hidden(X30,esk6_3(X29,X30,X31))
        | r2_hidden(X30,k8_setfam_1(X29,X31))
        | ~ r2_hidden(X30,X29)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k1_zfmisc_1(X29))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t58_setfam_1])])])])])).

cnf(c_0_23,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])])).

cnf(c_0_24,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,k8_setfam_1(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(spm,[status(thm)],[c_0_21,c_0_13])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,k8_setfam_1(X2,X3))
    | ~ r2_hidden(X4,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,k8_setfam_1(X2,X3))
    | ~ r2_hidden(X1,esk6_3(X2,X1,X3))
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(X1,esk1_0)
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk4_2(k8_setfam_1(esk1_0,esk3_0),k8_setfam_1(esk1_0,esk2_0)),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_18]),c_0_19])])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk4_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k8_setfam_1(esk1_0,esk3_0))
    | ~ r2_hidden(X2,esk3_0)
    | ~ r2_hidden(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_19])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(X1,k8_setfam_1(esk1_0,esk2_0))
    | ~ r2_hidden(X1,esk6_3(esk1_0,X1,esk2_0))
    | ~ r2_hidden(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk4_2(k8_setfam_1(esk1_0,esk3_0),k8_setfam_1(esk1_0,esk2_0)),esk1_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_38,negated_conjecture,
    ( ~ r2_hidden(esk4_2(k8_setfam_1(esk1_0,esk3_0),k8_setfam_1(esk1_0,esk2_0)),k8_setfam_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k8_setfam_1(esk1_0,esk3_0))
    | ~ r2_hidden(X1,esk1_0)
    | ~ r2_hidden(X2,esk2_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_40,negated_conjecture,
    ( ~ r2_hidden(esk4_2(k8_setfam_1(esk1_0,esk3_0),k8_setfam_1(esk1_0,esk2_0)),esk6_3(esk1_0,esk4_2(k8_setfam_1(esk1_0,esk3_0),k8_setfam_1(esk1_0,esk2_0)),esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk4_2(k8_setfam_1(esk1_0,esk3_0),k8_setfam_1(esk1_0,esk2_0)),X1)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_37]),c_0_18])])).

cnf(c_0_42,plain,
    ( r2_hidden(esk6_3(X1,X2,X3),X3)
    | r2_hidden(X2,k8_setfam_1(X1,X3))
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_43,negated_conjecture,
    ( ~ r2_hidden(esk6_3(esk1_0,esk4_2(k8_setfam_1(esk1_0,esk3_0),k8_setfam_1(esk1_0,esk2_0)),esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk6_3(esk1_0,X1,esk2_0),esk2_0)
    | r2_hidden(X1,k8_setfam_1(esk1_0,esk2_0))
    | ~ r2_hidden(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_30])).

cnf(c_0_45,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_37])]),c_0_38]),
    [proof]).
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : setfam_1__t49_setfam_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:17 EDT 2019

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   32 ( 105 expanded)
%              Number of clauses        :   19 (  40 expanded)
%              Number of leaves         :    6 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :  101 ( 411 expanded)
%              Number of equality atoms :   18 (  37 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t49_setfam_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r2_hidden(k3_subset_1(X1,X3),k7_setfam_1(X1,X2))
          <=> r2_hidden(X3,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t49_setfam_1.p',t49_setfam_1)).

fof(involutiveness_k7_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k7_setfam_1(X1,k7_setfam_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t49_setfam_1.p',involutiveness_k7_setfam_1)).

fof(dt_k7_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t49_setfam_1.p',dt_k7_setfam_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t49_setfam_1.p',involutiveness_k3_subset_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t49_setfam_1.p',dt_k3_subset_1)).

fof(d8_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
         => ( X3 = k7_setfam_1(X1,X2)
          <=> ! [X4] :
                ( m1_subset_1(X4,k1_zfmisc_1(X1))
               => ( r2_hidden(X4,X3)
                <=> r2_hidden(k3_subset_1(X1,X4),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t49_setfam_1.p',d8_setfam_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => ( r2_hidden(k3_subset_1(X1,X3),k7_setfam_1(X1,X2))
            <=> r2_hidden(X3,X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t49_setfam_1])).

fof(c_0_7,plain,(
    ! [X23,X24] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(k1_zfmisc_1(X23)))
      | k7_setfam_1(X23,k7_setfam_1(X23,X24)) = X24 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k7_setfam_1])])).

fof(c_0_8,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0)))
    & m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0))
    & ( ~ r2_hidden(k3_subset_1(esk1_0,esk3_0),k7_setfam_1(esk1_0,esk2_0))
      | ~ r2_hidden(esk3_0,esk2_0) )
    & ( r2_hidden(k3_subset_1(esk1_0,esk3_0),k7_setfam_1(esk1_0,esk2_0))
      | r2_hidden(esk3_0,esk2_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_9,plain,(
    ! [X17,X18] :
      ( ~ m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(X17)))
      | m1_subset_1(k7_setfam_1(X17,X18),k1_zfmisc_1(k1_zfmisc_1(X17))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_setfam_1])])).

fof(c_0_10,plain,(
    ! [X21,X22] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(X21))
      | k3_subset_1(X21,k3_subset_1(X21,X22)) = X22 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

fof(c_0_11,plain,(
    ! [X15,X16] :
      ( ~ m1_subset_1(X16,k1_zfmisc_1(X15))
      | m1_subset_1(k3_subset_1(X15,X16),k1_zfmisc_1(X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

fof(c_0_12,plain,(
    ! [X10,X11,X12,X13] :
      ( ( ~ r2_hidden(X13,X12)
        | r2_hidden(k3_subset_1(X10,X13),X11)
        | ~ m1_subset_1(X13,k1_zfmisc_1(X10))
        | X12 != k7_setfam_1(X10,X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k1_zfmisc_1(X10)))
        | ~ m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(X10))) )
      & ( ~ r2_hidden(k3_subset_1(X10,X13),X11)
        | r2_hidden(X13,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(X10))
        | X12 != k7_setfam_1(X10,X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k1_zfmisc_1(X10)))
        | ~ m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(X10))) )
      & ( m1_subset_1(esk4_3(X10,X11,X12),k1_zfmisc_1(X10))
        | X12 = k7_setfam_1(X10,X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k1_zfmisc_1(X10)))
        | ~ m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(X10))) )
      & ( ~ r2_hidden(esk4_3(X10,X11,X12),X12)
        | ~ r2_hidden(k3_subset_1(X10,esk4_3(X10,X11,X12)),X11)
        | X12 = k7_setfam_1(X10,X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k1_zfmisc_1(X10)))
        | ~ m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(X10))) )
      & ( r2_hidden(esk4_3(X10,X11,X12),X12)
        | r2_hidden(k3_subset_1(X10,esk4_3(X10,X11,X12)),X11)
        | X12 = k7_setfam_1(X10,X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k1_zfmisc_1(X10)))
        | ~ m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(X10))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_setfam_1])])])])])).

cnf(c_0_13,plain,
    ( k7_setfam_1(X2,k7_setfam_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( m1_subset_1(k7_setfam_1(X2,X1),k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_18,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k3_subset_1(X1,X2),X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | X4 != k7_setfam_1(X1,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(k3_subset_1(esk1_0,esk3_0),k7_setfam_1(esk1_0,esk2_0))
    | r2_hidden(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_21,negated_conjecture,
    ( k7_setfam_1(esk1_0,k7_setfam_1(esk1_0,esk2_0)) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(k7_setfam_1(esk1_0,esk2_0),k1_zfmisc_1(k1_zfmisc_1(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_15,c_0_14])).

cnf(c_0_23,negated_conjecture,
    ( k3_subset_1(esk1_0,k3_subset_1(esk1_0,esk3_0)) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(k3_subset_1(esk1_0,esk3_0),k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk3_0,esk2_0)
    | r2_hidden(esk3_0,X1)
    | X1 != esk2_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_17])]),c_0_21]),c_0_22])])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(k3_subset_1(esk1_0,esk3_0),X1)
    | X1 != k7_setfam_1(esk1_0,X2)
    | ~ r2_hidden(esk3_0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk1_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_23]),c_0_24])])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_14])).

cnf(c_0_28,negated_conjecture,
    ( ~ r2_hidden(k3_subset_1(esk1_0,esk3_0),k7_setfam_1(esk1_0,esk2_0))
    | ~ r2_hidden(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(k3_subset_1(esk1_0,esk3_0),X1)
    | X1 != k7_setfam_1(esk1_0,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_14])])).

cnf(c_0_30,negated_conjecture,
    ( ~ r2_hidden(k3_subset_1(esk1_0,esk3_0),k7_setfam_1(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_27])])).

cnf(c_0_31,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_22]),c_0_30]),
    [proof]).
%------------------------------------------------------------------------------

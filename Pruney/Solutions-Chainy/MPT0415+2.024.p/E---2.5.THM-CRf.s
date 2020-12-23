%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:47:41 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 584 expanded)
%              Number of clauses        :   39 ( 226 expanded)
%              Number of leaves         :    6 ( 143 expanded)
%              Depth                    :   17
%              Number of atoms          :  168 (2012 expanded)
%              Number of equality atoms :   31 ( 677 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t46_setfam_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ~ ( X2 != k1_xboole_0
          & k7_setfam_1(X1,X2) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_setfam_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_setfam_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(involutiveness_k7_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k7_setfam_1(X1,k7_setfam_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
       => ~ ( X2 != k1_xboole_0
            & k7_setfam_1(X1,X2) = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t46_setfam_1])).

fof(c_0_7,plain,(
    ! [X9,X10,X11,X12] :
      ( ( ~ r2_hidden(X12,X11)
        | r2_hidden(k3_subset_1(X9,X12),X10)
        | ~ m1_subset_1(X12,k1_zfmisc_1(X9))
        | X11 != k7_setfam_1(X9,X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(X9)))
        | ~ m1_subset_1(X10,k1_zfmisc_1(k1_zfmisc_1(X9))) )
      & ( ~ r2_hidden(k3_subset_1(X9,X12),X10)
        | r2_hidden(X12,X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(X9))
        | X11 != k7_setfam_1(X9,X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(X9)))
        | ~ m1_subset_1(X10,k1_zfmisc_1(k1_zfmisc_1(X9))) )
      & ( m1_subset_1(esk1_3(X9,X10,X11),k1_zfmisc_1(X9))
        | X11 = k7_setfam_1(X9,X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(X9)))
        | ~ m1_subset_1(X10,k1_zfmisc_1(k1_zfmisc_1(X9))) )
      & ( ~ r2_hidden(esk1_3(X9,X10,X11),X11)
        | ~ r2_hidden(k3_subset_1(X9,esk1_3(X9,X10,X11)),X10)
        | X11 = k7_setfam_1(X9,X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(X9)))
        | ~ m1_subset_1(X10,k1_zfmisc_1(k1_zfmisc_1(X9))) )
      & ( r2_hidden(esk1_3(X9,X10,X11),X11)
        | r2_hidden(k3_subset_1(X9,esk1_3(X9,X10,X11)),X10)
        | X11 = k7_setfam_1(X9,X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(X9)))
        | ~ m1_subset_1(X10,k1_zfmisc_1(k1_zfmisc_1(X9))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_setfam_1])])])])])).

fof(c_0_8,plain,(
    ! [X16,X17,X18] :
      ( ~ r2_hidden(X16,X17)
      | ~ m1_subset_1(X17,k1_zfmisc_1(X18))
      | m1_subset_1(X16,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_9,plain,(
    ! [X14,X15] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(X14)))
      | k7_setfam_1(X14,k7_setfam_1(X14,X15)) = X15 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k7_setfam_1])])).

fof(c_0_10,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))
    & esk3_0 != k1_xboole_0
    & k7_setfam_1(esk2_0,esk3_0) = k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

cnf(c_0_11,plain,
    ( r2_hidden(k3_subset_1(X3,X1),X4)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | X2 != k7_setfam_1(X3,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k7_setfam_1(X2,k7_setfam_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( k7_setfam_1(esk2_0,esk3_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_16,plain,(
    ! [X8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X8)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_17,plain,(
    ! [X5,X6,X7] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(X5))
      | ~ r2_hidden(X7,X6)
      | r2_hidden(X7,X5) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_18,plain,
    ( r2_hidden(k3_subset_1(X1,X2),X3)
    | X4 != k7_setfam_1(X1,X3)
    | ~ r2_hidden(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(csr,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( k7_setfam_1(esk2_0,k1_xboole_0) = esk3_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])).

cnf(c_0_20,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(k3_subset_1(esk2_0,X1),k1_xboole_0)
    | X2 != esk3_0
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(k3_subset_1(esk2_0,X1),k1_xboole_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_22]),c_0_14])])).

cnf(c_0_25,plain,
    ( X3 = k7_setfam_1(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(k3_subset_1(X1,esk1_3(X1,X2,X3)),X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(k3_subset_1(esk2_0,X1),X2)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_27,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k3_subset_1(X1,X2),X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | X4 != k7_setfam_1(X1,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_28,negated_conjecture,
    ( k7_setfam_1(esk2_0,X1) = esk3_0
    | ~ r2_hidden(esk1_3(esk2_0,X1,esk3_0),esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk2_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_14]),c_0_26])).

cnf(c_0_29,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(esk2_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_14])).

cnf(c_0_31,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(k3_subset_1(X1,esk1_3(X1,X2,X3)),X2)
    | X3 = k7_setfam_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(X1,X2)
    | X2 != k1_xboole_0
    | ~ r2_hidden(k3_subset_1(esk2_0,X1),esk3_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_15]),c_0_14])])).

cnf(c_0_33,negated_conjecture,
    ( ~ r2_hidden(esk1_3(esk2_0,esk3_0,esk3_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_14]),c_0_15]),c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( X1 = k7_setfam_1(X2,esk3_0)
    | r2_hidden(esk1_3(X2,esk3_0,X1),X1)
    | m1_subset_1(k3_subset_1(X2,esk1_3(X2,esk3_0,X1)),k1_zfmisc_1(esk2_0))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(k3_subset_1(esk2_0,X1),esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_32]),c_0_20])])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(k3_subset_1(esk2_0,esk1_3(esk2_0,esk3_0,esk3_0)),k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_15]),c_0_14])]),c_0_29])).

cnf(c_0_37,plain,
    ( r2_hidden(k3_subset_1(X1,X2),X3)
    | ~ r2_hidden(X2,k7_setfam_1(X1,X3))
    | ~ m1_subset_1(k7_setfam_1(X1,X3),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(k3_subset_1(esk2_0,esk1_3(esk2_0,esk3_0,esk3_0)),k1_xboole_0)
    | ~ r2_hidden(k3_subset_1(esk2_0,k3_subset_1(esk2_0,esk1_3(esk2_0,esk3_0,esk3_0))),esk3_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_39,plain,
    ( r2_hidden(k3_subset_1(X1,X2),X3)
    | ~ r2_hidden(X2,k7_setfam_1(X1,k1_xboole_0))
    | ~ m1_subset_1(k7_setfam_1(X1,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_37]),c_0_20])])).

cnf(c_0_40,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(X1))
    | X3 = k7_setfam_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(k3_subset_1(esk2_0,esk1_3(esk2_0,esk3_0,esk3_0)),k1_xboole_0)
    | ~ r2_hidden(k3_subset_1(esk2_0,esk1_3(esk2_0,esk3_0,esk3_0)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_19]),c_0_19]),c_0_14])])).

cnf(c_0_42,negated_conjecture,
    ( X1 = k7_setfam_1(esk2_0,X2)
    | r2_hidden(esk1_3(esk2_0,X2,X1),k1_xboole_0)
    | ~ r2_hidden(k3_subset_1(esk2_0,esk1_3(esk2_0,X2,X1)),esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_40])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(k3_subset_1(esk2_0,esk1_3(esk2_0,esk3_0,esk3_0)),k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_31]),c_0_15]),c_0_14])]),c_0_29]),c_0_33])).

cnf(c_0_44,negated_conjecture,
    ( k7_setfam_1(esk2_0,X1) = esk3_0
    | r2_hidden(esk1_3(esk2_0,X1,esk3_0),k1_xboole_0)
    | ~ r2_hidden(k3_subset_1(esk2_0,esk1_3(esk2_0,X1,esk3_0)),esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_14])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(k3_subset_1(esk2_0,esk1_3(esk2_0,esk3_0,esk3_0)),X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_43])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(X1,X2)
    | X2 != esk3_0
    | ~ r2_hidden(k3_subset_1(esk2_0,X1),k1_xboole_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_19]),c_0_20])])).

cnf(c_0_47,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_20])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk1_3(esk2_0,esk3_0,esk3_0),k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_14]),c_0_15]),c_0_45])]),c_0_29])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ r2_hidden(k3_subset_1(esk2_0,X1),k1_xboole_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_46]),c_0_14])])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(esk1_3(esk2_0,esk3_0,esk3_0),X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_51,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_45])]),c_0_33]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:43:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.46  # AutoSched0-Mode selected heuristic G_E___107_B00_00_F1_PI_AE_Q4_CS_SP_PS_S070I
% 0.21/0.46  # and selection function SelectVGNonCR.
% 0.21/0.46  #
% 0.21/0.46  # Preprocessing time       : 0.027 s
% 0.21/0.46  # Presaturation interreduction done
% 0.21/0.46  
% 0.21/0.46  # Proof found!
% 0.21/0.46  # SZS status Theorem
% 0.21/0.46  # SZS output start CNFRefutation
% 0.21/0.46  fof(t46_setfam_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>~((X2!=k1_xboole_0&k7_setfam_1(X1,X2)=k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_setfam_1)).
% 0.21/0.46  fof(d8_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(X3=k7_setfam_1(X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(X1))=>(r2_hidden(X4,X3)<=>r2_hidden(k3_subset_1(X1,X4),X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_setfam_1)).
% 0.21/0.46  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.21/0.46  fof(involutiveness_k7_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>k7_setfam_1(X1,k7_setfam_1(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k7_setfam_1)).
% 0.21/0.46  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.21/0.46  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 0.21/0.46  fof(c_0_6, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>~((X2!=k1_xboole_0&k7_setfam_1(X1,X2)=k1_xboole_0)))), inference(assume_negation,[status(cth)],[t46_setfam_1])).
% 0.21/0.46  fof(c_0_7, plain, ![X9, X10, X11, X12]:(((~r2_hidden(X12,X11)|r2_hidden(k3_subset_1(X9,X12),X10)|~m1_subset_1(X12,k1_zfmisc_1(X9))|X11!=k7_setfam_1(X9,X10)|~m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(X9)))|~m1_subset_1(X10,k1_zfmisc_1(k1_zfmisc_1(X9))))&(~r2_hidden(k3_subset_1(X9,X12),X10)|r2_hidden(X12,X11)|~m1_subset_1(X12,k1_zfmisc_1(X9))|X11!=k7_setfam_1(X9,X10)|~m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(X9)))|~m1_subset_1(X10,k1_zfmisc_1(k1_zfmisc_1(X9)))))&((m1_subset_1(esk1_3(X9,X10,X11),k1_zfmisc_1(X9))|X11=k7_setfam_1(X9,X10)|~m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(X9)))|~m1_subset_1(X10,k1_zfmisc_1(k1_zfmisc_1(X9))))&((~r2_hidden(esk1_3(X9,X10,X11),X11)|~r2_hidden(k3_subset_1(X9,esk1_3(X9,X10,X11)),X10)|X11=k7_setfam_1(X9,X10)|~m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(X9)))|~m1_subset_1(X10,k1_zfmisc_1(k1_zfmisc_1(X9))))&(r2_hidden(esk1_3(X9,X10,X11),X11)|r2_hidden(k3_subset_1(X9,esk1_3(X9,X10,X11)),X10)|X11=k7_setfam_1(X9,X10)|~m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(X9)))|~m1_subset_1(X10,k1_zfmisc_1(k1_zfmisc_1(X9))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_setfam_1])])])])])).
% 0.21/0.46  fof(c_0_8, plain, ![X16, X17, X18]:(~r2_hidden(X16,X17)|~m1_subset_1(X17,k1_zfmisc_1(X18))|m1_subset_1(X16,X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.21/0.46  fof(c_0_9, plain, ![X14, X15]:(~m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(X14)))|k7_setfam_1(X14,k7_setfam_1(X14,X15))=X15), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k7_setfam_1])])).
% 0.21/0.46  fof(c_0_10, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))&(esk3_0!=k1_xboole_0&k7_setfam_1(esk2_0,esk3_0)=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.21/0.46  cnf(c_0_11, plain, (r2_hidden(k3_subset_1(X3,X1),X4)|~r2_hidden(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X3))|X2!=k7_setfam_1(X3,X4)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X3)))|~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X3)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.21/0.46  cnf(c_0_12, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.46  cnf(c_0_13, plain, (k7_setfam_1(X2,k7_setfam_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.46  cnf(c_0_14, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.46  cnf(c_0_15, negated_conjecture, (k7_setfam_1(esk2_0,esk3_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.46  fof(c_0_16, plain, ![X8]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X8)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.21/0.46  fof(c_0_17, plain, ![X5, X6, X7]:(~m1_subset_1(X6,k1_zfmisc_1(X5))|(~r2_hidden(X7,X6)|r2_hidden(X7,X5))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.21/0.46  cnf(c_0_18, plain, (r2_hidden(k3_subset_1(X1,X2),X3)|X4!=k7_setfam_1(X1,X3)|~r2_hidden(X2,X4)|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))|~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(csr,[status(thm)],[c_0_11, c_0_12])).
% 0.21/0.46  cnf(c_0_19, negated_conjecture, (k7_setfam_1(esk2_0,k1_xboole_0)=esk3_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15])).
% 0.21/0.46  cnf(c_0_20, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.46  cnf(c_0_21, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.46  cnf(c_0_22, negated_conjecture, (r2_hidden(k3_subset_1(esk2_0,X1),k1_xboole_0)|X2!=esk3_0|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20])])).
% 0.21/0.46  cnf(c_0_23, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_21, c_0_20])).
% 0.21/0.46  cnf(c_0_24, negated_conjecture, (r2_hidden(k3_subset_1(esk2_0,X1),k1_xboole_0)|~r2_hidden(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_22]), c_0_14])])).
% 0.21/0.46  cnf(c_0_25, plain, (X3=k7_setfam_1(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(k3_subset_1(X1,esk1_3(X1,X2,X3)),X2)|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.21/0.46  cnf(c_0_26, negated_conjecture, (r2_hidden(k3_subset_1(esk2_0,X1),X2)|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.21/0.46  cnf(c_0_27, plain, (r2_hidden(X2,X4)|~r2_hidden(k3_subset_1(X1,X2),X3)|~m1_subset_1(X2,k1_zfmisc_1(X1))|X4!=k7_setfam_1(X1,X3)|~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1)))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.21/0.46  cnf(c_0_28, negated_conjecture, (k7_setfam_1(esk2_0,X1)=esk3_0|~r2_hidden(esk1_3(esk2_0,X1,esk3_0),esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_14]), c_0_26])).
% 0.21/0.46  cnf(c_0_29, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.46  cnf(c_0_30, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(esk2_0))|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_12, c_0_14])).
% 0.21/0.46  cnf(c_0_31, plain, (r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(k3_subset_1(X1,esk1_3(X1,X2,X3)),X2)|X3=k7_setfam_1(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.21/0.46  cnf(c_0_32, negated_conjecture, (r2_hidden(X1,X2)|X2!=k1_xboole_0|~r2_hidden(k3_subset_1(esk2_0,X1),esk3_0)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))|~m1_subset_1(X1,k1_zfmisc_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_15]), c_0_14])])).
% 0.21/0.46  cnf(c_0_33, negated_conjecture, (~r2_hidden(esk1_3(esk2_0,esk3_0,esk3_0),esk3_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_14]), c_0_15]), c_0_29])).
% 0.21/0.46  cnf(c_0_34, negated_conjecture, (X1=k7_setfam_1(X2,esk3_0)|r2_hidden(esk1_3(X2,esk3_0,X1),X1)|m1_subset_1(k3_subset_1(X2,esk1_3(X2,esk3_0,X1)),k1_zfmisc_1(esk2_0))|~m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(X2)))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.21/0.46  cnf(c_0_35, negated_conjecture, (r2_hidden(X1,k1_xboole_0)|~r2_hidden(k3_subset_1(esk2_0,X1),esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_32]), c_0_20])])).
% 0.21/0.46  cnf(c_0_36, negated_conjecture, (m1_subset_1(k3_subset_1(esk2_0,esk1_3(esk2_0,esk3_0,esk3_0)),k1_zfmisc_1(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_15]), c_0_14])]), c_0_29])).
% 0.21/0.46  cnf(c_0_37, plain, (r2_hidden(k3_subset_1(X1,X2),X3)|~r2_hidden(X2,k7_setfam_1(X1,X3))|~m1_subset_1(k7_setfam_1(X1,X3),k1_zfmisc_1(k1_zfmisc_1(X1)))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(er,[status(thm)],[c_0_18])).
% 0.21/0.46  cnf(c_0_38, negated_conjecture, (r2_hidden(k3_subset_1(esk2_0,esk1_3(esk2_0,esk3_0,esk3_0)),k1_xboole_0)|~r2_hidden(k3_subset_1(esk2_0,k3_subset_1(esk2_0,esk1_3(esk2_0,esk3_0,esk3_0))),esk3_0)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.21/0.46  cnf(c_0_39, plain, (r2_hidden(k3_subset_1(X1,X2),X3)|~r2_hidden(X2,k7_setfam_1(X1,k1_xboole_0))|~m1_subset_1(k7_setfam_1(X1,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_37]), c_0_20])])).
% 0.21/0.46  cnf(c_0_40, plain, (m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(X1))|X3=k7_setfam_1(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.21/0.46  cnf(c_0_41, negated_conjecture, (r2_hidden(k3_subset_1(esk2_0,esk1_3(esk2_0,esk3_0,esk3_0)),k1_xboole_0)|~r2_hidden(k3_subset_1(esk2_0,esk1_3(esk2_0,esk3_0,esk3_0)),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_19]), c_0_19]), c_0_14])])).
% 0.21/0.46  cnf(c_0_42, negated_conjecture, (X1=k7_setfam_1(esk2_0,X2)|r2_hidden(esk1_3(esk2_0,X2,X1),k1_xboole_0)|~r2_hidden(k3_subset_1(esk2_0,esk1_3(esk2_0,X2,X1)),esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))), inference(spm,[status(thm)],[c_0_35, c_0_40])).
% 0.21/0.46  cnf(c_0_43, negated_conjecture, (r2_hidden(k3_subset_1(esk2_0,esk1_3(esk2_0,esk3_0,esk3_0)),k1_xboole_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_31]), c_0_15]), c_0_14])]), c_0_29]), c_0_33])).
% 0.21/0.46  cnf(c_0_44, negated_conjecture, (k7_setfam_1(esk2_0,X1)=esk3_0|r2_hidden(esk1_3(esk2_0,X1,esk3_0),k1_xboole_0)|~r2_hidden(k3_subset_1(esk2_0,esk1_3(esk2_0,X1,esk3_0)),esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))), inference(spm,[status(thm)],[c_0_42, c_0_14])).
% 0.21/0.46  cnf(c_0_45, negated_conjecture, (r2_hidden(k3_subset_1(esk2_0,esk1_3(esk2_0,esk3_0,esk3_0)),X1)), inference(spm,[status(thm)],[c_0_23, c_0_43])).
% 0.21/0.46  cnf(c_0_46, negated_conjecture, (r2_hidden(X1,X2)|X2!=esk3_0|~r2_hidden(k3_subset_1(esk2_0,X1),k1_xboole_0)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))|~m1_subset_1(X1,k1_zfmisc_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_19]), c_0_20])])).
% 0.21/0.46  cnf(c_0_47, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_12, c_0_20])).
% 0.21/0.46  cnf(c_0_48, negated_conjecture, (r2_hidden(esk1_3(esk2_0,esk3_0,esk3_0),k1_xboole_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_14]), c_0_15]), c_0_45])]), c_0_29])).
% 0.21/0.46  cnf(c_0_49, negated_conjecture, (r2_hidden(X1,esk3_0)|~r2_hidden(k3_subset_1(esk2_0,X1),k1_xboole_0)|~m1_subset_1(X1,k1_zfmisc_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_46]), c_0_14])])).
% 0.21/0.46  cnf(c_0_50, negated_conjecture, (m1_subset_1(esk1_3(esk2_0,esk3_0,esk3_0),X1)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.21/0.46  cnf(c_0_51, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_45])]), c_0_33]), ['proof']).
% 0.21/0.46  # SZS output end CNFRefutation
% 0.21/0.46  # Proof object total steps             : 52
% 0.21/0.46  # Proof object clause steps            : 39
% 0.21/0.46  # Proof object formula steps           : 13
% 0.21/0.46  # Proof object conjectures             : 28
% 0.21/0.46  # Proof object clause conjectures      : 25
% 0.21/0.46  # Proof object formula conjectures     : 3
% 0.21/0.46  # Proof object initial clauses used    : 12
% 0.21/0.46  # Proof object initial formulas used   : 6
% 0.21/0.46  # Proof object generating inferences   : 26
% 0.21/0.46  # Proof object simplifying inferences  : 39
% 0.21/0.46  # Training examples: 0 positive, 0 negative
% 0.21/0.46  # Parsed axioms                        : 6
% 0.21/0.46  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.46  # Initial clauses                      : 12
% 0.21/0.46  # Removed in clause preprocessing      : 0
% 0.21/0.46  # Initial clauses in saturation        : 12
% 0.21/0.46  # Processed clauses                    : 466
% 0.21/0.46  # ...of these trivial                  : 12
% 0.21/0.46  # ...subsumed                          : 179
% 0.21/0.46  # ...remaining for further processing  : 275
% 0.21/0.46  # Other redundant clauses eliminated   : 0
% 0.21/0.46  # Clauses deleted for lack of memory   : 0
% 0.21/0.46  # Backward-subsumed                    : 9
% 0.21/0.46  # Backward-rewritten                   : 35
% 0.21/0.46  # Generated clauses                    : 2829
% 0.21/0.46  # ...of the previous two non-trivial   : 2677
% 0.21/0.46  # Contextual simplify-reflections      : 3
% 0.21/0.46  # Paramodulations                      : 2819
% 0.21/0.46  # Factorizations                       : 2
% 0.21/0.46  # Equation resolutions                 : 8
% 0.21/0.46  # Propositional unsat checks           : 0
% 0.21/0.46  #    Propositional check models        : 0
% 0.21/0.46  #    Propositional check unsatisfiable : 0
% 0.21/0.46  #    Propositional clauses             : 0
% 0.21/0.46  #    Propositional clauses after purity: 0
% 0.21/0.46  #    Propositional unsat core size     : 0
% 0.21/0.46  #    Propositional preprocessing time  : 0.000
% 0.21/0.46  #    Propositional encoding time       : 0.000
% 0.21/0.46  #    Propositional solver time         : 0.000
% 0.21/0.46  #    Success case prop preproc time    : 0.000
% 0.21/0.46  #    Success case prop encoding time   : 0.000
% 0.21/0.46  #    Success case prop solver time     : 0.000
% 0.21/0.46  # Current number of processed clauses  : 219
% 0.21/0.46  #    Positive orientable unit clauses  : 24
% 0.21/0.46  #    Positive unorientable unit clauses: 0
% 0.21/0.46  #    Negative unit clauses             : 2
% 0.21/0.46  #    Non-unit-clauses                  : 193
% 0.21/0.46  # Current number of unprocessed clauses: 2176
% 0.21/0.46  # ...number of literals in the above   : 10003
% 0.21/0.46  # Current number of archived formulas  : 0
% 0.21/0.46  # Current number of archived clauses   : 56
% 0.21/0.46  # Clause-clause subsumption calls (NU) : 3543
% 0.21/0.46  # Rec. Clause-clause subsumption calls : 2452
% 0.21/0.46  # Non-unit clause-clause subsumptions  : 190
% 0.21/0.46  # Unit Clause-clause subsumption calls : 103
% 0.21/0.46  # Rewrite failures with RHS unbound    : 0
% 0.21/0.46  # BW rewrite match attempts            : 295
% 0.21/0.46  # BW rewrite match successes           : 7
% 0.21/0.46  # Condensation attempts                : 0
% 0.21/0.46  # Condensation successes               : 0
% 0.21/0.46  # Termbank termtop insertions          : 86993
% 0.21/0.46  
% 0.21/0.46  # -------------------------------------------------
% 0.21/0.46  # User time                : 0.100 s
% 0.21/0.46  # System time              : 0.007 s
% 0.21/0.46  # Total time               : 0.107 s
% 0.21/0.46  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------

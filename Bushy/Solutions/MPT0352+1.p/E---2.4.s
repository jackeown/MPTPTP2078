%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : subset_1__t31_subset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:22 EDT 2019

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   39 ( 140 expanded)
%              Number of clauses        :   24 (  59 expanded)
%              Number of leaves         :    7 (  34 expanded)
%              Depth                    :    9
%              Number of atoms          :   65 ( 339 expanded)
%              Number of equality atoms :   15 (  54 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t31_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r1_tarski(X2,X3)
          <=> r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t31_subset_1.p',t31_subset_1)).

fof(dt_k6_subset_1,axiom,(
    ! [X1,X2] : m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t31_subset_1.p',dt_k6_subset_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t31_subset_1.p',redefinition_k6_subset_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t31_subset_1.p',d5_subset_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t31_subset_1.p',involutiveness_k3_subset_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t31_subset_1.p',dt_k3_subset_1)).

fof(t34_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k4_xboole_0(X3,X2),k4_xboole_0(X3,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t31_subset_1.p',t34_xboole_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => ( r1_tarski(X2,X3)
            <=> r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t31_subset_1])).

fof(c_0_8,plain,(
    ! [X13,X14] : m1_subset_1(k6_subset_1(X13,X14),k1_zfmisc_1(X13)) ),
    inference(variable_rename,[status(thm)],[dt_k6_subset_1])).

fof(c_0_9,plain,(
    ! [X19,X20] : k6_subset_1(X19,X20) = k4_xboole_0(X19,X20) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

fof(c_0_10,plain,(
    ! [X9,X10] :
      ( ~ m1_subset_1(X10,k1_zfmisc_1(X9))
      | k3_subset_1(X9,X10) = k4_xboole_0(X9,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_11,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0))
    & m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0))
    & ( ~ r1_tarski(esk2_0,esk3_0)
      | ~ r1_tarski(k3_subset_1(esk1_0,esk3_0),k3_subset_1(esk1_0,esk2_0)) )
    & ( r1_tarski(esk2_0,esk3_0)
      | r1_tarski(k3_subset_1(esk1_0,esk3_0),k3_subset_1(esk1_0,esk2_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

cnf(c_0_12,plain,
    ( m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_16,plain,(
    ! [X17,X18] :
      ( ~ m1_subset_1(X18,k1_zfmisc_1(X17))
      | k3_subset_1(X17,k3_subset_1(X17,X18)) = X18 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

fof(c_0_17,plain,(
    ! [X11,X12] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(X11))
      | m1_subset_1(k3_subset_1(X11,X12),k1_zfmisc_1(X11)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

fof(c_0_18,plain,(
    ! [X21,X22,X23] :
      ( ~ r1_tarski(X21,X22)
      | r1_tarski(k4_xboole_0(X23,X22),k4_xboole_0(X23,X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_xboole_1])])).

cnf(c_0_19,plain,
    ( m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( k4_xboole_0(esk1_0,esk3_0) = k3_subset_1(esk1_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_21,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_24,plain,
    ( r1_tarski(k4_xboole_0(X3,X2),k4_xboole_0(X3,X1))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0)
    | r1_tarski(k3_subset_1(esk1_0,esk3_0),k3_subset_1(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(k3_subset_1(esk1_0,esk3_0),k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( k3_subset_1(esk1_0,k3_subset_1(esk1_0,esk3_0)) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_21,c_0_15])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(k3_subset_1(esk1_0,esk2_0),k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( k3_subset_1(esk1_0,k3_subset_1(esk1_0,esk2_0)) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_21,c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(k4_xboole_0(X1,k3_subset_1(esk1_0,esk2_0)),k4_xboole_0(X1,k3_subset_1(esk1_0,esk3_0)))
    | r1_tarski(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( k4_xboole_0(esk1_0,k3_subset_1(esk1_0,esk3_0)) = esk3_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_26]),c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( k4_xboole_0(esk1_0,k3_subset_1(esk1_0,esk2_0)) = esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_28]),c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])])).

cnf(c_0_34,negated_conjecture,
    ( ~ r1_tarski(esk2_0,esk3_0)
    | ~ r1_tarski(k3_subset_1(esk1_0,esk3_0),k3_subset_1(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(k4_xboole_0(X1,esk3_0),k4_xboole_0(X1,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_33])).

cnf(c_0_36,negated_conjecture,
    ( k4_xboole_0(esk1_0,esk2_0) = k3_subset_1(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_23])).

cnf(c_0_37,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(esk1_0,esk3_0),k3_subset_1(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_33])])).

cnf(c_0_38,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_20]),c_0_37]),
    [proof]).
%------------------------------------------------------------------------------

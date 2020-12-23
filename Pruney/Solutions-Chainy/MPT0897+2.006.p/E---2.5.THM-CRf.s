%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:00 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 784 expanded)
%              Number of clauses        :   49 ( 355 expanded)
%              Number of leaves         :    5 ( 197 expanded)
%              Depth                    :   24
%              Number of atoms          :  260 (2079 expanded)
%              Number of equality atoms :  259 (2078 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :    9 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t57_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k4_zfmisc_1(X1,X2,X3,X4) = k4_zfmisc_1(X5,X6,X7,X8)
     => ( k4_zfmisc_1(X1,X2,X3,X4) = k1_xboole_0
        | ( X1 = X5
          & X2 = X6
          & X3 = X7
          & X4 = X8 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_mcart_1)).

fof(d4_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(t195_relat_1,axiom,(
    ! [X1,X2] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(X1,X2)) = X1
            & k2_relat_1(k2_zfmisc_1(X1,X2)) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_relat_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6,X7,X8] :
        ( k4_zfmisc_1(X1,X2,X3,X4) = k4_zfmisc_1(X5,X6,X7,X8)
       => ( k4_zfmisc_1(X1,X2,X3,X4) = k1_xboole_0
          | ( X1 = X5
            & X2 = X6
            & X3 = X7
            & X4 = X8 ) ) ) ),
    inference(assume_negation,[status(cth)],[t57_mcart_1])).

fof(c_0_6,plain,(
    ! [X16,X17,X18,X19] : k4_zfmisc_1(X16,X17,X18,X19) = k2_zfmisc_1(k3_zfmisc_1(X16,X17,X18),X19) ),
    inference(variable_rename,[status(thm)],[d4_zfmisc_1])).

fof(c_0_7,plain,(
    ! [X13,X14,X15] : k3_zfmisc_1(X13,X14,X15) = k2_zfmisc_1(k2_zfmisc_1(X13,X14),X15) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_8,negated_conjecture,
    ( k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0) = k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0)
    & k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0) != k1_xboole_0
    & ( esk1_0 != esk5_0
      | esk2_0 != esk6_0
      | esk3_0 != esk7_0
      | esk4_0 != esk8_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

cnf(c_0_9,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,plain,(
    ! [X11,X12] :
      ( ( k1_relat_1(k2_zfmisc_1(X11,X12)) = X11
        | X11 = k1_xboole_0
        | X12 = k1_xboole_0 )
      & ( k2_relat_1(k2_zfmisc_1(X11,X12)) = X12
        | X11 = k1_xboole_0
        | X12 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t195_relat_1])])])).

cnf(c_0_12,negated_conjecture,
    ( k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0) = k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4) ),
    inference(rw,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_14,plain,
    ( k1_relat_1(k2_zfmisc_1(X1,X2)) = X1
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0),esk8_0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_12,c_0_13]),c_0_13])).

cnf(c_0_16,negated_conjecture,
    ( k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)) = k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0)
    | k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0) = k1_xboole_0
    | esk8_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

fof(c_0_17,plain,(
    ! [X9,X10] :
      ( ( k2_zfmisc_1(X9,X10) != k1_xboole_0
        | X9 = k1_xboole_0
        | X10 = k1_xboole_0 )
      & ( X9 != k1_xboole_0
        | k2_zfmisc_1(X9,X10) = k1_xboole_0 )
      & ( X10 != k1_xboole_0
        | k2_zfmisc_1(X9,X10) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_18,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0) = k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)
    | k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0) = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0) = k1_xboole_0
    | esk8_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_14,c_0_16])).

cnf(c_0_19,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k2_zfmisc_1(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_20,negated_conjecture,
    ( k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)) = k2_zfmisc_1(esk5_0,esk6_0)
    | k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0) = k1_xboole_0
    | k2_zfmisc_1(esk5_0,esk6_0) = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_18]),c_0_19])).

cnf(c_0_21,plain,
    ( k2_relat_1(k2_zfmisc_1(X1,X2)) = X2
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_22,negated_conjecture,
    ( k2_zfmisc_1(esk5_0,esk6_0) = k2_zfmisc_1(esk1_0,esk2_0)
    | k2_zfmisc_1(esk5_0,esk6_0) = k1_xboole_0
    | k2_zfmisc_1(esk1_0,esk2_0) = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_20]),c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)) = esk8_0
    | k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0) = k1_xboole_0
    | esk8_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_21,c_0_15])).

cnf(c_0_24,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_26,negated_conjecture,
    ( k1_relat_1(k2_zfmisc_1(esk1_0,esk2_0)) = esk5_0
    | k2_zfmisc_1(esk1_0,esk2_0) = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_22]),c_0_19])).

cnf(c_0_27,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0) = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0) = k1_xboole_0
    | esk8_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk8_0 = esk4_0 ),
    inference(spm,[status(thm)],[c_0_21,c_0_23])).

cnf(c_0_29,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_25,c_0_13])).

cnf(c_0_31,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk1_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk5_0 = esk1_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_26]),c_0_19])).

cnf(c_0_32,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0) = k1_xboole_0
    | esk8_0 = esk4_0
    | esk4_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_28]),c_0_29]),c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( esk5_0 = esk1_0
    | esk2_0 = k1_xboole_0
    | esk1_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_31]),c_0_32]),c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( k2_relat_1(k2_zfmisc_1(esk1_0,esk2_0)) = esk6_0
    | k2_zfmisc_1(esk1_0,esk2_0) = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_19])).

cnf(c_0_36,negated_conjecture,
    ( k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)) = esk7_0
    | k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0) = k1_xboole_0
    | k2_zfmisc_1(esk5_0,esk6_0) = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_18]),c_0_19])).

cnf(c_0_37,negated_conjecture,
    ( esk1_0 != esk5_0
    | esk2_0 != esk6_0
    | esk3_0 != esk7_0
    | esk4_0 != esk8_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_38,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk8_0 = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_33]),c_0_29])])).

cnf(c_0_39,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk1_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk5_0 = esk1_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_34]),c_0_32]),c_0_29]),c_0_30])).

cnf(c_0_40,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk1_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk6_0 = esk2_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_35]),c_0_19])).

cnf(c_0_41,negated_conjecture,
    ( k2_zfmisc_1(esk5_0,esk6_0) = k1_xboole_0
    | k2_zfmisc_1(esk1_0,esk2_0) = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk7_0 = esk3_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_36]),c_0_19])).

cnf(c_0_42,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0
    | esk5_0 != esk1_0
    | esk6_0 != esk2_0
    | esk7_0 != esk3_0 ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( esk5_0 = esk1_0
    | esk2_0 = k1_xboole_0
    | esk1_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_39]),c_0_32]),c_0_29]),c_0_29]),c_0_30])).

cnf(c_0_44,negated_conjecture,
    ( esk6_0 = esk2_0
    | esk2_0 = k1_xboole_0
    | esk1_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_40]),c_0_32]),c_0_30])).

cnf(c_0_45,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,esk2_0) = k1_xboole_0
    | esk7_0 = esk3_0
    | esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_41]),c_0_29]),c_0_29]),c_0_30])).

cnf(c_0_46,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk1_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk6_0 != esk2_0
    | esk7_0 != esk3_0 ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_47,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk1_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk6_0 = esk2_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_44]),c_0_32]),c_0_29]),c_0_30])).

cnf(c_0_48,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk7_0 = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_45]),c_0_29]),c_0_29])])).

cnf(c_0_49,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk1_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk7_0 != esk3_0 ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_50,negated_conjecture,
    ( esk7_0 = esk3_0
    | esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_48]),c_0_32]),c_0_30])).

cnf(c_0_51,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk1_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_52,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk1_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_51]),c_0_32]),c_0_30])).

cnf(c_0_53,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk1_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_52]),c_0_32]),c_0_29]),c_0_30])).

cnf(c_0_54,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk1_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_53]),c_0_32]),c_0_29]),c_0_29]),c_0_30])).

cnf(c_0_55,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk1_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_54]),c_0_29]),c_0_29]),c_0_29]),c_0_30])).

cnf(c_0_56,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | esk1_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_55]),c_0_32])])).

cnf(c_0_57,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_56]),c_0_32]),c_0_29])])).

cnf(c_0_58,negated_conjecture,
    ( esk1_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_57]),c_0_32]),c_0_29]),c_0_29])])).

cnf(c_0_59,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_58]),c_0_29]),c_0_29]),c_0_29])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.32  % Computer   : n011.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 12:31:12 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.12/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.12/0.36  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.12/0.36  #
% 0.12/0.36  # Preprocessing time       : 0.026 s
% 0.12/0.36  # Presaturation interreduction done
% 0.12/0.36  
% 0.12/0.36  # Proof found!
% 0.12/0.36  # SZS status Theorem
% 0.12/0.36  # SZS output start CNFRefutation
% 0.12/0.36  fof(t57_mcart_1, conjecture, ![X1, X2, X3, X4, X5, X6, X7, X8]:(k4_zfmisc_1(X1,X2,X3,X4)=k4_zfmisc_1(X5,X6,X7,X8)=>(k4_zfmisc_1(X1,X2,X3,X4)=k1_xboole_0|(((X1=X5&X2=X6)&X3=X7)&X4=X8))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_mcart_1)).
% 0.12/0.36  fof(d4_zfmisc_1, axiom, ![X1, X2, X3, X4]:k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 0.12/0.36  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.12/0.36  fof(t195_relat_1, axiom, ![X1, X2]:~(((X1!=k1_xboole_0&X2!=k1_xboole_0)&~((k1_relat_1(k2_zfmisc_1(X1,X2))=X1&k2_relat_1(k2_zfmisc_1(X1,X2))=X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t195_relat_1)).
% 0.12/0.36  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.12/0.36  fof(c_0_5, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6, X7, X8]:(k4_zfmisc_1(X1,X2,X3,X4)=k4_zfmisc_1(X5,X6,X7,X8)=>(k4_zfmisc_1(X1,X2,X3,X4)=k1_xboole_0|(((X1=X5&X2=X6)&X3=X7)&X4=X8)))), inference(assume_negation,[status(cth)],[t57_mcart_1])).
% 0.12/0.36  fof(c_0_6, plain, ![X16, X17, X18, X19]:k4_zfmisc_1(X16,X17,X18,X19)=k2_zfmisc_1(k3_zfmisc_1(X16,X17,X18),X19), inference(variable_rename,[status(thm)],[d4_zfmisc_1])).
% 0.12/0.36  fof(c_0_7, plain, ![X13, X14, X15]:k3_zfmisc_1(X13,X14,X15)=k2_zfmisc_1(k2_zfmisc_1(X13,X14),X15), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.12/0.36  fof(c_0_8, negated_conjecture, (k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0)=k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0)&(k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0)!=k1_xboole_0&(esk1_0!=esk5_0|esk2_0!=esk6_0|esk3_0!=esk7_0|esk4_0!=esk8_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).
% 0.12/0.36  cnf(c_0_9, plain, (k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.36  cnf(c_0_10, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.36  fof(c_0_11, plain, ![X11, X12]:((k1_relat_1(k2_zfmisc_1(X11,X12))=X11|(X11=k1_xboole_0|X12=k1_xboole_0))&(k2_relat_1(k2_zfmisc_1(X11,X12))=X12|(X11=k1_xboole_0|X12=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t195_relat_1])])])).
% 0.12/0.36  cnf(c_0_12, negated_conjecture, (k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0)=k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.36  cnf(c_0_13, plain, (k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)), inference(rw,[status(thm)],[c_0_9, c_0_10])).
% 0.12/0.36  cnf(c_0_14, plain, (k1_relat_1(k2_zfmisc_1(X1,X2))=X1|X1=k1_xboole_0|X2=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.36  cnf(c_0_15, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0),esk8_0)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_12, c_0_13]), c_0_13])).
% 0.12/0.36  cnf(c_0_16, negated_conjecture, (k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0))=k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0)|k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0)=k1_xboole_0|esk8_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.12/0.36  fof(c_0_17, plain, ![X9, X10]:((k2_zfmisc_1(X9,X10)!=k1_xboole_0|(X9=k1_xboole_0|X10=k1_xboole_0))&((X9!=k1_xboole_0|k2_zfmisc_1(X9,X10)=k1_xboole_0)&(X10!=k1_xboole_0|k2_zfmisc_1(X9,X10)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.12/0.36  cnf(c_0_18, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0)=k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)|k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0)=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)=k1_xboole_0|esk8_0=k1_xboole_0|esk4_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_14, c_0_16])).
% 0.12/0.36  cnf(c_0_19, plain, (X1=k1_xboole_0|X2=k1_xboole_0|k2_zfmisc_1(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.36  cnf(c_0_20, negated_conjecture, (k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0))=k2_zfmisc_1(esk5_0,esk6_0)|k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)=k1_xboole_0|k2_zfmisc_1(esk5_0,esk6_0)=k1_xboole_0|esk4_0=k1_xboole_0|esk8_0=k1_xboole_0|esk7_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_18]), c_0_19])).
% 0.12/0.36  cnf(c_0_21, plain, (k2_relat_1(k2_zfmisc_1(X1,X2))=X2|X1=k1_xboole_0|X2=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.36  cnf(c_0_22, negated_conjecture, (k2_zfmisc_1(esk5_0,esk6_0)=k2_zfmisc_1(esk1_0,esk2_0)|k2_zfmisc_1(esk5_0,esk6_0)=k1_xboole_0|k2_zfmisc_1(esk1_0,esk2_0)=k1_xboole_0|esk7_0=k1_xboole_0|esk8_0=k1_xboole_0|esk4_0=k1_xboole_0|esk3_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_20]), c_0_19])).
% 0.12/0.36  cnf(c_0_23, negated_conjecture, (k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0))=esk8_0|k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0)=k1_xboole_0|esk8_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_21, c_0_15])).
% 0.12/0.36  cnf(c_0_24, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.36  cnf(c_0_25, negated_conjecture, (k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.36  cnf(c_0_26, negated_conjecture, (k1_relat_1(k2_zfmisc_1(esk1_0,esk2_0))=esk5_0|k2_zfmisc_1(esk1_0,esk2_0)=k1_xboole_0|esk3_0=k1_xboole_0|esk4_0=k1_xboole_0|esk8_0=k1_xboole_0|esk7_0=k1_xboole_0|esk5_0=k1_xboole_0|esk6_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_22]), c_0_19])).
% 0.12/0.36  cnf(c_0_27, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.36  cnf(c_0_28, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0)=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)=k1_xboole_0|esk8_0=k1_xboole_0|esk4_0=k1_xboole_0|esk8_0=esk4_0), inference(spm,[status(thm)],[c_0_21, c_0_23])).
% 0.12/0.36  cnf(c_0_29, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_24])).
% 0.12/0.36  cnf(c_0_30, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_25, c_0_13])).
% 0.12/0.36  cnf(c_0_31, negated_conjecture, (esk6_0=k1_xboole_0|esk5_0=k1_xboole_0|esk7_0=k1_xboole_0|esk8_0=k1_xboole_0|esk4_0=k1_xboole_0|esk3_0=k1_xboole_0|esk1_0=k1_xboole_0|esk2_0=k1_xboole_0|esk5_0=esk1_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_26]), c_0_19])).
% 0.12/0.36  cnf(c_0_32, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_27])).
% 0.12/0.36  cnf(c_0_33, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)=k1_xboole_0|esk8_0=esk4_0|esk4_0=k1_xboole_0|esk8_0=k1_xboole_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_28]), c_0_29]), c_0_30])).
% 0.12/0.36  cnf(c_0_34, negated_conjecture, (esk5_0=esk1_0|esk2_0=k1_xboole_0|esk1_0=k1_xboole_0|esk3_0=k1_xboole_0|esk4_0=k1_xboole_0|esk7_0=k1_xboole_0|esk5_0=k1_xboole_0|esk6_0=k1_xboole_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_31]), c_0_32]), c_0_30])).
% 0.12/0.36  cnf(c_0_35, negated_conjecture, (k2_relat_1(k2_zfmisc_1(esk1_0,esk2_0))=esk6_0|k2_zfmisc_1(esk1_0,esk2_0)=k1_xboole_0|esk3_0=k1_xboole_0|esk4_0=k1_xboole_0|esk8_0=k1_xboole_0|esk7_0=k1_xboole_0|esk5_0=k1_xboole_0|esk6_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_19])).
% 0.12/0.36  cnf(c_0_36, negated_conjecture, (k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0))=esk7_0|k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)=k1_xboole_0|k2_zfmisc_1(esk5_0,esk6_0)=k1_xboole_0|esk4_0=k1_xboole_0|esk8_0=k1_xboole_0|esk7_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_18]), c_0_19])).
% 0.12/0.36  cnf(c_0_37, negated_conjecture, (esk1_0!=esk5_0|esk2_0!=esk6_0|esk3_0!=esk7_0|esk4_0!=esk8_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.36  cnf(c_0_38, negated_conjecture, (esk8_0=k1_xboole_0|esk4_0=k1_xboole_0|esk8_0=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_33]), c_0_29])])).
% 0.12/0.36  cnf(c_0_39, negated_conjecture, (esk6_0=k1_xboole_0|esk5_0=k1_xboole_0|esk4_0=k1_xboole_0|esk3_0=k1_xboole_0|esk1_0=k1_xboole_0|esk2_0=k1_xboole_0|esk5_0=esk1_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_34]), c_0_32]), c_0_29]), c_0_30])).
% 0.12/0.36  cnf(c_0_40, negated_conjecture, (esk6_0=k1_xboole_0|esk5_0=k1_xboole_0|esk7_0=k1_xboole_0|esk8_0=k1_xboole_0|esk4_0=k1_xboole_0|esk3_0=k1_xboole_0|esk1_0=k1_xboole_0|esk2_0=k1_xboole_0|esk6_0=esk2_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_35]), c_0_19])).
% 0.12/0.36  cnf(c_0_41, negated_conjecture, (k2_zfmisc_1(esk5_0,esk6_0)=k1_xboole_0|k2_zfmisc_1(esk1_0,esk2_0)=k1_xboole_0|esk7_0=k1_xboole_0|esk8_0=k1_xboole_0|esk4_0=k1_xboole_0|esk3_0=k1_xboole_0|esk7_0=esk3_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_36]), c_0_19])).
% 0.12/0.36  cnf(c_0_42, negated_conjecture, (esk4_0=k1_xboole_0|esk8_0=k1_xboole_0|esk5_0!=esk1_0|esk6_0!=esk2_0|esk7_0!=esk3_0), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.12/0.36  cnf(c_0_43, negated_conjecture, (esk5_0=esk1_0|esk2_0=k1_xboole_0|esk1_0=k1_xboole_0|esk3_0=k1_xboole_0|esk4_0=k1_xboole_0|esk5_0=k1_xboole_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_39]), c_0_32]), c_0_29]), c_0_29]), c_0_30])).
% 0.12/0.36  cnf(c_0_44, negated_conjecture, (esk6_0=esk2_0|esk2_0=k1_xboole_0|esk1_0=k1_xboole_0|esk3_0=k1_xboole_0|esk4_0=k1_xboole_0|esk7_0=k1_xboole_0|esk5_0=k1_xboole_0|esk6_0=k1_xboole_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_40]), c_0_32]), c_0_30])).
% 0.12/0.36  cnf(c_0_45, negated_conjecture, (k2_zfmisc_1(esk1_0,esk2_0)=k1_xboole_0|esk7_0=esk3_0|esk3_0=k1_xboole_0|esk4_0=k1_xboole_0|esk8_0=k1_xboole_0|esk7_0=k1_xboole_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_41]), c_0_29]), c_0_29]), c_0_30])).
% 0.12/0.36  cnf(c_0_46, negated_conjecture, (esk5_0=k1_xboole_0|esk3_0=k1_xboole_0|esk1_0=k1_xboole_0|esk2_0=k1_xboole_0|esk8_0=k1_xboole_0|esk4_0=k1_xboole_0|esk6_0!=esk2_0|esk7_0!=esk3_0), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.12/0.36  cnf(c_0_47, negated_conjecture, (esk6_0=k1_xboole_0|esk5_0=k1_xboole_0|esk4_0=k1_xboole_0|esk3_0=k1_xboole_0|esk1_0=k1_xboole_0|esk2_0=k1_xboole_0|esk6_0=esk2_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_44]), c_0_32]), c_0_29]), c_0_30])).
% 0.12/0.36  cnf(c_0_48, negated_conjecture, (esk7_0=k1_xboole_0|esk8_0=k1_xboole_0|esk4_0=k1_xboole_0|esk3_0=k1_xboole_0|esk7_0=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_45]), c_0_29]), c_0_29])])).
% 0.12/0.36  cnf(c_0_49, negated_conjecture, (esk6_0=k1_xboole_0|esk4_0=k1_xboole_0|esk8_0=k1_xboole_0|esk2_0=k1_xboole_0|esk1_0=k1_xboole_0|esk3_0=k1_xboole_0|esk5_0=k1_xboole_0|esk7_0!=esk3_0), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.12/0.36  cnf(c_0_50, negated_conjecture, (esk7_0=esk3_0|esk3_0=k1_xboole_0|esk4_0=k1_xboole_0|esk7_0=k1_xboole_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_48]), c_0_32]), c_0_30])).
% 0.12/0.36  cnf(c_0_51, negated_conjecture, (esk7_0=k1_xboole_0|esk5_0=k1_xboole_0|esk3_0=k1_xboole_0|esk1_0=k1_xboole_0|esk2_0=k1_xboole_0|esk8_0=k1_xboole_0|esk4_0=k1_xboole_0|esk6_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.12/0.36  cnf(c_0_52, negated_conjecture, (esk6_0=k1_xboole_0|esk4_0=k1_xboole_0|esk2_0=k1_xboole_0|esk1_0=k1_xboole_0|esk3_0=k1_xboole_0|esk5_0=k1_xboole_0|esk7_0=k1_xboole_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_51]), c_0_32]), c_0_30])).
% 0.12/0.36  cnf(c_0_53, negated_conjecture, (esk5_0=k1_xboole_0|esk3_0=k1_xboole_0|esk1_0=k1_xboole_0|esk2_0=k1_xboole_0|esk4_0=k1_xboole_0|esk6_0=k1_xboole_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_52]), c_0_32]), c_0_29]), c_0_30])).
% 0.12/0.36  cnf(c_0_54, negated_conjecture, (esk4_0=k1_xboole_0|esk2_0=k1_xboole_0|esk1_0=k1_xboole_0|esk3_0=k1_xboole_0|esk5_0=k1_xboole_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_53]), c_0_32]), c_0_29]), c_0_29]), c_0_30])).
% 0.12/0.36  cnf(c_0_55, negated_conjecture, (esk3_0=k1_xboole_0|esk1_0=k1_xboole_0|esk2_0=k1_xboole_0|esk4_0=k1_xboole_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_54]), c_0_29]), c_0_29]), c_0_29]), c_0_30])).
% 0.12/0.36  cnf(c_0_56, negated_conjecture, (esk2_0=k1_xboole_0|esk1_0=k1_xboole_0|esk3_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_55]), c_0_32])])).
% 0.12/0.36  cnf(c_0_57, negated_conjecture, (esk1_0=k1_xboole_0|esk2_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_56]), c_0_32]), c_0_29])])).
% 0.12/0.36  cnf(c_0_58, negated_conjecture, (esk1_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_57]), c_0_32]), c_0_29]), c_0_29])])).
% 0.12/0.36  cnf(c_0_59, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_58]), c_0_29]), c_0_29]), c_0_29])]), ['proof']).
% 0.12/0.36  # SZS output end CNFRefutation
% 0.12/0.36  # Proof object total steps             : 60
% 0.12/0.36  # Proof object clause steps            : 49
% 0.12/0.36  # Proof object formula steps           : 11
% 0.12/0.36  # Proof object conjectures             : 42
% 0.12/0.36  # Proof object clause conjectures      : 39
% 0.12/0.36  # Proof object formula conjectures     : 3
% 0.12/0.36  # Proof object initial clauses used    : 10
% 0.12/0.36  # Proof object initial formulas used   : 5
% 0.12/0.36  # Proof object generating inferences   : 33
% 0.12/0.36  # Proof object simplifying inferences  : 67
% 0.12/0.36  # Training examples: 0 positive, 0 negative
% 0.12/0.36  # Parsed axioms                        : 5
% 0.12/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.36  # Initial clauses                      : 10
% 0.12/0.36  # Removed in clause preprocessing      : 2
% 0.12/0.36  # Initial clauses in saturation        : 8
% 0.12/0.36  # Processed clauses                    : 84
% 0.12/0.36  # ...of these trivial                  : 0
% 0.12/0.36  # ...subsumed                          : 18
% 0.12/0.36  # ...remaining for further processing  : 66
% 0.12/0.36  # Other redundant clauses eliminated   : 2
% 0.12/0.36  # Clauses deleted for lack of memory   : 0
% 0.12/0.36  # Backward-subsumed                    : 23
% 0.12/0.36  # Backward-rewritten                   : 25
% 0.12/0.36  # Generated clauses                    : 201
% 0.12/0.36  # ...of the previous two non-trivial   : 170
% 0.12/0.36  # Contextual simplify-reflections      : 12
% 0.12/0.36  # Paramodulations                      : 192
% 0.12/0.36  # Factorizations                       : 7
% 0.12/0.36  # Equation resolutions                 : 2
% 0.12/0.36  # Propositional unsat checks           : 0
% 0.12/0.36  #    Propositional check models        : 0
% 0.12/0.36  #    Propositional check unsatisfiable : 0
% 0.12/0.36  #    Propositional clauses             : 0
% 0.12/0.36  #    Propositional clauses after purity: 0
% 0.12/0.36  #    Propositional unsat core size     : 0
% 0.12/0.36  #    Propositional preprocessing time  : 0.000
% 0.12/0.36  #    Propositional encoding time       : 0.000
% 0.12/0.36  #    Propositional solver time         : 0.000
% 0.12/0.36  #    Success case prop preproc time    : 0.000
% 0.12/0.36  #    Success case prop encoding time   : 0.000
% 0.12/0.36  #    Success case prop solver time     : 0.000
% 0.12/0.36  # Current number of processed clauses  : 8
% 0.12/0.36  #    Positive orientable unit clauses  : 3
% 0.12/0.36  #    Positive unorientable unit clauses: 0
% 0.12/0.36  #    Negative unit clauses             : 0
% 0.12/0.36  #    Non-unit-clauses                  : 5
% 0.12/0.36  # Current number of unprocessed clauses: 64
% 0.12/0.36  # ...number of literals in the above   : 467
% 0.12/0.36  # Current number of archived formulas  : 0
% 0.12/0.36  # Current number of archived clauses   : 58
% 0.12/0.36  # Clause-clause subsumption calls (NU) : 515
% 0.12/0.36  # Rec. Clause-clause subsumption calls : 85
% 0.12/0.36  # Non-unit clause-clause subsumptions  : 45
% 0.12/0.36  # Unit Clause-clause subsumption calls : 0
% 0.12/0.36  # Rewrite failures with RHS unbound    : 0
% 0.12/0.36  # BW rewrite match attempts            : 1
% 0.12/0.36  # BW rewrite match successes           : 1
% 0.12/0.36  # Condensation attempts                : 0
% 0.12/0.36  # Condensation successes               : 0
% 0.12/0.36  # Termbank termtop insertions          : 5840
% 0.12/0.36  
% 0.12/0.36  # -------------------------------------------------
% 0.12/0.36  # User time                : 0.036 s
% 0.12/0.36  # System time              : 0.001 s
% 0.12/0.36  # Total time               : 0.037 s
% 0.12/0.36  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : mcart_1__t37_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:07 EDT 2019

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   35 ( 160 expanded)
%              Number of clauses        :   28 (  65 expanded)
%              Number of leaves         :    3 (  36 expanded)
%              Depth                    :   13
%              Number of atoms          :  130 ( 695 expanded)
%              Number of equality atoms :  129 ( 694 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   15 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t37_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( k3_zfmisc_1(X1,X2,X3) = k3_zfmisc_1(X4,X5,X6)
     => ( k3_zfmisc_1(X1,X2,X3) = k1_xboole_0
        | ( X1 = X4
          & X2 = X5
          & X3 = X6 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t37_mcart_1.p',t37_mcart_1)).

fof(t36_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( k3_zfmisc_1(X1,X2,X3) = k3_zfmisc_1(X4,X5,X6)
     => ( X1 = k1_xboole_0
        | X2 = k1_xboole_0
        | X3 = k1_xboole_0
        | ( X1 = X4
          & X2 = X5
          & X3 = X6 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t37_mcart_1.p',t36_mcart_1)).

fof(t35_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0 )
    <=> k3_zfmisc_1(X1,X2,X3) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t37_mcart_1.p',t35_mcart_1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6] :
        ( k3_zfmisc_1(X1,X2,X3) = k3_zfmisc_1(X4,X5,X6)
       => ( k3_zfmisc_1(X1,X2,X3) = k1_xboole_0
          | ( X1 = X4
            & X2 = X5
            & X3 = X6 ) ) ) ),
    inference(assume_negation,[status(cth)],[t37_mcart_1])).

fof(c_0_4,plain,(
    ! [X24,X25,X26,X27,X28,X29] :
      ( ( X24 = X27
        | X24 = k1_xboole_0
        | X25 = k1_xboole_0
        | X26 = k1_xboole_0
        | k3_zfmisc_1(X24,X25,X26) != k3_zfmisc_1(X27,X28,X29) )
      & ( X25 = X28
        | X24 = k1_xboole_0
        | X25 = k1_xboole_0
        | X26 = k1_xboole_0
        | k3_zfmisc_1(X24,X25,X26) != k3_zfmisc_1(X27,X28,X29) )
      & ( X26 = X29
        | X24 = k1_xboole_0
        | X25 = k1_xboole_0
        | X26 = k1_xboole_0
        | k3_zfmisc_1(X24,X25,X26) != k3_zfmisc_1(X27,X28,X29) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t36_mcart_1])])])).

fof(c_0_5,negated_conjecture,
    ( k3_zfmisc_1(esk1_0,esk2_0,esk3_0) = k3_zfmisc_1(esk4_0,esk5_0,esk6_0)
    & k3_zfmisc_1(esk1_0,esk2_0,esk3_0) != k1_xboole_0
    & ( esk1_0 != esk4_0
      | esk2_0 != esk5_0
      | esk3_0 != esk6_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

cnf(c_0_6,plain,
    ( X1 = X2
    | X1 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | k3_zfmisc_1(X1,X3,X4) != k3_zfmisc_1(X2,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( k3_zfmisc_1(esk1_0,esk2_0,esk3_0) = k3_zfmisc_1(esk4_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_8,plain,(
    ! [X21,X22,X23] :
      ( ( X21 = k1_xboole_0
        | X22 = k1_xboole_0
        | X23 = k1_xboole_0
        | k3_zfmisc_1(X21,X22,X23) != k1_xboole_0 )
      & ( X21 != k1_xboole_0
        | k3_zfmisc_1(X21,X22,X23) = k1_xboole_0 )
      & ( X22 != k1_xboole_0
        | k3_zfmisc_1(X21,X22,X23) = k1_xboole_0 )
      & ( X23 != k1_xboole_0
        | k3_zfmisc_1(X21,X22,X23) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_mcart_1])])])).

cnf(c_0_9,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | esk4_0 = X1
    | k3_zfmisc_1(esk1_0,esk2_0,esk3_0) != k3_zfmisc_1(X1,X2,X3) ),
    inference(spm,[status(thm)],[c_0_6,c_0_7])).

cnf(c_0_10,plain,
    ( k3_zfmisc_1(X2,X3,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( esk4_0 = esk1_0
    | esk6_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_9])).

cnf(c_0_12,plain,
    ( k3_zfmisc_1(X1,X2,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( k3_zfmisc_1(esk1_0,esk2_0,esk3_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_14,plain,
    ( k3_zfmisc_1(X2,X1,X3) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( X1 = X2
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X1 = k1_xboole_0
    | k3_zfmisc_1(X3,X4,X1) != k3_zfmisc_1(X5,X6,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_16,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk4_0 = esk1_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_11]),c_0_12]),c_0_13])).

cnf(c_0_17,plain,
    ( k3_zfmisc_1(X1,k1_xboole_0,X2) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( X1 = X2
    | X3 = k1_xboole_0
    | X1 = k1_xboole_0
    | X4 = k1_xboole_0
    | k3_zfmisc_1(X3,X1,X4) != k3_zfmisc_1(X5,X2,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_19,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk6_0 = X1
    | k3_zfmisc_1(esk1_0,esk2_0,esk3_0) != k3_zfmisc_1(X2,X3,X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_7])).

cnf(c_0_20,negated_conjecture,
    ( esk4_0 = esk1_0
    | esk4_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_16]),c_0_17]),c_0_13])).

cnf(c_0_21,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_22,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | esk5_0 = X1
    | k3_zfmisc_1(esk1_0,esk2_0,esk3_0) != k3_zfmisc_1(X2,X1,X3) ),
    inference(spm,[status(thm)],[c_0_18,c_0_7])).

cnf(c_0_23,negated_conjecture,
    ( esk1_0 != esk4_0
    | esk2_0 != esk5_0
    | esk3_0 != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_24,negated_conjecture,
    ( esk6_0 = esk3_0
    | esk5_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk1_0 != k1_xboole_0 ),
    inference(ef,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( k3_zfmisc_1(k1_xboole_0,X1,X2) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( esk5_0 = esk2_0
    | esk6_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk4_0 != esk1_0
    | esk5_0 != esk2_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_25]),c_0_26]),c_0_13])).

cnf(c_0_30,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk5_0 = esk2_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_27]),c_0_12]),c_0_13])).

cnf(c_0_31,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_20]),c_0_29]),c_0_30])).

cnf(c_0_32,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_31]),c_0_12]),c_0_13])).

cnf(c_0_33,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_32]),c_0_17]),c_0_13])).

cnf(c_0_34,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_7,c_0_33]),c_0_26]),c_0_13]),
    [proof]).
%------------------------------------------------------------------------------

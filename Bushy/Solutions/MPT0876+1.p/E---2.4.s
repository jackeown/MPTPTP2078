%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : mcart_1__t36_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:06 EDT 2019

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   60 (1952 expanded)
%              Number of clauses        :   51 ( 784 expanded)
%              Number of leaves         :    4 ( 476 expanded)
%              Depth                    :   24
%              Number of atoms          :  163 (7707 expanded)
%              Number of equality atoms :  162 (7706 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t36_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( k3_zfmisc_1(X1,X2,X3) = k3_zfmisc_1(X4,X5,X6)
     => ( X1 = k1_xboole_0
        | X2 = k1_xboole_0
        | X3 = k1_xboole_0
        | ( X1 = X4
          & X2 = X5
          & X3 = X6 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t36_mcart_1.p',t36_mcart_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t36_mcart_1.p',d3_zfmisc_1)).

fof(t134_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X3,X4)
     => ( X1 = k1_xboole_0
        | X2 = k1_xboole_0
        | ( X1 = X3
          & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t36_mcart_1.p',t134_zfmisc_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t36_mcart_1.p',t113_zfmisc_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6] :
        ( k3_zfmisc_1(X1,X2,X3) = k3_zfmisc_1(X4,X5,X6)
       => ( X1 = k1_xboole_0
          | X2 = k1_xboole_0
          | X3 = k1_xboole_0
          | ( X1 = X4
            & X2 = X5
            & X3 = X6 ) ) ) ),
    inference(assume_negation,[status(cth)],[t36_mcart_1])).

fof(c_0_5,negated_conjecture,
    ( k3_zfmisc_1(esk1_0,esk2_0,esk3_0) = k3_zfmisc_1(esk4_0,esk5_0,esk6_0)
    & esk1_0 != k1_xboole_0
    & esk2_0 != k1_xboole_0
    & esk3_0 != k1_xboole_0
    & ( esk1_0 != esk4_0
      | esk2_0 != esk5_0
      | esk3_0 != esk6_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_6,plain,(
    ! [X15,X16,X17] : k3_zfmisc_1(X15,X16,X17) = k2_zfmisc_1(k2_zfmisc_1(X15,X16),X17) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_7,plain,(
    ! [X22,X23,X24,X25] :
      ( ( X22 = X24
        | X22 = k1_xboole_0
        | X23 = k1_xboole_0
        | k2_zfmisc_1(X22,X23) != k2_zfmisc_1(X24,X25) )
      & ( X23 = X25
        | X22 = k1_xboole_0
        | X23 = k1_xboole_0
        | k2_zfmisc_1(X22,X23) != k2_zfmisc_1(X24,X25) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t134_zfmisc_1])])])).

cnf(c_0_8,negated_conjecture,
    ( k3_zfmisc_1(esk1_0,esk2_0,esk3_0) = k3_zfmisc_1(esk4_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( X1 = X2
    | X3 = k1_xboole_0
    | X1 = k1_xboole_0
    | k2_zfmisc_1(X3,X1) != k2_zfmisc_1(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0) = k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_8,c_0_9]),c_0_9])).

fof(c_0_12,plain,(
    ! [X20,X21] :
      ( ( k2_zfmisc_1(X20,X21) != k1_xboole_0
        | X20 = k1_xboole_0
        | X21 = k1_xboole_0 )
      & ( X20 != k1_xboole_0
        | k2_zfmisc_1(X20,X21) = k1_xboole_0 )
      & ( X21 != k1_xboole_0
        | k2_zfmisc_1(X20,X21) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_13,negated_conjecture,
    ( k2_zfmisc_1(esk4_0,esk5_0) = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | esk6_0 = X1
    | k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0) != k2_zfmisc_1(X2,X1) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_14,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_15,negated_conjecture,
    ( k2_zfmisc_1(esk4_0,esk5_0) = k1_xboole_0
    | esk6_0 = esk3_0
    | esk6_0 = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_16,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_17,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k2_zfmisc_1(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0) = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | esk6_0 = esk3_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_15]),c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_20,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,esk2_0) = k1_xboole_0
    | esk6_0 = esk3_0
    | esk6_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])).

cnf(c_0_21,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_22,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_23,negated_conjecture,
    ( X1 = esk6_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k2_zfmisc_1(X2,X1) != k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_24,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk6_0 = esk3_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_20]),c_0_21]),c_0_22])).

cnf(c_0_25,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,esk2_0) = k1_xboole_0
    | esk6_0 = esk3_0 ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_23]),c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk3_0) = k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)
    | esk6_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_11,c_0_24])).

cnf(c_0_27,negated_conjecture,
    ( esk6_0 = esk3_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_25]),c_0_21]),c_0_22])).

cnf(c_0_28,plain,
    ( X1 = X2
    | X1 = k1_xboole_0
    | X3 = k1_xboole_0
    | k2_zfmisc_1(X1,X3) != k2_zfmisc_1(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_29,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk3_0) = k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27]),c_0_19])).

cnf(c_0_30,negated_conjecture,
    ( k2_zfmisc_1(esk4_0,esk5_0) = k1_xboole_0
    | k2_zfmisc_1(esk4_0,esk5_0) = X1
    | k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0) != k2_zfmisc_1(X1,X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_19])).

cnf(c_0_31,negated_conjecture,
    ( k2_zfmisc_1(esk4_0,esk5_0) = k2_zfmisc_1(esk1_0,esk2_0)
    | k2_zfmisc_1(esk4_0,esk5_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_32,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk4_0 = X1
    | k2_zfmisc_1(esk1_0,esk2_0) != k2_zfmisc_1(X1,X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_31]),c_0_17])).

cnf(c_0_33,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_34,negated_conjecture,
    ( esk4_0 = esk1_0
    | esk4_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_35,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_36,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0) = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk4_0 = esk1_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_34]),c_0_35]),c_0_16])).

cnf(c_0_37,negated_conjecture,
    ( X1 = k2_zfmisc_1(esk4_0,esk5_0)
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k2_zfmisc_1(X1,X2) != k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_38,negated_conjecture,
    ( k2_zfmisc_1(esk4_0,esk5_0) = k1_xboole_0
    | X1 = esk4_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k2_zfmisc_1(X1,X2) != k2_zfmisc_1(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_31])).

cnf(c_0_39,negated_conjecture,
    ( esk1_0 != esk4_0
    | esk2_0 != esk5_0
    | esk3_0 != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_40,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,esk2_0) = k1_xboole_0
    | esk4_0 = esk1_0
    | esk4_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_36]),c_0_19])).

cnf(c_0_41,negated_conjecture,
    ( k2_zfmisc_1(esk4_0,esk5_0) = k2_zfmisc_1(esk1_0,esk2_0)
    | k2_zfmisc_1(esk1_0,esk2_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_37]),c_0_19])).

cnf(c_0_42,negated_conjecture,
    ( k2_zfmisc_1(esk4_0,esk5_0) = k1_xboole_0
    | esk4_0 = esk1_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_38]),c_0_22]),c_0_21])).

cnf(c_0_43,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk4_0 != esk1_0
    | esk5_0 != esk2_0 ),
    inference(spm,[status(thm)],[c_0_39,c_0_24])).

cnf(c_0_44,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk4_0 = esk1_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_40]),c_0_21]),c_0_22])).

cnf(c_0_45,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,esk2_0) = k1_xboole_0
    | esk4_0 = esk1_0 ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_46,negated_conjecture,
    ( k2_zfmisc_1(esk4_0,esk5_0) = k1_xboole_0
    | k2_zfmisc_1(esk1_0,esk2_0) != k1_xboole_0 ),
    inference(ef,[status(thm)],[c_0_31])).

cnf(c_0_47,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0) = k1_xboole_0
    | esk4_0 != esk1_0
    | esk5_0 != esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_43]),c_0_35])).

cnf(c_0_48,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,esk5_0) = k2_zfmisc_1(esk1_0,esk2_0)
    | k2_zfmisc_1(esk1_0,esk2_0) = k1_xboole_0
    | esk4_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_41,c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( esk4_0 = esk1_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_45]),c_0_21]),c_0_22])).

cnf(c_0_50,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | k2_zfmisc_1(esk1_0,esk2_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_17,c_0_46])).

cnf(c_0_51,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,esk2_0) = k1_xboole_0
    | esk4_0 != esk1_0
    | esk5_0 != esk2_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_47]),c_0_19])).

cnf(c_0_52,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,esk5_0) = k2_zfmisc_1(esk1_0,esk2_0)
    | k2_zfmisc_1(esk1_0,esk2_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_49]),c_0_21])).

cnf(c_0_53,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | k2_zfmisc_1(esk1_0,esk2_0) != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_49]),c_0_21])).

cnf(c_0_54,negated_conjecture,
    ( esk4_0 != esk1_0
    | esk5_0 != esk2_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_51]),c_0_21]),c_0_22])).

cnf(c_0_55,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk5_0 = X1
    | k2_zfmisc_1(esk1_0,esk2_0) != k2_zfmisc_1(X2,X1) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_52]),c_0_21]),c_0_53])).

cnf(c_0_56,negated_conjecture,
    ( esk5_0 != esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_49])])).

cnf(c_0_57,negated_conjecture,
    ( esk5_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_55]),c_0_56])).

cnf(c_0_58,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,esk2_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_57]),c_0_35])])).

cnf(c_0_59,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_58]),c_0_21]),c_0_22]),
    [proof]).
%------------------------------------------------------------------------------

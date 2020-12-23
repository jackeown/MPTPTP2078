%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:00 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   63 (1521 expanded)
%              Number of clauses        :   50 ( 704 expanded)
%              Number of leaves         :    6 ( 382 expanded)
%              Depth                    :   22
%              Number of atoms          :  184 (3250 expanded)
%              Number of equality atoms :  183 (3249 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    4 (   1 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_mcart_1)).

fof(d4_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(t37_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( k3_zfmisc_1(X1,X2,X3) = k3_zfmisc_1(X4,X5,X6)
     => ( k3_zfmisc_1(X1,X2,X3) = k1_xboole_0
        | ( X1 = X4
          & X2 = X5
          & X3 = X6 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_mcart_1)).

fof(t55_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & X4 != k1_xboole_0 )
    <=> k4_zfmisc_1(X1,X2,X3,X4) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_mcart_1)).

fof(t36_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( k3_zfmisc_1(X1,X2,X3) = k3_zfmisc_1(X4,X5,X6)
     => ( X1 = k1_xboole_0
        | X2 = k1_xboole_0
        | X3 = k1_xboole_0
        | ( X1 = X4
          & X2 = X5
          & X3 = X6 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_mcart_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6,X7,X8] :
        ( k4_zfmisc_1(X1,X2,X3,X4) = k4_zfmisc_1(X5,X6,X7,X8)
       => ( k4_zfmisc_1(X1,X2,X3,X4) = k1_xboole_0
          | ( X1 = X5
            & X2 = X6
            & X3 = X7
            & X4 = X8 ) ) ) ),
    inference(assume_negation,[status(cth)],[t57_mcart_1])).

fof(c_0_7,plain,(
    ! [X12,X13,X14,X15] : k4_zfmisc_1(X12,X13,X14,X15) = k2_zfmisc_1(k3_zfmisc_1(X12,X13,X14),X15) ),
    inference(variable_rename,[status(thm)],[d4_zfmisc_1])).

fof(c_0_8,plain,(
    ! [X9,X10,X11] : k3_zfmisc_1(X9,X10,X11) = k2_zfmisc_1(k2_zfmisc_1(X9,X10),X11) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_9,plain,(
    ! [X22,X23,X24,X25,X26,X27] :
      ( ( X22 = X25
        | k3_zfmisc_1(X22,X23,X24) = k1_xboole_0
        | k3_zfmisc_1(X22,X23,X24) != k3_zfmisc_1(X25,X26,X27) )
      & ( X23 = X26
        | k3_zfmisc_1(X22,X23,X24) = k1_xboole_0
        | k3_zfmisc_1(X22,X23,X24) != k3_zfmisc_1(X25,X26,X27) )
      & ( X24 = X27
        | k3_zfmisc_1(X22,X23,X24) = k1_xboole_0
        | k3_zfmisc_1(X22,X23,X24) != k3_zfmisc_1(X25,X26,X27) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_mcart_1])])])).

fof(c_0_10,negated_conjecture,
    ( k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0) = k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0)
    & k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0) != k1_xboole_0
    & ( esk1_0 != esk5_0
      | esk2_0 != esk6_0
      | esk3_0 != esk7_0
      | esk4_0 != esk8_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

cnf(c_0_11,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( X1 = X2
    | k3_zfmisc_1(X3,X4,X1) = k1_xboole_0
    | k3_zfmisc_1(X3,X4,X1) != k3_zfmisc_1(X5,X6,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0) = k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4) ),
    inference(rw,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( X1 = X2
    | k2_zfmisc_1(k2_zfmisc_1(X3,X4),X1) = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(X3,X4),X1) != k2_zfmisc_1(k2_zfmisc_1(X5,X6),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_12]),c_0_12]),c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0),esk8_0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14,c_0_15]),c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_16,c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( esk8_0 = X1
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0) != k2_zfmisc_1(k2_zfmisc_1(X2,X3),X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])).

cnf(c_0_21,plain,
    ( X1 = X2
    | k3_zfmisc_1(X3,X1,X4) = k1_xboole_0
    | k3_zfmisc_1(X3,X1,X4) != k3_zfmisc_1(X5,X2,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_22,negated_conjecture,
    ( esk8_0 = esk4_0 ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_23,plain,
    ( X1 = X2
    | k2_zfmisc_1(k2_zfmisc_1(X3,X1),X4) = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(X3,X1),X4) != k2_zfmisc_1(k2_zfmisc_1(X5,X2),X6) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_12]),c_0_12]),c_0_12])).

cnf(c_0_24,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0),esk4_0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0) ),
    inference(rw,[status(thm)],[c_0_18,c_0_22])).

cnf(c_0_25,negated_conjecture,
    ( esk7_0 = X1
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0) != k2_zfmisc_1(k2_zfmisc_1(X2,X1),X3) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_19])).

cnf(c_0_26,plain,
    ( X1 = X2
    | k3_zfmisc_1(X1,X3,X4) = k1_xboole_0
    | k3_zfmisc_1(X1,X3,X4) != k3_zfmisc_1(X2,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_27,negated_conjecture,
    ( esk7_0 = esk3_0 ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_28,plain,
    ( X1 = X2
    | k2_zfmisc_1(k2_zfmisc_1(X1,X3),X4) = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(X1,X3),X4) != k2_zfmisc_1(k2_zfmisc_1(X2,X5),X6) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_12]),c_0_12]),c_0_12])).

cnf(c_0_29,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk3_0),esk4_0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0) ),
    inference(rw,[status(thm)],[c_0_24,c_0_27])).

fof(c_0_30,plain,(
    ! [X28,X29,X30,X31] :
      ( ( X28 = k1_xboole_0
        | X29 = k1_xboole_0
        | X30 = k1_xboole_0
        | X31 = k1_xboole_0
        | k4_zfmisc_1(X28,X29,X30,X31) != k1_xboole_0 )
      & ( X28 != k1_xboole_0
        | k4_zfmisc_1(X28,X29,X30,X31) = k1_xboole_0 )
      & ( X29 != k1_xboole_0
        | k4_zfmisc_1(X28,X29,X30,X31) = k1_xboole_0 )
      & ( X30 != k1_xboole_0
        | k4_zfmisc_1(X28,X29,X30,X31) = k1_xboole_0 )
      & ( X31 != k1_xboole_0
        | k4_zfmisc_1(X28,X29,X30,X31) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_mcart_1])])])).

cnf(c_0_31,negated_conjecture,
    ( k2_zfmisc_1(esk5_0,esk6_0) = X1
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0) != k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_19])).

cnf(c_0_32,plain,
    ( k4_zfmisc_1(X2,X3,X1,X4) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_33,negated_conjecture,
    ( k2_zfmisc_1(esk5_0,esk6_0) = k2_zfmisc_1(esk1_0,esk2_0) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_34,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X3),X1),X4) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_32,c_0_15])).

cnf(c_0_35,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),X1) = k1_xboole_0
    | esk6_0 = X2
    | k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),X1) != k2_zfmisc_1(k2_zfmisc_1(X3,X2),X4) ),
    inference(spm,[status(thm)],[c_0_23,c_0_33])).

cnf(c_0_36,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),k1_xboole_0),X3) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_34])).

fof(c_0_37,plain,(
    ! [X16,X17,X18,X19,X20,X21] :
      ( ( X16 = X19
        | X16 = k1_xboole_0
        | X17 = k1_xboole_0
        | X18 = k1_xboole_0
        | k3_zfmisc_1(X16,X17,X18) != k3_zfmisc_1(X19,X20,X21) )
      & ( X17 = X20
        | X16 = k1_xboole_0
        | X17 = k1_xboole_0
        | X18 = k1_xboole_0
        | k3_zfmisc_1(X16,X17,X18) != k3_zfmisc_1(X19,X20,X21) )
      & ( X18 = X21
        | X16 = k1_xboole_0
        | X17 = k1_xboole_0
        | X18 = k1_xboole_0
        | k3_zfmisc_1(X16,X17,X18) != k3_zfmisc_1(X19,X20,X21) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t36_mcart_1])])])).

cnf(c_0_38,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),X1) = k1_xboole_0
    | esk6_0 = esk2_0 ),
    inference(er,[status(thm)],[c_0_35])).

cnf(c_0_39,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_36])).

cnf(c_0_40,negated_conjecture,
    ( esk1_0 != esk5_0
    | esk2_0 != esk6_0
    | esk3_0 != esk7_0
    | esk4_0 != esk8_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_41,plain,
    ( X1 = X2
    | X1 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | k3_zfmisc_1(X1,X3,X4) != k3_zfmisc_1(X2,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_42,negated_conjecture,
    ( esk6_0 = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_38]),c_0_39])])).

cnf(c_0_43,negated_conjecture,
    ( esk5_0 != esk1_0
    | esk6_0 != esk2_0
    | esk7_0 != esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_22])])).

cnf(c_0_44,plain,
    ( k4_zfmisc_1(X2,X1,X3,X4) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_45,plain,
    ( X1 = X2
    | X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X1 = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(X1,X3),X4) != k2_zfmisc_1(k2_zfmisc_1(X2,X5),X6) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_12]),c_0_12])).

cnf(c_0_46,negated_conjecture,
    ( k2_zfmisc_1(esk5_0,esk2_0) = k2_zfmisc_1(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_33,c_0_42])).

cnf(c_0_47,negated_conjecture,
    ( esk5_0 != esk1_0
    | esk6_0 != esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_27])])).

cnf(c_0_48,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | k4_zfmisc_1(X1,X2,X3,X4) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_49,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X1),X3),X4) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_44,c_0_15])).

cnf(c_0_50,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk5_0 = X1
    | X2 = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),X2) != k2_zfmisc_1(k2_zfmisc_1(X1,X3),X4) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_51,negated_conjecture,
    ( esk5_0 != esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_42])])).

cnf(c_0_52,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_48,c_0_15])).

cnf(c_0_53,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0),X2),X3) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | X1 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_50]),c_0_51])).

cnf(c_0_55,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_39])])).

cnf(c_0_56,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0 ),
    inference(ef,[status(thm)],[c_0_54])).

cnf(c_0_57,negated_conjecture,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_55]),c_0_39]),c_0_39])])).

cnf(c_0_58,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,esk2_0) = k1_xboole_0
    | esk2_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_56]),c_0_39])).

cnf(c_0_59,negated_conjecture,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0
    | X2 = k1_xboole_0 ),
    inference(ef,[status(thm)],[c_0_57])).

cnf(c_0_60,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_58]),c_0_39]),c_0_39])])).

cnf(c_0_61,negated_conjecture,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(ef,[status(thm)],[c_0_59])).

cnf(c_0_62,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_60]),c_0_61]),c_0_39]),c_0_39])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:46:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.14/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.14/0.39  #
% 0.14/0.39  # Preprocessing time       : 0.027 s
% 0.14/0.39  # Presaturation interreduction done
% 0.14/0.39  
% 0.14/0.39  # Proof found!
% 0.14/0.39  # SZS status Theorem
% 0.14/0.39  # SZS output start CNFRefutation
% 0.14/0.39  fof(t57_mcart_1, conjecture, ![X1, X2, X3, X4, X5, X6, X7, X8]:(k4_zfmisc_1(X1,X2,X3,X4)=k4_zfmisc_1(X5,X6,X7,X8)=>(k4_zfmisc_1(X1,X2,X3,X4)=k1_xboole_0|(((X1=X5&X2=X6)&X3=X7)&X4=X8))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_mcart_1)).
% 0.14/0.39  fof(d4_zfmisc_1, axiom, ![X1, X2, X3, X4]:k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 0.14/0.39  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.14/0.39  fof(t37_mcart_1, axiom, ![X1, X2, X3, X4, X5, X6]:(k3_zfmisc_1(X1,X2,X3)=k3_zfmisc_1(X4,X5,X6)=>(k3_zfmisc_1(X1,X2,X3)=k1_xboole_0|((X1=X4&X2=X5)&X3=X6))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_mcart_1)).
% 0.14/0.39  fof(t55_mcart_1, axiom, ![X1, X2, X3, X4]:((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&X4!=k1_xboole_0)<=>k4_zfmisc_1(X1,X2,X3,X4)!=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_mcart_1)).
% 0.14/0.39  fof(t36_mcart_1, axiom, ![X1, X2, X3, X4, X5, X6]:(k3_zfmisc_1(X1,X2,X3)=k3_zfmisc_1(X4,X5,X6)=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|((X1=X4&X2=X5)&X3=X6))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_mcart_1)).
% 0.14/0.39  fof(c_0_6, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6, X7, X8]:(k4_zfmisc_1(X1,X2,X3,X4)=k4_zfmisc_1(X5,X6,X7,X8)=>(k4_zfmisc_1(X1,X2,X3,X4)=k1_xboole_0|(((X1=X5&X2=X6)&X3=X7)&X4=X8)))), inference(assume_negation,[status(cth)],[t57_mcart_1])).
% 0.14/0.39  fof(c_0_7, plain, ![X12, X13, X14, X15]:k4_zfmisc_1(X12,X13,X14,X15)=k2_zfmisc_1(k3_zfmisc_1(X12,X13,X14),X15), inference(variable_rename,[status(thm)],[d4_zfmisc_1])).
% 0.14/0.39  fof(c_0_8, plain, ![X9, X10, X11]:k3_zfmisc_1(X9,X10,X11)=k2_zfmisc_1(k2_zfmisc_1(X9,X10),X11), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.14/0.39  fof(c_0_9, plain, ![X22, X23, X24, X25, X26, X27]:(((X22=X25|k3_zfmisc_1(X22,X23,X24)=k1_xboole_0|k3_zfmisc_1(X22,X23,X24)!=k3_zfmisc_1(X25,X26,X27))&(X23=X26|k3_zfmisc_1(X22,X23,X24)=k1_xboole_0|k3_zfmisc_1(X22,X23,X24)!=k3_zfmisc_1(X25,X26,X27)))&(X24=X27|k3_zfmisc_1(X22,X23,X24)=k1_xboole_0|k3_zfmisc_1(X22,X23,X24)!=k3_zfmisc_1(X25,X26,X27))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_mcart_1])])])).
% 0.14/0.39  fof(c_0_10, negated_conjecture, (k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0)=k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0)&(k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0)!=k1_xboole_0&(esk1_0!=esk5_0|esk2_0!=esk6_0|esk3_0!=esk7_0|esk4_0!=esk8_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.14/0.39  cnf(c_0_11, plain, (k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.39  cnf(c_0_12, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.39  cnf(c_0_13, plain, (X1=X2|k3_zfmisc_1(X3,X4,X1)=k1_xboole_0|k3_zfmisc_1(X3,X4,X1)!=k3_zfmisc_1(X5,X6,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.39  cnf(c_0_14, negated_conjecture, (k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0)=k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.39  cnf(c_0_15, plain, (k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)), inference(rw,[status(thm)],[c_0_11, c_0_12])).
% 0.14/0.39  cnf(c_0_16, negated_conjecture, (k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.39  cnf(c_0_17, plain, (X1=X2|k2_zfmisc_1(k2_zfmisc_1(X3,X4),X1)=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(X3,X4),X1)!=k2_zfmisc_1(k2_zfmisc_1(X5,X6),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13, c_0_12]), c_0_12]), c_0_12])).
% 0.14/0.39  cnf(c_0_18, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0),esk8_0)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14, c_0_15]), c_0_15])).
% 0.14/0.39  cnf(c_0_19, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_16, c_0_15])).
% 0.14/0.39  cnf(c_0_20, negated_conjecture, (esk8_0=X1|k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)!=k2_zfmisc_1(k2_zfmisc_1(X2,X3),X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19])).
% 0.14/0.39  cnf(c_0_21, plain, (X1=X2|k3_zfmisc_1(X3,X1,X4)=k1_xboole_0|k3_zfmisc_1(X3,X1,X4)!=k3_zfmisc_1(X5,X2,X6)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.39  cnf(c_0_22, negated_conjecture, (esk8_0=esk4_0), inference(er,[status(thm)],[c_0_20])).
% 0.14/0.39  cnf(c_0_23, plain, (X1=X2|k2_zfmisc_1(k2_zfmisc_1(X3,X1),X4)=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(X3,X1),X4)!=k2_zfmisc_1(k2_zfmisc_1(X5,X2),X6)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_12]), c_0_12]), c_0_12])).
% 0.14/0.39  cnf(c_0_24, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0),esk4_0)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)), inference(rw,[status(thm)],[c_0_18, c_0_22])).
% 0.14/0.39  cnf(c_0_25, negated_conjecture, (esk7_0=X1|k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)!=k2_zfmisc_1(k2_zfmisc_1(X2,X1),X3)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_19])).
% 0.14/0.39  cnf(c_0_26, plain, (X1=X2|k3_zfmisc_1(X1,X3,X4)=k1_xboole_0|k3_zfmisc_1(X1,X3,X4)!=k3_zfmisc_1(X2,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.39  cnf(c_0_27, negated_conjecture, (esk7_0=esk3_0), inference(er,[status(thm)],[c_0_25])).
% 0.14/0.39  cnf(c_0_28, plain, (X1=X2|k2_zfmisc_1(k2_zfmisc_1(X1,X3),X4)=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(X1,X3),X4)!=k2_zfmisc_1(k2_zfmisc_1(X2,X5),X6)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_12]), c_0_12]), c_0_12])).
% 0.14/0.39  cnf(c_0_29, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk3_0),esk4_0)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)), inference(rw,[status(thm)],[c_0_24, c_0_27])).
% 0.14/0.39  fof(c_0_30, plain, ![X28, X29, X30, X31]:((X28=k1_xboole_0|X29=k1_xboole_0|X30=k1_xboole_0|X31=k1_xboole_0|k4_zfmisc_1(X28,X29,X30,X31)!=k1_xboole_0)&((((X28!=k1_xboole_0|k4_zfmisc_1(X28,X29,X30,X31)=k1_xboole_0)&(X29!=k1_xboole_0|k4_zfmisc_1(X28,X29,X30,X31)=k1_xboole_0))&(X30!=k1_xboole_0|k4_zfmisc_1(X28,X29,X30,X31)=k1_xboole_0))&(X31!=k1_xboole_0|k4_zfmisc_1(X28,X29,X30,X31)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_mcart_1])])])).
% 0.14/0.39  cnf(c_0_31, negated_conjecture, (k2_zfmisc_1(esk5_0,esk6_0)=X1|k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)!=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_19])).
% 0.14/0.39  cnf(c_0_32, plain, (k4_zfmisc_1(X2,X3,X1,X4)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.14/0.39  cnf(c_0_33, negated_conjecture, (k2_zfmisc_1(esk5_0,esk6_0)=k2_zfmisc_1(esk1_0,esk2_0)), inference(er,[status(thm)],[c_0_31])).
% 0.14/0.39  cnf(c_0_34, plain, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X3),X1),X4)=k1_xboole_0|X1!=k1_xboole_0), inference(rw,[status(thm)],[c_0_32, c_0_15])).
% 0.14/0.39  cnf(c_0_35, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),X1)=k1_xboole_0|esk6_0=X2|k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),X1)!=k2_zfmisc_1(k2_zfmisc_1(X3,X2),X4)), inference(spm,[status(thm)],[c_0_23, c_0_33])).
% 0.14/0.39  cnf(c_0_36, plain, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),k1_xboole_0),X3)=k1_xboole_0), inference(er,[status(thm)],[c_0_34])).
% 0.14/0.39  fof(c_0_37, plain, ![X16, X17, X18, X19, X20, X21]:(((X16=X19|(X16=k1_xboole_0|X17=k1_xboole_0|X18=k1_xboole_0)|k3_zfmisc_1(X16,X17,X18)!=k3_zfmisc_1(X19,X20,X21))&(X17=X20|(X16=k1_xboole_0|X17=k1_xboole_0|X18=k1_xboole_0)|k3_zfmisc_1(X16,X17,X18)!=k3_zfmisc_1(X19,X20,X21)))&(X18=X21|(X16=k1_xboole_0|X17=k1_xboole_0|X18=k1_xboole_0)|k3_zfmisc_1(X16,X17,X18)!=k3_zfmisc_1(X19,X20,X21))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t36_mcart_1])])])).
% 0.14/0.39  cnf(c_0_38, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),X1)=k1_xboole_0|esk6_0=esk2_0), inference(er,[status(thm)],[c_0_35])).
% 0.14/0.39  cnf(c_0_39, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_36, c_0_36])).
% 0.14/0.39  cnf(c_0_40, negated_conjecture, (esk1_0!=esk5_0|esk2_0!=esk6_0|esk3_0!=esk7_0|esk4_0!=esk8_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.39  cnf(c_0_41, plain, (X1=X2|X1=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|k3_zfmisc_1(X1,X3,X4)!=k3_zfmisc_1(X2,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.14/0.39  cnf(c_0_42, negated_conjecture, (esk6_0=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_38]), c_0_39])])).
% 0.14/0.39  cnf(c_0_43, negated_conjecture, (esk5_0!=esk1_0|esk6_0!=esk2_0|esk7_0!=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_22])])).
% 0.14/0.39  cnf(c_0_44, plain, (k4_zfmisc_1(X2,X1,X3,X4)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.14/0.39  cnf(c_0_45, plain, (X1=X2|X4=k1_xboole_0|X3=k1_xboole_0|X1=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(X1,X3),X4)!=k2_zfmisc_1(k2_zfmisc_1(X2,X5),X6)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_12]), c_0_12])).
% 0.14/0.39  cnf(c_0_46, negated_conjecture, (k2_zfmisc_1(esk5_0,esk2_0)=k2_zfmisc_1(esk1_0,esk2_0)), inference(rw,[status(thm)],[c_0_33, c_0_42])).
% 0.14/0.39  cnf(c_0_47, negated_conjecture, (esk5_0!=esk1_0|esk6_0!=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_27])])).
% 0.14/0.39  cnf(c_0_48, plain, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|k4_zfmisc_1(X1,X2,X3,X4)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.14/0.39  cnf(c_0_49, plain, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X1),X3),X4)=k1_xboole_0|X1!=k1_xboole_0), inference(rw,[status(thm)],[c_0_44, c_0_15])).
% 0.14/0.39  cnf(c_0_50, negated_conjecture, (esk5_0=k1_xboole_0|esk2_0=k1_xboole_0|esk5_0=X1|X2=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),X2)!=k2_zfmisc_1(k2_zfmisc_1(X1,X3),X4)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.14/0.39  cnf(c_0_51, negated_conjecture, (esk5_0!=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_42])])).
% 0.14/0.39  cnf(c_0_52, plain, (X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_48, c_0_15])).
% 0.14/0.39  cnf(c_0_53, plain, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0),X2),X3)=k1_xboole_0), inference(er,[status(thm)],[c_0_49])).
% 0.14/0.39  cnf(c_0_54, negated_conjecture, (esk2_0=k1_xboole_0|esk5_0=k1_xboole_0|X1=k1_xboole_0), inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_50]), c_0_51])).
% 0.14/0.39  cnf(c_0_55, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_39])])).
% 0.14/0.39  cnf(c_0_56, negated_conjecture, (esk5_0=k1_xboole_0|esk2_0=k1_xboole_0), inference(ef,[status(thm)],[c_0_54])).
% 0.14/0.39  cnf(c_0_57, negated_conjecture, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_55]), c_0_39]), c_0_39])])).
% 0.14/0.39  cnf(c_0_58, negated_conjecture, (k2_zfmisc_1(esk1_0,esk2_0)=k1_xboole_0|esk2_0=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_56]), c_0_39])).
% 0.14/0.39  cnf(c_0_59, negated_conjecture, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0|X2=k1_xboole_0), inference(ef,[status(thm)],[c_0_57])).
% 0.14/0.39  cnf(c_0_60, negated_conjecture, (esk2_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_58]), c_0_39]), c_0_39])])).
% 0.14/0.39  cnf(c_0_61, negated_conjecture, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(ef,[status(thm)],[c_0_59])).
% 0.14/0.39  cnf(c_0_62, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_60]), c_0_61]), c_0_39]), c_0_39])]), ['proof']).
% 0.14/0.39  # SZS output end CNFRefutation
% 0.14/0.39  # Proof object total steps             : 63
% 0.14/0.39  # Proof object clause steps            : 50
% 0.14/0.39  # Proof object formula steps           : 13
% 0.14/0.39  # Proof object conjectures             : 32
% 0.14/0.39  # Proof object clause conjectures      : 29
% 0.14/0.39  # Proof object formula conjectures     : 3
% 0.14/0.39  # Proof object initial clauses used    : 12
% 0.14/0.39  # Proof object initial formulas used   : 6
% 0.14/0.39  # Proof object generating inferences   : 19
% 0.14/0.39  # Proof object simplifying inferences  : 49
% 0.14/0.39  # Training examples: 0 positive, 0 negative
% 0.14/0.39  # Parsed axioms                        : 6
% 0.14/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.39  # Initial clauses                      : 16
% 0.14/0.39  # Removed in clause preprocessing      : 2
% 0.14/0.39  # Initial clauses in saturation        : 14
% 0.14/0.39  # Processed clauses                    : 167
% 0.14/0.39  # ...of these trivial                  : 16
% 0.14/0.39  # ...subsumed                          : 70
% 0.14/0.39  # ...remaining for further processing  : 81
% 0.14/0.39  # Other redundant clauses eliminated   : 22
% 0.14/0.39  # Clauses deleted for lack of memory   : 0
% 0.14/0.39  # Backward-subsumed                    : 12
% 0.14/0.39  # Backward-rewritten                   : 35
% 0.14/0.39  # Generated clauses                    : 940
% 0.14/0.39  # ...of the previous two non-trivial   : 697
% 0.14/0.39  # Contextual simplify-reflections      : 0
% 0.14/0.39  # Paramodulations                      : 851
% 0.14/0.39  # Factorizations                       : 51
% 0.14/0.39  # Equation resolutions                 : 38
% 0.14/0.39  # Propositional unsat checks           : 0
% 0.14/0.39  #    Propositional check models        : 0
% 0.14/0.39  #    Propositional check unsatisfiable : 0
% 0.14/0.39  #    Propositional clauses             : 0
% 0.14/0.39  #    Propositional clauses after purity: 0
% 0.14/0.39  #    Propositional unsat core size     : 0
% 0.14/0.39  #    Propositional preprocessing time  : 0.000
% 0.14/0.39  #    Propositional encoding time       : 0.000
% 0.14/0.39  #    Propositional solver time         : 0.000
% 0.14/0.39  #    Success case prop preproc time    : 0.000
% 0.14/0.39  #    Success case prop encoding time   : 0.000
% 0.14/0.39  #    Success case prop solver time     : 0.000
% 0.14/0.39  # Current number of processed clauses  : 16
% 0.14/0.39  #    Positive orientable unit clauses  : 5
% 0.14/0.39  #    Positive unorientable unit clauses: 0
% 0.14/0.39  #    Negative unit clauses             : 2
% 0.14/0.39  #    Non-unit-clauses                  : 9
% 0.14/0.39  # Current number of unprocessed clauses: 198
% 0.14/0.39  # ...number of literals in the above   : 1142
% 0.14/0.39  # Current number of archived formulas  : 0
% 0.14/0.39  # Current number of archived clauses   : 63
% 0.14/0.39  # Clause-clause subsumption calls (NU) : 191
% 0.14/0.39  # Rec. Clause-clause subsumption calls : 150
% 0.14/0.39  # Non-unit clause-clause subsumptions  : 53
% 0.14/0.39  # Unit Clause-clause subsumption calls : 10
% 0.14/0.39  # Rewrite failures with RHS unbound    : 0
% 0.14/0.39  # BW rewrite match attempts            : 28
% 0.14/0.39  # BW rewrite match successes           : 10
% 0.14/0.39  # Condensation attempts                : 0
% 0.14/0.39  # Condensation successes               : 0
% 0.14/0.39  # Termbank termtop insertions          : 9647
% 0.14/0.39  
% 0.14/0.39  # -------------------------------------------------
% 0.14/0.39  # User time                : 0.039 s
% 0.14/0.39  # System time              : 0.005 s
% 0.14/0.39  # Total time               : 0.044 s
% 0.14/0.39  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------

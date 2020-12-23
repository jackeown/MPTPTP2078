%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:00 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   58 (1139 expanded)
%              Number of clauses        :   45 ( 522 expanded)
%              Number of leaves         :    6 ( 287 expanded)
%              Depth                    :   22
%              Number of atoms          :  164 (2431 expanded)
%              Number of equality atoms :  163 (2430 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   13 (   2 average)
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

fof(t195_relat_1,axiom,(
    ! [X1,X2] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(X1,X2)) = X1
            & k2_relat_1(k2_zfmisc_1(X1,X2)) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).

fof(t55_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & X4 != k1_xboole_0 )
    <=> k4_zfmisc_1(X1,X2,X3,X4) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_mcart_1)).

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
    ! [X14,X15,X16,X17] : k4_zfmisc_1(X14,X15,X16,X17) = k2_zfmisc_1(k3_zfmisc_1(X14,X15,X16),X17) ),
    inference(variable_rename,[status(thm)],[d4_zfmisc_1])).

fof(c_0_8,plain,(
    ! [X11,X12,X13] : k3_zfmisc_1(X11,X12,X13) = k2_zfmisc_1(k2_zfmisc_1(X11,X12),X13) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_9,plain,(
    ! [X18,X19,X20,X21,X22,X23] :
      ( ( X18 = X21
        | k3_zfmisc_1(X18,X19,X20) = k1_xboole_0
        | k3_zfmisc_1(X18,X19,X20) != k3_zfmisc_1(X21,X22,X23) )
      & ( X19 = X22
        | k3_zfmisc_1(X18,X19,X20) = k1_xboole_0
        | k3_zfmisc_1(X18,X19,X20) != k3_zfmisc_1(X21,X22,X23) )
      & ( X20 = X23
        | k3_zfmisc_1(X18,X19,X20) = k1_xboole_0
        | k3_zfmisc_1(X18,X19,X20) != k3_zfmisc_1(X21,X22,X23) ) ) ),
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
    ! [X9,X10] :
      ( ( k1_relat_1(k2_zfmisc_1(X9,X10)) = X9
        | X9 = k1_xboole_0
        | X10 = k1_xboole_0 )
      & ( k2_relat_1(k2_zfmisc_1(X9,X10)) = X10
        | X9 = k1_xboole_0
        | X10 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t195_relat_1])])])).

cnf(c_0_31,negated_conjecture,
    ( k2_zfmisc_1(esk5_0,esk6_0) = X1
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0) != k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_19])).

cnf(c_0_32,negated_conjecture,
    ( esk1_0 != esk5_0
    | esk2_0 != esk6_0
    | esk3_0 != esk7_0
    | esk4_0 != esk8_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_33,plain,
    ( k2_relat_1(k2_zfmisc_1(X1,X2)) = X2
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( k2_zfmisc_1(esk5_0,esk6_0) = k2_zfmisc_1(esk1_0,esk2_0) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_35,plain,
    ( k1_relat_1(k2_zfmisc_1(X1,X2)) = X1
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_36,plain,(
    ! [X24,X25,X26,X27] :
      ( ( X24 = k1_xboole_0
        | X25 = k1_xboole_0
        | X26 = k1_xboole_0
        | X27 = k1_xboole_0
        | k4_zfmisc_1(X24,X25,X26,X27) != k1_xboole_0 )
      & ( X24 != k1_xboole_0
        | k4_zfmisc_1(X24,X25,X26,X27) = k1_xboole_0 )
      & ( X25 != k1_xboole_0
        | k4_zfmisc_1(X24,X25,X26,X27) = k1_xboole_0 )
      & ( X26 != k1_xboole_0
        | k4_zfmisc_1(X24,X25,X26,X27) = k1_xboole_0 )
      & ( X27 != k1_xboole_0
        | k4_zfmisc_1(X24,X25,X26,X27) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_mcart_1])])])).

cnf(c_0_37,negated_conjecture,
    ( esk5_0 != esk1_0
    | esk6_0 != esk2_0
    | esk7_0 != esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_22])])).

cnf(c_0_38,negated_conjecture,
    ( k2_relat_1(k2_zfmisc_1(esk1_0,esk2_0)) = esk6_0
    | esk5_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( k1_relat_1(k2_zfmisc_1(esk1_0,esk2_0)) = esk5_0
    | esk5_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_35,c_0_34])).

cnf(c_0_40,plain,
    ( k4_zfmisc_1(X2,X1,X3,X4) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( esk5_0 != esk1_0
    | esk6_0 != esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_27])])).

cnf(c_0_42,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk1_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk6_0 = esk2_0 ),
    inference(spm,[status(thm)],[c_0_33,c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk1_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk5_0 = esk1_0 ),
    inference(spm,[status(thm)],[c_0_35,c_0_39])).

cnf(c_0_44,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X1),X3),X4) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_40,c_0_15])).

cnf(c_0_45,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | esk1_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])).

cnf(c_0_46,plain,
    ( k4_zfmisc_1(X2,X3,X1,X4) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_47,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0),X2),X3) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_44])).

cnf(c_0_48,negated_conjecture,
    ( k2_zfmisc_1(esk5_0,k1_xboole_0) = k2_zfmisc_1(esk1_0,esk2_0)
    | esk5_0 = k1_xboole_0
    | esk1_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_34,c_0_45])).

cnf(c_0_49,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X3),X1),X4) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_46,c_0_15])).

cnf(c_0_50,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),X1),X2) = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk1_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_51,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),k1_xboole_0),X3) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_49])).

cnf(c_0_52,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk1_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_19,c_0_50])).

cnf(c_0_53,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_51,c_0_51])).

cnf(c_0_54,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,esk2_0) = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk1_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_52]),c_0_53])).

cnf(c_0_55,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_54]),c_0_53]),c_0_53])])).

cnf(c_0_56,negated_conjecture,
    ( esk1_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_55]),c_0_47])])).

cnf(c_0_57,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_56]),c_0_53]),c_0_53]),c_0_53])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:30:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.12/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.12/0.38  #
% 0.12/0.38  # Preprocessing time       : 0.032 s
% 0.12/0.38  # Presaturation interreduction done
% 0.12/0.38  
% 0.12/0.38  # Proof found!
% 0.12/0.38  # SZS status Theorem
% 0.12/0.38  # SZS output start CNFRefutation
% 0.12/0.38  fof(t57_mcart_1, conjecture, ![X1, X2, X3, X4, X5, X6, X7, X8]:(k4_zfmisc_1(X1,X2,X3,X4)=k4_zfmisc_1(X5,X6,X7,X8)=>(k4_zfmisc_1(X1,X2,X3,X4)=k1_xboole_0|(((X1=X5&X2=X6)&X3=X7)&X4=X8))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_mcart_1)).
% 0.12/0.38  fof(d4_zfmisc_1, axiom, ![X1, X2, X3, X4]:k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 0.12/0.38  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.12/0.38  fof(t37_mcart_1, axiom, ![X1, X2, X3, X4, X5, X6]:(k3_zfmisc_1(X1,X2,X3)=k3_zfmisc_1(X4,X5,X6)=>(k3_zfmisc_1(X1,X2,X3)=k1_xboole_0|((X1=X4&X2=X5)&X3=X6))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_mcart_1)).
% 0.12/0.38  fof(t195_relat_1, axiom, ![X1, X2]:~(((X1!=k1_xboole_0&X2!=k1_xboole_0)&~((k1_relat_1(k2_zfmisc_1(X1,X2))=X1&k2_relat_1(k2_zfmisc_1(X1,X2))=X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t195_relat_1)).
% 0.12/0.38  fof(t55_mcart_1, axiom, ![X1, X2, X3, X4]:((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&X4!=k1_xboole_0)<=>k4_zfmisc_1(X1,X2,X3,X4)!=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_mcart_1)).
% 0.12/0.38  fof(c_0_6, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6, X7, X8]:(k4_zfmisc_1(X1,X2,X3,X4)=k4_zfmisc_1(X5,X6,X7,X8)=>(k4_zfmisc_1(X1,X2,X3,X4)=k1_xboole_0|(((X1=X5&X2=X6)&X3=X7)&X4=X8)))), inference(assume_negation,[status(cth)],[t57_mcart_1])).
% 0.12/0.38  fof(c_0_7, plain, ![X14, X15, X16, X17]:k4_zfmisc_1(X14,X15,X16,X17)=k2_zfmisc_1(k3_zfmisc_1(X14,X15,X16),X17), inference(variable_rename,[status(thm)],[d4_zfmisc_1])).
% 0.12/0.38  fof(c_0_8, plain, ![X11, X12, X13]:k3_zfmisc_1(X11,X12,X13)=k2_zfmisc_1(k2_zfmisc_1(X11,X12),X13), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.12/0.38  fof(c_0_9, plain, ![X18, X19, X20, X21, X22, X23]:(((X18=X21|k3_zfmisc_1(X18,X19,X20)=k1_xboole_0|k3_zfmisc_1(X18,X19,X20)!=k3_zfmisc_1(X21,X22,X23))&(X19=X22|k3_zfmisc_1(X18,X19,X20)=k1_xboole_0|k3_zfmisc_1(X18,X19,X20)!=k3_zfmisc_1(X21,X22,X23)))&(X20=X23|k3_zfmisc_1(X18,X19,X20)=k1_xboole_0|k3_zfmisc_1(X18,X19,X20)!=k3_zfmisc_1(X21,X22,X23))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_mcart_1])])])).
% 0.12/0.38  fof(c_0_10, negated_conjecture, (k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0)=k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0)&(k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0)!=k1_xboole_0&(esk1_0!=esk5_0|esk2_0!=esk6_0|esk3_0!=esk7_0|esk4_0!=esk8_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.12/0.38  cnf(c_0_11, plain, (k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.38  cnf(c_0_12, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.38  cnf(c_0_13, plain, (X1=X2|k3_zfmisc_1(X3,X4,X1)=k1_xboole_0|k3_zfmisc_1(X3,X4,X1)!=k3_zfmisc_1(X5,X6,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.38  cnf(c_0_14, negated_conjecture, (k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0)=k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.38  cnf(c_0_15, plain, (k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)), inference(rw,[status(thm)],[c_0_11, c_0_12])).
% 0.12/0.38  cnf(c_0_16, negated_conjecture, (k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.38  cnf(c_0_17, plain, (X1=X2|k2_zfmisc_1(k2_zfmisc_1(X3,X4),X1)=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(X3,X4),X1)!=k2_zfmisc_1(k2_zfmisc_1(X5,X6),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13, c_0_12]), c_0_12]), c_0_12])).
% 0.12/0.38  cnf(c_0_18, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0),esk8_0)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14, c_0_15]), c_0_15])).
% 0.12/0.38  cnf(c_0_19, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_16, c_0_15])).
% 0.12/0.38  cnf(c_0_20, negated_conjecture, (esk8_0=X1|k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)!=k2_zfmisc_1(k2_zfmisc_1(X2,X3),X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19])).
% 0.12/0.38  cnf(c_0_21, plain, (X1=X2|k3_zfmisc_1(X3,X1,X4)=k1_xboole_0|k3_zfmisc_1(X3,X1,X4)!=k3_zfmisc_1(X5,X2,X6)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.38  cnf(c_0_22, negated_conjecture, (esk8_0=esk4_0), inference(er,[status(thm)],[c_0_20])).
% 0.12/0.38  cnf(c_0_23, plain, (X1=X2|k2_zfmisc_1(k2_zfmisc_1(X3,X1),X4)=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(X3,X1),X4)!=k2_zfmisc_1(k2_zfmisc_1(X5,X2),X6)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_12]), c_0_12]), c_0_12])).
% 0.12/0.38  cnf(c_0_24, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0),esk4_0)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)), inference(rw,[status(thm)],[c_0_18, c_0_22])).
% 0.12/0.38  cnf(c_0_25, negated_conjecture, (esk7_0=X1|k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)!=k2_zfmisc_1(k2_zfmisc_1(X2,X1),X3)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_19])).
% 0.12/0.38  cnf(c_0_26, plain, (X1=X2|k3_zfmisc_1(X1,X3,X4)=k1_xboole_0|k3_zfmisc_1(X1,X3,X4)!=k3_zfmisc_1(X2,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.38  cnf(c_0_27, negated_conjecture, (esk7_0=esk3_0), inference(er,[status(thm)],[c_0_25])).
% 0.12/0.38  cnf(c_0_28, plain, (X1=X2|k2_zfmisc_1(k2_zfmisc_1(X1,X3),X4)=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(X1,X3),X4)!=k2_zfmisc_1(k2_zfmisc_1(X2,X5),X6)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_12]), c_0_12]), c_0_12])).
% 0.12/0.38  cnf(c_0_29, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk3_0),esk4_0)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)), inference(rw,[status(thm)],[c_0_24, c_0_27])).
% 0.12/0.38  fof(c_0_30, plain, ![X9, X10]:((k1_relat_1(k2_zfmisc_1(X9,X10))=X9|(X9=k1_xboole_0|X10=k1_xboole_0))&(k2_relat_1(k2_zfmisc_1(X9,X10))=X10|(X9=k1_xboole_0|X10=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t195_relat_1])])])).
% 0.12/0.38  cnf(c_0_31, negated_conjecture, (k2_zfmisc_1(esk5_0,esk6_0)=X1|k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)!=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_19])).
% 0.12/0.38  cnf(c_0_32, negated_conjecture, (esk1_0!=esk5_0|esk2_0!=esk6_0|esk3_0!=esk7_0|esk4_0!=esk8_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.38  cnf(c_0_33, plain, (k2_relat_1(k2_zfmisc_1(X1,X2))=X2|X1=k1_xboole_0|X2=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.12/0.38  cnf(c_0_34, negated_conjecture, (k2_zfmisc_1(esk5_0,esk6_0)=k2_zfmisc_1(esk1_0,esk2_0)), inference(er,[status(thm)],[c_0_31])).
% 0.12/0.38  cnf(c_0_35, plain, (k1_relat_1(k2_zfmisc_1(X1,X2))=X1|X1=k1_xboole_0|X2=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.12/0.38  fof(c_0_36, plain, ![X24, X25, X26, X27]:((X24=k1_xboole_0|X25=k1_xboole_0|X26=k1_xboole_0|X27=k1_xboole_0|k4_zfmisc_1(X24,X25,X26,X27)!=k1_xboole_0)&((((X24!=k1_xboole_0|k4_zfmisc_1(X24,X25,X26,X27)=k1_xboole_0)&(X25!=k1_xboole_0|k4_zfmisc_1(X24,X25,X26,X27)=k1_xboole_0))&(X26!=k1_xboole_0|k4_zfmisc_1(X24,X25,X26,X27)=k1_xboole_0))&(X27!=k1_xboole_0|k4_zfmisc_1(X24,X25,X26,X27)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_mcart_1])])])).
% 0.12/0.38  cnf(c_0_37, negated_conjecture, (esk5_0!=esk1_0|esk6_0!=esk2_0|esk7_0!=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_22])])).
% 0.12/0.38  cnf(c_0_38, negated_conjecture, (k2_relat_1(k2_zfmisc_1(esk1_0,esk2_0))=esk6_0|esk5_0=k1_xboole_0|esk6_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.12/0.38  cnf(c_0_39, negated_conjecture, (k1_relat_1(k2_zfmisc_1(esk1_0,esk2_0))=esk5_0|esk5_0=k1_xboole_0|esk6_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_35, c_0_34])).
% 0.12/0.38  cnf(c_0_40, plain, (k4_zfmisc_1(X2,X1,X3,X4)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.12/0.38  cnf(c_0_41, negated_conjecture, (esk5_0!=esk1_0|esk6_0!=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_27])])).
% 0.12/0.38  cnf(c_0_42, negated_conjecture, (esk6_0=k1_xboole_0|esk5_0=k1_xboole_0|esk1_0=k1_xboole_0|esk2_0=k1_xboole_0|esk6_0=esk2_0), inference(spm,[status(thm)],[c_0_33, c_0_38])).
% 0.12/0.38  cnf(c_0_43, negated_conjecture, (esk6_0=k1_xboole_0|esk5_0=k1_xboole_0|esk1_0=k1_xboole_0|esk2_0=k1_xboole_0|esk5_0=esk1_0), inference(spm,[status(thm)],[c_0_35, c_0_39])).
% 0.12/0.38  cnf(c_0_44, plain, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X1),X3),X4)=k1_xboole_0|X1!=k1_xboole_0), inference(rw,[status(thm)],[c_0_40, c_0_15])).
% 0.12/0.38  cnf(c_0_45, negated_conjecture, (esk2_0=k1_xboole_0|esk1_0=k1_xboole_0|esk5_0=k1_xboole_0|esk6_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43])).
% 0.12/0.38  cnf(c_0_46, plain, (k4_zfmisc_1(X2,X3,X1,X4)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.12/0.38  cnf(c_0_47, plain, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0),X2),X3)=k1_xboole_0), inference(er,[status(thm)],[c_0_44])).
% 0.12/0.38  cnf(c_0_48, negated_conjecture, (k2_zfmisc_1(esk5_0,k1_xboole_0)=k2_zfmisc_1(esk1_0,esk2_0)|esk5_0=k1_xboole_0|esk1_0=k1_xboole_0|esk2_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_34, c_0_45])).
% 0.12/0.38  cnf(c_0_49, plain, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X3),X1),X4)=k1_xboole_0|X1!=k1_xboole_0), inference(rw,[status(thm)],[c_0_46, c_0_15])).
% 0.12/0.38  cnf(c_0_50, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),X1),X2)=k1_xboole_0|esk2_0=k1_xboole_0|esk1_0=k1_xboole_0|esk5_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.12/0.38  cnf(c_0_51, plain, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),k1_xboole_0),X3)=k1_xboole_0), inference(er,[status(thm)],[c_0_49])).
% 0.12/0.38  cnf(c_0_52, negated_conjecture, (esk5_0=k1_xboole_0|esk1_0=k1_xboole_0|esk2_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_19, c_0_50])).
% 0.12/0.38  cnf(c_0_53, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_51, c_0_51])).
% 0.12/0.38  cnf(c_0_54, negated_conjecture, (k2_zfmisc_1(esk1_0,esk2_0)=k1_xboole_0|esk2_0=k1_xboole_0|esk1_0=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_52]), c_0_53])).
% 0.12/0.38  cnf(c_0_55, negated_conjecture, (esk1_0=k1_xboole_0|esk2_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_54]), c_0_53]), c_0_53])])).
% 0.12/0.38  cnf(c_0_56, negated_conjecture, (esk1_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_55]), c_0_47])])).
% 0.12/0.38  cnf(c_0_57, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_56]), c_0_53]), c_0_53]), c_0_53])]), ['proof']).
% 0.12/0.38  # SZS output end CNFRefutation
% 0.12/0.38  # Proof object total steps             : 58
% 0.12/0.38  # Proof object clause steps            : 45
% 0.12/0.38  # Proof object formula steps           : 13
% 0.12/0.38  # Proof object conjectures             : 30
% 0.12/0.38  # Proof object clause conjectures      : 27
% 0.12/0.38  # Proof object formula conjectures     : 3
% 0.12/0.38  # Proof object initial clauses used    : 12
% 0.12/0.38  # Proof object initial formulas used   : 6
% 0.12/0.38  # Proof object generating inferences   : 18
% 0.12/0.38  # Proof object simplifying inferences  : 38
% 0.12/0.38  # Training examples: 0 positive, 0 negative
% 0.12/0.38  # Parsed axioms                        : 6
% 0.12/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.38  # Initial clauses                      : 15
% 0.12/0.38  # Removed in clause preprocessing      : 2
% 0.12/0.38  # Initial clauses in saturation        : 13
% 0.12/0.38  # Processed clauses                    : 137
% 0.12/0.38  # ...of these trivial                  : 17
% 0.12/0.38  # ...subsumed                          : 48
% 0.12/0.38  # ...remaining for further processing  : 72
% 0.12/0.38  # Other redundant clauses eliminated   : 6
% 0.12/0.38  # Clauses deleted for lack of memory   : 0
% 0.12/0.38  # Backward-subsumed                    : 11
% 0.12/0.38  # Backward-rewritten                   : 27
% 0.12/0.38  # Generated clauses                    : 645
% 0.12/0.38  # ...of the previous two non-trivial   : 459
% 0.12/0.38  # Contextual simplify-reflections      : 1
% 0.12/0.38  # Paramodulations                      : 621
% 0.12/0.38  # Factorizations                       : 9
% 0.12/0.38  # Equation resolutions                 : 15
% 0.12/0.38  # Propositional unsat checks           : 0
% 0.12/0.38  #    Propositional check models        : 0
% 0.12/0.38  #    Propositional check unsatisfiable : 0
% 0.12/0.38  #    Propositional clauses             : 0
% 0.12/0.38  #    Propositional clauses after purity: 0
% 0.12/0.38  #    Propositional unsat core size     : 0
% 0.12/0.38  #    Propositional preprocessing time  : 0.000
% 0.12/0.38  #    Propositional encoding time       : 0.000
% 0.12/0.38  #    Propositional solver time         : 0.000
% 0.12/0.38  #    Success case prop preproc time    : 0.000
% 0.12/0.38  #    Success case prop encoding time   : 0.000
% 0.12/0.38  #    Success case prop solver time     : 0.000
% 0.12/0.38  # Current number of processed clauses  : 17
% 0.12/0.38  #    Positive orientable unit clauses  : 7
% 0.12/0.38  #    Positive unorientable unit clauses: 0
% 0.12/0.38  #    Negative unit clauses             : 0
% 0.12/0.38  #    Non-unit-clauses                  : 10
% 0.12/0.38  # Current number of unprocessed clauses: 291
% 0.12/0.38  # ...number of literals in the above   : 1259
% 0.12/0.38  # Current number of archived formulas  : 0
% 0.12/0.38  # Current number of archived clauses   : 53
% 0.12/0.38  # Clause-clause subsumption calls (NU) : 125
% 0.12/0.38  # Rec. Clause-clause subsumption calls : 81
% 0.12/0.38  # Non-unit clause-clause subsumptions  : 29
% 0.12/0.38  # Unit Clause-clause subsumption calls : 0
% 0.12/0.38  # Rewrite failures with RHS unbound    : 0
% 0.12/0.38  # BW rewrite match attempts            : 23
% 0.12/0.38  # BW rewrite match successes           : 6
% 0.12/0.38  # Condensation attempts                : 0
% 0.12/0.38  # Condensation successes               : 0
% 0.12/0.38  # Termbank termtop insertions          : 8453
% 0.12/0.38  
% 0.12/0.38  # -------------------------------------------------
% 0.12/0.38  # User time                : 0.040 s
% 0.12/0.38  # System time              : 0.006 s
% 0.12/0.38  # Total time               : 0.046 s
% 0.12/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------

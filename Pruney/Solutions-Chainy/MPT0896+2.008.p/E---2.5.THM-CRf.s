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
% DateTime   : Thu Dec  3 10:59:59 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   71 (2343 expanded)
%              Number of clauses        :   52 ( 972 expanded)
%              Number of leaves         :    9 ( 595 expanded)
%              Depth                    :   22
%              Number of atoms          :  196 (8339 expanded)
%              Number of equality atoms :  169 (8260 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t56_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k4_zfmisc_1(X1,X2,X3,X4) = k4_zfmisc_1(X5,X6,X7,X8)
     => ( X1 = k1_xboole_0
        | X2 = k1_xboole_0
        | X3 = k1_xboole_0
        | X4 = k1_xboole_0
        | ( X1 = X5
          & X2 = X6
          & X3 = X7
          & X4 = X8 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_mcart_1)).

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

fof(t49_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( ~ ( ~ r1_tarski(X1,k3_zfmisc_1(X1,X2,X3))
          & ~ r1_tarski(X1,k3_zfmisc_1(X2,X3,X1))
          & ~ r1_tarski(X1,k3_zfmisc_1(X3,X1,X2)) )
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_mcart_1)).

fof(t35_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0 )
    <=> k3_zfmisc_1(X1,X2,X3) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_mcart_1)).

fof(t118_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => ( r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
        & r1_tarski(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6,X7,X8] :
        ( k4_zfmisc_1(X1,X2,X3,X4) = k4_zfmisc_1(X5,X6,X7,X8)
       => ( X1 = k1_xboole_0
          | X2 = k1_xboole_0
          | X3 = k1_xboole_0
          | X4 = k1_xboole_0
          | ( X1 = X5
            & X2 = X6
            & X3 = X7
            & X4 = X8 ) ) ) ),
    inference(assume_negation,[status(cth)],[t56_mcart_1])).

fof(c_0_10,plain,(
    ! [X16,X17,X18,X19] : k4_zfmisc_1(X16,X17,X18,X19) = k2_zfmisc_1(k3_zfmisc_1(X16,X17,X18),X19) ),
    inference(variable_rename,[status(thm)],[d4_zfmisc_1])).

fof(c_0_11,plain,(
    ! [X13,X14,X15] : k3_zfmisc_1(X13,X14,X15) = k2_zfmisc_1(k2_zfmisc_1(X13,X14),X15) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_12,plain,(
    ! [X23,X24,X25,X26,X27,X28] :
      ( ( X23 = X26
        | k3_zfmisc_1(X23,X24,X25) = k1_xboole_0
        | k3_zfmisc_1(X23,X24,X25) != k3_zfmisc_1(X26,X27,X28) )
      & ( X24 = X27
        | k3_zfmisc_1(X23,X24,X25) = k1_xboole_0
        | k3_zfmisc_1(X23,X24,X25) != k3_zfmisc_1(X26,X27,X28) )
      & ( X25 = X28
        | k3_zfmisc_1(X23,X24,X25) = k1_xboole_0
        | k3_zfmisc_1(X23,X24,X25) != k3_zfmisc_1(X26,X27,X28) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_mcart_1])])])).

fof(c_0_13,negated_conjecture,
    ( k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0) = k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0)
    & esk1_0 != k1_xboole_0
    & esk2_0 != k1_xboole_0
    & esk3_0 != k1_xboole_0
    & esk4_0 != k1_xboole_0
    & ( esk1_0 != esk5_0
      | esk2_0 != esk6_0
      | esk3_0 != esk7_0
      | esk4_0 != esk8_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

cnf(c_0_14,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( X1 = X2
    | k3_zfmisc_1(X3,X4,X1) = k1_xboole_0
    | k3_zfmisc_1(X3,X4,X1) != k3_zfmisc_1(X5,X6,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0) = k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

fof(c_0_19,plain,(
    ! [X32,X33,X34,X35] :
      ( ( X32 = k1_xboole_0
        | X33 = k1_xboole_0
        | X34 = k1_xboole_0
        | X35 = k1_xboole_0
        | k4_zfmisc_1(X32,X33,X34,X35) != k1_xboole_0 )
      & ( X32 != k1_xboole_0
        | k4_zfmisc_1(X32,X33,X34,X35) = k1_xboole_0 )
      & ( X33 != k1_xboole_0
        | k4_zfmisc_1(X32,X33,X34,X35) = k1_xboole_0 )
      & ( X34 != k1_xboole_0
        | k4_zfmisc_1(X32,X33,X34,X35) = k1_xboole_0 )
      & ( X35 != k1_xboole_0
        | k4_zfmisc_1(X32,X33,X34,X35) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_mcart_1])])])).

cnf(c_0_20,plain,
    ( X1 = X2
    | k2_zfmisc_1(k2_zfmisc_1(X3,X4),X1) = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(X3,X4),X1) != k2_zfmisc_1(k2_zfmisc_1(X5,X6),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_15]),c_0_15]),c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0),esk8_0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_18]),c_0_18])).

cnf(c_0_22,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | k4_zfmisc_1(X1,X2,X3,X4) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) = k1_xboole_0
    | X3 = esk8_0
    | k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_24,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_22,c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0) = k1_xboole_0
    | esk8_0 = esk4_0 ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_26,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_27,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_28,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_29,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_30,plain,
    ( X1 = X2
    | k3_zfmisc_1(X3,X1,X4) = k1_xboole_0
    | k3_zfmisc_1(X3,X1,X4) != k3_zfmisc_1(X5,X2,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_31,negated_conjecture,
    ( esk8_0 = esk4_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29])).

cnf(c_0_32,plain,
    ( X1 = X2
    | k2_zfmisc_1(k2_zfmisc_1(X3,X1),X4) = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(X3,X1),X4) != k2_zfmisc_1(k2_zfmisc_1(X5,X2),X6) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_15]),c_0_15]),c_0_15])).

cnf(c_0_33,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0),esk4_0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0) ),
    inference(rw,[status(thm)],[c_0_21,c_0_31])).

fof(c_0_34,plain,(
    ! [X29,X30,X31] :
      ( ( ~ r1_tarski(X29,k3_zfmisc_1(X29,X30,X31))
        | X29 = k1_xboole_0 )
      & ( ~ r1_tarski(X29,k3_zfmisc_1(X30,X31,X29))
        | X29 = k1_xboole_0 )
      & ( ~ r1_tarski(X29,k3_zfmisc_1(X31,X29,X30))
        | X29 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t49_mcart_1])])])])).

fof(c_0_35,plain,(
    ! [X20,X21,X22] :
      ( ( X20 = k1_xboole_0
        | X21 = k1_xboole_0
        | X22 = k1_xboole_0
        | k3_zfmisc_1(X20,X21,X22) != k1_xboole_0 )
      & ( X20 != k1_xboole_0
        | k3_zfmisc_1(X20,X21,X22) = k1_xboole_0 )
      & ( X21 != k1_xboole_0
        | k3_zfmisc_1(X20,X21,X22) = k1_xboole_0 )
      & ( X22 != k1_xboole_0
        | k3_zfmisc_1(X20,X21,X22) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_mcart_1])])])).

cnf(c_0_36,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0) = k1_xboole_0
    | esk7_0 = X1
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0) != k2_zfmisc_1(k2_zfmisc_1(X2,X1),X3) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_37,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k3_zfmisc_1(X2,X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_38,plain,(
    ! [X10,X11,X12] :
      ( ( r1_tarski(k2_zfmisc_1(X10,X12),k2_zfmisc_1(X11,X12))
        | ~ r1_tarski(X10,X11) )
      & ( r1_tarski(k2_zfmisc_1(X12,X10),k2_zfmisc_1(X12,X11))
        | ~ r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t118_zfmisc_1])])])).

cnf(c_0_39,plain,
    ( k3_zfmisc_1(X2,X1,X3) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_40,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0) = k1_xboole_0
    | esk7_0 = esk3_0 ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_41,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X1),X3)) ),
    inference(rw,[status(thm)],[c_0_37,c_0_15])).

cnf(c_0_42,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2))
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_43,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X2,X1),X3) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_39,c_0_15])).

cnf(c_0_44,plain,
    ( X1 = X2
    | k3_zfmisc_1(X1,X3,X4) = k1_xboole_0
    | k3_zfmisc_1(X1,X3,X4) != k3_zfmisc_1(X2,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_45,negated_conjecture,
    ( esk7_0 = esk3_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_40]),c_0_26]),c_0_27]),c_0_28]),c_0_29])).

cnf(c_0_46,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,k2_zfmisc_1(X3,k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_47,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0),X2) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_43])).

cnf(c_0_48,plain,
    ( X1 = X2
    | k2_zfmisc_1(k2_zfmisc_1(X1,X3),X4) = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(X1,X3),X4) != k2_zfmisc_1(k2_zfmisc_1(X2,X5),X6) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_15]),c_0_15]),c_0_15])).

cnf(c_0_49,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk3_0),esk4_0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0) ),
    inference(rw,[status(thm)],[c_0_33,c_0_45])).

cnf(c_0_50,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_51,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0) = k1_xboole_0
    | k2_zfmisc_1(esk5_0,esk6_0) = X1
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0) != k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_52,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0) = k1_xboole_0
    | ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_50])).

cnf(c_0_53,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0) = k1_xboole_0
    | k2_zfmisc_1(esk5_0,esk6_0) = k2_zfmisc_1(esk1_0,esk2_0) ),
    inference(er,[status(thm)],[c_0_51])).

cnf(c_0_54,negated_conjecture,
    ( ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0),k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_52]),c_0_26]),c_0_27]),c_0_28]),c_0_29])).

cnf(c_0_55,negated_conjecture,
    ( k2_zfmisc_1(esk5_0,esk6_0) = k2_zfmisc_1(esk1_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_53]),c_0_26]),c_0_27]),c_0_28]),c_0_29])).

cnf(c_0_56,negated_conjecture,
    ( ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk3_0),k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_54,c_0_45])).

cnf(c_0_57,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),X1) = k1_xboole_0
    | esk6_0 = X2
    | k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),X1) != k2_zfmisc_1(k2_zfmisc_1(X3,X2),X4) ),
    inference(spm,[status(thm)],[c_0_32,c_0_55])).

fof(c_0_58,plain,(
    ! [X9] : r1_tarski(k1_xboole_0,X9) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_59,negated_conjecture,
    ( ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_56,c_0_55])).

cnf(c_0_60,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),X1) = k1_xboole_0
    | esk6_0 = esk2_0 ),
    inference(er,[status(thm)],[c_0_57])).

cnf(c_0_61,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_62,negated_conjecture,
    ( esk1_0 != esk5_0
    | esk2_0 != esk6_0
    | esk3_0 != esk7_0
    | esk4_0 != esk8_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_63,negated_conjecture,
    ( esk6_0 = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61])])).

cnf(c_0_64,negated_conjecture,
    ( esk5_0 != esk1_0
    | esk6_0 != esk2_0
    | esk7_0 != esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_31])])).

cnf(c_0_65,negated_conjecture,
    ( k2_zfmisc_1(esk5_0,esk2_0) = k2_zfmisc_1(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_55,c_0_63])).

cnf(c_0_66,negated_conjecture,
    ( esk5_0 != esk1_0
    | esk6_0 != esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_45])])).

cnf(c_0_67,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),X1) = k1_xboole_0
    | esk5_0 = X2
    | k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),X1) != k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4) ),
    inference(spm,[status(thm)],[c_0_48,c_0_65])).

cnf(c_0_68,negated_conjecture,
    ( esk5_0 != esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_63])])).

cnf(c_0_69,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),X1) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_67]),c_0_68])).

cnf(c_0_70,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_69]),c_0_61])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:30:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.18/0.44  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S0Y
% 0.18/0.44  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.18/0.44  #
% 0.18/0.44  # Preprocessing time       : 0.027 s
% 0.18/0.44  # Presaturation interreduction done
% 0.18/0.44  
% 0.18/0.44  # Proof found!
% 0.18/0.44  # SZS status Theorem
% 0.18/0.44  # SZS output start CNFRefutation
% 0.18/0.44  fof(t56_mcart_1, conjecture, ![X1, X2, X3, X4, X5, X6, X7, X8]:(k4_zfmisc_1(X1,X2,X3,X4)=k4_zfmisc_1(X5,X6,X7,X8)=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|(((X1=X5&X2=X6)&X3=X7)&X4=X8))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_mcart_1)).
% 0.18/0.44  fof(d4_zfmisc_1, axiom, ![X1, X2, X3, X4]:k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 0.18/0.44  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.18/0.44  fof(t37_mcart_1, axiom, ![X1, X2, X3, X4, X5, X6]:(k3_zfmisc_1(X1,X2,X3)=k3_zfmisc_1(X4,X5,X6)=>(k3_zfmisc_1(X1,X2,X3)=k1_xboole_0|((X1=X4&X2=X5)&X3=X6))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_mcart_1)).
% 0.18/0.44  fof(t55_mcart_1, axiom, ![X1, X2, X3, X4]:((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&X4!=k1_xboole_0)<=>k4_zfmisc_1(X1,X2,X3,X4)!=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_mcart_1)).
% 0.18/0.44  fof(t49_mcart_1, axiom, ![X1, X2, X3]:(~(((~(r1_tarski(X1,k3_zfmisc_1(X1,X2,X3)))&~(r1_tarski(X1,k3_zfmisc_1(X2,X3,X1))))&~(r1_tarski(X1,k3_zfmisc_1(X3,X1,X2)))))=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_mcart_1)).
% 0.18/0.44  fof(t35_mcart_1, axiom, ![X1, X2, X3]:(((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)<=>k3_zfmisc_1(X1,X2,X3)!=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_mcart_1)).
% 0.18/0.44  fof(t118_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>(r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&r1_tarski(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 0.18/0.44  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.18/0.44  fof(c_0_9, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6, X7, X8]:(k4_zfmisc_1(X1,X2,X3,X4)=k4_zfmisc_1(X5,X6,X7,X8)=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|(((X1=X5&X2=X6)&X3=X7)&X4=X8)))), inference(assume_negation,[status(cth)],[t56_mcart_1])).
% 0.18/0.44  fof(c_0_10, plain, ![X16, X17, X18, X19]:k4_zfmisc_1(X16,X17,X18,X19)=k2_zfmisc_1(k3_zfmisc_1(X16,X17,X18),X19), inference(variable_rename,[status(thm)],[d4_zfmisc_1])).
% 0.18/0.44  fof(c_0_11, plain, ![X13, X14, X15]:k3_zfmisc_1(X13,X14,X15)=k2_zfmisc_1(k2_zfmisc_1(X13,X14),X15), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.18/0.44  fof(c_0_12, plain, ![X23, X24, X25, X26, X27, X28]:(((X23=X26|k3_zfmisc_1(X23,X24,X25)=k1_xboole_0|k3_zfmisc_1(X23,X24,X25)!=k3_zfmisc_1(X26,X27,X28))&(X24=X27|k3_zfmisc_1(X23,X24,X25)=k1_xboole_0|k3_zfmisc_1(X23,X24,X25)!=k3_zfmisc_1(X26,X27,X28)))&(X25=X28|k3_zfmisc_1(X23,X24,X25)=k1_xboole_0|k3_zfmisc_1(X23,X24,X25)!=k3_zfmisc_1(X26,X27,X28))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_mcart_1])])])).
% 0.18/0.44  fof(c_0_13, negated_conjecture, (k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0)=k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0)&((((esk1_0!=k1_xboole_0&esk2_0!=k1_xboole_0)&esk3_0!=k1_xboole_0)&esk4_0!=k1_xboole_0)&(esk1_0!=esk5_0|esk2_0!=esk6_0|esk3_0!=esk7_0|esk4_0!=esk8_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.18/0.44  cnf(c_0_14, plain, (k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.44  cnf(c_0_15, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.44  cnf(c_0_16, plain, (X1=X2|k3_zfmisc_1(X3,X4,X1)=k1_xboole_0|k3_zfmisc_1(X3,X4,X1)!=k3_zfmisc_1(X5,X6,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.44  cnf(c_0_17, negated_conjecture, (k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0)=k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.44  cnf(c_0_18, plain, (k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.18/0.44  fof(c_0_19, plain, ![X32, X33, X34, X35]:((X32=k1_xboole_0|X33=k1_xboole_0|X34=k1_xboole_0|X35=k1_xboole_0|k4_zfmisc_1(X32,X33,X34,X35)!=k1_xboole_0)&((((X32!=k1_xboole_0|k4_zfmisc_1(X32,X33,X34,X35)=k1_xboole_0)&(X33!=k1_xboole_0|k4_zfmisc_1(X32,X33,X34,X35)=k1_xboole_0))&(X34!=k1_xboole_0|k4_zfmisc_1(X32,X33,X34,X35)=k1_xboole_0))&(X35!=k1_xboole_0|k4_zfmisc_1(X32,X33,X34,X35)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_mcart_1])])])).
% 0.18/0.44  cnf(c_0_20, plain, (X1=X2|k2_zfmisc_1(k2_zfmisc_1(X3,X4),X1)=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(X3,X4),X1)!=k2_zfmisc_1(k2_zfmisc_1(X5,X6),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16, c_0_15]), c_0_15]), c_0_15])).
% 0.18/0.44  cnf(c_0_21, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0),esk8_0)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17, c_0_18]), c_0_18])).
% 0.18/0.44  cnf(c_0_22, plain, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|k4_zfmisc_1(X1,X2,X3,X4)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.18/0.44  cnf(c_0_23, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)=k1_xboole_0|X3=esk8_0|k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)!=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.18/0.44  cnf(c_0_24, plain, (X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_22, c_0_18])).
% 0.18/0.44  cnf(c_0_25, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)=k1_xboole_0|esk8_0=esk4_0), inference(er,[status(thm)],[c_0_23])).
% 0.18/0.44  cnf(c_0_26, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.44  cnf(c_0_27, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.44  cnf(c_0_28, negated_conjecture, (esk2_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.44  cnf(c_0_29, negated_conjecture, (esk1_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.44  cnf(c_0_30, plain, (X1=X2|k3_zfmisc_1(X3,X1,X4)=k1_xboole_0|k3_zfmisc_1(X3,X1,X4)!=k3_zfmisc_1(X5,X2,X6)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.44  cnf(c_0_31, negated_conjecture, (esk8_0=esk4_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26]), c_0_27]), c_0_28]), c_0_29])).
% 0.18/0.44  cnf(c_0_32, plain, (X1=X2|k2_zfmisc_1(k2_zfmisc_1(X3,X1),X4)=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(X3,X1),X4)!=k2_zfmisc_1(k2_zfmisc_1(X5,X2),X6)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_15]), c_0_15]), c_0_15])).
% 0.18/0.44  cnf(c_0_33, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0),esk4_0)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)), inference(rw,[status(thm)],[c_0_21, c_0_31])).
% 0.18/0.44  fof(c_0_34, plain, ![X29, X30, X31]:(((~r1_tarski(X29,k3_zfmisc_1(X29,X30,X31))|X29=k1_xboole_0)&(~r1_tarski(X29,k3_zfmisc_1(X30,X31,X29))|X29=k1_xboole_0))&(~r1_tarski(X29,k3_zfmisc_1(X31,X29,X30))|X29=k1_xboole_0)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t49_mcart_1])])])])).
% 0.18/0.44  fof(c_0_35, plain, ![X20, X21, X22]:((X20=k1_xboole_0|X21=k1_xboole_0|X22=k1_xboole_0|k3_zfmisc_1(X20,X21,X22)!=k1_xboole_0)&(((X20!=k1_xboole_0|k3_zfmisc_1(X20,X21,X22)=k1_xboole_0)&(X21!=k1_xboole_0|k3_zfmisc_1(X20,X21,X22)=k1_xboole_0))&(X22!=k1_xboole_0|k3_zfmisc_1(X20,X21,X22)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_mcart_1])])])).
% 0.18/0.44  cnf(c_0_36, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)=k1_xboole_0|esk7_0=X1|k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)!=k2_zfmisc_1(k2_zfmisc_1(X2,X1),X3)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.18/0.44  cnf(c_0_37, plain, (X1=k1_xboole_0|~r1_tarski(X1,k3_zfmisc_1(X2,X1,X3))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.18/0.44  fof(c_0_38, plain, ![X10, X11, X12]:((r1_tarski(k2_zfmisc_1(X10,X12),k2_zfmisc_1(X11,X12))|~r1_tarski(X10,X11))&(r1_tarski(k2_zfmisc_1(X12,X10),k2_zfmisc_1(X12,X11))|~r1_tarski(X10,X11))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t118_zfmisc_1])])])).
% 0.18/0.44  cnf(c_0_39, plain, (k3_zfmisc_1(X2,X1,X3)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.18/0.44  cnf(c_0_40, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)=k1_xboole_0|esk7_0=esk3_0), inference(er,[status(thm)],[c_0_36])).
% 0.18/0.44  cnf(c_0_41, plain, (X1=k1_xboole_0|~r1_tarski(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X1),X3))), inference(rw,[status(thm)],[c_0_37, c_0_15])).
% 0.18/0.44  cnf(c_0_42, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2))|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.18/0.44  cnf(c_0_43, plain, (k2_zfmisc_1(k2_zfmisc_1(X2,X1),X3)=k1_xboole_0|X1!=k1_xboole_0), inference(rw,[status(thm)],[c_0_39, c_0_15])).
% 0.18/0.44  cnf(c_0_44, plain, (X1=X2|k3_zfmisc_1(X1,X3,X4)=k1_xboole_0|k3_zfmisc_1(X1,X3,X4)!=k3_zfmisc_1(X2,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.44  cnf(c_0_45, negated_conjecture, (esk7_0=esk3_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_40]), c_0_26]), c_0_27]), c_0_28]), c_0_29])).
% 0.18/0.44  cnf(c_0_46, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|~r1_tarski(X1,k2_zfmisc_1(X3,k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.18/0.44  cnf(c_0_47, plain, (k2_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0),X2)=k1_xboole_0), inference(er,[status(thm)],[c_0_43])).
% 0.18/0.44  cnf(c_0_48, plain, (X1=X2|k2_zfmisc_1(k2_zfmisc_1(X1,X3),X4)=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(X1,X3),X4)!=k2_zfmisc_1(k2_zfmisc_1(X2,X5),X6)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_15]), c_0_15]), c_0_15])).
% 0.18/0.44  cnf(c_0_49, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk3_0),esk4_0)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)), inference(rw,[status(thm)],[c_0_33, c_0_45])).
% 0.18/0.44  cnf(c_0_50, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.18/0.44  cnf(c_0_51, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)=k1_xboole_0|k2_zfmisc_1(esk5_0,esk6_0)=X1|k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)!=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.18/0.44  cnf(c_0_52, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)=k1_xboole_0|~r1_tarski(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_21, c_0_50])).
% 0.18/0.44  cnf(c_0_53, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)=k1_xboole_0|k2_zfmisc_1(esk5_0,esk6_0)=k2_zfmisc_1(esk1_0,esk2_0)), inference(er,[status(thm)],[c_0_51])).
% 0.18/0.44  cnf(c_0_54, negated_conjecture, (~r1_tarski(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0),k1_xboole_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_52]), c_0_26]), c_0_27]), c_0_28]), c_0_29])).
% 0.18/0.44  cnf(c_0_55, negated_conjecture, (k2_zfmisc_1(esk5_0,esk6_0)=k2_zfmisc_1(esk1_0,esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_53]), c_0_26]), c_0_27]), c_0_28]), c_0_29])).
% 0.18/0.44  cnf(c_0_56, negated_conjecture, (~r1_tarski(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk3_0),k1_xboole_0)), inference(rw,[status(thm)],[c_0_54, c_0_45])).
% 0.18/0.44  cnf(c_0_57, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),X1)=k1_xboole_0|esk6_0=X2|k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),X1)!=k2_zfmisc_1(k2_zfmisc_1(X3,X2),X4)), inference(spm,[status(thm)],[c_0_32, c_0_55])).
% 0.18/0.44  fof(c_0_58, plain, ![X9]:r1_tarski(k1_xboole_0,X9), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.18/0.44  cnf(c_0_59, negated_conjecture, (~r1_tarski(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),k1_xboole_0)), inference(rw,[status(thm)],[c_0_56, c_0_55])).
% 0.18/0.44  cnf(c_0_60, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),X1)=k1_xboole_0|esk6_0=esk2_0), inference(er,[status(thm)],[c_0_57])).
% 0.18/0.44  cnf(c_0_61, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.18/0.44  cnf(c_0_62, negated_conjecture, (esk1_0!=esk5_0|esk2_0!=esk6_0|esk3_0!=esk7_0|esk4_0!=esk8_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.44  cnf(c_0_63, negated_conjecture, (esk6_0=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61])])).
% 0.18/0.44  cnf(c_0_64, negated_conjecture, (esk5_0!=esk1_0|esk6_0!=esk2_0|esk7_0!=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_31])])).
% 0.18/0.44  cnf(c_0_65, negated_conjecture, (k2_zfmisc_1(esk5_0,esk2_0)=k2_zfmisc_1(esk1_0,esk2_0)), inference(rw,[status(thm)],[c_0_55, c_0_63])).
% 0.18/0.44  cnf(c_0_66, negated_conjecture, (esk5_0!=esk1_0|esk6_0!=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_45])])).
% 0.18/0.44  cnf(c_0_67, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),X1)=k1_xboole_0|esk5_0=X2|k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),X1)!=k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4)), inference(spm,[status(thm)],[c_0_48, c_0_65])).
% 0.18/0.44  cnf(c_0_68, negated_conjecture, (esk5_0!=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_63])])).
% 0.18/0.44  cnf(c_0_69, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),X1)=k1_xboole_0), inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_67]), c_0_68])).
% 0.18/0.44  cnf(c_0_70, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_69]), c_0_61])]), ['proof']).
% 0.18/0.44  # SZS output end CNFRefutation
% 0.18/0.44  # Proof object total steps             : 71
% 0.18/0.44  # Proof object clause steps            : 52
% 0.18/0.44  # Proof object formula steps           : 19
% 0.18/0.44  # Proof object conjectures             : 35
% 0.18/0.44  # Proof object clause conjectures      : 32
% 0.18/0.44  # Proof object formula conjectures     : 3
% 0.18/0.44  # Proof object initial clauses used    : 16
% 0.18/0.44  # Proof object initial formulas used   : 9
% 0.18/0.44  # Proof object generating inferences   : 18
% 0.18/0.44  # Proof object simplifying inferences  : 49
% 0.18/0.44  # Training examples: 0 positive, 0 negative
% 0.18/0.44  # Parsed axioms                        : 9
% 0.18/0.44  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.44  # Initial clauses                      : 26
% 0.18/0.44  # Removed in clause preprocessing      : 2
% 0.18/0.44  # Initial clauses in saturation        : 24
% 0.18/0.44  # Processed clauses                    : 1721
% 0.18/0.44  # ...of these trivial                  : 2
% 0.18/0.44  # ...subsumed                          : 1408
% 0.18/0.44  # ...remaining for further processing  : 311
% 0.18/0.44  # Other redundant clauses eliminated   : 14
% 0.18/0.44  # Clauses deleted for lack of memory   : 0
% 0.18/0.44  # Backward-subsumed                    : 26
% 0.18/0.44  # Backward-rewritten                   : 183
% 0.18/0.44  # Generated clauses                    : 4279
% 0.18/0.44  # ...of the previous two non-trivial   : 2930
% 0.18/0.44  # Contextual simplify-reflections      : 2
% 0.18/0.44  # Paramodulations                      : 4236
% 0.18/0.44  # Factorizations                       : 19
% 0.18/0.44  # Equation resolutions                 : 24
% 0.18/0.44  # Propositional unsat checks           : 0
% 0.18/0.44  #    Propositional check models        : 0
% 0.18/0.44  #    Propositional check unsatisfiable : 0
% 0.18/0.44  #    Propositional clauses             : 0
% 0.18/0.44  #    Propositional clauses after purity: 0
% 0.18/0.44  #    Propositional unsat core size     : 0
% 0.18/0.44  #    Propositional preprocessing time  : 0.000
% 0.18/0.44  #    Propositional encoding time       : 0.000
% 0.18/0.44  #    Propositional solver time         : 0.000
% 0.18/0.44  #    Success case prop preproc time    : 0.000
% 0.18/0.44  #    Success case prop encoding time   : 0.000
% 0.18/0.44  #    Success case prop solver time     : 0.000
% 0.18/0.44  # Current number of processed clauses  : 75
% 0.18/0.44  #    Positive orientable unit clauses  : 8
% 0.18/0.44  #    Positive unorientable unit clauses: 0
% 0.18/0.44  #    Negative unit clauses             : 12
% 0.18/0.44  #    Non-unit-clauses                  : 55
% 0.18/0.44  # Current number of unprocessed clauses: 63
% 0.18/0.44  # ...number of literals in the above   : 202
% 0.18/0.44  # Current number of archived formulas  : 0
% 0.18/0.44  # Current number of archived clauses   : 231
% 0.18/0.44  # Clause-clause subsumption calls (NU) : 6340
% 0.18/0.44  # Rec. Clause-clause subsumption calls : 5347
% 0.18/0.44  # Non-unit clause-clause subsumptions  : 447
% 0.18/0.44  # Unit Clause-clause subsumption calls : 194
% 0.18/0.44  # Rewrite failures with RHS unbound    : 0
% 0.18/0.44  # BW rewrite match attempts            : 11
% 0.18/0.44  # BW rewrite match successes           : 10
% 0.18/0.44  # Condensation attempts                : 0
% 0.18/0.44  # Condensation successes               : 0
% 0.18/0.44  # Termbank termtop insertions          : 58626
% 0.18/0.44  
% 0.18/0.44  # -------------------------------------------------
% 0.18/0.44  # User time                : 0.102 s
% 0.18/0.44  # System time              : 0.003 s
% 0.18/0.44  # Total time               : 0.104 s
% 0.18/0.44  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------

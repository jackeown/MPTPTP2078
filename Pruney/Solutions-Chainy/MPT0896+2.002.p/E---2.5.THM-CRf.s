%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:58 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   94 (2272 expanded)
%              Number of clauses        :   71 ( 924 expanded)
%              Number of leaves         :   11 ( 577 expanded)
%              Depth                    :   20
%              Number of atoms          :  305 (9308 expanded)
%              Number of equality atoms :  231 (8403 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   15 (   3 average)
%              Maximal term depth       :    4 (   1 average)

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

fof(t37_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( k3_zfmisc_1(X1,X2,X3) = k3_zfmisc_1(X4,X5,X6)
     => ( k3_zfmisc_1(X1,X2,X3) = k1_xboole_0
        | ( X1 = X4
          & X2 = X5
          & X3 = X6 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_mcart_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(t53_mcart_1,axiom,(
    ! [X1,X2,X3,X4] : k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_mcart_1)).

fof(t118_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => ( r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
        & r1_tarski(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(t55_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & X4 != k1_xboole_0 )
    <=> k4_zfmisc_1(X1,X2,X3,X4) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_mcart_1)).

fof(t117_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & ( r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X3,X1))
          | r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) )
        & ~ r1_tarski(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

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

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(c_0_11,negated_conjecture,(
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

fof(c_0_12,plain,(
    ! [X33,X34,X35,X36,X37,X38] :
      ( ( X33 = X36
        | k3_zfmisc_1(X33,X34,X35) = k1_xboole_0
        | k3_zfmisc_1(X33,X34,X35) != k3_zfmisc_1(X36,X37,X38) )
      & ( X34 = X37
        | k3_zfmisc_1(X33,X34,X35) = k1_xboole_0
        | k3_zfmisc_1(X33,X34,X35) != k3_zfmisc_1(X36,X37,X38) )
      & ( X35 = X38
        | k3_zfmisc_1(X33,X34,X35) = k1_xboole_0
        | k3_zfmisc_1(X33,X34,X35) != k3_zfmisc_1(X36,X37,X38) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_mcart_1])])])).

fof(c_0_13,plain,(
    ! [X24,X25,X26] : k3_zfmisc_1(X24,X25,X26) = k2_zfmisc_1(k2_zfmisc_1(X24,X25),X26) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_14,negated_conjecture,
    ( k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0) = k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0)
    & esk1_0 != k1_xboole_0
    & esk2_0 != k1_xboole_0
    & esk3_0 != k1_xboole_0
    & esk4_0 != k1_xboole_0
    & ( esk1_0 != esk5_0
      | esk2_0 != esk6_0
      | esk3_0 != esk7_0
      | esk4_0 != esk8_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

fof(c_0_15,plain,(
    ! [X39,X40,X41,X42] : k4_zfmisc_1(X39,X40,X41,X42) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X39,X40),X41),X42) ),
    inference(variable_rename,[status(thm)],[t53_mcart_1])).

cnf(c_0_16,plain,
    ( X1 = X2
    | k3_zfmisc_1(X3,X4,X1) = k1_xboole_0
    | k3_zfmisc_1(X3,X4,X1) != k3_zfmisc_1(X5,X6,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0) = k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_20,plain,(
    ! [X17,X18,X19] :
      ( ( r1_tarski(k2_zfmisc_1(X17,X19),k2_zfmisc_1(X18,X19))
        | ~ r1_tarski(X17,X18) )
      & ( r1_tarski(k2_zfmisc_1(X19,X17),k2_zfmisc_1(X19,X18))
        | ~ r1_tarski(X17,X18) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t118_zfmisc_1])])])).

fof(c_0_21,plain,(
    ! [X43,X44,X45,X46] :
      ( ( X43 = k1_xboole_0
        | X44 = k1_xboole_0
        | X45 = k1_xboole_0
        | X46 = k1_xboole_0
        | k4_zfmisc_1(X43,X44,X45,X46) != k1_xboole_0 )
      & ( X43 != k1_xboole_0
        | k4_zfmisc_1(X43,X44,X45,X46) = k1_xboole_0 )
      & ( X44 != k1_xboole_0
        | k4_zfmisc_1(X43,X44,X45,X46) = k1_xboole_0 )
      & ( X45 != k1_xboole_0
        | k4_zfmisc_1(X43,X44,X45,X46) = k1_xboole_0 )
      & ( X46 != k1_xboole_0
        | k4_zfmisc_1(X43,X44,X45,X46) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_mcart_1])])])).

cnf(c_0_22,plain,
    ( X1 = X2
    | k2_zfmisc_1(k2_zfmisc_1(X3,X4),X1) = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(X3,X4),X1) != k2_zfmisc_1(k2_zfmisc_1(X5,X6),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_17]),c_0_17]),c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0),esk8_0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_19]),c_0_19])).

fof(c_0_24,plain,(
    ! [X14,X15,X16] :
      ( ( ~ r1_tarski(k2_zfmisc_1(X15,X14),k2_zfmisc_1(X16,X14))
        | X14 = k1_xboole_0
        | r1_tarski(X15,X16) )
      & ( ~ r1_tarski(k2_zfmisc_1(X14,X15),k2_zfmisc_1(X14,X16))
        | X14 = k1_xboole_0
        | r1_tarski(X15,X16) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t117_zfmisc_1])])])])).

cnf(c_0_25,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | k4_zfmisc_1(X1,X2,X3,X4) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) = k1_xboole_0
    | X3 = esk8_0
    | k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

fof(c_0_28,plain,(
    ! [X9,X10] :
      ( ( r1_tarski(X9,X10)
        | X9 != X10 )
      & ( r1_tarski(X10,X9)
        | X9 != X10 )
      & ( ~ r1_tarski(X9,X10)
        | ~ r1_tarski(X10,X9)
        | X9 = X10 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_29,plain,
    ( X2 = k1_xboole_0
    | r1_tarski(X1,X3)
    | ~ r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0),X1),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0))
    | ~ r1_tarski(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_32,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_26,c_0_19])).

cnf(c_0_33,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0) = k1_xboole_0
    | esk8_0 = esk4_0 ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_35,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_36,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0),k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0))
    | ~ r1_tarski(esk4_0,esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])).

cnf(c_0_39,negated_conjecture,
    ( esk8_0 = esk4_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_31]),c_0_34]),c_0_35]),c_0_36])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | r1_tarski(X1,k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0))
    | ~ r1_tarski(k2_zfmisc_1(X1,esk8_0),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_23])).

cnf(c_0_42,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2))
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_43,plain,(
    ! [X12,X13] :
      ( ( k2_zfmisc_1(X12,X13) != k1_xboole_0
        | X12 = k1_xboole_0
        | X13 = k1_xboole_0 )
      & ( X12 != k1_xboole_0
        | k2_zfmisc_1(X12,X13) = k1_xboole_0 )
      & ( X13 != k1_xboole_0
        | k2_zfmisc_1(X12,X13) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_44,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0),k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_39]),c_0_40])])).

cnf(c_0_46,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | r1_tarski(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0))
    | ~ r1_tarski(esk8_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_25])).

fof(c_0_47,plain,(
    ! [X27,X28,X29,X30,X31,X32] :
      ( ( X27 = X30
        | X27 = k1_xboole_0
        | X28 = k1_xboole_0
        | X29 = k1_xboole_0
        | k3_zfmisc_1(X27,X28,X29) != k3_zfmisc_1(X30,X31,X32) )
      & ( X28 = X31
        | X27 = k1_xboole_0
        | X28 = k1_xboole_0
        | X29 = k1_xboole_0
        | k3_zfmisc_1(X27,X28,X29) != k3_zfmisc_1(X30,X31,X32) )
      & ( X29 = X32
        | X27 = k1_xboole_0
        | X28 = k1_xboole_0
        | X29 = k1_xboole_0
        | k3_zfmisc_1(X27,X28,X29) != k3_zfmisc_1(X30,X31,X32) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t36_mcart_1])])])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0),k2_zfmisc_1(X1,esk8_0))
    | ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0),X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_23])).

cnf(c_0_49,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_50,plain,(
    ! [X11] : r1_tarski(k1_xboole_0,X11) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_51,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_52,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0) = k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)
    | ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_39]),c_0_39]),c_0_40])]),c_0_31])).

cnf(c_0_54,plain,
    ( X1 = X2
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X1 = k1_xboole_0
    | k3_zfmisc_1(X3,X4,X1) != k3_zfmisc_1(X5,X6,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_55,negated_conjecture,
    ( k2_zfmisc_1(X1,esk8_0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)
    | ~ r1_tarski(k2_zfmisc_1(X1,esk8_0),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0))
    | ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0),X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_48])).

cnf(c_0_56,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_49])).

cnf(c_0_57,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_58,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_51])).

cnf(c_0_59,plain,
    ( X1 = X2
    | X3 = k1_xboole_0
    | X1 = k1_xboole_0
    | X4 = k1_xboole_0
    | k3_zfmisc_1(X3,X1,X4) != k3_zfmisc_1(X5,X2,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_60,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0) = k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_53])])).

cnf(c_0_61,plain,
    ( X1 = X2
    | X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X1 = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(X3,X4),X1) != k2_zfmisc_1(k2_zfmisc_1(X5,X6),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_17]),c_0_17])).

cnf(c_0_62,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0) = k1_xboole_0
    | ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57])])).

cnf(c_0_63,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k1_xboole_0)
    | ~ r1_tarski(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_58])).

cnf(c_0_64,plain,
    ( X1 = X2
    | X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X1 = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(X3,X1),X4) != k2_zfmisc_1(k2_zfmisc_1(X5,X2),X6) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_17]),c_0_17])).

cnf(c_0_65,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r1_tarski(k2_zfmisc_1(esk5_0,esk6_0),X1)
    | ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),k2_zfmisc_1(X1,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_60])).

cnf(c_0_66,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | esk7_0 = X1
    | k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0) != k2_zfmisc_1(k2_zfmisc_1(X2,X3),X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_60])).

cnf(c_0_67,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0) = k1_xboole_0
    | ~ r1_tarski(esk7_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_68,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | esk6_0 = X1
    | k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0) != k2_zfmisc_1(k2_zfmisc_1(X2,X1),X3) ),
    inference(spm,[status(thm)],[c_0_64,c_0_60])).

cnf(c_0_69,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r1_tarski(k2_zfmisc_1(esk5_0,esk6_0),k2_zfmisc_1(esk1_0,esk2_0))
    | ~ r1_tarski(esk3_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_25])).

cnf(c_0_70,negated_conjecture,
    ( esk7_0 = esk3_0
    | esk6_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_66])).

cnf(c_0_71,negated_conjecture,
    ( ~ r1_tarski(esk7_0,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_67]),c_0_31]),c_0_34]),c_0_35]),c_0_36])).

cnf(c_0_72,negated_conjecture,
    ( esk6_0 = esk2_0
    | esk7_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_68])).

cnf(c_0_73,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r1_tarski(X1,k2_zfmisc_1(esk5_0,esk6_0))
    | ~ r1_tarski(k2_zfmisc_1(X1,esk7_0),k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_60])).

cnf(c_0_74,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | r1_tarski(k2_zfmisc_1(esk5_0,esk6_0),k2_zfmisc_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_40])]),c_0_34])).

cnf(c_0_75,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk6_0 = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_57])])).

cnf(c_0_76,negated_conjecture,
    ( esk1_0 != esk5_0
    | esk2_0 != esk6_0
    | esk3_0 != esk7_0
    | esk4_0 != esk8_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_77,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k1_xboole_0)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_56])).

cnf(c_0_78,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk5_0,esk6_0))
    | ~ r1_tarski(esk7_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_25])).

cnf(c_0_79,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | r1_tarski(k2_zfmisc_1(esk5_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_35])).

cnf(c_0_80,negated_conjecture,
    ( esk5_0 != esk1_0
    | esk6_0 != esk2_0
    | esk7_0 != esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_39])])).

cnf(c_0_81,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_77]),c_0_57])])).

cnf(c_0_82,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_70]),c_0_40])]),c_0_34])).

cnf(c_0_83,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | r1_tarski(esk5_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_79]),c_0_35])).

cnf(c_0_84,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | esk5_0 != esk1_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_70]),c_0_75])).

cnf(c_0_85,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_81,c_0_77])).

cnf(c_0_86,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk5_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_75]),c_0_35])).

cnf(c_0_87,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | ~ r1_tarski(esk1_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_83]),c_0_84])).

cnf(c_0_88,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0) = k1_xboole_0
    | ~ r1_tarski(k2_zfmisc_1(esk5_0,esk6_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_85])).

cnf(c_0_89,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_86]),c_0_35]),c_0_87])).

cnf(c_0_90,negated_conjecture,
    ( ~ r1_tarski(k2_zfmisc_1(esk5_0,esk6_0),k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_88]),c_0_31]),c_0_34]),c_0_35]),c_0_36])).

cnf(c_0_91,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_89]),c_0_57])])).

cnf(c_0_92,negated_conjecture,
    ( esk5_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_58]),c_0_57])])).

cnf(c_0_93,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_90,c_0_92]),c_0_56]),c_0_57])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n025.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 14:53:20 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.44  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.44  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.44  #
% 0.19/0.44  # Preprocessing time       : 0.028 s
% 0.19/0.44  # Presaturation interreduction done
% 0.19/0.44  
% 0.19/0.44  # Proof found!
% 0.19/0.44  # SZS status Theorem
% 0.19/0.44  # SZS output start CNFRefutation
% 0.19/0.44  fof(t56_mcart_1, conjecture, ![X1, X2, X3, X4, X5, X6, X7, X8]:(k4_zfmisc_1(X1,X2,X3,X4)=k4_zfmisc_1(X5,X6,X7,X8)=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|(((X1=X5&X2=X6)&X3=X7)&X4=X8))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_mcart_1)).
% 0.19/0.44  fof(t37_mcart_1, axiom, ![X1, X2, X3, X4, X5, X6]:(k3_zfmisc_1(X1,X2,X3)=k3_zfmisc_1(X4,X5,X6)=>(k3_zfmisc_1(X1,X2,X3)=k1_xboole_0|((X1=X4&X2=X5)&X3=X6))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_mcart_1)).
% 0.19/0.44  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.19/0.44  fof(t53_mcart_1, axiom, ![X1, X2, X3, X4]:k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_mcart_1)).
% 0.19/0.44  fof(t118_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>(r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&r1_tarski(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 0.19/0.44  fof(t55_mcart_1, axiom, ![X1, X2, X3, X4]:((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&X4!=k1_xboole_0)<=>k4_zfmisc_1(X1,X2,X3,X4)!=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_mcart_1)).
% 0.19/0.44  fof(t117_zfmisc_1, axiom, ![X1, X2, X3]:~(((X1!=k1_xboole_0&(r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X3,X1))|r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))))&~(r1_tarski(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_zfmisc_1)).
% 0.19/0.44  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.44  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.19/0.44  fof(t36_mcart_1, axiom, ![X1, X2, X3, X4, X5, X6]:(k3_zfmisc_1(X1,X2,X3)=k3_zfmisc_1(X4,X5,X6)=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|((X1=X4&X2=X5)&X3=X6))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_mcart_1)).
% 0.19/0.44  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.19/0.44  fof(c_0_11, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6, X7, X8]:(k4_zfmisc_1(X1,X2,X3,X4)=k4_zfmisc_1(X5,X6,X7,X8)=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|(((X1=X5&X2=X6)&X3=X7)&X4=X8)))), inference(assume_negation,[status(cth)],[t56_mcart_1])).
% 0.19/0.44  fof(c_0_12, plain, ![X33, X34, X35, X36, X37, X38]:(((X33=X36|k3_zfmisc_1(X33,X34,X35)=k1_xboole_0|k3_zfmisc_1(X33,X34,X35)!=k3_zfmisc_1(X36,X37,X38))&(X34=X37|k3_zfmisc_1(X33,X34,X35)=k1_xboole_0|k3_zfmisc_1(X33,X34,X35)!=k3_zfmisc_1(X36,X37,X38)))&(X35=X38|k3_zfmisc_1(X33,X34,X35)=k1_xboole_0|k3_zfmisc_1(X33,X34,X35)!=k3_zfmisc_1(X36,X37,X38))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_mcart_1])])])).
% 0.19/0.44  fof(c_0_13, plain, ![X24, X25, X26]:k3_zfmisc_1(X24,X25,X26)=k2_zfmisc_1(k2_zfmisc_1(X24,X25),X26), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.19/0.44  fof(c_0_14, negated_conjecture, (k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0)=k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0)&((((esk1_0!=k1_xboole_0&esk2_0!=k1_xboole_0)&esk3_0!=k1_xboole_0)&esk4_0!=k1_xboole_0)&(esk1_0!=esk5_0|esk2_0!=esk6_0|esk3_0!=esk7_0|esk4_0!=esk8_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 0.19/0.44  fof(c_0_15, plain, ![X39, X40, X41, X42]:k4_zfmisc_1(X39,X40,X41,X42)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X39,X40),X41),X42), inference(variable_rename,[status(thm)],[t53_mcart_1])).
% 0.19/0.44  cnf(c_0_16, plain, (X1=X2|k3_zfmisc_1(X3,X4,X1)=k1_xboole_0|k3_zfmisc_1(X3,X4,X1)!=k3_zfmisc_1(X5,X6,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.44  cnf(c_0_17, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.44  cnf(c_0_18, negated_conjecture, (k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0)=k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.44  cnf(c_0_19, plain, (k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.44  fof(c_0_20, plain, ![X17, X18, X19]:((r1_tarski(k2_zfmisc_1(X17,X19),k2_zfmisc_1(X18,X19))|~r1_tarski(X17,X18))&(r1_tarski(k2_zfmisc_1(X19,X17),k2_zfmisc_1(X19,X18))|~r1_tarski(X17,X18))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t118_zfmisc_1])])])).
% 0.19/0.44  fof(c_0_21, plain, ![X43, X44, X45, X46]:((X43=k1_xboole_0|X44=k1_xboole_0|X45=k1_xboole_0|X46=k1_xboole_0|k4_zfmisc_1(X43,X44,X45,X46)!=k1_xboole_0)&((((X43!=k1_xboole_0|k4_zfmisc_1(X43,X44,X45,X46)=k1_xboole_0)&(X44!=k1_xboole_0|k4_zfmisc_1(X43,X44,X45,X46)=k1_xboole_0))&(X45!=k1_xboole_0|k4_zfmisc_1(X43,X44,X45,X46)=k1_xboole_0))&(X46!=k1_xboole_0|k4_zfmisc_1(X43,X44,X45,X46)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_mcart_1])])])).
% 0.19/0.44  cnf(c_0_22, plain, (X1=X2|k2_zfmisc_1(k2_zfmisc_1(X3,X4),X1)=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(X3,X4),X1)!=k2_zfmisc_1(k2_zfmisc_1(X5,X6),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16, c_0_17]), c_0_17]), c_0_17])).
% 0.19/0.44  cnf(c_0_23, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0),esk8_0)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_19]), c_0_19])).
% 0.19/0.44  fof(c_0_24, plain, ![X14, X15, X16]:((~r1_tarski(k2_zfmisc_1(X15,X14),k2_zfmisc_1(X16,X14))|X14=k1_xboole_0|r1_tarski(X15,X16))&(~r1_tarski(k2_zfmisc_1(X14,X15),k2_zfmisc_1(X14,X16))|X14=k1_xboole_0|r1_tarski(X15,X16))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t117_zfmisc_1])])])])).
% 0.19/0.44  cnf(c_0_25, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.44  cnf(c_0_26, plain, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|k4_zfmisc_1(X1,X2,X3,X4)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.44  cnf(c_0_27, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)=k1_xboole_0|X3=esk8_0|k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)!=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.19/0.44  fof(c_0_28, plain, ![X9, X10]:(((r1_tarski(X9,X10)|X9!=X10)&(r1_tarski(X10,X9)|X9!=X10))&(~r1_tarski(X9,X10)|~r1_tarski(X10,X9)|X9=X10)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.44  cnf(c_0_29, plain, (X2=k1_xboole_0|r1_tarski(X1,X3)|~r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.44  cnf(c_0_30, negated_conjecture, (r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0),X1),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0))|~r1_tarski(X1,esk8_0)), inference(spm,[status(thm)],[c_0_25, c_0_23])).
% 0.19/0.44  cnf(c_0_31, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.44  cnf(c_0_32, plain, (X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_26, c_0_19])).
% 0.19/0.44  cnf(c_0_33, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)=k1_xboole_0|esk8_0=esk4_0), inference(er,[status(thm)],[c_0_27])).
% 0.19/0.44  cnf(c_0_34, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.44  cnf(c_0_35, negated_conjecture, (esk2_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.44  cnf(c_0_36, negated_conjecture, (esk1_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.44  cnf(c_0_37, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.44  cnf(c_0_38, negated_conjecture, (r1_tarski(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0),k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0))|~r1_tarski(esk4_0,esk8_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])).
% 0.19/0.44  cnf(c_0_39, negated_conjecture, (esk8_0=esk4_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_31]), c_0_34]), c_0_35]), c_0_36])).
% 0.19/0.44  cnf(c_0_40, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_37])).
% 0.19/0.44  cnf(c_0_41, negated_conjecture, (esk8_0=k1_xboole_0|r1_tarski(X1,k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0))|~r1_tarski(k2_zfmisc_1(X1,esk8_0),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0))), inference(spm,[status(thm)],[c_0_29, c_0_23])).
% 0.19/0.44  cnf(c_0_42, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2))|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.44  fof(c_0_43, plain, ![X12, X13]:((k2_zfmisc_1(X12,X13)!=k1_xboole_0|(X12=k1_xboole_0|X13=k1_xboole_0))&((X12!=k1_xboole_0|k2_zfmisc_1(X12,X13)=k1_xboole_0)&(X13!=k1_xboole_0|k2_zfmisc_1(X12,X13)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.19/0.44  cnf(c_0_44, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.44  cnf(c_0_45, negated_conjecture, (r1_tarski(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0),k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_39]), c_0_40])])).
% 0.19/0.44  cnf(c_0_46, negated_conjecture, (esk8_0=k1_xboole_0|r1_tarski(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0))|~r1_tarski(esk8_0,esk4_0)), inference(spm,[status(thm)],[c_0_41, c_0_25])).
% 0.19/0.44  fof(c_0_47, plain, ![X27, X28, X29, X30, X31, X32]:(((X27=X30|(X27=k1_xboole_0|X28=k1_xboole_0|X29=k1_xboole_0)|k3_zfmisc_1(X27,X28,X29)!=k3_zfmisc_1(X30,X31,X32))&(X28=X31|(X27=k1_xboole_0|X28=k1_xboole_0|X29=k1_xboole_0)|k3_zfmisc_1(X27,X28,X29)!=k3_zfmisc_1(X30,X31,X32)))&(X29=X32|(X27=k1_xboole_0|X28=k1_xboole_0|X29=k1_xboole_0)|k3_zfmisc_1(X27,X28,X29)!=k3_zfmisc_1(X30,X31,X32))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t36_mcart_1])])])).
% 0.19/0.44  cnf(c_0_48, negated_conjecture, (r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0),k2_zfmisc_1(X1,esk8_0))|~r1_tarski(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0),X1)), inference(spm,[status(thm)],[c_0_42, c_0_23])).
% 0.19/0.44  cnf(c_0_49, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.44  fof(c_0_50, plain, ![X11]:r1_tarski(k1_xboole_0,X11), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.19/0.44  cnf(c_0_51, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.44  cnf(c_0_52, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0)=k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)|~r1_tarski(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.19/0.44  cnf(c_0_53, negated_conjecture, (r1_tarski(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_39]), c_0_39]), c_0_40])]), c_0_31])).
% 0.19/0.44  cnf(c_0_54, plain, (X1=X2|X3=k1_xboole_0|X4=k1_xboole_0|X1=k1_xboole_0|k3_zfmisc_1(X3,X4,X1)!=k3_zfmisc_1(X5,X6,X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.44  cnf(c_0_55, negated_conjecture, (k2_zfmisc_1(X1,esk8_0)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)|~r1_tarski(k2_zfmisc_1(X1,esk8_0),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0))|~r1_tarski(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0),X1)), inference(spm,[status(thm)],[c_0_44, c_0_48])).
% 0.19/0.44  cnf(c_0_56, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_49])).
% 0.19/0.44  cnf(c_0_57, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.19/0.44  cnf(c_0_58, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_51])).
% 0.19/0.44  cnf(c_0_59, plain, (X1=X2|X3=k1_xboole_0|X1=k1_xboole_0|X4=k1_xboole_0|k3_zfmisc_1(X3,X1,X4)!=k3_zfmisc_1(X5,X2,X6)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.44  cnf(c_0_60, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0)=k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_53])])).
% 0.19/0.44  cnf(c_0_61, plain, (X1=X2|X4=k1_xboole_0|X3=k1_xboole_0|X1=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(X3,X4),X1)!=k2_zfmisc_1(k2_zfmisc_1(X5,X6),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_17]), c_0_17])).
% 0.19/0.44  cnf(c_0_62, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)=k1_xboole_0|~r1_tarski(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57])])).
% 0.19/0.44  cnf(c_0_63, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k1_xboole_0)|~r1_tarski(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_25, c_0_58])).
% 0.19/0.44  cnf(c_0_64, plain, (X1=X2|X4=k1_xboole_0|X3=k1_xboole_0|X1=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(X3,X1),X4)!=k2_zfmisc_1(k2_zfmisc_1(X5,X2),X6)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_17]), c_0_17])).
% 0.19/0.44  cnf(c_0_65, negated_conjecture, (esk7_0=k1_xboole_0|r1_tarski(k2_zfmisc_1(esk5_0,esk6_0),X1)|~r1_tarski(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),k2_zfmisc_1(X1,esk7_0))), inference(spm,[status(thm)],[c_0_29, c_0_60])).
% 0.19/0.44  cnf(c_0_66, negated_conjecture, (esk7_0=k1_xboole_0|esk5_0=k1_xboole_0|esk6_0=k1_xboole_0|esk7_0=X1|k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)!=k2_zfmisc_1(k2_zfmisc_1(X2,X3),X1)), inference(spm,[status(thm)],[c_0_61, c_0_60])).
% 0.19/0.44  cnf(c_0_67, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)=k1_xboole_0|~r1_tarski(esk7_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.19/0.44  cnf(c_0_68, negated_conjecture, (esk6_0=k1_xboole_0|esk5_0=k1_xboole_0|esk7_0=k1_xboole_0|esk6_0=X1|k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)!=k2_zfmisc_1(k2_zfmisc_1(X2,X1),X3)), inference(spm,[status(thm)],[c_0_64, c_0_60])).
% 0.19/0.44  cnf(c_0_69, negated_conjecture, (esk7_0=k1_xboole_0|r1_tarski(k2_zfmisc_1(esk5_0,esk6_0),k2_zfmisc_1(esk1_0,esk2_0))|~r1_tarski(esk3_0,esk7_0)), inference(spm,[status(thm)],[c_0_65, c_0_25])).
% 0.19/0.44  cnf(c_0_70, negated_conjecture, (esk7_0=esk3_0|esk6_0=k1_xboole_0|esk5_0=k1_xboole_0|esk7_0=k1_xboole_0), inference(er,[status(thm)],[c_0_66])).
% 0.19/0.44  cnf(c_0_71, negated_conjecture, (~r1_tarski(esk7_0,k1_xboole_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_67]), c_0_31]), c_0_34]), c_0_35]), c_0_36])).
% 0.19/0.44  cnf(c_0_72, negated_conjecture, (esk6_0=esk2_0|esk7_0=k1_xboole_0|esk5_0=k1_xboole_0|esk6_0=k1_xboole_0), inference(er,[status(thm)],[c_0_68])).
% 0.19/0.44  cnf(c_0_73, negated_conjecture, (esk7_0=k1_xboole_0|r1_tarski(X1,k2_zfmisc_1(esk5_0,esk6_0))|~r1_tarski(k2_zfmisc_1(X1,esk7_0),k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0))), inference(spm,[status(thm)],[c_0_29, c_0_60])).
% 0.19/0.44  cnf(c_0_74, negated_conjecture, (esk7_0=k1_xboole_0|esk5_0=k1_xboole_0|esk6_0=k1_xboole_0|r1_tarski(k2_zfmisc_1(esk5_0,esk6_0),k2_zfmisc_1(esk1_0,esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_40])]), c_0_34])).
% 0.19/0.44  cnf(c_0_75, negated_conjecture, (esk6_0=k1_xboole_0|esk5_0=k1_xboole_0|esk6_0=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_57])])).
% 0.19/0.44  cnf(c_0_76, negated_conjecture, (esk1_0!=esk5_0|esk2_0!=esk6_0|esk3_0!=esk7_0|esk4_0!=esk8_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.44  cnf(c_0_77, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k1_xboole_0)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_42, c_0_56])).
% 0.19/0.44  cnf(c_0_78, negated_conjecture, (esk7_0=k1_xboole_0|r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk5_0,esk6_0))|~r1_tarski(esk7_0,esk3_0)), inference(spm,[status(thm)],[c_0_73, c_0_25])).
% 0.19/0.44  cnf(c_0_79, negated_conjecture, (esk6_0=k1_xboole_0|esk5_0=k1_xboole_0|esk7_0=k1_xboole_0|r1_tarski(k2_zfmisc_1(esk5_0,esk2_0),k2_zfmisc_1(esk1_0,esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_35])).
% 0.19/0.44  cnf(c_0_80, negated_conjecture, (esk5_0!=esk1_0|esk6_0!=esk2_0|esk7_0!=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_39])])).
% 0.19/0.44  cnf(c_0_81, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_77]), c_0_57])])).
% 0.19/0.44  cnf(c_0_82, negated_conjecture, (esk7_0=k1_xboole_0|esk5_0=k1_xboole_0|esk6_0=k1_xboole_0|r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk5_0,esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_70]), c_0_40])]), c_0_34])).
% 0.19/0.44  cnf(c_0_83, negated_conjecture, (esk7_0=k1_xboole_0|esk5_0=k1_xboole_0|esk6_0=k1_xboole_0|r1_tarski(esk5_0,esk1_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_79]), c_0_35])).
% 0.19/0.44  cnf(c_0_84, negated_conjecture, (esk7_0=k1_xboole_0|esk5_0=k1_xboole_0|esk6_0=k1_xboole_0|esk5_0!=esk1_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_70]), c_0_75])).
% 0.19/0.44  cnf(c_0_85, plain, (k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_81, c_0_77])).
% 0.19/0.44  cnf(c_0_86, negated_conjecture, (esk6_0=k1_xboole_0|esk5_0=k1_xboole_0|esk7_0=k1_xboole_0|r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk5_0,esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_75]), c_0_35])).
% 0.19/0.44  cnf(c_0_87, negated_conjecture, (esk6_0=k1_xboole_0|esk5_0=k1_xboole_0|esk7_0=k1_xboole_0|~r1_tarski(esk1_0,esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_83]), c_0_84])).
% 0.19/0.44  cnf(c_0_88, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)=k1_xboole_0|~r1_tarski(k2_zfmisc_1(esk5_0,esk6_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_23, c_0_85])).
% 0.19/0.44  cnf(c_0_89, negated_conjecture, (esk7_0=k1_xboole_0|esk5_0=k1_xboole_0|esk6_0=k1_xboole_0), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_86]), c_0_35]), c_0_87])).
% 0.19/0.44  cnf(c_0_90, negated_conjecture, (~r1_tarski(k2_zfmisc_1(esk5_0,esk6_0),k1_xboole_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_88]), c_0_31]), c_0_34]), c_0_35]), c_0_36])).
% 0.19/0.44  cnf(c_0_91, negated_conjecture, (esk6_0=k1_xboole_0|esk5_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_89]), c_0_57])])).
% 0.19/0.44  cnf(c_0_92, negated_conjecture, (esk5_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_91]), c_0_58]), c_0_57])])).
% 0.19/0.44  cnf(c_0_93, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_90, c_0_92]), c_0_56]), c_0_57])]), ['proof']).
% 0.19/0.44  # SZS output end CNFRefutation
% 0.19/0.44  # Proof object total steps             : 94
% 0.19/0.44  # Proof object clause steps            : 71
% 0.19/0.44  # Proof object formula steps           : 23
% 0.19/0.44  # Proof object conjectures             : 49
% 0.19/0.44  # Proof object clause conjectures      : 46
% 0.19/0.44  # Proof object formula conjectures     : 3
% 0.19/0.44  # Proof object initial clauses used    : 20
% 0.19/0.44  # Proof object initial formulas used   : 11
% 0.19/0.44  # Proof object generating inferences   : 38
% 0.19/0.44  # Proof object simplifying inferences  : 66
% 0.19/0.44  # Training examples: 0 positive, 0 negative
% 0.19/0.44  # Parsed axioms                        : 12
% 0.19/0.44  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.44  # Initial clauses                      : 31
% 0.19/0.44  # Removed in clause preprocessing      : 2
% 0.19/0.44  # Initial clauses in saturation        : 29
% 0.19/0.44  # Processed clauses                    : 1109
% 0.19/0.44  # ...of these trivial                  : 1
% 0.19/0.44  # ...subsumed                          : 811
% 0.19/0.44  # ...remaining for further processing  : 297
% 0.19/0.44  # Other redundant clauses eliminated   : 8
% 0.19/0.44  # Clauses deleted for lack of memory   : 0
% 0.19/0.44  # Backward-subsumed                    : 67
% 0.19/0.44  # Backward-rewritten                   : 125
% 0.19/0.44  # Generated clauses                    : 3282
% 0.19/0.44  # ...of the previous two non-trivial   : 2594
% 0.19/0.44  # Contextual simplify-reflections      : 6
% 0.19/0.44  # Paramodulations                      : 3263
% 0.19/0.44  # Factorizations                       : 2
% 0.19/0.44  # Equation resolutions                 : 17
% 0.19/0.44  # Propositional unsat checks           : 0
% 0.19/0.44  #    Propositional check models        : 0
% 0.19/0.44  #    Propositional check unsatisfiable : 0
% 0.19/0.44  #    Propositional clauses             : 0
% 0.19/0.44  #    Propositional clauses after purity: 0
% 0.19/0.44  #    Propositional unsat core size     : 0
% 0.19/0.44  #    Propositional preprocessing time  : 0.000
% 0.19/0.44  #    Propositional encoding time       : 0.000
% 0.19/0.44  #    Propositional solver time         : 0.000
% 0.19/0.44  #    Success case prop preproc time    : 0.000
% 0.19/0.44  #    Success case prop encoding time   : 0.000
% 0.19/0.44  #    Success case prop solver time     : 0.000
% 0.19/0.44  # Current number of processed clauses  : 73
% 0.19/0.44  #    Positive orientable unit clauses  : 6
% 0.19/0.44  #    Positive unorientable unit clauses: 0
% 0.19/0.44  #    Negative unit clauses             : 10
% 0.19/0.44  #    Non-unit-clauses                  : 57
% 0.19/0.44  # Current number of unprocessed clauses: 1145
% 0.19/0.44  # ...number of literals in the above   : 5617
% 0.19/0.44  # Current number of archived formulas  : 0
% 0.19/0.44  # Current number of archived clauses   : 218
% 0.19/0.44  # Clause-clause subsumption calls (NU) : 5768
% 0.19/0.44  # Rec. Clause-clause subsumption calls : 4564
% 0.19/0.44  # Non-unit clause-clause subsumptions  : 444
% 0.19/0.44  # Unit Clause-clause subsumption calls : 134
% 0.19/0.44  # Rewrite failures with RHS unbound    : 0
% 0.19/0.44  # BW rewrite match attempts            : 6
% 0.19/0.44  # BW rewrite match successes           : 4
% 0.19/0.44  # Condensation attempts                : 0
% 0.19/0.44  # Condensation successes               : 0
% 0.19/0.44  # Termbank termtop insertions          : 46204
% 0.19/0.44  
% 0.19/0.44  # -------------------------------------------------
% 0.19/0.44  # User time                : 0.099 s
% 0.19/0.44  # System time              : 0.003 s
% 0.19/0.44  # Total time               : 0.102 s
% 0.19/0.44  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------

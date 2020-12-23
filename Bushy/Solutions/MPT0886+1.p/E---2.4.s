%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : mcart_1__t46_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:08 EDT 2019

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   30 (  87 expanded)
%              Number of clauses        :   13 (  34 expanded)
%              Number of leaves         :    8 (  26 expanded)
%              Depth                    :    5
%              Number of atoms          :   32 (  89 expanded)
%              Number of equality atoms :   31 (  88 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t46_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6] : k3_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4),k2_tarski(X5,X6)) = k6_enumset1(k3_mcart_1(X1,X3,X5),k3_mcart_1(X1,X4,X5),k3_mcart_1(X1,X3,X6),k3_mcart_1(X1,X4,X6),k3_mcart_1(X2,X3,X5),k3_mcart_1(X2,X4,X5),k3_mcart_1(X2,X3,X6),k3_mcart_1(X2,X4,X6)) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t46_mcart_1.p',t46_mcart_1)).

fof(t65_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t46_mcart_1.p',t65_enumset1)).

fof(t45_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t46_mcart_1.p',t45_enumset1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t46_mcart_1.p',d3_zfmisc_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t46_mcart_1.p',d3_mcart_1)).

fof(t104_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X3,X2,X4) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t46_mcart_1.p',t104_enumset1)).

fof(t25_mcart_1,axiom,(
    ! [X1,X2,X3,X4] : k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4)) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t46_mcart_1.p',t25_mcart_1)).

fof(t120_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
      & k2_zfmisc_1(X3,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t46_mcart_1.p',t120_zfmisc_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6] : k3_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4),k2_tarski(X5,X6)) = k6_enumset1(k3_mcart_1(X1,X3,X5),k3_mcart_1(X1,X4,X5),k3_mcart_1(X1,X3,X6),k3_mcart_1(X1,X4,X6),k3_mcart_1(X2,X3,X5),k3_mcart_1(X2,X4,X5),k3_mcart_1(X2,X3,X6),k3_mcart_1(X2,X4,X6)) ),
    inference(assume_negation,[status(cth)],[t46_mcart_1])).

fof(c_0_9,plain,(
    ! [X50,X51,X52,X53,X54,X55,X56,X57] : k6_enumset1(X50,X51,X52,X53,X54,X55,X56,X57) = k2_xboole_0(k2_enumset1(X50,X51,X52,X53),k2_enumset1(X54,X55,X56,X57)) ),
    inference(variable_rename,[status(thm)],[t65_enumset1])).

fof(c_0_10,plain,(
    ! [X46,X47,X48,X49] : k2_enumset1(X46,X47,X48,X49) = k2_xboole_0(k2_tarski(X46,X47),k2_tarski(X48,X49)) ),
    inference(variable_rename,[status(thm)],[t45_enumset1])).

fof(c_0_11,negated_conjecture,(
    k3_zfmisc_1(k2_tarski(esk1_0,esk2_0),k2_tarski(esk3_0,esk4_0),k2_tarski(esk5_0,esk6_0)) != k6_enumset1(k3_mcart_1(esk1_0,esk3_0,esk5_0),k3_mcart_1(esk1_0,esk4_0,esk5_0),k3_mcart_1(esk1_0,esk3_0,esk6_0),k3_mcart_1(esk1_0,esk4_0,esk6_0),k3_mcart_1(esk2_0,esk3_0,esk5_0),k3_mcart_1(esk2_0,esk4_0,esk5_0),k3_mcart_1(esk2_0,esk3_0,esk6_0),k3_mcart_1(esk2_0,esk4_0,esk6_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_12,plain,(
    ! [X24,X25,X26] : k3_zfmisc_1(X24,X25,X26) = k2_zfmisc_1(k2_zfmisc_1(X24,X25),X26) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_13,plain,(
    ! [X21,X22,X23] : k3_mcart_1(X21,X22,X23) = k4_tarski(k4_tarski(X21,X22),X23) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

cnf(c_0_14,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_16,plain,(
    ! [X30,X31,X32,X33] : k2_enumset1(X30,X31,X32,X33) = k2_enumset1(X30,X32,X31,X33) ),
    inference(variable_rename,[status(thm)],[t104_enumset1])).

fof(c_0_17,plain,(
    ! [X40,X41,X42,X43] : k2_zfmisc_1(k2_tarski(X40,X41),k2_tarski(X42,X43)) = k2_enumset1(k4_tarski(X40,X42),k4_tarski(X40,X43),k4_tarski(X41,X42),k4_tarski(X41,X43)) ),
    inference(variable_rename,[status(thm)],[t25_mcart_1])).

cnf(c_0_18,negated_conjecture,
    ( k3_zfmisc_1(k2_tarski(esk1_0,esk2_0),k2_tarski(esk3_0,esk4_0),k2_tarski(esk5_0,esk6_0)) != k6_enumset1(k3_mcart_1(esk1_0,esk3_0,esk5_0),k3_mcart_1(esk1_0,esk4_0,esk5_0),k3_mcart_1(esk1_0,esk3_0,esk6_0),k3_mcart_1(esk1_0,esk4_0,esk6_0),k3_mcart_1(esk2_0,esk3_0,esk5_0),k3_mcart_1(esk2_0,esk4_0,esk5_0),k3_mcart_1(esk2_0,esk3_0,esk6_0),k3_mcart_1(esk2_0,esk4_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)),k2_xboole_0(k2_tarski(X5,X6),k2_tarski(X7,X8))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14,c_0_15]),c_0_15])).

cnf(c_0_22,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X3,X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_24,plain,(
    ! [X34,X35,X36] :
      ( k2_zfmisc_1(k2_xboole_0(X34,X35),X36) = k2_xboole_0(k2_zfmisc_1(X34,X36),k2_zfmisc_1(X35,X36))
      & k2_zfmisc_1(X36,k2_xboole_0(X34,X35)) = k2_xboole_0(k2_zfmisc_1(X36,X34),k2_zfmisc_1(X36,X35)) ) ),
    inference(variable_rename,[status(thm)],[t120_zfmisc_1])).

cnf(c_0_25,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_tarski(esk1_0,esk2_0),k2_tarski(esk3_0,esk4_0)),k2_tarski(esk5_0,esk6_0)) != k2_xboole_0(k2_xboole_0(k2_tarski(k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0),k4_tarski(k4_tarski(esk1_0,esk4_0),esk5_0)),k2_tarski(k4_tarski(k4_tarski(esk1_0,esk3_0),esk6_0),k4_tarski(k4_tarski(esk1_0,esk4_0),esk6_0))),k2_xboole_0(k2_tarski(k4_tarski(k4_tarski(esk2_0,esk3_0),esk5_0),k4_tarski(k4_tarski(esk2_0,esk4_0),esk5_0)),k2_tarski(k4_tarski(k4_tarski(esk2_0,esk3_0),esk6_0),k4_tarski(k4_tarski(esk2_0,esk4_0),esk6_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_20]),c_0_20]),c_0_20]),c_0_20]),c_0_20]),c_0_20]),c_0_20]),c_0_21])).

cnf(c_0_26,plain,
    ( k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_xboole_0(k2_tarski(X1,X3),k2_tarski(X2,X4)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_15]),c_0_15])).

cnf(c_0_27,plain,
    ( k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_xboole_0(k2_tarski(k4_tarski(X1,X3),k4_tarski(X1,X4)),k2_tarski(k4_tarski(X2,X3),k4_tarski(X2,X4))) ),
    inference(rw,[status(thm)],[c_0_23,c_0_15])).

cnf(c_0_28,plain,
    ( k2_zfmisc_1(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_26]),c_0_26]),c_0_27]),c_0_27]),c_0_28]),c_0_27])]),
    [proof]).
%------------------------------------------------------------------------------

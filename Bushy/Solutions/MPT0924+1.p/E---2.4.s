%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : mcart_1__t84_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:14 EDT 2019

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 226 expanded)
%              Number of clauses        :   34 (  99 expanded)
%              Number of leaves         :    6 (  59 expanded)
%              Depth                    :   10
%              Number of atoms          :  122 ( 609 expanded)
%              Number of equality atoms :   10 ( 117 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t84_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] :
      ( r2_hidden(k4_mcart_1(X1,X2,X3,X4),k4_zfmisc_1(X5,X6,X7,X8))
    <=> ( r2_hidden(X1,X5)
        & r2_hidden(X2,X6)
        & r2_hidden(X3,X7)
        & r2_hidden(X4,X8) ) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t84_mcart_1.p',t84_mcart_1)).

fof(d4_mcart_1,axiom,(
    ! [X1,X2,X3,X4] : k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k3_mcart_1(X1,X2,X3),X4) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t84_mcart_1.p',d4_mcart_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t84_mcart_1.p',d3_mcart_1)).

fof(t54_mcart_1,axiom,(
    ! [X1,X2,X3,X4] : k3_zfmisc_1(k2_zfmisc_1(X1,X2),X3,X4) = k4_zfmisc_1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t84_mcart_1.p',t54_mcart_1)).

fof(t73_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( r2_hidden(k3_mcart_1(X1,X2,X3),k3_zfmisc_1(X4,X5,X6))
    <=> ( r2_hidden(X1,X4)
        & r2_hidden(X2,X5)
        & r2_hidden(X3,X6) ) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t84_mcart_1.p',t73_mcart_1)).

fof(t106_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t84_mcart_1.p',t106_zfmisc_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6,X7,X8] :
        ( r2_hidden(k4_mcart_1(X1,X2,X3,X4),k4_zfmisc_1(X5,X6,X7,X8))
      <=> ( r2_hidden(X1,X5)
          & r2_hidden(X2,X6)
          & r2_hidden(X3,X7)
          & r2_hidden(X4,X8) ) ) ),
    inference(assume_negation,[status(cth)],[t84_mcart_1])).

fof(c_0_7,plain,(
    ! [X22,X23,X24,X25] : k4_mcart_1(X22,X23,X24,X25) = k4_tarski(k3_mcart_1(X22,X23,X24),X25) ),
    inference(variable_rename,[status(thm)],[d4_mcart_1])).

fof(c_0_8,plain,(
    ! [X19,X20,X21] : k3_mcart_1(X19,X20,X21) = k4_tarski(k4_tarski(X19,X20),X21) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_9,negated_conjecture,
    ( ( ~ r2_hidden(k4_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0))
      | ~ r2_hidden(esk1_0,esk5_0)
      | ~ r2_hidden(esk2_0,esk6_0)
      | ~ r2_hidden(esk3_0,esk7_0)
      | ~ r2_hidden(esk4_0,esk8_0) )
    & ( r2_hidden(esk1_0,esk5_0)
      | r2_hidden(k4_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0)) )
    & ( r2_hidden(esk2_0,esk6_0)
      | r2_hidden(k4_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0)) )
    & ( r2_hidden(esk3_0,esk7_0)
      | r2_hidden(k4_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0)) )
    & ( r2_hidden(esk4_0,esk8_0)
      | r2_hidden(k4_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0)) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])).

cnf(c_0_10,plain,
    ( k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k3_mcart_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_12,plain,(
    ! [X36,X37,X38,X39] : k3_zfmisc_1(k2_zfmisc_1(X36,X37),X38,X39) = k4_zfmisc_1(X36,X37,X38,X39) ),
    inference(variable_rename,[status(thm)],[t54_mcart_1])).

fof(c_0_13,plain,(
    ! [X41,X42,X43,X44,X45,X46] :
      ( ( r2_hidden(X41,X44)
        | ~ r2_hidden(k3_mcart_1(X41,X42,X43),k3_zfmisc_1(X44,X45,X46)) )
      & ( r2_hidden(X42,X45)
        | ~ r2_hidden(k3_mcart_1(X41,X42,X43),k3_zfmisc_1(X44,X45,X46)) )
      & ( r2_hidden(X43,X46)
        | ~ r2_hidden(k3_mcart_1(X41,X42,X43),k3_zfmisc_1(X44,X45,X46)) )
      & ( ~ r2_hidden(X41,X44)
        | ~ r2_hidden(X42,X45)
        | ~ r2_hidden(X43,X46)
        | r2_hidden(k3_mcart_1(X41,X42,X43),k3_zfmisc_1(X44,X45,X46)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t73_mcart_1])])])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(esk4_0,esk8_0)
    | r2_hidden(k4_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4) ),
    inference(rw,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_16,plain,
    ( k3_zfmisc_1(k2_zfmisc_1(X1,X2),X3,X4) = k4_zfmisc_1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k3_mcart_1(X3,X4,X1),k3_zfmisc_1(X5,X6,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k3_mcart_1(X3,X1,X4),k3_zfmisc_1(X5,X2,X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(esk3_0,esk7_0)
    | r2_hidden(k4_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_20,negated_conjecture,
    ( ~ r2_hidden(k4_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0))
    | ~ r2_hidden(esk1_0,esk5_0)
    | ~ r2_hidden(esk2_0,esk6_0)
    | ~ r2_hidden(esk3_0,esk7_0)
    | ~ r2_hidden(esk4_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(esk4_0,esk8_0)
    | r2_hidden(k4_tarski(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),esk4_0),k3_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0,esk8_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14,c_0_15]),c_0_16])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(k4_tarski(X3,X4),X1),k3_zfmisc_1(X5,X6,X2)) ),
    inference(rw,[status(thm)],[c_0_17,c_0_11])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(k4_tarski(X3,X1),X4),k3_zfmisc_1(X5,X2,X6)) ),
    inference(rw,[status(thm)],[c_0_18,c_0_11])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk3_0,esk7_0)
    | r2_hidden(k4_tarski(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),esk4_0),k3_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0,esk8_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_15]),c_0_16])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k3_mcart_1(X1,X3,X4),k3_zfmisc_1(X2,X5,X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk1_0,esk5_0)
    | r2_hidden(k4_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_27,plain,(
    ! [X28,X29,X30,X31] :
      ( ( r2_hidden(X28,X30)
        | ~ r2_hidden(k4_tarski(X28,X29),k2_zfmisc_1(X30,X31)) )
      & ( r2_hidden(X29,X31)
        | ~ r2_hidden(k4_tarski(X28,X29),k2_zfmisc_1(X30,X31)) )
      & ( ~ r2_hidden(X28,X30)
        | ~ r2_hidden(X29,X31)
        | r2_hidden(k4_tarski(X28,X29),k2_zfmisc_1(X30,X31)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_zfmisc_1])])])).

cnf(c_0_28,negated_conjecture,
    ( ~ r2_hidden(esk1_0,esk5_0)
    | ~ r2_hidden(esk2_0,esk6_0)
    | ~ r2_hidden(esk3_0,esk7_0)
    | ~ r2_hidden(esk4_0,esk8_0)
    | ~ r2_hidden(k4_tarski(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),esk4_0),k3_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0,esk8_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_15]),c_0_16])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk4_0,esk8_0) ),
    inference(csr,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk3_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(k4_tarski(X1,X3),X4),k3_zfmisc_1(X2,X5,X6)) ),
    inference(rw,[status(thm)],[c_0_25,c_0_11])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk1_0,esk5_0)
    | r2_hidden(k4_tarski(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),esk4_0),k3_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0,esk8_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_15]),c_0_16])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk2_0,esk6_0)
    | r2_hidden(k4_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_35,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),esk4_0),k3_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0,esk8_0))
    | ~ r2_hidden(esk1_0,esk5_0)
    | ~ r2_hidden(esk2_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_29])]),c_0_30])])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk1_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk2_0,esk6_0)
    | r2_hidden(k4_tarski(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),esk4_0),k3_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0,esk8_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_15]),c_0_16])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_39,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),esk4_0),k3_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0,esk8_0))
    | ~ r2_hidden(esk2_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36])])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk2_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_37]),c_0_38])).

cnf(c_0_41,plain,
    ( r2_hidden(k3_mcart_1(X1,X3,X5),k3_zfmisc_1(X2,X4,X6))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4)
    | ~ r2_hidden(X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_42,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),esk4_0),k3_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_40])])).

cnf(c_0_43,plain,
    ( r2_hidden(k4_tarski(k4_tarski(X1,X3),X5),k3_zfmisc_1(X2,X4,X6))
    | ~ r2_hidden(X5,X6)
    | ~ r2_hidden(X3,X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_41,c_0_11])).

cnf(c_0_44,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk1_0,esk2_0),k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_29]),c_0_30])])).

cnf(c_0_45,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_46,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_40]),c_0_36])]),
    [proof]).
%------------------------------------------------------------------------------

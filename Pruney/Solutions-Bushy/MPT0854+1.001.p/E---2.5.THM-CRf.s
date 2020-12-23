%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0854+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:17 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   30 (  45 expanded)
%              Number of clauses        :   21 (  24 expanded)
%              Number of leaves         :    4 (   9 expanded)
%              Depth                    :    9
%              Number of atoms          :  113 ( 236 expanded)
%              Number of equality atoms :   63 ( 108 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d2_mcart_1,axiom,(
    ! [X1] :
      ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
     => ! [X2] :
          ( X2 = k2_mcart_1(X1)
        <=> ! [X3,X4] :
              ( X1 = k4_tarski(X3,X4)
             => X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_mcart_1)).

fof(d2_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_zfmisc_1(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5,X6] :
              ( r2_hidden(X5,X1)
              & r2_hidden(X6,X2)
              & X4 = k4_tarski(X5,X6) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(d1_mcart_1,axiom,(
    ! [X1] :
      ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
     => ! [X2] :
          ( X2 = k1_mcart_1(X1)
        <=> ! [X3,X4] :
              ( X1 = k4_tarski(X3,X4)
             => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_mcart_1)).

fof(t10_mcart_1,conjecture,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(c_0_4,plain,(
    ! [X16,X17,X18,X19,X20,X21,X22] :
      ( ( X19 != k2_mcart_1(X16)
        | X16 != k4_tarski(X20,X21)
        | X19 = X21
        | X16 != k4_tarski(X17,X18) )
      & ( X16 = k4_tarski(esk3_2(X16,X22),esk4_2(X16,X22))
        | X22 = k2_mcart_1(X16)
        | X16 != k4_tarski(X17,X18) )
      & ( X22 != esk4_2(X16,X22)
        | X22 = k2_mcart_1(X16)
        | X16 != k4_tarski(X17,X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_mcart_1])])])])])])).

cnf(c_0_5,plain,
    ( X1 = X4
    | X1 != k2_mcart_1(X2)
    | X2 != k4_tarski(X3,X4)
    | X2 != k4_tarski(X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

fof(c_0_6,plain,(
    ! [X25,X26,X27,X28,X31,X32,X33,X34,X35,X36,X38,X39] :
      ( ( r2_hidden(esk5_4(X25,X26,X27,X28),X25)
        | ~ r2_hidden(X28,X27)
        | X27 != k2_zfmisc_1(X25,X26) )
      & ( r2_hidden(esk6_4(X25,X26,X27,X28),X26)
        | ~ r2_hidden(X28,X27)
        | X27 != k2_zfmisc_1(X25,X26) )
      & ( X28 = k4_tarski(esk5_4(X25,X26,X27,X28),esk6_4(X25,X26,X27,X28))
        | ~ r2_hidden(X28,X27)
        | X27 != k2_zfmisc_1(X25,X26) )
      & ( ~ r2_hidden(X32,X25)
        | ~ r2_hidden(X33,X26)
        | X31 != k4_tarski(X32,X33)
        | r2_hidden(X31,X27)
        | X27 != k2_zfmisc_1(X25,X26) )
      & ( ~ r2_hidden(esk7_3(X34,X35,X36),X36)
        | ~ r2_hidden(X38,X34)
        | ~ r2_hidden(X39,X35)
        | esk7_3(X34,X35,X36) != k4_tarski(X38,X39)
        | X36 = k2_zfmisc_1(X34,X35) )
      & ( r2_hidden(esk8_3(X34,X35,X36),X34)
        | r2_hidden(esk7_3(X34,X35,X36),X36)
        | X36 = k2_zfmisc_1(X34,X35) )
      & ( r2_hidden(esk9_3(X34,X35,X36),X35)
        | r2_hidden(esk7_3(X34,X35,X36),X36)
        | X36 = k2_zfmisc_1(X34,X35) )
      & ( esk7_3(X34,X35,X36) = k4_tarski(esk8_3(X34,X35,X36),esk9_3(X34,X35,X36))
        | r2_hidden(esk7_3(X34,X35,X36),X36)
        | X36 = k2_zfmisc_1(X34,X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).

fof(c_0_7,plain,(
    ! [X7,X8,X9,X10,X11,X12,X13] :
      ( ( X10 != k1_mcart_1(X7)
        | X7 != k4_tarski(X11,X12)
        | X10 = X11
        | X7 != k4_tarski(X8,X9) )
      & ( X7 = k4_tarski(esk1_2(X7,X13),esk2_2(X7,X13))
        | X13 = k1_mcart_1(X7)
        | X7 != k4_tarski(X8,X9) )
      & ( X13 != esk1_2(X7,X13)
        | X13 = k1_mcart_1(X7)
        | X7 != k4_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_mcart_1])])])])])])).

cnf(c_0_8,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X3
    | k4_tarski(X1,X2) != k4_tarski(X4,X3) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_5])])).

cnf(c_0_9,plain,
    ( X1 = k4_tarski(esk5_4(X2,X3,X4,X1),esk6_4(X2,X3,X4,X1))
    | ~ r2_hidden(X1,X4)
    | X4 != k2_zfmisc_1(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( X1 = X3
    | X1 != k1_mcart_1(X2)
    | X2 != k4_tarski(X3,X4)
    | X2 != k4_tarski(X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( r2_hidden(esk6_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(er,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k4_tarski(esk5_4(X1,X2,k2_zfmisc_1(X1,X2),X3),esk6_4(X1,X2,k2_zfmisc_1(X1,X2),X3)) = X3
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_9])).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
       => ( r2_hidden(k1_mcart_1(X1),X2)
          & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    inference(assume_negation,[status(cth)],[t10_mcart_1])).

cnf(c_0_15,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X3
    | k4_tarski(X1,X2) != k4_tarski(X3,X4) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_10])])).

cnf(c_0_16,plain,
    ( r2_hidden(esk6_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X2)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( esk6_4(X1,X2,k2_zfmisc_1(X1,X2),X3) = k2_mcart_1(X3)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

fof(c_0_18,negated_conjecture,
    ( r2_hidden(esk10_0,k2_zfmisc_1(esk11_0,esk12_0))
    & ( ~ r2_hidden(k1_mcart_1(esk10_0),esk11_0)
      | ~ r2_hidden(k2_mcart_1(esk10_0),esk12_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

cnf(c_0_19,plain,
    ( r2_hidden(esk5_4(X1,X2,X3,X4),X1)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_20,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( r2_hidden(k2_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk10_0,k2_zfmisc_1(esk11_0,esk12_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( r2_hidden(esk5_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X1)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( esk5_4(X1,X2,k2_zfmisc_1(X1,X2),X3) = k1_mcart_1(X3)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_13])).

cnf(c_0_25,negated_conjecture,
    ( ~ r2_hidden(k1_mcart_1(esk10_0),esk11_0)
    | ~ r2_hidden(k2_mcart_1(esk10_0),esk12_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk10_0),esk12_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_27,plain,
    ( r2_hidden(k1_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( ~ r2_hidden(k1_mcart_1(esk10_0),esk11_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_26])])).

cnf(c_0_29,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_22]),c_0_28]),
    [proof]).

%------------------------------------------------------------------------------

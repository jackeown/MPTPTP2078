%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0912+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:23 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   27 (  46 expanded)
%              Number of clauses        :   18 (  24 expanded)
%              Number of leaves         :    4 (  10 expanded)
%              Depth                    :   10
%              Number of atoms          :   97 ( 292 expanded)
%              Number of equality atoms :   34 ( 112 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t72_mcart_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ~ ( r2_hidden(X1,k3_zfmisc_1(X2,X3,X4))
        & ! [X5,X6,X7] :
            ~ ( r2_hidden(X5,X2)
              & r2_hidden(X6,X3)
              & r2_hidden(X7,X4)
              & X1 = k3_mcart_1(X5,X6,X7) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_mcart_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(d2_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_zfmisc_1(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5,X6] :
              ( r2_hidden(X5,X1)
              & r2_hidden(X6,X2)
              & X4 = k4_tarski(X5,X6) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ~ ( r2_hidden(X1,k3_zfmisc_1(X2,X3,X4))
          & ! [X5,X6,X7] :
              ~ ( r2_hidden(X5,X2)
                & r2_hidden(X6,X3)
                & r2_hidden(X7,X4)
                & X1 = k3_mcart_1(X5,X6,X7) ) ) ),
    inference(assume_negation,[status(cth)],[t72_mcart_1])).

fof(c_0_5,negated_conjecture,(
    ! [X35,X36,X37] :
      ( r2_hidden(esk6_0,k3_zfmisc_1(esk7_0,esk8_0,esk9_0))
      & ( ~ r2_hidden(X35,esk7_0)
        | ~ r2_hidden(X36,esk8_0)
        | ~ r2_hidden(X37,esk9_0)
        | esk6_0 != k3_mcart_1(X35,X36,X37) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])).

fof(c_0_6,plain,(
    ! [X25,X26,X27] : k3_mcart_1(X25,X26,X27) = k4_tarski(k4_tarski(X25,X26),X27) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_7,plain,(
    ! [X8,X9,X10,X11,X14,X15,X16,X17,X18,X19,X21,X22] :
      ( ( r2_hidden(esk1_4(X8,X9,X10,X11),X8)
        | ~ r2_hidden(X11,X10)
        | X10 != k2_zfmisc_1(X8,X9) )
      & ( r2_hidden(esk2_4(X8,X9,X10,X11),X9)
        | ~ r2_hidden(X11,X10)
        | X10 != k2_zfmisc_1(X8,X9) )
      & ( X11 = k4_tarski(esk1_4(X8,X9,X10,X11),esk2_4(X8,X9,X10,X11))
        | ~ r2_hidden(X11,X10)
        | X10 != k2_zfmisc_1(X8,X9) )
      & ( ~ r2_hidden(X15,X8)
        | ~ r2_hidden(X16,X9)
        | X14 != k4_tarski(X15,X16)
        | r2_hidden(X14,X10)
        | X10 != k2_zfmisc_1(X8,X9) )
      & ( ~ r2_hidden(esk3_3(X17,X18,X19),X19)
        | ~ r2_hidden(X21,X17)
        | ~ r2_hidden(X22,X18)
        | esk3_3(X17,X18,X19) != k4_tarski(X21,X22)
        | X19 = k2_zfmisc_1(X17,X18) )
      & ( r2_hidden(esk4_3(X17,X18,X19),X17)
        | r2_hidden(esk3_3(X17,X18,X19),X19)
        | X19 = k2_zfmisc_1(X17,X18) )
      & ( r2_hidden(esk5_3(X17,X18,X19),X18)
        | r2_hidden(esk3_3(X17,X18,X19),X19)
        | X19 = k2_zfmisc_1(X17,X18) )
      & ( esk3_3(X17,X18,X19) = k4_tarski(esk4_3(X17,X18,X19),esk5_3(X17,X18,X19))
        | r2_hidden(esk3_3(X17,X18,X19),X19)
        | X19 = k2_zfmisc_1(X17,X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).

cnf(c_0_8,negated_conjecture,
    ( ~ r2_hidden(X1,esk7_0)
    | ~ r2_hidden(X2,esk8_0)
    | ~ r2_hidden(X3,esk9_0)
    | esk6_0 != k3_mcart_1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( X1 = k4_tarski(esk1_4(X2,X3,X4,X1),esk2_4(X2,X3,X4,X1))
    | ~ r2_hidden(X1,X4)
    | X4 != k2_zfmisc_1(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( esk6_0 != k4_tarski(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X3,esk9_0)
    | ~ r2_hidden(X2,esk8_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(rw,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_12,plain,
    ( k4_tarski(esk1_4(X1,X2,k2_zfmisc_1(X1,X2),X3),esk2_4(X1,X2,k2_zfmisc_1(X1,X2),X3)) = X3
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_10])).

cnf(c_0_13,plain,
    ( r2_hidden(esk2_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,negated_conjecture,
    ( k4_tarski(X1,X2) != esk6_0
    | ~ r2_hidden(esk2_4(X3,X4,k2_zfmisc_1(X3,X4),X1),esk8_0)
    | ~ r2_hidden(esk1_4(X3,X4,k2_zfmisc_1(X3,X4),X1),esk7_0)
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,X4))
    | ~ r2_hidden(X2,esk9_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_15,plain,
    ( r2_hidden(esk2_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X2)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_16,plain,
    ( r2_hidden(esk1_4(X1,X2,X3,X4),X1)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_17,negated_conjecture,
    ( k4_tarski(X1,X2) != esk6_0
    | ~ r2_hidden(esk1_4(X3,esk8_0,k2_zfmisc_1(X3,esk8_0),X1),esk7_0)
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,esk8_0))
    | ~ r2_hidden(X2,esk9_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_18,plain,
    ( r2_hidden(esk1_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X1)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( k4_tarski(X1,X2) != esk6_0
    | ~ r2_hidden(X1,k2_zfmisc_1(esk7_0,esk8_0))
    | ~ r2_hidden(X2,esk9_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

fof(c_0_20,plain,(
    ! [X28,X29,X30] : k3_zfmisc_1(X28,X29,X30) = k2_zfmisc_1(k2_zfmisc_1(X28,X29),X30) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

cnf(c_0_21,negated_conjecture,
    ( k4_tarski(esk1_4(k2_zfmisc_1(esk7_0,esk8_0),X1,k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),X1),X2),X3) != esk6_0
    | ~ r2_hidden(X2,k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),X1))
    | ~ r2_hidden(X3,esk9_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk6_0,k3_zfmisc_1(esk7_0,esk8_0,esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_23,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( ~ r2_hidden(esk2_4(k2_zfmisc_1(esk7_0,esk8_0),X1,k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),X1),esk6_0),esk9_0)
    | ~ r2_hidden(esk6_0,k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),X1)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_12])])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk6_0,k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0)) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_26,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_15]),c_0_25])]),
    [proof]).

%------------------------------------------------------------------------------

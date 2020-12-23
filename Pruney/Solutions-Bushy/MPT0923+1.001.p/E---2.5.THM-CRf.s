%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0923+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:25 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   34 (  47 expanded)
%              Number of clauses        :   23 (  23 expanded)
%              Number of leaves         :    5 (  11 expanded)
%              Depth                    :   11
%              Number of atoms          :  129 ( 252 expanded)
%              Number of equality atoms :   38 (  75 expanded)
%              Maximal formula depth    :   23 (   6 average)
%              Maximal clause size      :   28 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t83_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5] :
      ~ ( r2_hidden(X1,k4_zfmisc_1(X2,X3,X4,X5))
        & ! [X6,X7,X8,X9] :
            ~ ( r2_hidden(X6,X2)
              & r2_hidden(X7,X3)
              & r2_hidden(X8,X4)
              & r2_hidden(X9,X5)
              & X1 = k4_mcart_1(X6,X7,X8,X9) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_mcart_1)).

fof(d4_mcart_1,axiom,(
    ! [X1,X2,X3,X4] : k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k3_mcart_1(X1,X2,X3),X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).

fof(t72_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ~ ( r2_hidden(X1,k3_zfmisc_1(X2,X3,X4))
        & ! [X5,X6,X7] :
            ~ ( r2_hidden(X5,X2)
              & r2_hidden(X6,X3)
              & r2_hidden(X7,X4)
              & X1 = k3_mcart_1(X5,X6,X7) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_mcart_1)).

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

fof(d4_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5] :
        ~ ( r2_hidden(X1,k4_zfmisc_1(X2,X3,X4,X5))
          & ! [X6,X7,X8,X9] :
              ~ ( r2_hidden(X6,X2)
                & r2_hidden(X7,X3)
                & r2_hidden(X8,X4)
                & r2_hidden(X9,X5)
                & X1 = k4_mcart_1(X6,X7,X8,X9) ) ) ),
    inference(assume_negation,[status(cth)],[t83_mcart_1])).

fof(c_0_6,negated_conjecture,(
    ! [X47,X48,X49,X50] :
      ( r2_hidden(esk9_0,k4_zfmisc_1(esk10_0,esk11_0,esk12_0,esk13_0))
      & ( ~ r2_hidden(X47,esk10_0)
        | ~ r2_hidden(X48,esk11_0)
        | ~ r2_hidden(X49,esk12_0)
        | ~ r2_hidden(X50,esk13_0)
        | esk9_0 != k4_mcart_1(X47,X48,X49,X50) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])).

fof(c_0_7,plain,(
    ! [X27,X28,X29,X30] : k4_mcart_1(X27,X28,X29,X30) = k4_tarski(k3_mcart_1(X27,X28,X29),X30) ),
    inference(variable_rename,[status(thm)],[d4_mcart_1])).

cnf(c_0_8,negated_conjecture,
    ( ~ r2_hidden(X1,esk10_0)
    | ~ r2_hidden(X2,esk11_0)
    | ~ r2_hidden(X3,esk12_0)
    | ~ r2_hidden(X4,esk13_0)
    | esk9_0 != k4_mcart_1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,plain,
    ( k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k3_mcart_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_10,plain,(
    ! [X35,X36,X37,X38] :
      ( ( r2_hidden(esk6_4(X35,X36,X37,X38),X36)
        | ~ r2_hidden(X35,k3_zfmisc_1(X36,X37,X38)) )
      & ( r2_hidden(esk7_4(X35,X36,X37,X38),X37)
        | ~ r2_hidden(X35,k3_zfmisc_1(X36,X37,X38)) )
      & ( r2_hidden(esk8_4(X35,X36,X37,X38),X38)
        | ~ r2_hidden(X35,k3_zfmisc_1(X36,X37,X38)) )
      & ( X35 = k3_mcart_1(esk6_4(X35,X36,X37,X38),esk7_4(X35,X36,X37,X38),esk8_4(X35,X36,X37,X38))
        | ~ r2_hidden(X35,k3_zfmisc_1(X36,X37,X38)) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t72_mcart_1])])])])).

cnf(c_0_11,negated_conjecture,
    ( esk9_0 != k4_tarski(k3_mcart_1(X1,X2,X3),X4)
    | ~ r2_hidden(X4,esk13_0)
    | ~ r2_hidden(X3,esk12_0)
    | ~ r2_hidden(X2,esk11_0)
    | ~ r2_hidden(X1,esk10_0) ),
    inference(rw,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_12,plain,
    ( X1 = k3_mcart_1(esk6_4(X1,X2,X3,X4),esk7_4(X1,X2,X3,X4),esk8_4(X1,X2,X3,X4))
    | ~ r2_hidden(X1,k3_zfmisc_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( k4_tarski(X1,X2) != esk9_0
    | ~ r2_hidden(esk8_4(X1,X3,X4,X5),esk12_0)
    | ~ r2_hidden(esk7_4(X1,X3,X4,X5),esk11_0)
    | ~ r2_hidden(esk6_4(X1,X3,X4,X5),esk10_0)
    | ~ r2_hidden(X1,k3_zfmisc_1(X3,X4,X5))
    | ~ r2_hidden(X2,esk13_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_14,plain,
    ( r2_hidden(esk8_4(X1,X2,X3,X4),X4)
    | ~ r2_hidden(X1,k3_zfmisc_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( k4_tarski(X1,X2) != esk9_0
    | ~ r2_hidden(esk7_4(X1,X3,X4,esk12_0),esk11_0)
    | ~ r2_hidden(esk6_4(X1,X3,X4,esk12_0),esk10_0)
    | ~ r2_hidden(X1,k3_zfmisc_1(X3,X4,esk12_0))
    | ~ r2_hidden(X2,esk13_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_16,plain,
    ( r2_hidden(esk7_4(X1,X2,X3,X4),X3)
    | ~ r2_hidden(X1,k3_zfmisc_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_17,plain,(
    ! [X10,X11,X12,X13,X16,X17,X18,X19,X20,X21,X23,X24] :
      ( ( r2_hidden(esk1_4(X10,X11,X12,X13),X10)
        | ~ r2_hidden(X13,X12)
        | X12 != k2_zfmisc_1(X10,X11) )
      & ( r2_hidden(esk2_4(X10,X11,X12,X13),X11)
        | ~ r2_hidden(X13,X12)
        | X12 != k2_zfmisc_1(X10,X11) )
      & ( X13 = k4_tarski(esk1_4(X10,X11,X12,X13),esk2_4(X10,X11,X12,X13))
        | ~ r2_hidden(X13,X12)
        | X12 != k2_zfmisc_1(X10,X11) )
      & ( ~ r2_hidden(X17,X10)
        | ~ r2_hidden(X18,X11)
        | X16 != k4_tarski(X17,X18)
        | r2_hidden(X16,X12)
        | X12 != k2_zfmisc_1(X10,X11) )
      & ( ~ r2_hidden(esk3_3(X19,X20,X21),X21)
        | ~ r2_hidden(X23,X19)
        | ~ r2_hidden(X24,X20)
        | esk3_3(X19,X20,X21) != k4_tarski(X23,X24)
        | X21 = k2_zfmisc_1(X19,X20) )
      & ( r2_hidden(esk4_3(X19,X20,X21),X19)
        | r2_hidden(esk3_3(X19,X20,X21),X21)
        | X21 = k2_zfmisc_1(X19,X20) )
      & ( r2_hidden(esk5_3(X19,X20,X21),X20)
        | r2_hidden(esk3_3(X19,X20,X21),X21)
        | X21 = k2_zfmisc_1(X19,X20) )
      & ( esk3_3(X19,X20,X21) = k4_tarski(esk4_3(X19,X20,X21),esk5_3(X19,X20,X21))
        | r2_hidden(esk3_3(X19,X20,X21),X21)
        | X21 = k2_zfmisc_1(X19,X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).

cnf(c_0_18,negated_conjecture,
    ( k4_tarski(X1,X2) != esk9_0
    | ~ r2_hidden(esk6_4(X1,X3,esk11_0,esk12_0),esk10_0)
    | ~ r2_hidden(X1,k3_zfmisc_1(X3,esk11_0,esk12_0))
    | ~ r2_hidden(X2,esk13_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_19,plain,
    ( r2_hidden(esk6_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X1,k3_zfmisc_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_20,plain,
    ( r2_hidden(esk1_4(X1,X2,X3,X4),X1)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( k4_tarski(X1,X2) != esk9_0
    | ~ r2_hidden(X1,k3_zfmisc_1(esk10_0,esk11_0,esk12_0))
    | ~ r2_hidden(X2,esk13_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_22,plain,
    ( r2_hidden(esk1_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X1)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_23,plain,
    ( X1 = k4_tarski(esk1_4(X2,X3,X4,X1),esk2_4(X2,X3,X4,X1))
    | ~ r2_hidden(X1,X4)
    | X4 != k2_zfmisc_1(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_24,plain,(
    ! [X31,X32,X33,X34] : k4_zfmisc_1(X31,X32,X33,X34) = k2_zfmisc_1(k3_zfmisc_1(X31,X32,X33),X34) ),
    inference(variable_rename,[status(thm)],[d4_zfmisc_1])).

cnf(c_0_25,negated_conjecture,
    ( k4_tarski(esk1_4(k3_zfmisc_1(esk10_0,esk11_0,esk12_0),X1,k2_zfmisc_1(k3_zfmisc_1(esk10_0,esk11_0,esk12_0),X1),X2),X3) != esk9_0
    | ~ r2_hidden(X2,k2_zfmisc_1(k3_zfmisc_1(esk10_0,esk11_0,esk12_0),X1))
    | ~ r2_hidden(X3,esk13_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_26,plain,
    ( k4_tarski(esk1_4(X1,X2,k2_zfmisc_1(X1,X2),X3),esk2_4(X1,X2,k2_zfmisc_1(X1,X2),X3)) = X3
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_27,plain,
    ( r2_hidden(esk2_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk9_0,k4_zfmisc_1(esk10_0,esk11_0,esk12_0,esk13_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_29,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( ~ r2_hidden(esk2_4(k3_zfmisc_1(esk10_0,esk11_0,esk12_0),X1,k2_zfmisc_1(k3_zfmisc_1(esk10_0,esk11_0,esk12_0),X1),esk9_0),esk13_0)
    | ~ r2_hidden(esk9_0,k2_zfmisc_1(k3_zfmisc_1(esk10_0,esk11_0,esk12_0),X1)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26])])).

cnf(c_0_31,plain,
    ( r2_hidden(esk2_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X2)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk9_0,k2_zfmisc_1(k3_zfmisc_1(esk10_0,esk11_0,esk12_0),esk13_0)) ),
    inference(rw,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])]),
    [proof]).

%------------------------------------------------------------------------------

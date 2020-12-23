%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0296+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:22 EST 2020

% Result     : Theorem 0.11s
% Output     : CNFRefutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :   41 ( 141 expanded)
%              Number of clauses        :   32 (  75 expanded)
%              Number of leaves         :    4 (  30 expanded)
%              Depth                    :    9
%              Number of atoms          :  151 ( 869 expanded)
%              Number of equality atoms :   48 ( 330 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(t33_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( k4_tarski(X1,X2) = k4_tarski(X3,X4)
     => ( X1 = X3
        & X2 = X4 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_zfmisc_1)).

fof(t104_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4,X5] :
      ~ ( r2_hidden(X1,k3_xboole_0(k2_zfmisc_1(X2,X3),k2_zfmisc_1(X4,X5)))
        & ! [X6,X7] :
            ~ ( X1 = k4_tarski(X6,X7)
              & r2_hidden(X6,k3_xboole_0(X2,X4))
              & r2_hidden(X7,k3_xboole_0(X3,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_zfmisc_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(c_0_4,plain,(
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

fof(c_0_5,plain,(
    ! [X34,X35,X36,X37] :
      ( ( X34 = X36
        | k4_tarski(X34,X35) != k4_tarski(X36,X37) )
      & ( X35 = X37
        | k4_tarski(X34,X35) != k4_tarski(X36,X37) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_zfmisc_1])])])).

cnf(c_0_6,plain,
    ( X1 = k4_tarski(esk1_4(X2,X3,X4,X1),esk2_4(X2,X3,X4,X1))
    | ~ r2_hidden(X1,X4)
    | X4 != k2_zfmisc_1(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5] :
        ~ ( r2_hidden(X1,k3_xboole_0(k2_zfmisc_1(X2,X3),k2_zfmisc_1(X4,X5)))
          & ! [X6,X7] :
              ~ ( X1 = k4_tarski(X6,X7)
                & r2_hidden(X6,k3_xboole_0(X2,X4))
                & r2_hidden(X7,k3_xboole_0(X3,X5)) ) ) ),
    inference(assume_negation,[status(cth)],[t104_zfmisc_1])).

fof(c_0_8,plain,(
    ! [X25,X26,X27,X28,X29,X30,X31,X32] :
      ( ( r2_hidden(X28,X25)
        | ~ r2_hidden(X28,X27)
        | X27 != k3_xboole_0(X25,X26) )
      & ( r2_hidden(X28,X26)
        | ~ r2_hidden(X28,X27)
        | X27 != k3_xboole_0(X25,X26) )
      & ( ~ r2_hidden(X29,X25)
        | ~ r2_hidden(X29,X26)
        | r2_hidden(X29,X27)
        | X27 != k3_xboole_0(X25,X26) )
      & ( ~ r2_hidden(esk6_3(X30,X31,X32),X32)
        | ~ r2_hidden(esk6_3(X30,X31,X32),X30)
        | ~ r2_hidden(esk6_3(X30,X31,X32),X31)
        | X32 = k3_xboole_0(X30,X31) )
      & ( r2_hidden(esk6_3(X30,X31,X32),X30)
        | r2_hidden(esk6_3(X30,X31,X32),X32)
        | X32 = k3_xboole_0(X30,X31) )
      & ( r2_hidden(esk6_3(X30,X31,X32),X31)
        | r2_hidden(esk6_3(X30,X31,X32),X32)
        | X32 = k3_xboole_0(X30,X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_9,plain,
    ( r2_hidden(esk1_4(X1,X2,X3,X4),X1)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_10,plain,
    ( X1 = X2
    | k4_tarski(X1,X3) != k4_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_11,plain,
    ( k4_tarski(esk1_4(X1,X2,k2_zfmisc_1(X1,X2),X3),esk2_4(X1,X2,k2_zfmisc_1(X1,X2),X3)) = X3
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( r2_hidden(esk2_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_13,plain,
    ( X1 = X2
    | k4_tarski(X3,X1) != k4_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_14,negated_conjecture,(
    ! [X43,X44] :
      ( r2_hidden(esk7_0,k3_xboole_0(k2_zfmisc_1(esk8_0,esk9_0),k2_zfmisc_1(esk10_0,esk11_0)))
      & ( esk7_0 != k4_tarski(X43,X44)
        | ~ r2_hidden(X43,k3_xboole_0(esk8_0,esk10_0))
        | ~ r2_hidden(X44,k3_xboole_0(esk9_0,esk11_0)) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,plain,
    ( r2_hidden(esk1_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X1)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_9])).

cnf(c_0_17,plain,
    ( esk1_4(X1,X2,k2_zfmisc_1(X1,X2),k4_tarski(X3,X4)) = X3
    | ~ r2_hidden(k4_tarski(X3,X4),k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11])])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_20,plain,
    ( r2_hidden(esk2_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X2)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_21,plain,
    ( esk2_4(X1,X2,k2_zfmisc_1(X1,X2),k4_tarski(X3,X4)) = X4
    | ~ r2_hidden(k4_tarski(X3,X4),k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_11])])).

cnf(c_0_22,negated_conjecture,
    ( esk7_0 != k4_tarski(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(esk8_0,esk10_0))
    | ~ r2_hidden(X2,k3_xboole_0(esk9_0,esk11_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk7_0,k3_xboole_0(k2_zfmisc_1(esk8_0,esk9_0),k2_zfmisc_1(esk10_0,esk11_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( k4_tarski(X1,X2) != esk7_0
    | ~ r2_hidden(X1,k3_xboole_0(esk8_0,esk10_0))
    | ~ r2_hidden(X2,esk11_0)
    | ~ r2_hidden(X2,esk9_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_30,plain,
    ( r2_hidden(esk1_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X4)
    | ~ r2_hidden(X3,k2_zfmisc_1(X4,X5))
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_11])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk7_0,k2_zfmisc_1(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk7_0,k2_zfmisc_1(esk10_0,esk11_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_26])).

cnf(c_0_33,plain,
    ( r2_hidden(esk2_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X4)
    | ~ r2_hidden(X3,k2_zfmisc_1(X5,X4))
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_11])).

cnf(c_0_34,negated_conjecture,
    ( k4_tarski(X1,X2) != esk7_0
    | ~ r2_hidden(X2,esk11_0)
    | ~ r2_hidden(X2,esk9_0)
    | ~ r2_hidden(X1,esk10_0)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_23])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk1_4(X1,X2,k2_zfmisc_1(X1,X2),esk7_0),esk8_0)
    | ~ r2_hidden(esk7_0,k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk1_4(X1,X2,k2_zfmisc_1(X1,X2),esk7_0),esk10_0)
    | ~ r2_hidden(esk7_0,k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk2_4(X1,X2,k2_zfmisc_1(X1,X2),esk7_0),esk9_0)
    | ~ r2_hidden(esk7_0,k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk2_4(X1,X2,k2_zfmisc_1(X1,X2),esk7_0),esk11_0)
    | ~ r2_hidden(esk7_0,k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( ~ r2_hidden(esk7_0,k2_zfmisc_1(X1,X2)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_11])]),c_0_35]),c_0_36]),c_0_37]),c_0_38])).

cnf(c_0_40,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_32,c_0_39]),
    [proof]).

%------------------------------------------------------------------------------

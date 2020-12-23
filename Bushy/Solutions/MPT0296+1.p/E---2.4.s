%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : zfmisc_1__t104_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:57 EDT 2019

% Result     : Theorem 11.11s
% Output     : CNFRefutation 11.11s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 156 expanded)
%              Number of clauses        :   36 (  82 expanded)
%              Number of leaves         :    4 (  32 expanded)
%              Depth                    :   11
%              Number of atoms          :  141 ( 850 expanded)
%              Number of equality atoms :   52 ( 293 expanded)
%              Maximal formula depth    :   23 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t104_zfmisc_1.p',d4_xboole_0)).

fof(t104_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4,X5] :
      ~ ( r2_hidden(X1,k3_xboole_0(k2_zfmisc_1(X2,X3),k2_zfmisc_1(X4,X5)))
        & ! [X6,X7] :
            ~ ( X1 = k4_tarski(X6,X7)
              & r2_hidden(X6,k3_xboole_0(X2,X4))
              & r2_hidden(X7,k3_xboole_0(X3,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t104_zfmisc_1.p',t104_zfmisc_1)).

fof(d2_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_zfmisc_1(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5,X6] :
              ( r2_hidden(X5,X1)
              & r2_hidden(X6,X2)
              & X4 = k4_tarski(X5,X6) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t104_zfmisc_1.p',d2_zfmisc_1)).

fof(t33_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( k4_tarski(X1,X2) = k4_tarski(X3,X4)
     => ( X1 = X3
        & X2 = X4 ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t104_zfmisc_1.p',t33_zfmisc_1)).

fof(c_0_4,plain,(
    ! [X36,X37,X38,X39,X40,X41,X42,X43] :
      ( ( r2_hidden(X39,X36)
        | ~ r2_hidden(X39,X38)
        | X38 != k3_xboole_0(X36,X37) )
      & ( r2_hidden(X39,X37)
        | ~ r2_hidden(X39,X38)
        | X38 != k3_xboole_0(X36,X37) )
      & ( ~ r2_hidden(X40,X36)
        | ~ r2_hidden(X40,X37)
        | r2_hidden(X40,X38)
        | X38 != k3_xboole_0(X36,X37) )
      & ( ~ r2_hidden(esk11_3(X41,X42,X43),X43)
        | ~ r2_hidden(esk11_3(X41,X42,X43),X41)
        | ~ r2_hidden(esk11_3(X41,X42,X43),X42)
        | X43 = k3_xboole_0(X41,X42) )
      & ( r2_hidden(esk11_3(X41,X42,X43),X41)
        | r2_hidden(esk11_3(X41,X42,X43),X43)
        | X43 = k3_xboole_0(X41,X42) )
      & ( r2_hidden(esk11_3(X41,X42,X43),X42)
        | r2_hidden(esk11_3(X41,X42,X43),X43)
        | X43 = k3_xboole_0(X41,X42) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5] :
        ~ ( r2_hidden(X1,k3_xboole_0(k2_zfmisc_1(X2,X3),k2_zfmisc_1(X4,X5)))
          & ! [X6,X7] :
              ~ ( X1 = k4_tarski(X6,X7)
                & r2_hidden(X6,k3_xboole_0(X2,X4))
                & r2_hidden(X7,k3_xboole_0(X3,X5)) ) ) ),
    inference(assume_negation,[status(cth)],[t104_zfmisc_1])).

fof(c_0_6,plain,(
    ! [X19,X20,X21,X22,X25,X26,X27,X28,X29,X30,X32,X33] :
      ( ( r2_hidden(esk6_4(X19,X20,X21,X22),X19)
        | ~ r2_hidden(X22,X21)
        | X21 != k2_zfmisc_1(X19,X20) )
      & ( r2_hidden(esk7_4(X19,X20,X21,X22),X20)
        | ~ r2_hidden(X22,X21)
        | X21 != k2_zfmisc_1(X19,X20) )
      & ( X22 = k4_tarski(esk6_4(X19,X20,X21,X22),esk7_4(X19,X20,X21,X22))
        | ~ r2_hidden(X22,X21)
        | X21 != k2_zfmisc_1(X19,X20) )
      & ( ~ r2_hidden(X26,X19)
        | ~ r2_hidden(X27,X20)
        | X25 != k4_tarski(X26,X27)
        | r2_hidden(X25,X21)
        | X21 != k2_zfmisc_1(X19,X20) )
      & ( ~ r2_hidden(esk8_3(X28,X29,X30),X30)
        | ~ r2_hidden(X32,X28)
        | ~ r2_hidden(X33,X29)
        | esk8_3(X28,X29,X30) != k4_tarski(X32,X33)
        | X30 = k2_zfmisc_1(X28,X29) )
      & ( r2_hidden(esk9_3(X28,X29,X30),X28)
        | r2_hidden(esk8_3(X28,X29,X30),X30)
        | X30 = k2_zfmisc_1(X28,X29) )
      & ( r2_hidden(esk10_3(X28,X29,X30),X29)
        | r2_hidden(esk8_3(X28,X29,X30),X30)
        | X30 = k2_zfmisc_1(X28,X29) )
      & ( esk8_3(X28,X29,X30) = k4_tarski(esk9_3(X28,X29,X30),esk10_3(X28,X29,X30))
        | r2_hidden(esk8_3(X28,X29,X30),X30)
        | X30 = k2_zfmisc_1(X28,X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).

cnf(c_0_7,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

fof(c_0_8,negated_conjecture,(
    ! [X13,X14] :
      ( r2_hidden(esk1_0,k3_xboole_0(k2_zfmisc_1(esk2_0,esk3_0),k2_zfmisc_1(esk4_0,esk5_0)))
      & ( esk1_0 != k4_tarski(X13,X14)
        | ~ r2_hidden(X13,k3_xboole_0(esk2_0,esk4_0))
        | ~ r2_hidden(X14,k3_xboole_0(esk3_0,esk5_0)) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])).

cnf(c_0_9,plain,
    ( X1 = k4_tarski(esk6_4(X2,X3,X4,X1),esk7_4(X2,X3,X4,X1))
    | ~ r2_hidden(X1,X4)
    | X4 != k2_zfmisc_1(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( r2_hidden(esk1_0,k3_xboole_0(k2_zfmisc_1(esk2_0,esk3_0),k2_zfmisc_1(esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

fof(c_0_13,plain,(
    ! [X47,X48,X49,X50] :
      ( ( X47 = X49
        | k4_tarski(X47,X48) != k4_tarski(X49,X50) )
      & ( X48 = X50
        | k4_tarski(X47,X48) != k4_tarski(X49,X50) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_zfmisc_1])])])).

cnf(c_0_14,plain,
    ( k4_tarski(esk6_4(X1,X2,k2_zfmisc_1(X1,X2),X3),esk7_4(X1,X2,k2_zfmisc_1(X1,X2),X3)) = X3
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( r2_hidden(esk1_0,k2_zfmisc_1(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( r2_hidden(esk7_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_18,plain,
    ( X1 = X2
    | k4_tarski(X3,X1) != k4_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( k4_tarski(esk6_4(esk4_0,esk5_0,k2_zfmisc_1(esk4_0,esk5_0),esk1_0),esk7_4(esk4_0,esk5_0,k2_zfmisc_1(esk4_0,esk5_0),esk1_0)) = esk1_0 ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(esk1_0,k2_zfmisc_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_11])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_22,plain,
    ( r2_hidden(esk7_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X2)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( X1 = esk7_4(esk4_0,esk5_0,k2_zfmisc_1(esk4_0,esk5_0),esk1_0)
    | k4_tarski(X2,X1) != esk1_0 ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( k4_tarski(esk6_4(esk2_0,esk3_0,k2_zfmisc_1(esk2_0,esk3_0),esk1_0),esk7_4(esk2_0,esk3_0,k2_zfmisc_1(esk2_0,esk3_0),esk1_0)) = esk1_0 ),
    inference(spm,[status(thm)],[c_0_14,c_0_20])).

cnf(c_0_25,plain,
    ( r2_hidden(esk6_4(X1,X2,X3,X4),X1)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_26,plain,
    ( X1 = X2
    | k4_tarski(X1,X3) != k4_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk7_4(esk2_0,esk3_0,k2_zfmisc_1(esk2_0,esk3_0),esk1_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_20])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk7_4(esk4_0,esk5_0,k2_zfmisc_1(esk4_0,esk5_0),esk1_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_15])).

cnf(c_0_30,negated_conjecture,
    ( esk7_4(esk4_0,esk5_0,k2_zfmisc_1(esk4_0,esk5_0),esk1_0) = esk7_4(esk2_0,esk3_0,k2_zfmisc_1(esk2_0,esk3_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_31,plain,
    ( r2_hidden(esk6_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X1)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( X1 = esk6_4(esk4_0,esk5_0,k2_zfmisc_1(esk4_0,esk5_0),esk1_0)
    | k4_tarski(X1,X2) != esk1_0 ),
    inference(spm,[status(thm)],[c_0_26,c_0_19])).

cnf(c_0_33,negated_conjecture,
    ( esk1_0 != k4_tarski(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(esk2_0,esk4_0))
    | ~ r2_hidden(X2,k3_xboole_0(esk3_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk7_4(esk2_0,esk3_0,k2_zfmisc_1(esk2_0,esk3_0),esk1_0),k3_xboole_0(esk3_0,X1))
    | ~ r2_hidden(esk7_4(esk2_0,esk3_0,k2_zfmisc_1(esk2_0,esk3_0),esk1_0),X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk7_4(esk2_0,esk3_0,k2_zfmisc_1(esk2_0,esk3_0),esk1_0),esk5_0) ),
    inference(rw,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk6_4(esk2_0,esk3_0,k2_zfmisc_1(esk2_0,esk3_0),esk1_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_20])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk6_4(esk4_0,esk5_0,k2_zfmisc_1(esk4_0,esk5_0),esk1_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_15])).

cnf(c_0_38,negated_conjecture,
    ( esk6_4(esk4_0,esk5_0,k2_zfmisc_1(esk4_0,esk5_0),esk1_0) = esk6_4(esk2_0,esk3_0,k2_zfmisc_1(esk2_0,esk3_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_24])).

cnf(c_0_39,negated_conjecture,
    ( ~ r2_hidden(esk7_4(esk2_0,esk3_0,k2_zfmisc_1(esk2_0,esk3_0),esk1_0),k3_xboole_0(esk3_0,esk5_0))
    | ~ r2_hidden(esk6_4(esk2_0,esk3_0,k2_zfmisc_1(esk2_0,esk3_0),esk1_0),k3_xboole_0(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_24])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk7_4(esk2_0,esk3_0,k2_zfmisc_1(esk2_0,esk3_0),esk1_0),k3_xboole_0(esk3_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk6_4(esk2_0,esk3_0,k2_zfmisc_1(esk2_0,esk3_0),esk1_0),k3_xboole_0(esk2_0,X1))
    | ~ r2_hidden(esk6_4(esk2_0,esk3_0,k2_zfmisc_1(esk2_0,esk3_0),esk1_0),X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_36])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk6_4(esk2_0,esk3_0,k2_zfmisc_1(esk2_0,esk3_0),esk1_0),esk4_0) ),
    inference(rw,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( ~ r2_hidden(esk6_4(esk2_0,esk3_0,k2_zfmisc_1(esk2_0,esk3_0),esk1_0),k3_xboole_0(esk2_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_40])])).

cnf(c_0_44,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43]),
    [proof]).
%------------------------------------------------------------------------------

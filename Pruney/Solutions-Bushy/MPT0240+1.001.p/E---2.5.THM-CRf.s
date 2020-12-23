%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0240+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:16 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   27 (  59 expanded)
%              Number of clauses        :   20 (  32 expanded)
%              Number of leaves         :    3 (  13 expanded)
%              Depth                    :   11
%              Number of atoms          :  104 ( 336 expanded)
%              Number of equality atoms :   63 ( 191 expanded)
%              Maximal formula depth    :   23 (   4 average)
%              Maximal clause size      :   28 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

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

fof(t35_zfmisc_1,conjecture,(
    ! [X1,X2] : k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k4_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_zfmisc_1)).

fof(c_0_3,plain,(
    ! [X7,X8,X9,X10,X11,X12] :
      ( ( ~ r2_hidden(X9,X8)
        | X9 = X7
        | X8 != k1_tarski(X7) )
      & ( X10 != X7
        | r2_hidden(X10,X8)
        | X8 != k1_tarski(X7) )
      & ( ~ r2_hidden(esk1_2(X11,X12),X12)
        | esk1_2(X11,X12) != X11
        | X12 = k1_tarski(X11) )
      & ( r2_hidden(esk1_2(X11,X12),X12)
        | esk1_2(X11,X12) = X11
        | X12 = k1_tarski(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_4,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

fof(c_0_5,plain,(
    ! [X14,X15,X16,X17,X20,X21,X22,X23,X24,X25,X27,X28] :
      ( ( r2_hidden(esk2_4(X14,X15,X16,X17),X14)
        | ~ r2_hidden(X17,X16)
        | X16 != k2_zfmisc_1(X14,X15) )
      & ( r2_hidden(esk3_4(X14,X15,X16,X17),X15)
        | ~ r2_hidden(X17,X16)
        | X16 != k2_zfmisc_1(X14,X15) )
      & ( X17 = k4_tarski(esk2_4(X14,X15,X16,X17),esk3_4(X14,X15,X16,X17))
        | ~ r2_hidden(X17,X16)
        | X16 != k2_zfmisc_1(X14,X15) )
      & ( ~ r2_hidden(X21,X14)
        | ~ r2_hidden(X22,X15)
        | X20 != k4_tarski(X21,X22)
        | r2_hidden(X20,X16)
        | X16 != k2_zfmisc_1(X14,X15) )
      & ( ~ r2_hidden(esk4_3(X23,X24,X25),X25)
        | ~ r2_hidden(X27,X23)
        | ~ r2_hidden(X28,X24)
        | esk4_3(X23,X24,X25) != k4_tarski(X27,X28)
        | X25 = k2_zfmisc_1(X23,X24) )
      & ( r2_hidden(esk5_3(X23,X24,X25),X23)
        | r2_hidden(esk4_3(X23,X24,X25),X25)
        | X25 = k2_zfmisc_1(X23,X24) )
      & ( r2_hidden(esk6_3(X23,X24,X25),X24)
        | r2_hidden(esk4_3(X23,X24,X25),X25)
        | X25 = k2_zfmisc_1(X23,X24) )
      & ( esk4_3(X23,X24,X25) = k4_tarski(esk5_3(X23,X24,X25),esk6_3(X23,X24,X25))
        | r2_hidden(esk4_3(X23,X24,X25),X25)
        | X25 = k2_zfmisc_1(X23,X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).

cnf(c_0_6,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_4])).

cnf(c_0_7,plain,
    ( r2_hidden(esk6_3(X1,X2,X3),X2)
    | r2_hidden(esk4_3(X1,X2,X3),X3)
    | X3 = k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,plain,
    ( esk4_3(X1,X2,X3) = k4_tarski(esk5_3(X1,X2,X3),esk6_3(X1,X2,X3))
    | r2_hidden(esk4_3(X1,X2,X3),X3)
    | X3 = k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( esk6_3(X1,k1_tarski(X2),X3) = X2
    | X3 = k2_zfmisc_1(X1,k1_tarski(X2))
    | r2_hidden(esk4_3(X1,k1_tarski(X2),X3),X3) ),
    inference(spm,[status(thm)],[c_0_6,c_0_7])).

cnf(c_0_10,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),X1)
    | r2_hidden(esk4_3(X1,X2,X3),X3)
    | X3 = k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_11,plain,
    ( k4_tarski(esk5_3(X1,X2,k1_tarski(X3)),esk6_3(X1,X2,k1_tarski(X3))) = esk4_3(X1,X2,k1_tarski(X3))
    | esk4_3(X1,X2,k1_tarski(X3)) = X3
    | k1_tarski(X3) = k2_zfmisc_1(X1,X2) ),
    inference(spm,[status(thm)],[c_0_6,c_0_8])).

cnf(c_0_12,plain,
    ( esk6_3(X1,k1_tarski(X2),k1_tarski(X3)) = X2
    | esk4_3(X1,k1_tarski(X2),k1_tarski(X3)) = X3
    | k1_tarski(X3) = k2_zfmisc_1(X1,k1_tarski(X2)) ),
    inference(spm,[status(thm)],[c_0_6,c_0_9])).

cnf(c_0_13,plain,
    ( esk5_3(k1_tarski(X1),X2,X3) = X1
    | X3 = k2_zfmisc_1(k1_tarski(X1),X2)
    | r2_hidden(esk4_3(k1_tarski(X1),X2,X3),X3) ),
    inference(spm,[status(thm)],[c_0_6,c_0_10])).

cnf(c_0_14,plain,
    ( k4_tarski(esk5_3(X1,k1_tarski(X2),k1_tarski(X3)),X2) = esk4_3(X1,k1_tarski(X2),k1_tarski(X3))
    | esk4_3(X1,k1_tarski(X2),k1_tarski(X3)) = X3
    | k1_tarski(X3) = k2_zfmisc_1(X1,k1_tarski(X2)) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_15,plain,
    ( esk5_3(k1_tarski(X1),X2,k1_tarski(X3)) = X1
    | esk4_3(k1_tarski(X1),X2,k1_tarski(X3)) = X3
    | k1_tarski(X3) = k2_zfmisc_1(k1_tarski(X1),X2) ),
    inference(spm,[status(thm)],[c_0_6,c_0_13])).

cnf(c_0_16,plain,
    ( esk4_3(k1_tarski(X1),k1_tarski(X2),k1_tarski(X3)) = k4_tarski(X1,X2)
    | esk4_3(k1_tarski(X1),k1_tarski(X2),k1_tarski(X3)) = X3
    | k1_tarski(X3) = k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1,X2] : k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k4_tarski(X1,X2)) ),
    inference(assume_negation,[status(cth)],[t35_zfmisc_1])).

cnf(c_0_19,plain,
    ( X3 = k2_zfmisc_1(X1,X2)
    | ~ r2_hidden(esk4_3(X1,X2,X3),X3)
    | ~ r2_hidden(X4,X1)
    | ~ r2_hidden(X5,X2)
    | esk4_3(X1,X2,X3) != k4_tarski(X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_20,plain,
    ( esk4_3(k1_tarski(X1),k1_tarski(X2),k1_tarski(k4_tarski(X1,X2))) = k4_tarski(X1,X2)
    | k1_tarski(k4_tarski(X1,X2)) = k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2)) ),
    inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_16])])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,k1_tarski(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_17])])).

fof(c_0_22,negated_conjecture,(
    k2_zfmisc_1(k1_tarski(esk7_0),k1_tarski(esk8_0)) != k1_tarski(k4_tarski(esk7_0,esk8_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

cnf(c_0_23,plain,
    ( k1_tarski(k4_tarski(X1,X2)) = k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2))
    | k4_tarski(X1,X2) != k4_tarski(X3,X4)
    | ~ r2_hidden(X4,k1_tarski(X2))
    | ~ r2_hidden(X3,k1_tarski(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])])).

cnf(c_0_24,negated_conjecture,
    ( k2_zfmisc_1(k1_tarski(esk7_0),k1_tarski(esk8_0)) != k1_tarski(k4_tarski(esk7_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_25,plain,
    ( k1_tarski(k4_tarski(X1,X2)) = k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_23]),c_0_21]),c_0_21])])).

cnf(c_0_26,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25])]),
    [proof]).

%------------------------------------------------------------------------------

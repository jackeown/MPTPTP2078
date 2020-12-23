%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:39:28 EST 2020

% Result     : Theorem 4.12s
% Output     : CNFRefutation 4.12s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 485 expanded)
%              Number of clauses        :   41 ( 185 expanded)
%              Number of leaves         :   10 ( 148 expanded)
%              Depth                    :   11
%              Number of atoms          :  168 ( 866 expanded)
%              Number of equality atoms :  104 ( 683 expanded)
%              Maximal formula depth    :   23 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t35_zfmisc_1,conjecture,(
    ! [X1,X2] : k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k4_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

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

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2] : k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k4_tarski(X1,X2)) ),
    inference(assume_negation,[status(cth)],[t35_zfmisc_1])).

fof(c_0_11,negated_conjecture,(
    k2_zfmisc_1(k1_tarski(esk7_0),k1_tarski(esk8_0)) != k1_tarski(k4_tarski(esk7_0,esk8_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

fof(c_0_12,plain,(
    ! [X17] : k2_tarski(X17,X17) = k1_tarski(X17) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_13,plain,(
    ! [X18,X19] : k1_enumset1(X18,X18,X19) = k2_tarski(X18,X19) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_14,plain,(
    ! [X20,X21,X22] : k2_enumset1(X20,X20,X21,X22) = k1_enumset1(X20,X21,X22) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_15,plain,(
    ! [X23,X24,X25,X26] : k3_enumset1(X23,X23,X24,X25,X26) = k2_enumset1(X23,X24,X25,X26) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_16,plain,(
    ! [X27,X28,X29,X30,X31] : k4_enumset1(X27,X27,X28,X29,X30,X31) = k3_enumset1(X27,X28,X29,X30,X31) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_17,plain,(
    ! [X32,X33,X34,X35,X36,X37] : k5_enumset1(X32,X32,X33,X34,X35,X36,X37) = k4_enumset1(X32,X33,X34,X35,X36,X37) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_18,plain,(
    ! [X38,X39,X40,X41,X42,X43,X44] : k6_enumset1(X38,X38,X39,X40,X41,X42,X43,X44) = k5_enumset1(X38,X39,X40,X41,X42,X43,X44) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_19,plain,(
    ! [X8,X9,X10,X11,X12,X13,X14,X15] :
      ( ( ~ r2_hidden(X11,X10)
        | X11 = X8
        | X11 = X9
        | X10 != k2_tarski(X8,X9) )
      & ( X12 != X8
        | r2_hidden(X12,X10)
        | X10 != k2_tarski(X8,X9) )
      & ( X12 != X9
        | r2_hidden(X12,X10)
        | X10 != k2_tarski(X8,X9) )
      & ( esk1_3(X13,X14,X15) != X13
        | ~ r2_hidden(esk1_3(X13,X14,X15),X15)
        | X15 = k2_tarski(X13,X14) )
      & ( esk1_3(X13,X14,X15) != X14
        | ~ r2_hidden(esk1_3(X13,X14,X15),X15)
        | X15 = k2_tarski(X13,X14) )
      & ( r2_hidden(esk1_3(X13,X14,X15),X15)
        | esk1_3(X13,X14,X15) = X13
        | esk1_3(X13,X14,X15) = X14
        | X15 = k2_tarski(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

cnf(c_0_20,negated_conjecture,
    ( k2_zfmisc_1(k1_tarski(esk7_0),k1_tarski(esk8_0)) != k1_tarski(k4_tarski(esk7_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_21,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X3)
    | esk1_3(X1,X2,X3) = X1
    | esk1_3(X1,X2,X3) = X2
    | X3 = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_29,plain,(
    ! [X45,X46,X47,X48,X51,X52,X53,X54,X55,X56,X58,X59] :
      ( ( r2_hidden(esk2_4(X45,X46,X47,X48),X45)
        | ~ r2_hidden(X48,X47)
        | X47 != k2_zfmisc_1(X45,X46) )
      & ( r2_hidden(esk3_4(X45,X46,X47,X48),X46)
        | ~ r2_hidden(X48,X47)
        | X47 != k2_zfmisc_1(X45,X46) )
      & ( X48 = k4_tarski(esk2_4(X45,X46,X47,X48),esk3_4(X45,X46,X47,X48))
        | ~ r2_hidden(X48,X47)
        | X47 != k2_zfmisc_1(X45,X46) )
      & ( ~ r2_hidden(X52,X45)
        | ~ r2_hidden(X53,X46)
        | X51 != k4_tarski(X52,X53)
        | r2_hidden(X51,X47)
        | X47 != k2_zfmisc_1(X45,X46) )
      & ( ~ r2_hidden(esk4_3(X54,X55,X56),X56)
        | ~ r2_hidden(X58,X54)
        | ~ r2_hidden(X59,X55)
        | esk4_3(X54,X55,X56) != k4_tarski(X58,X59)
        | X56 = k2_zfmisc_1(X54,X55) )
      & ( r2_hidden(esk5_3(X54,X55,X56),X54)
        | r2_hidden(esk4_3(X54,X55,X56),X56)
        | X56 = k2_zfmisc_1(X54,X55) )
      & ( r2_hidden(esk6_3(X54,X55,X56),X55)
        | r2_hidden(esk4_3(X54,X55,X56),X56)
        | X56 = k2_zfmisc_1(X54,X55) )
      & ( esk4_3(X54,X55,X56) = k4_tarski(esk5_3(X54,X55,X56),esk6_3(X54,X55,X56))
        | r2_hidden(esk4_3(X54,X55,X56),X56)
        | X56 = k2_zfmisc_1(X54,X55) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).

cnf(c_0_30,negated_conjecture,
    ( k2_zfmisc_1(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)) != k6_enumset1(k4_tarski(esk7_0,esk8_0),k4_tarski(esk7_0,esk8_0),k4_tarski(esk7_0,esk8_0),k4_tarski(esk7_0,esk8_0),k4_tarski(esk7_0,esk8_0),k4_tarski(esk7_0,esk8_0),k4_tarski(esk7_0,esk8_0),k4_tarski(esk7_0,esk8_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21]),c_0_21]),c_0_21]),c_0_22]),c_0_22]),c_0_22]),c_0_23]),c_0_23]),c_0_23]),c_0_24]),c_0_24]),c_0_24]),c_0_25]),c_0_25]),c_0_25]),c_0_26]),c_0_26]),c_0_26]),c_0_27]),c_0_27]),c_0_27])).

cnf(c_0_31,plain,
    ( esk1_3(X1,X2,X3) = X2
    | esk1_3(X1,X2,X3) = X1
    | X3 = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)
    | r2_hidden(esk1_3(X1,X2,X3),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26]),c_0_27])).

cnf(c_0_32,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_33,plain,
    ( r2_hidden(esk3_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( esk1_3(k4_tarski(esk7_0,esk8_0),k4_tarski(esk7_0,esk8_0),X1) = k4_tarski(esk7_0,esk8_0)
    | r2_hidden(esk1_3(k4_tarski(esk7_0,esk8_0),k4_tarski(esk7_0,esk8_0),X1),X1)
    | X1 != k2_zfmisc_1(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_36,plain,
    ( X1 = k4_tarski(esk2_4(X2,X3,X4,X1),esk3_4(X2,X3,X4,X1))
    | ~ r2_hidden(X1,X4)
    | X4 != k2_zfmisc_1(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,plain,
    ( X1 = X4
    | X1 = X3
    | X2 != k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26]),c_0_27])).

cnf(c_0_38,plain,
    ( r2_hidden(esk3_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X2)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( esk1_3(k4_tarski(esk7_0,esk8_0),k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0))) = k4_tarski(esk7_0,esk8_0)
    | r2_hidden(esk1_3(k4_tarski(esk7_0,esk8_0),k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0))),k2_zfmisc_1(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0))) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_40,plain,
    ( r2_hidden(esk2_4(X1,X2,X3,X4),X1)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_41,plain,
    ( r2_hidden(X5,X6)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4)
    | X5 != k4_tarski(X1,X3)
    | X6 != k2_zfmisc_1(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X4) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26]),c_0_27])).

cnf(c_0_43,plain,
    ( k4_tarski(esk2_4(X1,X2,k2_zfmisc_1(X1,X2),X3),esk3_4(X1,X2,k2_zfmisc_1(X1,X2),X3)) = X3
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_44,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2)) ),
    inference(er,[status(thm)],[c_0_37])).

cnf(c_0_45,negated_conjecture,
    ( esk1_3(k4_tarski(esk7_0,esk8_0),k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0))) = k4_tarski(esk7_0,esk8_0)
    | r2_hidden(esk3_4(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0),k2_zfmisc_1(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)),esk1_3(k4_tarski(esk7_0,esk8_0),k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)))),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_46,plain,
    ( r2_hidden(esk2_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X1)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
    | X1 != k4_tarski(X4,X5)
    | ~ r2_hidden(X5,X3)
    | ~ r2_hidden(X4,X2) ),
    inference(er,[status(thm)],[c_0_41])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,X2)
    | X2 != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3) ),
    inference(er,[status(thm)],[c_0_42])).

cnf(c_0_49,plain,
    ( k4_tarski(esk2_4(X1,X2,k2_zfmisc_1(X1,X2),esk1_3(X3,X4,k2_zfmisc_1(X1,X2))),esk3_4(X1,X2,k2_zfmisc_1(X1,X2),esk1_3(X3,X4,k2_zfmisc_1(X1,X2)))) = esk1_3(X3,X4,k2_zfmisc_1(X1,X2))
    | k2_zfmisc_1(X1,X2) = k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4)
    | esk1_3(X3,X4,k2_zfmisc_1(X1,X2)) = X4
    | esk1_3(X3,X4,k2_zfmisc_1(X1,X2)) = X3 ),
    inference(spm,[status(thm)],[c_0_43,c_0_31])).

cnf(c_0_50,negated_conjecture,
    ( esk3_4(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0),k2_zfmisc_1(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)),esk1_3(k4_tarski(esk7_0,esk8_0),k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)))) = esk8_0
    | esk1_3(k4_tarski(esk7_0,esk8_0),k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0))) = k4_tarski(esk7_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_51,negated_conjecture,
    ( esk1_3(k4_tarski(esk7_0,esk8_0),k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0))) = k4_tarski(esk7_0,esk8_0)
    | r2_hidden(esk2_4(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0),k2_zfmisc_1(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)),esk1_3(k4_tarski(esk7_0,esk8_0),k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)))),k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_39])).

cnf(c_0_52,plain,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    | ~ r2_hidden(X2,X4)
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_47])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
    inference(er,[status(thm)],[c_0_48])).

cnf(c_0_54,plain,
    ( X3 = k2_tarski(X1,X2)
    | esk1_3(X1,X2,X3) != X2
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_55,negated_conjecture,
    ( k4_tarski(esk2_4(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0),k2_zfmisc_1(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)),esk1_3(k4_tarski(esk7_0,esk8_0),k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)))),esk8_0) = esk1_3(k4_tarski(esk7_0,esk8_0),k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)))
    | esk1_3(k4_tarski(esk7_0,esk8_0),k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0))) = k4_tarski(esk7_0,esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_30])).

cnf(c_0_56,negated_conjecture,
    ( esk2_4(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0),k2_zfmisc_1(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)),esk1_3(k4_tarski(esk7_0,esk8_0),k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)))) = esk7_0
    | esk1_3(k4_tarski(esk7_0,esk8_0),k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0))) = k4_tarski(esk7_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_51])).

cnf(c_0_57,plain,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3),X4))
    | ~ r2_hidden(X2,X4) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_58,plain,
    ( X3 = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)
    | esk1_3(X1,X2,X3) != X2
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26]),c_0_27])).

cnf(c_0_59,negated_conjecture,
    ( esk1_3(k4_tarski(esk7_0,esk8_0),k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0))) = k4_tarski(esk7_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_60,plain,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X4))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_53])).

cnf(c_0_61,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60])]),c_0_30]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:26:16 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 4.12/4.30  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_S0a
% 4.12/4.30  # and selection function SelectNegativeLiterals.
% 4.12/4.30  #
% 4.12/4.30  # Preprocessing time       : 0.028 s
% 4.12/4.30  
% 4.12/4.30  # Proof found!
% 4.12/4.30  # SZS status Theorem
% 4.12/4.30  # SZS output start CNFRefutation
% 4.12/4.30  fof(t35_zfmisc_1, conjecture, ![X1, X2]:k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2))=k1_tarski(k4_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_zfmisc_1)).
% 4.12/4.30  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 4.12/4.30  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 4.12/4.30  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 4.12/4.30  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 4.12/4.30  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 4.12/4.30  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 4.12/4.30  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 4.12/4.30  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 4.12/4.30  fof(d2_zfmisc_1, axiom, ![X1, X2, X3]:(X3=k2_zfmisc_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5, X6]:((r2_hidden(X5,X1)&r2_hidden(X6,X2))&X4=k4_tarski(X5,X6)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 4.12/4.30  fof(c_0_10, negated_conjecture, ~(![X1, X2]:k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2))=k1_tarski(k4_tarski(X1,X2))), inference(assume_negation,[status(cth)],[t35_zfmisc_1])).
% 4.12/4.30  fof(c_0_11, negated_conjecture, k2_zfmisc_1(k1_tarski(esk7_0),k1_tarski(esk8_0))!=k1_tarski(k4_tarski(esk7_0,esk8_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 4.12/4.30  fof(c_0_12, plain, ![X17]:k2_tarski(X17,X17)=k1_tarski(X17), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 4.12/4.30  fof(c_0_13, plain, ![X18, X19]:k1_enumset1(X18,X18,X19)=k2_tarski(X18,X19), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 4.12/4.30  fof(c_0_14, plain, ![X20, X21, X22]:k2_enumset1(X20,X20,X21,X22)=k1_enumset1(X20,X21,X22), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 4.12/4.30  fof(c_0_15, plain, ![X23, X24, X25, X26]:k3_enumset1(X23,X23,X24,X25,X26)=k2_enumset1(X23,X24,X25,X26), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 4.12/4.30  fof(c_0_16, plain, ![X27, X28, X29, X30, X31]:k4_enumset1(X27,X27,X28,X29,X30,X31)=k3_enumset1(X27,X28,X29,X30,X31), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 4.12/4.30  fof(c_0_17, plain, ![X32, X33, X34, X35, X36, X37]:k5_enumset1(X32,X32,X33,X34,X35,X36,X37)=k4_enumset1(X32,X33,X34,X35,X36,X37), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 4.12/4.30  fof(c_0_18, plain, ![X38, X39, X40, X41, X42, X43, X44]:k6_enumset1(X38,X38,X39,X40,X41,X42,X43,X44)=k5_enumset1(X38,X39,X40,X41,X42,X43,X44), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 4.12/4.30  fof(c_0_19, plain, ![X8, X9, X10, X11, X12, X13, X14, X15]:(((~r2_hidden(X11,X10)|(X11=X8|X11=X9)|X10!=k2_tarski(X8,X9))&((X12!=X8|r2_hidden(X12,X10)|X10!=k2_tarski(X8,X9))&(X12!=X9|r2_hidden(X12,X10)|X10!=k2_tarski(X8,X9))))&(((esk1_3(X13,X14,X15)!=X13|~r2_hidden(esk1_3(X13,X14,X15),X15)|X15=k2_tarski(X13,X14))&(esk1_3(X13,X14,X15)!=X14|~r2_hidden(esk1_3(X13,X14,X15),X15)|X15=k2_tarski(X13,X14)))&(r2_hidden(esk1_3(X13,X14,X15),X15)|(esk1_3(X13,X14,X15)=X13|esk1_3(X13,X14,X15)=X14)|X15=k2_tarski(X13,X14)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 4.12/4.30  cnf(c_0_20, negated_conjecture, (k2_zfmisc_1(k1_tarski(esk7_0),k1_tarski(esk8_0))!=k1_tarski(k4_tarski(esk7_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 4.12/4.30  cnf(c_0_21, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 4.12/4.30  cnf(c_0_22, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 4.12/4.30  cnf(c_0_23, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 4.12/4.30  cnf(c_0_24, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 4.12/4.30  cnf(c_0_25, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 4.12/4.30  cnf(c_0_26, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 4.12/4.30  cnf(c_0_27, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 4.12/4.30  cnf(c_0_28, plain, (r2_hidden(esk1_3(X1,X2,X3),X3)|esk1_3(X1,X2,X3)=X1|esk1_3(X1,X2,X3)=X2|X3=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 4.12/4.30  fof(c_0_29, plain, ![X45, X46, X47, X48, X51, X52, X53, X54, X55, X56, X58, X59]:(((((r2_hidden(esk2_4(X45,X46,X47,X48),X45)|~r2_hidden(X48,X47)|X47!=k2_zfmisc_1(X45,X46))&(r2_hidden(esk3_4(X45,X46,X47,X48),X46)|~r2_hidden(X48,X47)|X47!=k2_zfmisc_1(X45,X46)))&(X48=k4_tarski(esk2_4(X45,X46,X47,X48),esk3_4(X45,X46,X47,X48))|~r2_hidden(X48,X47)|X47!=k2_zfmisc_1(X45,X46)))&(~r2_hidden(X52,X45)|~r2_hidden(X53,X46)|X51!=k4_tarski(X52,X53)|r2_hidden(X51,X47)|X47!=k2_zfmisc_1(X45,X46)))&((~r2_hidden(esk4_3(X54,X55,X56),X56)|(~r2_hidden(X58,X54)|~r2_hidden(X59,X55)|esk4_3(X54,X55,X56)!=k4_tarski(X58,X59))|X56=k2_zfmisc_1(X54,X55))&(((r2_hidden(esk5_3(X54,X55,X56),X54)|r2_hidden(esk4_3(X54,X55,X56),X56)|X56=k2_zfmisc_1(X54,X55))&(r2_hidden(esk6_3(X54,X55,X56),X55)|r2_hidden(esk4_3(X54,X55,X56),X56)|X56=k2_zfmisc_1(X54,X55)))&(esk4_3(X54,X55,X56)=k4_tarski(esk5_3(X54,X55,X56),esk6_3(X54,X55,X56))|r2_hidden(esk4_3(X54,X55,X56),X56)|X56=k2_zfmisc_1(X54,X55))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).
% 4.12/4.30  cnf(c_0_30, negated_conjecture, (k2_zfmisc_1(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0))!=k6_enumset1(k4_tarski(esk7_0,esk8_0),k4_tarski(esk7_0,esk8_0),k4_tarski(esk7_0,esk8_0),k4_tarski(esk7_0,esk8_0),k4_tarski(esk7_0,esk8_0),k4_tarski(esk7_0,esk8_0),k4_tarski(esk7_0,esk8_0),k4_tarski(esk7_0,esk8_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_21]), c_0_21]), c_0_21]), c_0_22]), c_0_22]), c_0_22]), c_0_23]), c_0_23]), c_0_23]), c_0_24]), c_0_24]), c_0_24]), c_0_25]), c_0_25]), c_0_25]), c_0_26]), c_0_26]), c_0_26]), c_0_27]), c_0_27]), c_0_27])).
% 4.12/4.30  cnf(c_0_31, plain, (esk1_3(X1,X2,X3)=X2|esk1_3(X1,X2,X3)=X1|X3=k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)|r2_hidden(esk1_3(X1,X2,X3),X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_22]), c_0_23]), c_0_24]), c_0_25]), c_0_26]), c_0_27])).
% 4.12/4.30  cnf(c_0_32, plain, (X1=X3|X1=X4|~r2_hidden(X1,X2)|X2!=k2_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 4.12/4.30  cnf(c_0_33, plain, (r2_hidden(esk3_4(X1,X2,X3,X4),X2)|~r2_hidden(X4,X3)|X3!=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 4.12/4.30  cnf(c_0_34, negated_conjecture, (esk1_3(k4_tarski(esk7_0,esk8_0),k4_tarski(esk7_0,esk8_0),X1)=k4_tarski(esk7_0,esk8_0)|r2_hidden(esk1_3(k4_tarski(esk7_0,esk8_0),k4_tarski(esk7_0,esk8_0),X1),X1)|X1!=k2_zfmisc_1(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 4.12/4.30  cnf(c_0_35, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 4.12/4.30  cnf(c_0_36, plain, (X1=k4_tarski(esk2_4(X2,X3,X4,X1),esk3_4(X2,X3,X4,X1))|~r2_hidden(X1,X4)|X4!=k2_zfmisc_1(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 4.12/4.30  cnf(c_0_37, plain, (X1=X4|X1=X3|X2!=k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_22]), c_0_23]), c_0_24]), c_0_25]), c_0_26]), c_0_27])).
% 4.12/4.30  cnf(c_0_38, plain, (r2_hidden(esk3_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X2)|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(er,[status(thm)],[c_0_33])).
% 4.12/4.30  cnf(c_0_39, negated_conjecture, (esk1_3(k4_tarski(esk7_0,esk8_0),k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)))=k4_tarski(esk7_0,esk8_0)|r2_hidden(esk1_3(k4_tarski(esk7_0,esk8_0),k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0))),k2_zfmisc_1(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)))), inference(er,[status(thm)],[c_0_34])).
% 4.12/4.30  cnf(c_0_40, plain, (r2_hidden(esk2_4(X1,X2,X3,X4),X1)|~r2_hidden(X4,X3)|X3!=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 4.12/4.30  cnf(c_0_41, plain, (r2_hidden(X5,X6)|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)|X5!=k4_tarski(X1,X3)|X6!=k2_zfmisc_1(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 4.12/4.30  cnf(c_0_42, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X4)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_22]), c_0_23]), c_0_24]), c_0_25]), c_0_26]), c_0_27])).
% 4.12/4.30  cnf(c_0_43, plain, (k4_tarski(esk2_4(X1,X2,k2_zfmisc_1(X1,X2),X3),esk3_4(X1,X2,k2_zfmisc_1(X1,X2),X3))=X3|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(er,[status(thm)],[c_0_36])).
% 4.12/4.30  cnf(c_0_44, plain, (X1=X2|X1=X3|~r2_hidden(X1,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2))), inference(er,[status(thm)],[c_0_37])).
% 4.12/4.30  cnf(c_0_45, negated_conjecture, (esk1_3(k4_tarski(esk7_0,esk8_0),k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)))=k4_tarski(esk7_0,esk8_0)|r2_hidden(esk3_4(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0),k2_zfmisc_1(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)),esk1_3(k4_tarski(esk7_0,esk8_0),k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)))),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 4.12/4.30  cnf(c_0_46, plain, (r2_hidden(esk2_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X1)|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(er,[status(thm)],[c_0_40])).
% 4.12/4.30  cnf(c_0_47, plain, (r2_hidden(X1,k2_zfmisc_1(X2,X3))|X1!=k4_tarski(X4,X5)|~r2_hidden(X5,X3)|~r2_hidden(X4,X2)), inference(er,[status(thm)],[c_0_41])).
% 4.12/4.30  cnf(c_0_48, plain, (r2_hidden(X1,X2)|X2!=k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3)), inference(er,[status(thm)],[c_0_42])).
% 4.12/4.30  cnf(c_0_49, plain, (k4_tarski(esk2_4(X1,X2,k2_zfmisc_1(X1,X2),esk1_3(X3,X4,k2_zfmisc_1(X1,X2))),esk3_4(X1,X2,k2_zfmisc_1(X1,X2),esk1_3(X3,X4,k2_zfmisc_1(X1,X2))))=esk1_3(X3,X4,k2_zfmisc_1(X1,X2))|k2_zfmisc_1(X1,X2)=k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4)|esk1_3(X3,X4,k2_zfmisc_1(X1,X2))=X4|esk1_3(X3,X4,k2_zfmisc_1(X1,X2))=X3), inference(spm,[status(thm)],[c_0_43, c_0_31])).
% 4.12/4.30  cnf(c_0_50, negated_conjecture, (esk3_4(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0),k2_zfmisc_1(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)),esk1_3(k4_tarski(esk7_0,esk8_0),k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0))))=esk8_0|esk1_3(k4_tarski(esk7_0,esk8_0),k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)))=k4_tarski(esk7_0,esk8_0)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 4.12/4.30  cnf(c_0_51, negated_conjecture, (esk1_3(k4_tarski(esk7_0,esk8_0),k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)))=k4_tarski(esk7_0,esk8_0)|r2_hidden(esk2_4(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0),k2_zfmisc_1(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)),esk1_3(k4_tarski(esk7_0,esk8_0),k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)))),k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0))), inference(spm,[status(thm)],[c_0_46, c_0_39])).
% 4.12/4.30  cnf(c_0_52, plain, (r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))|~r2_hidden(X2,X4)|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_47])).
% 4.12/4.30  cnf(c_0_53, plain, (r2_hidden(X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))), inference(er,[status(thm)],[c_0_48])).
% 4.12/4.30  cnf(c_0_54, plain, (X3=k2_tarski(X1,X2)|esk1_3(X1,X2,X3)!=X2|~r2_hidden(esk1_3(X1,X2,X3),X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 4.12/4.30  cnf(c_0_55, negated_conjecture, (k4_tarski(esk2_4(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0),k2_zfmisc_1(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)),esk1_3(k4_tarski(esk7_0,esk8_0),k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)))),esk8_0)=esk1_3(k4_tarski(esk7_0,esk8_0),k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)))|esk1_3(k4_tarski(esk7_0,esk8_0),k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)))=k4_tarski(esk7_0,esk8_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_30])).
% 4.12/4.30  cnf(c_0_56, negated_conjecture, (esk2_4(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0),k2_zfmisc_1(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)),esk1_3(k4_tarski(esk7_0,esk8_0),k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0))))=esk7_0|esk1_3(k4_tarski(esk7_0,esk8_0),k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)))=k4_tarski(esk7_0,esk8_0)), inference(spm,[status(thm)],[c_0_44, c_0_51])).
% 4.12/4.30  cnf(c_0_57, plain, (r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3),X4))|~r2_hidden(X2,X4)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 4.12/4.30  cnf(c_0_58, plain, (X3=k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)|esk1_3(X1,X2,X3)!=X2|~r2_hidden(esk1_3(X1,X2,X3),X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_22]), c_0_23]), c_0_24]), c_0_25]), c_0_26]), c_0_27])).
% 4.12/4.30  cnf(c_0_59, negated_conjecture, (esk1_3(k4_tarski(esk7_0,esk8_0),k4_tarski(esk7_0,esk8_0),k2_zfmisc_1(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)))=k4_tarski(esk7_0,esk8_0)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 4.12/4.30  cnf(c_0_60, plain, (r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X4)))), inference(spm,[status(thm)],[c_0_57, c_0_53])).
% 4.12/4.30  cnf(c_0_61, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_60])]), c_0_30]), ['proof']).
% 4.12/4.30  # SZS output end CNFRefutation
% 4.12/4.30  # Proof object total steps             : 62
% 4.12/4.30  # Proof object clause steps            : 41
% 4.12/4.30  # Proof object formula steps           : 21
% 4.12/4.30  # Proof object conjectures             : 14
% 4.12/4.30  # Proof object clause conjectures      : 11
% 4.12/4.30  # Proof object formula conjectures     : 3
% 4.12/4.30  # Proof object initial clauses used    : 16
% 4.12/4.30  # Proof object initial formulas used   : 10
% 4.12/4.30  # Proof object generating inferences   : 19
% 4.12/4.30  # Proof object simplifying inferences  : 50
% 4.12/4.30  # Training examples: 0 positive, 0 negative
% 4.12/4.30  # Parsed axioms                        : 10
% 4.12/4.30  # Removed by relevancy pruning/SinE    : 0
% 4.12/4.30  # Initial clauses                      : 22
% 4.12/4.30  # Removed in clause preprocessing      : 7
% 4.12/4.30  # Initial clauses in saturation        : 15
% 4.12/4.30  # Processed clauses                    : 2654
% 4.12/4.30  # ...of these trivial                  : 12
% 4.12/4.30  # ...subsumed                          : 1268
% 4.12/4.30  # ...remaining for further processing  : 1374
% 4.12/4.30  # Other redundant clauses eliminated   : 2971
% 4.12/4.30  # Clauses deleted for lack of memory   : 0
% 4.12/4.30  # Backward-subsumed                    : 6
% 4.12/4.30  # Backward-rewritten                   : 232
% 4.12/4.30  # Generated clauses                    : 179932
% 4.12/4.30  # ...of the previous two non-trivial   : 176643
% 4.12/4.30  # Contextual simplify-reflections      : 2
% 4.12/4.30  # Paramodulations                      : 175722
% 4.12/4.30  # Factorizations                       : 42
% 4.12/4.30  # Equation resolutions                 : 4168
% 4.12/4.30  # Propositional unsat checks           : 0
% 4.12/4.30  #    Propositional check models        : 0
% 4.12/4.30  #    Propositional check unsatisfiable : 0
% 4.12/4.30  #    Propositional clauses             : 0
% 4.12/4.30  #    Propositional clauses after purity: 0
% 4.12/4.30  #    Propositional unsat core size     : 0
% 4.12/4.30  #    Propositional preprocessing time  : 0.000
% 4.12/4.30  #    Propositional encoding time       : 0.000
% 4.12/4.30  #    Propositional solver time         : 0.000
% 4.12/4.30  #    Success case prop preproc time    : 0.000
% 4.12/4.30  #    Success case prop encoding time   : 0.000
% 4.12/4.30  #    Success case prop solver time     : 0.000
% 4.12/4.30  # Current number of processed clauses  : 1134
% 4.12/4.30  #    Positive orientable unit clauses  : 7
% 4.12/4.30  #    Positive unorientable unit clauses: 0
% 4.12/4.30  #    Negative unit clauses             : 1
% 4.12/4.30  #    Non-unit-clauses                  : 1126
% 4.12/4.30  # Current number of unprocessed clauses: 173913
% 4.12/4.30  # ...number of literals in the above   : 1596719
% 4.12/4.30  # Current number of archived formulas  : 0
% 4.12/4.30  # Current number of archived clauses   : 245
% 4.12/4.30  # Clause-clause subsumption calls (NU) : 241459
% 4.12/4.30  # Rec. Clause-clause subsumption calls : 40132
% 4.12/4.30  # Non-unit clause-clause subsumptions  : 1276
% 4.12/4.30  # Unit Clause-clause subsumption calls : 496
% 4.12/4.30  # Rewrite failures with RHS unbound    : 0
% 4.12/4.30  # BW rewrite match attempts            : 24
% 4.12/4.30  # BW rewrite match successes           : 1
% 4.12/4.30  # Condensation attempts                : 0
% 4.12/4.30  # Condensation successes               : 0
% 4.12/4.30  # Termbank termtop insertions          : 10719631
% 4.12/4.31  
% 4.12/4.31  # -------------------------------------------------
% 4.12/4.31  # User time                : 3.885 s
% 4.12/4.31  # System time              : 0.084 s
% 4.12/4.31  # Total time               : 3.969 s
% 4.12/4.31  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------

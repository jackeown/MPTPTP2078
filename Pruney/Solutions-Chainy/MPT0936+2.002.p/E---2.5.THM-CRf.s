%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:37 EST 2020

% Result     : Theorem 0.60s
% Output     : CNFRefutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 208 expanded)
%              Number of clauses        :   41 ( 102 expanded)
%              Number of leaves         :    8 (  52 expanded)
%              Depth                    :   12
%              Number of atoms          :  159 ( 594 expanded)
%              Number of equality atoms :   95 ( 333 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(t28_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( k3_mcart_1(X1,X2,X3) = k3_mcart_1(X4,X5,X6)
     => ( X1 = X4
        & X2 = X5
        & X3 = X6 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_mcart_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(t97_mcart_1,conjecture,(
    ! [X1,X2,X3] : k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X1,X2,X3)))) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_mcart_1)).

fof(c_0_8,plain,(
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

fof(c_0_9,plain,(
    ! [X23] : k2_tarski(X23,X23) = k1_tarski(X23) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_10,plain,(
    ! [X24,X25] : k1_enumset1(X24,X24,X25) = k2_tarski(X24,X25) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_11,plain,(
    ! [X14,X15,X16,X17,X18,X19,X20,X21] :
      ( ( ~ r2_hidden(X17,X16)
        | X17 = X14
        | X17 = X15
        | X16 != k2_tarski(X14,X15) )
      & ( X18 != X14
        | r2_hidden(X18,X16)
        | X16 != k2_tarski(X14,X15) )
      & ( X18 != X15
        | r2_hidden(X18,X16)
        | X16 != k2_tarski(X14,X15) )
      & ( esk2_3(X19,X20,X21) != X19
        | ~ r2_hidden(esk2_3(X19,X20,X21),X21)
        | X21 = k2_tarski(X19,X20) )
      & ( esk2_3(X19,X20,X21) != X20
        | ~ r2_hidden(esk2_3(X19,X20,X21),X21)
        | X21 = k2_tarski(X19,X20) )
      & ( r2_hidden(esk2_3(X19,X20,X21),X21)
        | esk2_3(X19,X20,X21) = X19
        | esk2_3(X19,X20,X21) = X20
        | X21 = k2_tarski(X19,X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

cnf(c_0_12,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_15,plain,(
    ! [X26,X27,X28,X30,X31,X32,X33,X35] :
      ( ( ~ r2_hidden(X28,X27)
        | r2_hidden(k4_tarski(X28,esk3_3(X26,X27,X28)),X26)
        | X27 != k1_relat_1(X26) )
      & ( ~ r2_hidden(k4_tarski(X30,X31),X26)
        | r2_hidden(X30,X27)
        | X27 != k1_relat_1(X26) )
      & ( ~ r2_hidden(esk4_2(X32,X33),X33)
        | ~ r2_hidden(k4_tarski(esk4_2(X32,X33),X35),X32)
        | X33 = k1_relat_1(X32) )
      & ( r2_hidden(esk4_2(X32,X33),X33)
        | r2_hidden(k4_tarski(esk4_2(X32,X33),esk5_2(X32,X33)),X32)
        | X33 = k1_relat_1(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_17,plain,(
    ! [X40,X41,X42,X43,X44,X45] :
      ( ( X40 = X43
        | k3_mcart_1(X40,X41,X42) != k3_mcart_1(X43,X44,X45) )
      & ( X41 = X44
        | k3_mcart_1(X40,X41,X42) != k3_mcart_1(X43,X44,X45) )
      & ( X42 = X45
        | k3_mcart_1(X40,X41,X42) != k3_mcart_1(X43,X44,X45) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_mcart_1])])])).

fof(c_0_18,plain,(
    ! [X37,X38,X39] : k3_mcart_1(X37,X38,X39) = k4_tarski(k4_tarski(X37,X38),X39) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

cnf(c_0_19,plain,
    ( X1 = X3
    | X2 != k1_enumset1(X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_12,c_0_13]),c_0_14])).

cnf(c_0_20,plain,
    ( r2_hidden(k4_tarski(X1,esk3_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X2,X4) ),
    inference(rw,[status(thm)],[c_0_16,c_0_14])).

fof(c_0_23,negated_conjecture,(
    ~ ! [X1,X2,X3] : k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X1,X2,X3)))) = k1_tarski(X1) ),
    inference(assume_negation,[status(cth)],[t97_mcart_1])).

cnf(c_0_24,plain,
    ( X1 = X2
    | k3_mcart_1(X1,X3,X4) != k3_mcart_1(X2,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_enumset1(X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( r2_hidden(k4_tarski(X1,esk3_3(X2,k1_relat_1(X2),X1)),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,k1_enumset1(X1,X1,X2)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_22])])).

fof(c_0_30,negated_conjecture,(
    k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(esk6_0,esk7_0,esk8_0)))) != k1_tarski(esk6_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).

cnf(c_0_31,plain,
    ( X1 = X2
    | k4_tarski(k4_tarski(X1,X3),X4) != k4_tarski(k4_tarski(X2,X5),X6) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25]),c_0_25])).

cnf(c_0_32,plain,
    ( k4_tarski(X1,esk3_3(k1_enumset1(X2,X2,X2),k1_relat_1(k1_enumset1(X2,X2,X2)),X1)) = X2
    | ~ r2_hidden(X1,k1_relat_1(k1_enumset1(X2,X2,X2))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,k1_relat_1(k1_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),X3))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(esk6_0,esk7_0,esk8_0)))) != k1_tarski(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_35,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | esk1_2(X1,X2) = X1
    | X2 = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_36,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X1,X3),k1_relat_1(k1_enumset1(k4_tarski(k4_tarski(X2,X4),X5),k4_tarski(k4_tarski(X2,X4),X5),k4_tarski(k4_tarski(X2,X4),X5)))) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32])])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,k1_relat_1(k1_relat_1(k1_enumset1(k4_tarski(k4_tarski(X1,X2),X3),k4_tarski(k4_tarski(X1,X2),X3),X4)))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( k1_relat_1(k1_relat_1(k1_enumset1(k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0)))) != k1_enumset1(esk6_0,esk6_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_13]),c_0_13]),c_0_14]),c_0_14]),c_0_25]),c_0_25]),c_0_25])).

cnf(c_0_39,plain,
    ( esk1_2(X1,X2) = X1
    | X2 = k1_enumset1(X1,X1,X1)
    | r2_hidden(esk1_2(X1,X2),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_13]),c_0_14])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_41,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X1,X3),k1_relat_1(k1_enumset1(X4,X4,X4)))
    | ~ r2_hidden(k4_tarski(X2,X5),k1_relat_1(k1_enumset1(X4,X4,X4))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_32])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,k1_relat_1(k1_relat_1(k1_enumset1(X2,X2,X3))))
    | ~ r2_hidden(k4_tarski(X1,X4),k1_relat_1(k1_enumset1(X2,X2,X2))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_32])).

cnf(c_0_43,negated_conjecture,
    ( esk1_2(X1,k1_relat_1(k1_relat_1(k1_enumset1(k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0))))) = X1
    | r2_hidden(esk1_2(X1,k1_relat_1(k1_relat_1(k1_enumset1(k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0))))),k1_relat_1(k1_relat_1(k1_enumset1(k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0)))))
    | k1_enumset1(X1,X1,X1) != k1_enumset1(esk6_0,esk6_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X4,X2) ),
    inference(rw,[status(thm)],[c_0_40,c_0_14])).

cnf(c_0_45,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X2,X3),k1_relat_1(k1_enumset1(X4,X4,X4)))
    | ~ r2_hidden(X1,k1_relat_1(k1_relat_1(k1_enumset1(X4,X4,X4)))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_27])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,k1_relat_1(k1_relat_1(k1_enumset1(X2,X2,X3))))
    | ~ r2_hidden(X1,k1_relat_1(k1_relat_1(k1_enumset1(X2,X2,X2)))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_27])).

cnf(c_0_47,negated_conjecture,
    ( esk1_2(esk6_0,k1_relat_1(k1_relat_1(k1_enumset1(k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0))))) = esk6_0
    | r2_hidden(esk1_2(esk6_0,k1_relat_1(k1_relat_1(k1_enumset1(k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0))))),k1_relat_1(k1_relat_1(k1_enumset1(k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0))))) ),
    inference(er,[status(thm)],[c_0_43])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,k1_enumset1(X2,X2,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_44])])).

cnf(c_0_49,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_relat_1(k1_relat_1(k1_enumset1(X3,X3,X3))))
    | ~ r2_hidden(X2,k1_relat_1(k1_relat_1(k1_enumset1(X3,X3,X3)))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_27])).

cnf(c_0_50,negated_conjecture,
    ( esk1_2(esk6_0,k1_relat_1(k1_relat_1(k1_enumset1(k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0))))) = esk6_0
    | r2_hidden(esk1_2(esk6_0,k1_relat_1(k1_relat_1(k1_enumset1(k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0))))),k1_relat_1(k1_relat_1(k1_enumset1(k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0),X1)))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,k1_relat_1(k1_enumset1(X2,X2,k4_tarski(X1,X3)))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_48])).

cnf(c_0_52,plain,
    ( X2 = k1_tarski(X1)
    | ~ r2_hidden(esk1_2(X1,X2),X2)
    | esk1_2(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_53,negated_conjecture,
    ( esk1_2(esk6_0,k1_relat_1(k1_relat_1(k1_enumset1(k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0))))) = esk6_0
    | esk1_2(esk6_0,k1_relat_1(k1_relat_1(k1_enumset1(k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0))))) = X1
    | ~ r2_hidden(X1,k1_relat_1(k1_relat_1(k1_enumset1(k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0))))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,k1_relat_1(k1_relat_1(k1_enumset1(X2,X2,k4_tarski(k4_tarski(X1,X3),X4))))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_51])).

cnf(c_0_55,plain,
    ( X2 = k1_enumset1(X1,X1,X1)
    | esk1_2(X1,X2) != X1
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_13]),c_0_14])).

cnf(c_0_56,negated_conjecture,
    ( esk1_2(esk6_0,k1_relat_1(k1_relat_1(k1_enumset1(k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0))))) = esk6_0 ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_57,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_37])]),c_0_38]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:03:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.60/0.79  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.60/0.79  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.60/0.79  #
% 0.60/0.79  # Preprocessing time       : 0.028 s
% 0.60/0.79  # Presaturation interreduction done
% 0.60/0.79  
% 0.60/0.79  # Proof found!
% 0.60/0.79  # SZS status Theorem
% 0.60/0.79  # SZS output start CNFRefutation
% 0.60/0.79  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.60/0.79  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.60/0.79  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.60/0.79  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 0.60/0.79  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 0.60/0.79  fof(t28_mcart_1, axiom, ![X1, X2, X3, X4, X5, X6]:(k3_mcart_1(X1,X2,X3)=k3_mcart_1(X4,X5,X6)=>((X1=X4&X2=X5)&X3=X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_mcart_1)).
% 0.60/0.79  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 0.60/0.79  fof(t97_mcart_1, conjecture, ![X1, X2, X3]:k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X1,X2,X3))))=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_mcart_1)).
% 0.60/0.79  fof(c_0_8, plain, ![X7, X8, X9, X10, X11, X12]:(((~r2_hidden(X9,X8)|X9=X7|X8!=k1_tarski(X7))&(X10!=X7|r2_hidden(X10,X8)|X8!=k1_tarski(X7)))&((~r2_hidden(esk1_2(X11,X12),X12)|esk1_2(X11,X12)!=X11|X12=k1_tarski(X11))&(r2_hidden(esk1_2(X11,X12),X12)|esk1_2(X11,X12)=X11|X12=k1_tarski(X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.60/0.79  fof(c_0_9, plain, ![X23]:k2_tarski(X23,X23)=k1_tarski(X23), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.60/0.79  fof(c_0_10, plain, ![X24, X25]:k1_enumset1(X24,X24,X25)=k2_tarski(X24,X25), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.60/0.79  fof(c_0_11, plain, ![X14, X15, X16, X17, X18, X19, X20, X21]:(((~r2_hidden(X17,X16)|(X17=X14|X17=X15)|X16!=k2_tarski(X14,X15))&((X18!=X14|r2_hidden(X18,X16)|X16!=k2_tarski(X14,X15))&(X18!=X15|r2_hidden(X18,X16)|X16!=k2_tarski(X14,X15))))&(((esk2_3(X19,X20,X21)!=X19|~r2_hidden(esk2_3(X19,X20,X21),X21)|X21=k2_tarski(X19,X20))&(esk2_3(X19,X20,X21)!=X20|~r2_hidden(esk2_3(X19,X20,X21),X21)|X21=k2_tarski(X19,X20)))&(r2_hidden(esk2_3(X19,X20,X21),X21)|(esk2_3(X19,X20,X21)=X19|esk2_3(X19,X20,X21)=X20)|X21=k2_tarski(X19,X20)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.60/0.79  cnf(c_0_12, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.60/0.79  cnf(c_0_13, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.60/0.79  cnf(c_0_14, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.60/0.79  fof(c_0_15, plain, ![X26, X27, X28, X30, X31, X32, X33, X35]:(((~r2_hidden(X28,X27)|r2_hidden(k4_tarski(X28,esk3_3(X26,X27,X28)),X26)|X27!=k1_relat_1(X26))&(~r2_hidden(k4_tarski(X30,X31),X26)|r2_hidden(X30,X27)|X27!=k1_relat_1(X26)))&((~r2_hidden(esk4_2(X32,X33),X33)|~r2_hidden(k4_tarski(esk4_2(X32,X33),X35),X32)|X33=k1_relat_1(X32))&(r2_hidden(esk4_2(X32,X33),X33)|r2_hidden(k4_tarski(esk4_2(X32,X33),esk5_2(X32,X33)),X32)|X33=k1_relat_1(X32)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 0.60/0.79  cnf(c_0_16, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.60/0.79  fof(c_0_17, plain, ![X40, X41, X42, X43, X44, X45]:(((X40=X43|k3_mcart_1(X40,X41,X42)!=k3_mcart_1(X43,X44,X45))&(X41=X44|k3_mcart_1(X40,X41,X42)!=k3_mcart_1(X43,X44,X45)))&(X42=X45|k3_mcart_1(X40,X41,X42)!=k3_mcart_1(X43,X44,X45))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_mcart_1])])])).
% 0.60/0.79  fof(c_0_18, plain, ![X37, X38, X39]:k3_mcart_1(X37,X38,X39)=k4_tarski(k4_tarski(X37,X38),X39), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 0.60/0.79  cnf(c_0_19, plain, (X1=X3|X2!=k1_enumset1(X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_12, c_0_13]), c_0_14])).
% 0.60/0.79  cnf(c_0_20, plain, (r2_hidden(k4_tarski(X1,esk3_3(X3,X2,X1)),X3)|~r2_hidden(X1,X2)|X2!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.60/0.79  cnf(c_0_21, plain, (r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.60/0.79  cnf(c_0_22, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X2,X4)), inference(rw,[status(thm)],[c_0_16, c_0_14])).
% 0.60/0.79  fof(c_0_23, negated_conjecture, ~(![X1, X2, X3]:k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X1,X2,X3))))=k1_tarski(X1)), inference(assume_negation,[status(cth)],[t97_mcart_1])).
% 0.60/0.79  cnf(c_0_24, plain, (X1=X2|k3_mcart_1(X1,X3,X4)!=k3_mcart_1(X2,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.60/0.79  cnf(c_0_25, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.60/0.79  cnf(c_0_26, plain, (X1=X2|~r2_hidden(X1,k1_enumset1(X2,X2,X2))), inference(er,[status(thm)],[c_0_19])).
% 0.60/0.79  cnf(c_0_27, plain, (r2_hidden(k4_tarski(X1,esk3_3(X2,k1_relat_1(X2),X1)),X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(er,[status(thm)],[c_0_20])).
% 0.60/0.79  cnf(c_0_28, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)), inference(er,[status(thm)],[c_0_21])).
% 0.60/0.79  cnf(c_0_29, plain, (r2_hidden(X1,k1_enumset1(X1,X1,X2))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_22])])).
% 0.60/0.79  fof(c_0_30, negated_conjecture, k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(esk6_0,esk7_0,esk8_0))))!=k1_tarski(esk6_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).
% 0.60/0.79  cnf(c_0_31, plain, (X1=X2|k4_tarski(k4_tarski(X1,X3),X4)!=k4_tarski(k4_tarski(X2,X5),X6)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_25]), c_0_25])).
% 0.60/0.79  cnf(c_0_32, plain, (k4_tarski(X1,esk3_3(k1_enumset1(X2,X2,X2),k1_relat_1(k1_enumset1(X2,X2,X2)),X1))=X2|~r2_hidden(X1,k1_relat_1(k1_enumset1(X2,X2,X2)))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.60/0.79  cnf(c_0_33, plain, (r2_hidden(X1,k1_relat_1(k1_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),X3)))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.60/0.79  cnf(c_0_34, negated_conjecture, (k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(esk6_0,esk7_0,esk8_0))))!=k1_tarski(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.60/0.79  cnf(c_0_35, plain, (r2_hidden(esk1_2(X1,X2),X2)|esk1_2(X1,X2)=X1|X2=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.60/0.79  cnf(c_0_36, plain, (X1=X2|~r2_hidden(k4_tarski(X1,X3),k1_relat_1(k1_enumset1(k4_tarski(k4_tarski(X2,X4),X5),k4_tarski(k4_tarski(X2,X4),X5),k4_tarski(k4_tarski(X2,X4),X5))))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32])])).
% 0.60/0.79  cnf(c_0_37, plain, (r2_hidden(X1,k1_relat_1(k1_relat_1(k1_enumset1(k4_tarski(k4_tarski(X1,X2),X3),k4_tarski(k4_tarski(X1,X2),X3),X4))))), inference(spm,[status(thm)],[c_0_28, c_0_33])).
% 0.60/0.79  cnf(c_0_38, negated_conjecture, (k1_relat_1(k1_relat_1(k1_enumset1(k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0))))!=k1_enumset1(esk6_0,esk6_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_13]), c_0_13]), c_0_14]), c_0_14]), c_0_25]), c_0_25]), c_0_25])).
% 0.60/0.79  cnf(c_0_39, plain, (esk1_2(X1,X2)=X1|X2=k1_enumset1(X1,X1,X1)|r2_hidden(esk1_2(X1,X2),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_13]), c_0_14])).
% 0.60/0.79  cnf(c_0_40, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.60/0.79  cnf(c_0_41, plain, (X1=X2|~r2_hidden(k4_tarski(X1,X3),k1_relat_1(k1_enumset1(X4,X4,X4)))|~r2_hidden(k4_tarski(X2,X5),k1_relat_1(k1_enumset1(X4,X4,X4)))), inference(spm,[status(thm)],[c_0_36, c_0_32])).
% 0.60/0.79  cnf(c_0_42, plain, (r2_hidden(X1,k1_relat_1(k1_relat_1(k1_enumset1(X2,X2,X3))))|~r2_hidden(k4_tarski(X1,X4),k1_relat_1(k1_enumset1(X2,X2,X2)))), inference(spm,[status(thm)],[c_0_37, c_0_32])).
% 0.60/0.79  cnf(c_0_43, negated_conjecture, (esk1_2(X1,k1_relat_1(k1_relat_1(k1_enumset1(k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0)))))=X1|r2_hidden(esk1_2(X1,k1_relat_1(k1_relat_1(k1_enumset1(k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0))))),k1_relat_1(k1_relat_1(k1_enumset1(k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0)))))|k1_enumset1(X1,X1,X1)!=k1_enumset1(esk6_0,esk6_0,esk6_0)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.60/0.79  cnf(c_0_44, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X4,X2)), inference(rw,[status(thm)],[c_0_40, c_0_14])).
% 0.60/0.79  cnf(c_0_45, plain, (X1=X2|~r2_hidden(k4_tarski(X2,X3),k1_relat_1(k1_enumset1(X4,X4,X4)))|~r2_hidden(X1,k1_relat_1(k1_relat_1(k1_enumset1(X4,X4,X4))))), inference(spm,[status(thm)],[c_0_41, c_0_27])).
% 0.60/0.79  cnf(c_0_46, plain, (r2_hidden(X1,k1_relat_1(k1_relat_1(k1_enumset1(X2,X2,X3))))|~r2_hidden(X1,k1_relat_1(k1_relat_1(k1_enumset1(X2,X2,X2))))), inference(spm,[status(thm)],[c_0_42, c_0_27])).
% 0.60/0.79  cnf(c_0_47, negated_conjecture, (esk1_2(esk6_0,k1_relat_1(k1_relat_1(k1_enumset1(k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0)))))=esk6_0|r2_hidden(esk1_2(esk6_0,k1_relat_1(k1_relat_1(k1_enumset1(k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0))))),k1_relat_1(k1_relat_1(k1_enumset1(k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0)))))), inference(er,[status(thm)],[c_0_43])).
% 0.60/0.79  cnf(c_0_48, plain, (r2_hidden(X1,k1_enumset1(X2,X2,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_44])])).
% 0.60/0.79  cnf(c_0_49, plain, (X1=X2|~r2_hidden(X1,k1_relat_1(k1_relat_1(k1_enumset1(X3,X3,X3))))|~r2_hidden(X2,k1_relat_1(k1_relat_1(k1_enumset1(X3,X3,X3))))), inference(spm,[status(thm)],[c_0_45, c_0_27])).
% 0.60/0.79  cnf(c_0_50, negated_conjecture, (esk1_2(esk6_0,k1_relat_1(k1_relat_1(k1_enumset1(k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0)))))=esk6_0|r2_hidden(esk1_2(esk6_0,k1_relat_1(k1_relat_1(k1_enumset1(k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0))))),k1_relat_1(k1_relat_1(k1_enumset1(k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0),X1))))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.60/0.79  cnf(c_0_51, plain, (r2_hidden(X1,k1_relat_1(k1_enumset1(X2,X2,k4_tarski(X1,X3))))), inference(spm,[status(thm)],[c_0_28, c_0_48])).
% 0.60/0.79  cnf(c_0_52, plain, (X2=k1_tarski(X1)|~r2_hidden(esk1_2(X1,X2),X2)|esk1_2(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.60/0.79  cnf(c_0_53, negated_conjecture, (esk1_2(esk6_0,k1_relat_1(k1_relat_1(k1_enumset1(k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0)))))=esk6_0|esk1_2(esk6_0,k1_relat_1(k1_relat_1(k1_enumset1(k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0)))))=X1|~r2_hidden(X1,k1_relat_1(k1_relat_1(k1_enumset1(k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0)))))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.60/0.79  cnf(c_0_54, plain, (r2_hidden(X1,k1_relat_1(k1_relat_1(k1_enumset1(X2,X2,k4_tarski(k4_tarski(X1,X3),X4)))))), inference(spm,[status(thm)],[c_0_28, c_0_51])).
% 0.60/0.79  cnf(c_0_55, plain, (X2=k1_enumset1(X1,X1,X1)|esk1_2(X1,X2)!=X1|~r2_hidden(esk1_2(X1,X2),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_13]), c_0_14])).
% 0.60/0.79  cnf(c_0_56, negated_conjecture, (esk1_2(esk6_0,k1_relat_1(k1_relat_1(k1_enumset1(k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0)))))=esk6_0), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.60/0.79  cnf(c_0_57, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_37])]), c_0_38]), ['proof']).
% 0.60/0.79  # SZS output end CNFRefutation
% 0.60/0.79  # Proof object total steps             : 58
% 0.60/0.79  # Proof object clause steps            : 41
% 0.60/0.79  # Proof object formula steps           : 17
% 0.60/0.79  # Proof object conjectures             : 11
% 0.60/0.79  # Proof object clause conjectures      : 8
% 0.60/0.79  # Proof object formula conjectures     : 3
% 0.60/0.79  # Proof object initial clauses used    : 12
% 0.60/0.79  # Proof object initial formulas used   : 8
% 0.60/0.79  # Proof object generating inferences   : 17
% 0.60/0.79  # Proof object simplifying inferences  : 28
% 0.60/0.79  # Training examples: 0 positive, 0 negative
% 0.60/0.79  # Parsed axioms                        : 8
% 0.60/0.79  # Removed by relevancy pruning/SinE    : 0
% 0.60/0.79  # Initial clauses                      : 21
% 0.60/0.79  # Removed in clause preprocessing      : 3
% 0.60/0.79  # Initial clauses in saturation        : 18
% 0.60/0.79  # Processed clauses                    : 300
% 0.60/0.79  # ...of these trivial                  : 0
% 0.60/0.79  # ...subsumed                          : 77
% 0.60/0.79  # ...remaining for further processing  : 223
% 0.60/0.79  # Other redundant clauses eliminated   : 342
% 0.60/0.79  # Clauses deleted for lack of memory   : 0
% 0.60/0.79  # Backward-subsumed                    : 1
% 0.60/0.79  # Backward-rewritten                   : 3
% 0.60/0.79  # Generated clauses                    : 12573
% 0.60/0.79  # ...of the previous two non-trivial   : 12086
% 0.60/0.79  # Contextual simplify-reflections      : 0
% 0.60/0.79  # Paramodulations                      : 12212
% 0.60/0.79  # Factorizations                       : 14
% 0.60/0.79  # Equation resolutions                 : 350
% 0.60/0.79  # Propositional unsat checks           : 0
% 0.60/0.79  #    Propositional check models        : 0
% 0.60/0.79  #    Propositional check unsatisfiable : 0
% 0.60/0.79  #    Propositional clauses             : 0
% 0.60/0.79  #    Propositional clauses after purity: 0
% 0.60/0.79  #    Propositional unsat core size     : 0
% 0.60/0.79  #    Propositional preprocessing time  : 0.000
% 0.60/0.79  #    Propositional encoding time       : 0.000
% 0.60/0.79  #    Propositional solver time         : 0.000
% 0.60/0.79  #    Success case prop preproc time    : 0.000
% 0.60/0.79  #    Success case prop encoding time   : 0.000
% 0.60/0.79  #    Success case prop solver time     : 0.000
% 0.60/0.79  # Current number of processed clauses  : 195
% 0.60/0.79  #    Positive orientable unit clauses  : 9
% 0.60/0.79  #    Positive unorientable unit clauses: 0
% 0.60/0.79  #    Negative unit clauses             : 1
% 0.60/0.79  #    Non-unit-clauses                  : 185
% 0.60/0.79  # Current number of unprocessed clauses: 11820
% 0.60/0.79  # ...number of literals in the above   : 75388
% 0.60/0.79  # Current number of archived formulas  : 0
% 0.60/0.79  # Current number of archived clauses   : 24
% 0.60/0.79  # Clause-clause subsumption calls (NU) : 5750
% 0.60/0.79  # Rec. Clause-clause subsumption calls : 2340
% 0.60/0.79  # Non-unit clause-clause subsumptions  : 78
% 0.60/0.79  # Unit Clause-clause subsumption calls : 57
% 0.60/0.79  # Rewrite failures with RHS unbound    : 0
% 0.60/0.79  # BW rewrite match attempts            : 23
% 0.60/0.79  # BW rewrite match successes           : 1
% 0.60/0.79  # Condensation attempts                : 0
% 0.60/0.79  # Condensation successes               : 0
% 0.60/0.79  # Termbank termtop insertions          : 732882
% 0.60/0.79  
% 0.60/0.79  # -------------------------------------------------
% 0.60/0.79  # User time                : 0.438 s
% 0.60/0.79  # System time              : 0.012 s
% 0.60/0.79  # Total time               : 0.450 s
% 0.60/0.79  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------

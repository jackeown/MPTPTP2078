%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : enumset1__t42_enumset1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:35:59 EDT 2019

% Result     : Theorem 0.63s
% Output     : CNFRefutation 0.63s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 106 expanded)
%              Number of clauses        :   31 (  49 expanded)
%              Number of leaves         :    6 (  26 expanded)
%              Depth                    :   11
%              Number of atoms          :  174 ( 526 expanded)
%              Number of equality atoms :  103 ( 319 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t42_enumset1,conjecture,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t42_enumset1.p',t42_enumset1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t42_enumset1.p',commutativity_k2_xboole_0)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t42_enumset1.p',d1_tarski)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t42_enumset1.p',d3_xboole_0)).

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t42_enumset1.p',d1_enumset1)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t42_enumset1.p',d2_tarski)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    inference(assume_negation,[status(cth)],[t42_enumset1])).

fof(c_0_7,negated_conjecture,(
    k1_enumset1(esk1_0,esk2_0,esk3_0) != k2_xboole_0(k1_tarski(esk1_0),k2_tarski(esk2_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_8,plain,(
    ! [X13,X14] : k2_xboole_0(X13,X14) = k2_xboole_0(X14,X13) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_9,plain,(
    ! [X26,X27,X28,X29,X30,X31] :
      ( ( ~ r2_hidden(X28,X27)
        | X28 = X26
        | X27 != k1_tarski(X26) )
      & ( X29 != X26
        | r2_hidden(X29,X27)
        | X27 != k1_tarski(X26) )
      & ( ~ r2_hidden(esk5_2(X30,X31),X31)
        | esk5_2(X30,X31) != X30
        | X31 = k1_tarski(X30) )
      & ( r2_hidden(esk5_2(X30,X31),X31)
        | esk5_2(X30,X31) = X30
        | X31 = k1_tarski(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_10,negated_conjecture,
    ( k1_enumset1(esk1_0,esk2_0,esk3_0) != k2_xboole_0(k1_tarski(esk1_0),k2_tarski(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_12,plain,(
    ! [X42,X43,X44,X45,X46,X47,X48,X49] :
      ( ( ~ r2_hidden(X45,X44)
        | r2_hidden(X45,X42)
        | r2_hidden(X45,X43)
        | X44 != k2_xboole_0(X42,X43) )
      & ( ~ r2_hidden(X46,X42)
        | r2_hidden(X46,X44)
        | X44 != k2_xboole_0(X42,X43) )
      & ( ~ r2_hidden(X46,X43)
        | r2_hidden(X46,X44)
        | X44 != k2_xboole_0(X42,X43) )
      & ( ~ r2_hidden(esk7_3(X47,X48,X49),X47)
        | ~ r2_hidden(esk7_3(X47,X48,X49),X49)
        | X49 = k2_xboole_0(X47,X48) )
      & ( ~ r2_hidden(esk7_3(X47,X48,X49),X48)
        | ~ r2_hidden(esk7_3(X47,X48,X49),X49)
        | X49 = k2_xboole_0(X47,X48) )
      & ( r2_hidden(esk7_3(X47,X48,X49),X49)
        | r2_hidden(esk7_3(X47,X48,X49),X47)
        | r2_hidden(esk7_3(X47,X48,X49),X48)
        | X49 = k2_xboole_0(X47,X48) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

cnf(c_0_13,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( k2_xboole_0(k2_tarski(esk2_0,esk3_0),k1_tarski(esk1_0)) != k1_enumset1(esk1_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_15,plain,
    ( r2_hidden(esk7_3(X1,X2,X3),X3)
    | r2_hidden(esk7_3(X1,X2,X3),X1)
    | r2_hidden(esk7_3(X1,X2,X3),X2)
    | X3 = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X15,X16,X17,X18,X19,X20,X21,X22,X23,X24] :
      ( ( ~ r2_hidden(X19,X18)
        | X19 = X15
        | X19 = X16
        | X19 = X17
        | X18 != k1_enumset1(X15,X16,X17) )
      & ( X20 != X15
        | r2_hidden(X20,X18)
        | X18 != k1_enumset1(X15,X16,X17) )
      & ( X20 != X16
        | r2_hidden(X20,X18)
        | X18 != k1_enumset1(X15,X16,X17) )
      & ( X20 != X17
        | r2_hidden(X20,X18)
        | X18 != k1_enumset1(X15,X16,X17) )
      & ( esk4_4(X21,X22,X23,X24) != X21
        | ~ r2_hidden(esk4_4(X21,X22,X23,X24),X24)
        | X24 = k1_enumset1(X21,X22,X23) )
      & ( esk4_4(X21,X22,X23,X24) != X22
        | ~ r2_hidden(esk4_4(X21,X22,X23,X24),X24)
        | X24 = k1_enumset1(X21,X22,X23) )
      & ( esk4_4(X21,X22,X23,X24) != X23
        | ~ r2_hidden(esk4_4(X21,X22,X23,X24),X24)
        | X24 = k1_enumset1(X21,X22,X23) )
      & ( r2_hidden(esk4_4(X21,X22,X23,X24),X24)
        | esk4_4(X21,X22,X23,X24) = X21
        | esk4_4(X21,X22,X23,X24) = X22
        | esk4_4(X21,X22,X23,X24) = X23
        | X24 = k1_enumset1(X21,X22,X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

cnf(c_0_17,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(esk7_3(k2_tarski(esk2_0,esk3_0),k1_tarski(esk1_0),k1_enumset1(esk1_0,esk2_0,esk3_0)),k1_enumset1(esk1_0,esk2_0,esk3_0))
    | r2_hidden(esk7_3(k2_tarski(esk2_0,esk3_0),k1_tarski(esk1_0),k1_enumset1(esk1_0,esk2_0,esk3_0)),k2_tarski(esk2_0,esk3_0))
    | r2_hidden(esk7_3(k2_tarski(esk2_0,esk3_0),k1_tarski(esk1_0),k1_enumset1(esk1_0,esk2_0,esk3_0)),k1_tarski(esk1_0)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15])])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_21,plain,(
    ! [X33,X34,X35,X36,X37,X38,X39,X40] :
      ( ( ~ r2_hidden(X36,X35)
        | X36 = X33
        | X36 = X34
        | X35 != k2_tarski(X33,X34) )
      & ( X37 != X33
        | r2_hidden(X37,X35)
        | X35 != k2_tarski(X33,X34) )
      & ( X37 != X34
        | r2_hidden(X37,X35)
        | X35 != k2_tarski(X33,X34) )
      & ( esk6_3(X38,X39,X40) != X38
        | ~ r2_hidden(esk6_3(X38,X39,X40),X40)
        | X40 = k2_tarski(X38,X39) )
      & ( esk6_3(X38,X39,X40) != X39
        | ~ r2_hidden(esk6_3(X38,X39,X40),X40)
        | X40 = k2_tarski(X38,X39) )
      & ( r2_hidden(esk6_3(X38,X39,X40),X40)
        | esk6_3(X38,X39,X40) = X38
        | esk6_3(X38,X39,X40) = X39
        | X40 = k2_tarski(X38,X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

cnf(c_0_22,plain,
    ( X1 = X3
    | X1 = X4
    | X1 = X5
    | ~ r2_hidden(X1,X2)
    | X2 != k1_enumset1(X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( X3 = k2_xboole_0(X1,X2)
    | ~ r2_hidden(esk7_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk7_3(X1,X2,X3),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_24,negated_conjecture,
    ( esk7_3(k2_tarski(esk2_0,esk3_0),k1_tarski(esk1_0),k1_enumset1(esk1_0,esk2_0,esk3_0)) = esk1_0
    | r2_hidden(esk7_3(k2_tarski(esk2_0,esk3_0),k1_tarski(esk1_0),k1_enumset1(esk1_0,esk2_0,esk3_0)),k1_enumset1(esk1_0,esk2_0,esk3_0))
    | r2_hidden(esk7_3(k2_tarski(esk2_0,esk3_0),k1_tarski(esk1_0),k1_enumset1(esk1_0,esk2_0,esk3_0)),k2_tarski(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,k1_enumset1(X1,X2,X3)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_19])])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,k1_tarski(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_20])])).

cnf(c_0_27,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( X1 = X2
    | X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,k1_enumset1(X4,X3,X2)) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk7_3(k2_tarski(esk2_0,esk3_0),k1_tarski(esk1_0),k1_enumset1(esk1_0,esk2_0,esk3_0)),k1_enumset1(esk1_0,esk2_0,esk3_0))
    | r2_hidden(esk7_3(k2_tarski(esk2_0,esk3_0),k1_tarski(esk1_0),k1_enumset1(esk1_0,esk2_0,esk3_0)),k2_tarski(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_26])]),c_0_14])).

cnf(c_0_30,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k2_tarski(X3,X2)) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,plain,
    ( X3 = k2_xboole_0(X1,X2)
    | ~ r2_hidden(esk7_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk7_3(X1,X2,X3),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_34,negated_conjecture,
    ( esk7_3(k2_tarski(esk2_0,esk3_0),k1_tarski(esk1_0),k1_enumset1(esk1_0,esk2_0,esk3_0)) = esk3_0
    | esk7_3(k2_tarski(esk2_0,esk3_0),k1_tarski(esk1_0),k1_enumset1(esk1_0,esk2_0,esk3_0)) = esk2_0
    | esk7_3(k2_tarski(esk2_0,esk3_0),k1_tarski(esk1_0),k1_enumset1(esk1_0,esk2_0,esk3_0)) = esk1_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,k1_enumset1(X2,X3,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_31])])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,k2_tarski(X2,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_32])])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X2,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_39,negated_conjecture,
    ( esk7_3(k2_tarski(esk2_0,esk3_0),k1_tarski(esk1_0),k1_enumset1(esk1_0,esk2_0,esk3_0)) = esk1_0
    | esk7_3(k2_tarski(esk2_0,esk3_0),k1_tarski(esk1_0),k1_enumset1(esk1_0,esk2_0,esk3_0)) = esk2_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_36])]),c_0_14])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,k1_enumset1(X2,X1,X3)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_37])])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,k2_tarski(X1,X2)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_38])])).

cnf(c_0_42,negated_conjecture,
    ( esk7_3(k2_tarski(esk2_0,esk3_0),k1_tarski(esk1_0),k1_enumset1(esk1_0,esk2_0,esk3_0)) = esk1_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_39]),c_0_40]),c_0_41])]),c_0_14])).

cnf(c_0_43,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_42]),c_0_25]),c_0_26])]),c_0_14]),
    [proof]).
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:37 EST 2020

% Result     : Theorem 0.90s
% Output     : CNFRefutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 162 expanded)
%              Number of clauses        :   31 (  68 expanded)
%              Number of leaves         :    8 (  46 expanded)
%              Depth                    :   10
%              Number of atoms          :  106 ( 310 expanded)
%              Number of equality atoms :   64 ( 215 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal clause size      :   12 (   2 average)
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

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(t97_mcart_1,conjecture,(
    ! [X1,X2,X3] : k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X1,X2,X3)))) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_mcart_1)).

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(c_0_8,plain,(
    ! [X5,X6,X7,X8,X9,X10] :
      ( ( ~ r2_hidden(X7,X6)
        | X7 = X5
        | X6 != k1_tarski(X5) )
      & ( X8 != X5
        | r2_hidden(X8,X6)
        | X6 != k1_tarski(X5) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | esk1_2(X9,X10) != X9
        | X10 = k1_tarski(X9) )
      & ( r2_hidden(esk1_2(X9,X10),X10)
        | esk1_2(X9,X10) = X9
        | X10 = k1_tarski(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_9,plain,(
    ! [X12] : k2_tarski(X12,X12) = k1_tarski(X12) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_10,plain,(
    ! [X13,X14] : k1_enumset1(X13,X13,X14) = k2_tarski(X13,X14) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_11,plain,(
    ! [X15,X16,X17] : k2_enumset1(X15,X15,X16,X17) = k1_enumset1(X15,X16,X17) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

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

cnf(c_0_15,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_16,plain,(
    ! [X18,X19,X20,X22,X23,X24,X25,X27] :
      ( ( ~ r2_hidden(X20,X19)
        | r2_hidden(k4_tarski(X20,esk2_3(X18,X19,X20)),X18)
        | X19 != k1_relat_1(X18) )
      & ( ~ r2_hidden(k4_tarski(X22,X23),X18)
        | r2_hidden(X22,X19)
        | X19 != k1_relat_1(X18) )
      & ( ~ r2_hidden(esk3_2(X24,X25),X25)
        | ~ r2_hidden(k4_tarski(esk3_2(X24,X25),X27),X24)
        | X25 = k1_relat_1(X24) )
      & ( r2_hidden(esk3_2(X24,X25),X25)
        | r2_hidden(k4_tarski(esk3_2(X24,X25),esk4_2(X24,X25)),X24)
        | X25 = k1_relat_1(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

cnf(c_0_17,plain,
    ( X1 = X3
    | X2 != k2_enumset1(X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_12,c_0_13]),c_0_14]),c_0_15])).

cnf(c_0_18,plain,
    ( r2_hidden(k4_tarski(X1,esk2_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1,X2,X3] : k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X1,X2,X3)))) = k1_tarski(X1) ),
    inference(assume_negation,[status(cth)],[t97_mcart_1])).

fof(c_0_20,plain,(
    ! [X32,X33] :
      ( k1_mcart_1(k4_tarski(X32,X33)) = X32
      & k2_mcart_1(k4_tarski(X32,X33)) = X33 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

cnf(c_0_21,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k2_enumset1(X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( r2_hidden(k4_tarski(X1,esk2_3(X2,k1_relat_1(X2),X1)),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_18])).

fof(c_0_23,negated_conjecture,(
    k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(esk5_0,esk6_0,esk7_0)))) != k1_tarski(esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

fof(c_0_24,plain,(
    ! [X29,X30,X31] : k3_mcart_1(X29,X30,X31) = k4_tarski(k4_tarski(X29,X30),X31) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

cnf(c_0_25,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( k4_tarski(X1,esk2_3(k2_enumset1(X2,X2,X2,X2),k1_relat_1(k2_enumset1(X2,X2,X2,X2)),X1)) = X2
    | ~ r2_hidden(X1,k1_relat_1(k2_enumset1(X2,X2,X2,X2))) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(esk5_0,esk6_0,esk7_0)))) != k1_tarski(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | esk1_2(X1,X2) = X1
    | X2 = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_31,plain,
    ( k1_mcart_1(X1) = X2
    | ~ r2_hidden(X2,k1_relat_1(k2_enumset1(X1,X1,X1,X1))) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( k1_relat_1(k1_relat_1(k2_enumset1(k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0),k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0),k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0),k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0)))) != k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_13]),c_0_13]),c_0_14]),c_0_14]),c_0_15]),c_0_15]),c_0_28]),c_0_28]),c_0_28]),c_0_28])).

cnf(c_0_33,plain,
    ( esk1_2(X1,X2) = X1
    | X2 = k2_enumset1(X1,X1,X1,X1)
    | r2_hidden(esk1_2(X1,X2),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_13]),c_0_14]),c_0_15])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X2,X2,X2,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_13]),c_0_14]),c_0_15])).

cnf(c_0_36,plain,
    ( k4_tarski(X1,esk2_3(k1_relat_1(k2_enumset1(X2,X2,X2,X2)),k1_relat_1(k1_relat_1(k2_enumset1(X2,X2,X2,X2))),X1)) = k1_mcart_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(k1_relat_1(k2_enumset1(X2,X2,X2,X2)))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_22])).

cnf(c_0_37,negated_conjecture,
    ( esk1_2(X1,k1_relat_1(k1_relat_1(k2_enumset1(k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0),k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0),k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0),k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0))))) = X1
    | r2_hidden(esk1_2(X1,k1_relat_1(k1_relat_1(k2_enumset1(k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0),k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0),k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0),k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0))))),k1_relat_1(k1_relat_1(k2_enumset1(k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0),k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0),k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0),k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0)))))
    | k2_enumset1(X1,X1,X1,X1) != k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,k2_enumset1(X1,X1,X1,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_35])])).

cnf(c_0_40,plain,
    ( X2 = k1_tarski(X1)
    | ~ r2_hidden(esk1_2(X1,X2),X2)
    | esk1_2(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_41,plain,
    ( k1_mcart_1(k1_mcart_1(X1)) = X2
    | ~ r2_hidden(X2,k1_relat_1(k1_relat_1(k2_enumset1(X1,X1,X1,X1)))) ),
    inference(spm,[status(thm)],[c_0_25,c_0_36])).

cnf(c_0_42,negated_conjecture,
    ( esk1_2(esk5_0,k1_relat_1(k1_relat_1(k2_enumset1(k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0),k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0),k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0),k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0))))) = esk5_0
    | r2_hidden(esk1_2(esk5_0,k1_relat_1(k1_relat_1(k2_enumset1(k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0),k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0),k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0),k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0))))),k1_relat_1(k1_relat_1(k2_enumset1(k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0),k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0),k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0),k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0))))) ),
    inference(er,[status(thm)],[c_0_37])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,k1_relat_1(k2_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_44,plain,
    ( X2 = k2_enumset1(X1,X1,X1,X1)
    | esk1_2(X1,X2) != X1
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_13]),c_0_14]),c_0_15])).

cnf(c_0_45,negated_conjecture,
    ( esk1_2(esk5_0,k1_relat_1(k1_relat_1(k2_enumset1(k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0),k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0),k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0),k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0))))) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_25]),c_0_25])])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,k1_relat_1(k1_relat_1(k2_enumset1(k4_tarski(k4_tarski(X1,X2),X3),k4_tarski(k4_tarski(X1,X2),X3),k4_tarski(k4_tarski(X1,X2),X3),k4_tarski(k4_tarski(X1,X2),X3))))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_43])).

cnf(c_0_47,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46])]),c_0_32]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:25:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.90/1.14  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.90/1.14  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.90/1.14  #
% 0.90/1.14  # Preprocessing time       : 0.042 s
% 0.90/1.14  # Presaturation interreduction done
% 0.90/1.14  
% 0.90/1.14  # Proof found!
% 0.90/1.14  # SZS status Theorem
% 0.90/1.14  # SZS output start CNFRefutation
% 0.90/1.14  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.90/1.14  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.90/1.14  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.90/1.14  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.90/1.14  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 0.90/1.14  fof(t97_mcart_1, conjecture, ![X1, X2, X3]:k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X1,X2,X3))))=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_mcart_1)).
% 0.90/1.14  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 0.90/1.14  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 0.90/1.14  fof(c_0_8, plain, ![X5, X6, X7, X8, X9, X10]:(((~r2_hidden(X7,X6)|X7=X5|X6!=k1_tarski(X5))&(X8!=X5|r2_hidden(X8,X6)|X6!=k1_tarski(X5)))&((~r2_hidden(esk1_2(X9,X10),X10)|esk1_2(X9,X10)!=X9|X10=k1_tarski(X9))&(r2_hidden(esk1_2(X9,X10),X10)|esk1_2(X9,X10)=X9|X10=k1_tarski(X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.90/1.14  fof(c_0_9, plain, ![X12]:k2_tarski(X12,X12)=k1_tarski(X12), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.90/1.14  fof(c_0_10, plain, ![X13, X14]:k1_enumset1(X13,X13,X14)=k2_tarski(X13,X14), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.90/1.14  fof(c_0_11, plain, ![X15, X16, X17]:k2_enumset1(X15,X15,X16,X17)=k1_enumset1(X15,X16,X17), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.90/1.14  cnf(c_0_12, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.90/1.14  cnf(c_0_13, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.90/1.14  cnf(c_0_14, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.90/1.14  cnf(c_0_15, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.90/1.14  fof(c_0_16, plain, ![X18, X19, X20, X22, X23, X24, X25, X27]:(((~r2_hidden(X20,X19)|r2_hidden(k4_tarski(X20,esk2_3(X18,X19,X20)),X18)|X19!=k1_relat_1(X18))&(~r2_hidden(k4_tarski(X22,X23),X18)|r2_hidden(X22,X19)|X19!=k1_relat_1(X18)))&((~r2_hidden(esk3_2(X24,X25),X25)|~r2_hidden(k4_tarski(esk3_2(X24,X25),X27),X24)|X25=k1_relat_1(X24))&(r2_hidden(esk3_2(X24,X25),X25)|r2_hidden(k4_tarski(esk3_2(X24,X25),esk4_2(X24,X25)),X24)|X25=k1_relat_1(X24)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 0.90/1.14  cnf(c_0_17, plain, (X1=X3|X2!=k2_enumset1(X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_12, c_0_13]), c_0_14]), c_0_15])).
% 0.90/1.14  cnf(c_0_18, plain, (r2_hidden(k4_tarski(X1,esk2_3(X3,X2,X1)),X3)|~r2_hidden(X1,X2)|X2!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.90/1.14  fof(c_0_19, negated_conjecture, ~(![X1, X2, X3]:k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X1,X2,X3))))=k1_tarski(X1)), inference(assume_negation,[status(cth)],[t97_mcart_1])).
% 0.90/1.14  fof(c_0_20, plain, ![X32, X33]:(k1_mcart_1(k4_tarski(X32,X33))=X32&k2_mcart_1(k4_tarski(X32,X33))=X33), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 0.90/1.14  cnf(c_0_21, plain, (X1=X2|~r2_hidden(X1,k2_enumset1(X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_17])).
% 0.90/1.14  cnf(c_0_22, plain, (r2_hidden(k4_tarski(X1,esk2_3(X2,k1_relat_1(X2),X1)),X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(er,[status(thm)],[c_0_18])).
% 0.90/1.14  fof(c_0_23, negated_conjecture, k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(esk5_0,esk6_0,esk7_0))))!=k1_tarski(esk5_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 0.90/1.14  fof(c_0_24, plain, ![X29, X30, X31]:k3_mcart_1(X29,X30,X31)=k4_tarski(k4_tarski(X29,X30),X31), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 0.90/1.14  cnf(c_0_25, plain, (k1_mcart_1(k4_tarski(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.90/1.14  cnf(c_0_26, plain, (k4_tarski(X1,esk2_3(k2_enumset1(X2,X2,X2,X2),k1_relat_1(k2_enumset1(X2,X2,X2,X2)),X1))=X2|~r2_hidden(X1,k1_relat_1(k2_enumset1(X2,X2,X2,X2)))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.90/1.14  cnf(c_0_27, negated_conjecture, (k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(esk5_0,esk6_0,esk7_0))))!=k1_tarski(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.90/1.14  cnf(c_0_28, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.90/1.14  cnf(c_0_29, plain, (r2_hidden(esk1_2(X1,X2),X2)|esk1_2(X1,X2)=X1|X2=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.90/1.14  cnf(c_0_30, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.90/1.14  cnf(c_0_31, plain, (k1_mcart_1(X1)=X2|~r2_hidden(X2,k1_relat_1(k2_enumset1(X1,X1,X1,X1)))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.90/1.14  cnf(c_0_32, negated_conjecture, (k1_relat_1(k1_relat_1(k2_enumset1(k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0),k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0),k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0),k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0))))!=k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_13]), c_0_13]), c_0_14]), c_0_14]), c_0_15]), c_0_15]), c_0_28]), c_0_28]), c_0_28]), c_0_28])).
% 0.90/1.14  cnf(c_0_33, plain, (esk1_2(X1,X2)=X1|X2=k2_enumset1(X1,X1,X1,X1)|r2_hidden(esk1_2(X1,X2),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_13]), c_0_14]), c_0_15])).
% 0.90/1.14  cnf(c_0_34, plain, (r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.90/1.14  cnf(c_0_35, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X2,X2,X2,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_13]), c_0_14]), c_0_15])).
% 0.90/1.14  cnf(c_0_36, plain, (k4_tarski(X1,esk2_3(k1_relat_1(k2_enumset1(X2,X2,X2,X2)),k1_relat_1(k1_relat_1(k2_enumset1(X2,X2,X2,X2))),X1))=k1_mcart_1(X2)|~r2_hidden(X1,k1_relat_1(k1_relat_1(k2_enumset1(X2,X2,X2,X2))))), inference(spm,[status(thm)],[c_0_31, c_0_22])).
% 0.90/1.14  cnf(c_0_37, negated_conjecture, (esk1_2(X1,k1_relat_1(k1_relat_1(k2_enumset1(k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0),k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0),k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0),k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0)))))=X1|r2_hidden(esk1_2(X1,k1_relat_1(k1_relat_1(k2_enumset1(k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0),k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0),k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0),k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0))))),k1_relat_1(k1_relat_1(k2_enumset1(k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0),k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0),k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0),k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0)))))|k2_enumset1(X1,X1,X1,X1)!=k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.90/1.14  cnf(c_0_38, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)), inference(er,[status(thm)],[c_0_34])).
% 0.90/1.14  cnf(c_0_39, plain, (r2_hidden(X1,k2_enumset1(X1,X1,X1,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_35])])).
% 0.90/1.14  cnf(c_0_40, plain, (X2=k1_tarski(X1)|~r2_hidden(esk1_2(X1,X2),X2)|esk1_2(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.90/1.14  cnf(c_0_41, plain, (k1_mcart_1(k1_mcart_1(X1))=X2|~r2_hidden(X2,k1_relat_1(k1_relat_1(k2_enumset1(X1,X1,X1,X1))))), inference(spm,[status(thm)],[c_0_25, c_0_36])).
% 0.90/1.14  cnf(c_0_42, negated_conjecture, (esk1_2(esk5_0,k1_relat_1(k1_relat_1(k2_enumset1(k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0),k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0),k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0),k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0)))))=esk5_0|r2_hidden(esk1_2(esk5_0,k1_relat_1(k1_relat_1(k2_enumset1(k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0),k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0),k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0),k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0))))),k1_relat_1(k1_relat_1(k2_enumset1(k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0),k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0),k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0),k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0)))))), inference(er,[status(thm)],[c_0_37])).
% 0.90/1.14  cnf(c_0_43, plain, (r2_hidden(X1,k1_relat_1(k2_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2))))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.90/1.14  cnf(c_0_44, plain, (X2=k2_enumset1(X1,X1,X1,X1)|esk1_2(X1,X2)!=X1|~r2_hidden(esk1_2(X1,X2),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_13]), c_0_14]), c_0_15])).
% 0.90/1.14  cnf(c_0_45, negated_conjecture, (esk1_2(esk5_0,k1_relat_1(k1_relat_1(k2_enumset1(k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0),k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0),k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0),k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0)))))=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_25]), c_0_25])])).
% 0.90/1.14  cnf(c_0_46, plain, (r2_hidden(X1,k1_relat_1(k1_relat_1(k2_enumset1(k4_tarski(k4_tarski(X1,X2),X3),k4_tarski(k4_tarski(X1,X2),X3),k4_tarski(k4_tarski(X1,X2),X3),k4_tarski(k4_tarski(X1,X2),X3)))))), inference(spm,[status(thm)],[c_0_38, c_0_43])).
% 0.90/1.14  cnf(c_0_47, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46])]), c_0_32]), ['proof']).
% 0.90/1.14  # SZS output end CNFRefutation
% 0.90/1.14  # Proof object total steps             : 48
% 0.90/1.14  # Proof object clause steps            : 31
% 0.90/1.14  # Proof object formula steps           : 17
% 0.90/1.14  # Proof object conjectures             : 9
% 0.90/1.14  # Proof object clause conjectures      : 6
% 0.90/1.14  # Proof object formula conjectures     : 3
% 0.90/1.14  # Proof object initial clauses used    : 12
% 0.90/1.14  # Proof object initial formulas used   : 8
% 0.90/1.14  # Proof object generating inferences   : 10
% 0.90/1.14  # Proof object simplifying inferences  : 33
% 0.90/1.14  # Training examples: 0 positive, 0 negative
% 0.90/1.14  # Parsed axioms                        : 8
% 0.90/1.14  # Removed by relevancy pruning/SinE    : 0
% 0.90/1.14  # Initial clauses                      : 15
% 0.90/1.14  # Removed in clause preprocessing      : 4
% 0.90/1.14  # Initial clauses in saturation        : 11
% 0.90/1.14  # Processed clauses                    : 724
% 0.90/1.14  # ...of these trivial                  : 0
% 0.90/1.14  # ...subsumed                          : 285
% 0.90/1.14  # ...remaining for further processing  : 439
% 0.90/1.14  # Other redundant clauses eliminated   : 1485
% 0.90/1.14  # Clauses deleted for lack of memory   : 0
% 0.90/1.14  # Backward-subsumed                    : 6
% 0.90/1.14  # Backward-rewritten                   : 11
% 0.90/1.14  # Generated clauses                    : 33892
% 0.90/1.14  # ...of the previous two non-trivial   : 31979
% 0.90/1.14  # Contextual simplify-reflections      : 4
% 0.90/1.14  # Paramodulations                      : 32296
% 0.90/1.14  # Factorizations                       : 88
% 0.90/1.14  # Equation resolutions                 : 1509
% 0.90/1.14  # Propositional unsat checks           : 0
% 0.90/1.14  #    Propositional check models        : 0
% 0.90/1.14  #    Propositional check unsatisfiable : 0
% 0.90/1.14  #    Propositional clauses             : 0
% 0.90/1.14  #    Propositional clauses after purity: 0
% 0.90/1.14  #    Propositional unsat core size     : 0
% 0.90/1.14  #    Propositional preprocessing time  : 0.000
% 0.90/1.14  #    Propositional encoding time       : 0.000
% 0.90/1.14  #    Propositional solver time         : 0.000
% 0.90/1.14  #    Success case prop preproc time    : 0.000
% 0.90/1.14  #    Success case prop encoding time   : 0.000
% 0.90/1.14  #    Success case prop solver time     : 0.000
% 0.90/1.14  # Current number of processed clauses  : 407
% 0.90/1.14  #    Positive orientable unit clauses  : 6
% 0.90/1.14  #    Positive unorientable unit clauses: 0
% 0.90/1.14  #    Negative unit clauses             : 1
% 0.90/1.14  #    Non-unit-clauses                  : 400
% 0.90/1.14  # Current number of unprocessed clauses: 31268
% 0.90/1.14  # ...number of literals in the above   : 267525
% 0.90/1.14  # Current number of archived formulas  : 0
% 0.90/1.14  # Current number of archived clauses   : 32
% 0.90/1.14  # Clause-clause subsumption calls (NU) : 28564
% 0.90/1.14  # Rec. Clause-clause subsumption calls : 9990
% 0.90/1.14  # Non-unit clause-clause subsumptions  : 295
% 0.90/1.14  # Unit Clause-clause subsumption calls : 29
% 0.90/1.14  # Rewrite failures with RHS unbound    : 0
% 0.90/1.14  # BW rewrite match attempts            : 10
% 0.90/1.14  # BW rewrite match successes           : 1
% 0.90/1.14  # Condensation attempts                : 0
% 0.90/1.14  # Condensation successes               : 0
% 0.90/1.14  # Termbank termtop insertions          : 1642924
% 0.90/1.14  
% 0.90/1.14  # -------------------------------------------------
% 0.90/1.14  # User time                : 0.767 s
% 0.90/1.14  # System time              : 0.026 s
% 0.90/1.14  # Total time               : 0.794 s
% 0.90/1.14  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:35:34 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   41 ( 319 expanded)
%              Number of clauses        :   26 ( 136 expanded)
%              Number of leaves         :    7 (  88 expanded)
%              Depth                    :    9
%              Number of atoms          :   86 ( 625 expanded)
%              Number of equality atoms :   37 ( 355 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t70_enumset1,conjecture,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t42_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(assume_negation,[status(cth)],[t70_enumset1])).

fof(c_0_8,plain,(
    ! [X20,X21,X22] : k1_enumset1(X20,X21,X22) = k2_xboole_0(k1_tarski(X20),k2_tarski(X21,X22)) ),
    inference(variable_rename,[status(thm)],[t42_enumset1])).

fof(c_0_9,plain,(
    ! [X23] : k2_tarski(X23,X23) = k1_tarski(X23) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_10,plain,(
    ! [X16,X17] : k2_xboole_0(X16,X17) = k5_xboole_0(X16,k4_xboole_0(X17,X16)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_11,plain,(
    ! [X14,X15] : k4_xboole_0(X14,X15) = k5_xboole_0(X14,k3_xboole_0(X14,X15)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_12,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( ~ r2_hidden(X8,X7)
        | r2_hidden(X8,X5)
        | r2_hidden(X8,X6)
        | X7 != k2_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | r2_hidden(X9,X7)
        | X7 != k2_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k2_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k2_xboole_0(X10,X11) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k2_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X12)
        | r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k2_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

fof(c_0_13,negated_conjecture,(
    k1_enumset1(esk2_0,esk2_0,esk3_0) != k2_tarski(esk2_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

cnf(c_0_14,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_19,plain,(
    ! [X18,X19] : k2_tarski(X18,X19) = k2_xboole_0(k1_tarski(X18),k1_tarski(X19)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

cnf(c_0_20,negated_conjecture,
    ( k1_enumset1(esk2_0,esk2_0,esk3_0) != k2_tarski(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( k1_enumset1(X1,X2,X3) = k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14,c_0_15]),c_0_16]),c_0_17])).

cnf(c_0_22,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X2)
    | X3 = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X3)
    | X3 != k5_xboole_0(X4,k5_xboole_0(X2,k3_xboole_0(X2,X4)))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_16]),c_0_17])).

cnf(c_0_25,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( X3 = k2_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_27,negated_conjecture,
    ( k5_xboole_0(k2_tarski(esk2_0,esk2_0),k5_xboole_0(k2_tarski(esk2_0,esk3_0),k3_xboole_0(k2_tarski(esk2_0,esk3_0),k2_tarski(esk2_0,esk2_0)))) != k2_tarski(esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_28,plain,
    ( X3 = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X2)
    | r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_16]),c_0_17])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X3)
    | X3 != k5_xboole_0(X2,k5_xboole_0(X4,k3_xboole_0(X4,X2)))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_16]),c_0_17])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( k2_tarski(X1,X2) = k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X2),k3_xboole_0(k2_tarski(X2,X2),k2_tarski(X1,X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_15]),c_0_15]),c_0_16]),c_0_17])).

cnf(c_0_32,plain,
    ( X3 = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_16]),c_0_17])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk1_3(k2_tarski(esk2_0,esk2_0),k2_tarski(esk2_0,esk3_0),k2_tarski(esk2_0,esk3_0)),k2_tarski(esk2_0,esk2_0))
    | r2_hidden(esk1_3(k2_tarski(esk2_0,esk2_0),k2_tarski(esk2_0,esk3_0),k2_tarski(esk2_0,esk3_0)),k2_tarski(esk2_0,esk3_0)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28])])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))))
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,k2_tarski(X2,X3))
    | ~ r2_hidden(X1,k2_tarski(X3,X3)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk1_3(k2_tarski(esk2_0,esk2_0),k2_tarski(esk2_0,esk3_0),k2_tarski(esk2_0,esk3_0)),k2_tarski(esk2_0,esk2_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_27]),c_0_33])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,k2_tarski(X2,X3))
    | ~ r2_hidden(X1,k2_tarski(X2,X2)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk1_3(k2_tarski(esk2_0,esk2_0),k2_tarski(esk2_0,esk3_0),k2_tarski(esk2_0,esk3_0)),k2_tarski(X1,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk1_3(k2_tarski(esk2_0,esk2_0),k2_tarski(esk2_0,esk3_0),k2_tarski(esk2_0,esk3_0)),k2_tarski(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_40,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_39]),c_0_39])]),c_0_27]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:48:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.21/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.21/0.38  #
% 0.21/0.38  # Preprocessing time       : 0.027 s
% 0.21/0.38  # Presaturation interreduction done
% 0.21/0.38  
% 0.21/0.38  # Proof found!
% 0.21/0.38  # SZS status Theorem
% 0.21/0.38  # SZS output start CNFRefutation
% 0.21/0.38  fof(t70_enumset1, conjecture, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.21/0.38  fof(t42_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 0.21/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.21/0.38  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.21/0.38  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.21/0.38  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 0.21/0.38  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 0.21/0.38  fof(c_0_7, negated_conjecture, ~(![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(assume_negation,[status(cth)],[t70_enumset1])).
% 0.21/0.38  fof(c_0_8, plain, ![X20, X21, X22]:k1_enumset1(X20,X21,X22)=k2_xboole_0(k1_tarski(X20),k2_tarski(X21,X22)), inference(variable_rename,[status(thm)],[t42_enumset1])).
% 0.21/0.38  fof(c_0_9, plain, ![X23]:k2_tarski(X23,X23)=k1_tarski(X23), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.21/0.38  fof(c_0_10, plain, ![X16, X17]:k2_xboole_0(X16,X17)=k5_xboole_0(X16,k4_xboole_0(X17,X16)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.21/0.38  fof(c_0_11, plain, ![X14, X15]:k4_xboole_0(X14,X15)=k5_xboole_0(X14,k3_xboole_0(X14,X15)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.21/0.38  fof(c_0_12, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:(((~r2_hidden(X8,X7)|(r2_hidden(X8,X5)|r2_hidden(X8,X6))|X7!=k2_xboole_0(X5,X6))&((~r2_hidden(X9,X5)|r2_hidden(X9,X7)|X7!=k2_xboole_0(X5,X6))&(~r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k2_xboole_0(X5,X6))))&(((~r2_hidden(esk1_3(X10,X11,X12),X10)|~r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k2_xboole_0(X10,X11))&(~r2_hidden(esk1_3(X10,X11,X12),X11)|~r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k2_xboole_0(X10,X11)))&(r2_hidden(esk1_3(X10,X11,X12),X12)|(r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k2_xboole_0(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 0.21/0.38  fof(c_0_13, negated_conjecture, k1_enumset1(esk2_0,esk2_0,esk3_0)!=k2_tarski(esk2_0,esk3_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.21/0.38  cnf(c_0_14, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.38  cnf(c_0_15, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.38  cnf(c_0_16, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.38  cnf(c_0_17, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.38  cnf(c_0_18, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.38  fof(c_0_19, plain, ![X18, X19]:k2_tarski(X18,X19)=k2_xboole_0(k1_tarski(X18),k1_tarski(X19)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 0.21/0.38  cnf(c_0_20, negated_conjecture, (k1_enumset1(esk2_0,esk2_0,esk3_0)!=k2_tarski(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.38  cnf(c_0_21, plain, (k1_enumset1(X1,X2,X3)=k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14, c_0_15]), c_0_16]), c_0_17])).
% 0.21/0.38  cnf(c_0_22, plain, (r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X2)|X3=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.38  cnf(c_0_23, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.38  cnf(c_0_24, plain, (r2_hidden(X1,X3)|X3!=k5_xboole_0(X4,k5_xboole_0(X2,k3_xboole_0(X2,X4)))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_16]), c_0_17])).
% 0.21/0.38  cnf(c_0_25, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.38  cnf(c_0_26, plain, (X3=k2_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.38  cnf(c_0_27, negated_conjecture, (k5_xboole_0(k2_tarski(esk2_0,esk2_0),k5_xboole_0(k2_tarski(esk2_0,esk3_0),k3_xboole_0(k2_tarski(esk2_0,esk3_0),k2_tarski(esk2_0,esk2_0))))!=k2_tarski(esk2_0,esk3_0)), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 0.21/0.38  cnf(c_0_28, plain, (X3=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X2)|r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_16]), c_0_17])).
% 0.21/0.38  cnf(c_0_29, plain, (r2_hidden(X1,X3)|X3!=k5_xboole_0(X2,k5_xboole_0(X4,k3_xboole_0(X4,X2)))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_16]), c_0_17])).
% 0.21/0.38  cnf(c_0_30, plain, (r2_hidden(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_24])).
% 0.21/0.38  cnf(c_0_31, plain, (k2_tarski(X1,X2)=k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X2),k3_xboole_0(k2_tarski(X2,X2),k2_tarski(X1,X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_15]), c_0_15]), c_0_16]), c_0_17])).
% 0.21/0.38  cnf(c_0_32, plain, (X3=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_16]), c_0_17])).
% 0.21/0.38  cnf(c_0_33, negated_conjecture, (r2_hidden(esk1_3(k2_tarski(esk2_0,esk2_0),k2_tarski(esk2_0,esk3_0),k2_tarski(esk2_0,esk3_0)),k2_tarski(esk2_0,esk2_0))|r2_hidden(esk1_3(k2_tarski(esk2_0,esk2_0),k2_tarski(esk2_0,esk3_0),k2_tarski(esk2_0,esk3_0)),k2_tarski(esk2_0,esk3_0))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28])])).
% 0.21/0.38  cnf(c_0_34, plain, (r2_hidden(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))))|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_29])).
% 0.21/0.38  cnf(c_0_35, plain, (r2_hidden(X1,k2_tarski(X2,X3))|~r2_hidden(X1,k2_tarski(X3,X3))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.21/0.38  cnf(c_0_36, negated_conjecture, (r2_hidden(esk1_3(k2_tarski(esk2_0,esk2_0),k2_tarski(esk2_0,esk3_0),k2_tarski(esk2_0,esk3_0)),k2_tarski(esk2_0,esk2_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_27]), c_0_33])).
% 0.21/0.38  cnf(c_0_37, plain, (r2_hidden(X1,k2_tarski(X2,X3))|~r2_hidden(X1,k2_tarski(X2,X2))), inference(spm,[status(thm)],[c_0_34, c_0_31])).
% 0.21/0.38  cnf(c_0_38, negated_conjecture, (r2_hidden(esk1_3(k2_tarski(esk2_0,esk2_0),k2_tarski(esk2_0,esk3_0),k2_tarski(esk2_0,esk3_0)),k2_tarski(X1,esk2_0))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.21/0.38  cnf(c_0_39, negated_conjecture, (r2_hidden(esk1_3(k2_tarski(esk2_0,esk2_0),k2_tarski(esk2_0,esk3_0),k2_tarski(esk2_0,esk3_0)),k2_tarski(esk2_0,X1))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.21/0.38  cnf(c_0_40, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_39]), c_0_39])]), c_0_27]), ['proof']).
% 0.21/0.38  # SZS output end CNFRefutation
% 0.21/0.38  # Proof object total steps             : 41
% 0.21/0.38  # Proof object clause steps            : 26
% 0.21/0.38  # Proof object formula steps           : 15
% 0.21/0.38  # Proof object conjectures             : 10
% 0.21/0.38  # Proof object clause conjectures      : 7
% 0.21/0.38  # Proof object formula conjectures     : 3
% 0.21/0.38  # Proof object initial clauses used    : 10
% 0.21/0.38  # Proof object initial formulas used   : 7
% 0.21/0.38  # Proof object generating inferences   : 7
% 0.21/0.38  # Proof object simplifying inferences  : 24
% 0.21/0.38  # Training examples: 0 positive, 0 negative
% 0.21/0.38  # Parsed axioms                        : 7
% 0.21/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.38  # Initial clauses                      : 12
% 0.21/0.38  # Removed in clause preprocessing      : 4
% 0.21/0.38  # Initial clauses in saturation        : 8
% 0.21/0.38  # Processed clauses                    : 25
% 0.21/0.38  # ...of these trivial                  : 0
% 0.21/0.38  # ...subsumed                          : 0
% 0.21/0.38  # ...remaining for further processing  : 25
% 0.21/0.38  # Other redundant clauses eliminated   : 4
% 0.21/0.38  # Clauses deleted for lack of memory   : 0
% 0.21/0.38  # Backward-subsumed                    : 0
% 0.21/0.38  # Backward-rewritten                   : 2
% 0.21/0.38  # Generated clauses                    : 71
% 0.21/0.38  # ...of the previous two non-trivial   : 59
% 0.21/0.38  # Contextual simplify-reflections      : 1
% 0.21/0.38  # Paramodulations                      : 61
% 0.21/0.38  # Factorizations                       : 6
% 0.21/0.38  # Equation resolutions                 : 4
% 0.21/0.38  # Propositional unsat checks           : 0
% 0.21/0.38  #    Propositional check models        : 0
% 0.21/0.38  #    Propositional check unsatisfiable : 0
% 0.21/0.38  #    Propositional clauses             : 0
% 0.21/0.38  #    Propositional clauses after purity: 0
% 0.21/0.38  #    Propositional unsat core size     : 0
% 0.21/0.38  #    Propositional preprocessing time  : 0.000
% 0.21/0.38  #    Propositional encoding time       : 0.000
% 0.21/0.38  #    Propositional solver time         : 0.000
% 0.21/0.38  #    Success case prop preproc time    : 0.000
% 0.21/0.38  #    Success case prop encoding time   : 0.000
% 0.21/0.38  #    Success case prop solver time     : 0.000
% 0.21/0.38  # Current number of processed clauses  : 12
% 0.21/0.38  #    Positive orientable unit clauses  : 3
% 0.21/0.38  #    Positive unorientable unit clauses: 0
% 0.21/0.38  #    Negative unit clauses             : 1
% 0.21/0.38  #    Non-unit-clauses                  : 8
% 0.21/0.38  # Current number of unprocessed clauses: 50
% 0.21/0.38  # ...number of literals in the above   : 229
% 0.21/0.38  # Current number of archived formulas  : 0
% 0.21/0.38  # Current number of archived clauses   : 14
% 0.21/0.38  # Clause-clause subsumption calls (NU) : 45
% 0.21/0.38  # Rec. Clause-clause subsumption calls : 31
% 0.21/0.38  # Non-unit clause-clause subsumptions  : 1
% 0.21/0.38  # Unit Clause-clause subsumption calls : 0
% 0.21/0.38  # Rewrite failures with RHS unbound    : 0
% 0.21/0.38  # BW rewrite match attempts            : 4
% 0.21/0.38  # BW rewrite match successes           : 2
% 0.21/0.38  # Condensation attempts                : 0
% 0.21/0.38  # Condensation successes               : 0
% 0.21/0.38  # Termbank termtop insertions          : 2261
% 0.21/0.38  
% 0.21/0.38  # -------------------------------------------------
% 0.21/0.38  # User time                : 0.029 s
% 0.21/0.38  # System time              : 0.003 s
% 0.21/0.38  # Total time               : 0.033 s
% 0.21/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------

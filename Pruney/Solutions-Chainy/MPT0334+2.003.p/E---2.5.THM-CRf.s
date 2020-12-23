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
% DateTime   : Thu Dec  3 10:44:38 EST 2020

% Result     : Theorem 1.32s
% Output     : CNFRefutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 187 expanded)
%              Number of clauses        :   21 (  69 expanded)
%              Number of leaves         :   10 (  58 expanded)
%              Depth                    :    7
%              Number of atoms          :   70 ( 218 expanded)
%              Number of equality atoms :   54 ( 202 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   1 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t147_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ( X1 != X2
     => k4_xboole_0(k2_xboole_0(X3,k1_tarski(X1)),k1_tarski(X2)) = k2_xboole_0(k4_xboole_0(X3,k1_tarski(X2)),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t42_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).

fof(l33_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),X2) = k1_tarski(X1)
    <=> ~ r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( X1 != X2
       => k4_xboole_0(k2_xboole_0(X3,k1_tarski(X1)),k1_tarski(X2)) = k2_xboole_0(k4_xboole_0(X3,k1_tarski(X2)),k1_tarski(X1)) ) ),
    inference(assume_negation,[status(cth)],[t147_zfmisc_1])).

fof(c_0_11,negated_conjecture,
    ( esk2_0 != esk3_0
    & k4_xboole_0(k2_xboole_0(esk4_0,k1_tarski(esk2_0)),k1_tarski(esk3_0)) != k2_xboole_0(k4_xboole_0(esk4_0,k1_tarski(esk3_0)),k1_tarski(esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

fof(c_0_12,plain,(
    ! [X20] : k2_tarski(X20,X20) = k1_tarski(X20) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_13,plain,(
    ! [X21,X22] : k1_enumset1(X21,X21,X22) = k2_tarski(X21,X22) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_14,plain,(
    ! [X11,X12] : k2_xboole_0(X11,X12) = k5_xboole_0(X11,k4_xboole_0(X12,X11)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_15,plain,(
    ! [X6,X7] : k4_xboole_0(X6,X7) = k5_xboole_0(X6,k3_xboole_0(X6,X7)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_16,plain,(
    ! [X23,X24,X25] : k2_enumset1(X23,X23,X24,X25) = k1_enumset1(X23,X24,X25) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_17,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_18,plain,(
    ! [X8,X9,X10] : k4_xboole_0(k2_xboole_0(X8,X9),X10) = k2_xboole_0(k4_xboole_0(X8,X10),k4_xboole_0(X9,X10)) ),
    inference(variable_rename,[status(thm)],[t42_xboole_1])).

fof(c_0_19,plain,(
    ! [X26,X27] :
      ( ( k4_xboole_0(k1_tarski(X26),X27) != k1_tarski(X26)
        | ~ r2_hidden(X26,X27) )
      & ( r2_hidden(X26,X27)
        | k4_xboole_0(k1_tarski(X26),X27) = k1_tarski(X26) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l33_zfmisc_1])])])).

fof(c_0_20,plain,(
    ! [X13,X14,X15,X16,X17,X18] :
      ( ( ~ r2_hidden(X15,X14)
        | X15 = X13
        | X14 != k1_tarski(X13) )
      & ( X16 != X13
        | r2_hidden(X16,X14)
        | X14 != k1_tarski(X13) )
      & ( ~ r2_hidden(esk1_2(X17,X18),X18)
        | esk1_2(X17,X18) != X17
        | X18 = k1_tarski(X17) )
      & ( r2_hidden(esk1_2(X17,X18),X18)
        | esk1_2(X17,X18) = X17
        | X18 = k1_tarski(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_21,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk4_0,k1_tarski(esk2_0)),k1_tarski(esk3_0)) != k2_xboole_0(k4_xboole_0(esk4_0,k1_tarski(esk3_0)),k1_tarski(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_22,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_23,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X2)
    | k4_xboole_0(k1_tarski(X1),X2) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(esk4_0,k5_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),k3_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk4_0))),k3_xboole_0(k5_xboole_0(esk4_0,k5_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),k3_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk4_0))),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))) != k5_xboole_0(k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))),k5_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),k3_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_22]),c_0_22]),c_0_22]),c_0_22]),c_0_23]),c_0_23]),c_0_23]),c_0_23]),c_0_24]),c_0_24]),c_0_25]),c_0_25]),c_0_25]),c_0_25]),c_0_25]),c_0_26]),c_0_26]),c_0_26]),c_0_26]),c_0_26]),c_0_26]),c_0_26]),c_0_26]),c_0_26])).

cnf(c_0_32,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_24]),c_0_24]),c_0_25]),c_0_25])).

cnf(c_0_33,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),X3)) = k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X3)),k5_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X3)),k3_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X3)),k5_xboole_0(X1,k3_xboole_0(X1,X3))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_24]),c_0_24]),c_0_25]),c_0_25]),c_0_25]),c_0_25]),c_0_25]),c_0_25])).

cnf(c_0_34,plain,
    ( k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k3_xboole_0(k2_enumset1(X1,X1,X1,X1),X2)) = k2_enumset1(X1,X1,X1,X1)
    | r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_22]),c_0_22]),c_0_23]),c_0_23]),c_0_25]),c_0_26]),c_0_26]),c_0_26])).

cnf(c_0_35,plain,
    ( X1 = X3
    | X2 != k2_enumset1(X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_22]),c_0_23]),c_0_26])).

cnf(c_0_36,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(esk4_0,k5_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),k3_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk4_0))),k3_xboole_0(k5_xboole_0(esk4_0,k5_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),k3_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk4_0))),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))) != k5_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),k5_xboole_0(k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))),k3_xboole_0(k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))),k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0)))) ),
    inference(rw,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_37,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(k2_enumset1(X3,X3,X3,X3),k3_xboole_0(k2_enumset1(X3,X3,X3,X3),k5_xboole_0(X1,k3_xboole_0(X1,X2))))) = k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(k2_enumset1(X3,X3,X3,X3),k3_xboole_0(k2_enumset1(X3,X3,X3,X3),X1))),k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(k2_enumset1(X3,X3,X3,X3),k3_xboole_0(k2_enumset1(X3,X3,X3,X3),X1))),X2))
    | r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_38,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k2_enumset1(X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_35])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_32])])).

cnf(c_0_40,negated_conjecture,
    ( esk2_0 != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_41,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.19/0.34  % CPULimit   : 60
% 0.19/0.34  % WCLimit    : 600
% 0.19/0.34  % DateTime   : Tue Dec  1 15:45:01 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  # Version: 2.5pre002
% 0.19/0.34  # No SInE strategy applied
% 0.19/0.34  # Trying AutoSched0 for 299 seconds
% 1.32/1.48  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 1.32/1.48  # and selection function SelectComplexExceptUniqMaxHorn.
% 1.32/1.48  #
% 1.32/1.48  # Preprocessing time       : 0.027 s
% 1.32/1.48  # Presaturation interreduction done
% 1.32/1.48  
% 1.32/1.48  # Proof found!
% 1.32/1.48  # SZS status Theorem
% 1.32/1.48  # SZS output start CNFRefutation
% 1.32/1.48  fof(t147_zfmisc_1, conjecture, ![X1, X2, X3]:(X1!=X2=>k4_xboole_0(k2_xboole_0(X3,k1_tarski(X1)),k1_tarski(X2))=k2_xboole_0(k4_xboole_0(X3,k1_tarski(X2)),k1_tarski(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_zfmisc_1)).
% 1.32/1.48  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.32/1.48  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 1.32/1.48  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 1.32/1.48  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.32/1.48  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 1.32/1.48  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.32/1.48  fof(t42_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_xboole_1)).
% 1.32/1.48  fof(l33_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),X2)=k1_tarski(X1)<=>~(r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 1.32/1.48  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 1.32/1.48  fof(c_0_10, negated_conjecture, ~(![X1, X2, X3]:(X1!=X2=>k4_xboole_0(k2_xboole_0(X3,k1_tarski(X1)),k1_tarski(X2))=k2_xboole_0(k4_xboole_0(X3,k1_tarski(X2)),k1_tarski(X1)))), inference(assume_negation,[status(cth)],[t147_zfmisc_1])).
% 1.32/1.48  fof(c_0_11, negated_conjecture, (esk2_0!=esk3_0&k4_xboole_0(k2_xboole_0(esk4_0,k1_tarski(esk2_0)),k1_tarski(esk3_0))!=k2_xboole_0(k4_xboole_0(esk4_0,k1_tarski(esk3_0)),k1_tarski(esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 1.32/1.48  fof(c_0_12, plain, ![X20]:k2_tarski(X20,X20)=k1_tarski(X20), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 1.32/1.48  fof(c_0_13, plain, ![X21, X22]:k1_enumset1(X21,X21,X22)=k2_tarski(X21,X22), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 1.32/1.48  fof(c_0_14, plain, ![X11, X12]:k2_xboole_0(X11,X12)=k5_xboole_0(X11,k4_xboole_0(X12,X11)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 1.32/1.48  fof(c_0_15, plain, ![X6, X7]:k4_xboole_0(X6,X7)=k5_xboole_0(X6,k3_xboole_0(X6,X7)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 1.32/1.48  fof(c_0_16, plain, ![X23, X24, X25]:k2_enumset1(X23,X23,X24,X25)=k1_enumset1(X23,X24,X25), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 1.32/1.48  fof(c_0_17, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 1.32/1.48  fof(c_0_18, plain, ![X8, X9, X10]:k4_xboole_0(k2_xboole_0(X8,X9),X10)=k2_xboole_0(k4_xboole_0(X8,X10),k4_xboole_0(X9,X10)), inference(variable_rename,[status(thm)],[t42_xboole_1])).
% 1.32/1.48  fof(c_0_19, plain, ![X26, X27]:((k4_xboole_0(k1_tarski(X26),X27)!=k1_tarski(X26)|~r2_hidden(X26,X27))&(r2_hidden(X26,X27)|k4_xboole_0(k1_tarski(X26),X27)=k1_tarski(X26))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l33_zfmisc_1])])])).
% 1.32/1.48  fof(c_0_20, plain, ![X13, X14, X15, X16, X17, X18]:(((~r2_hidden(X15,X14)|X15=X13|X14!=k1_tarski(X13))&(X16!=X13|r2_hidden(X16,X14)|X14!=k1_tarski(X13)))&((~r2_hidden(esk1_2(X17,X18),X18)|esk1_2(X17,X18)!=X17|X18=k1_tarski(X17))&(r2_hidden(esk1_2(X17,X18),X18)|esk1_2(X17,X18)=X17|X18=k1_tarski(X17)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 1.32/1.48  cnf(c_0_21, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk4_0,k1_tarski(esk2_0)),k1_tarski(esk3_0))!=k2_xboole_0(k4_xboole_0(esk4_0,k1_tarski(esk3_0)),k1_tarski(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 1.32/1.48  cnf(c_0_22, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.32/1.48  cnf(c_0_23, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 1.32/1.48  cnf(c_0_24, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.32/1.48  cnf(c_0_25, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.32/1.48  cnf(c_0_26, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.32/1.48  cnf(c_0_27, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.32/1.48  cnf(c_0_28, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.32/1.48  cnf(c_0_29, plain, (r2_hidden(X1,X2)|k4_xboole_0(k1_tarski(X1),X2)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.32/1.48  cnf(c_0_30, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.32/1.48  cnf(c_0_31, negated_conjecture, (k5_xboole_0(k5_xboole_0(esk4_0,k5_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),k3_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk4_0))),k3_xboole_0(k5_xboole_0(esk4_0,k5_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),k3_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk4_0))),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)))!=k5_xboole_0(k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))),k5_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),k3_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_22]), c_0_22]), c_0_22]), c_0_22]), c_0_23]), c_0_23]), c_0_23]), c_0_23]), c_0_24]), c_0_24]), c_0_25]), c_0_25]), c_0_25]), c_0_25]), c_0_25]), c_0_26]), c_0_26]), c_0_26]), c_0_26]), c_0_26]), c_0_26]), c_0_26]), c_0_26]), c_0_26])).
% 1.32/1.48  cnf(c_0_32, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_24]), c_0_24]), c_0_25]), c_0_25])).
% 1.32/1.48  cnf(c_0_33, plain, (k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),X3))=k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X3)),k5_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X3)),k3_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X3)),k5_xboole_0(X1,k3_xboole_0(X1,X3)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_24]), c_0_24]), c_0_25]), c_0_25]), c_0_25]), c_0_25]), c_0_25]), c_0_25])).
% 1.32/1.48  cnf(c_0_34, plain, (k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k3_xboole_0(k2_enumset1(X1,X1,X1,X1),X2))=k2_enumset1(X1,X1,X1,X1)|r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_22]), c_0_22]), c_0_23]), c_0_23]), c_0_25]), c_0_26]), c_0_26]), c_0_26])).
% 1.32/1.48  cnf(c_0_35, plain, (X1=X3|X2!=k2_enumset1(X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_22]), c_0_23]), c_0_26])).
% 1.32/1.48  cnf(c_0_36, negated_conjecture, (k5_xboole_0(k5_xboole_0(esk4_0,k5_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),k3_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk4_0))),k3_xboole_0(k5_xboole_0(esk4_0,k5_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),k3_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk4_0))),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)))!=k5_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),k5_xboole_0(k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))),k3_xboole_0(k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))),k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0))))), inference(rw,[status(thm)],[c_0_31, c_0_32])).
% 1.32/1.48  cnf(c_0_37, plain, (k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(k2_enumset1(X3,X3,X3,X3),k3_xboole_0(k2_enumset1(X3,X3,X3,X3),k5_xboole_0(X1,k3_xboole_0(X1,X2)))))=k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(k2_enumset1(X3,X3,X3,X3),k3_xboole_0(k2_enumset1(X3,X3,X3,X3),X1))),k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(k2_enumset1(X3,X3,X3,X3),k3_xboole_0(k2_enumset1(X3,X3,X3,X3),X1))),X2))|r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 1.32/1.48  cnf(c_0_38, plain, (X1=X2|~r2_hidden(X1,k2_enumset1(X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_35])).
% 1.32/1.48  cnf(c_0_39, negated_conjecture, (r2_hidden(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_32])])).
% 1.32/1.48  cnf(c_0_40, negated_conjecture, (esk2_0!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 1.32/1.48  cnf(c_0_41, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40]), ['proof']).
% 1.32/1.48  # SZS output end CNFRefutation
% 1.32/1.48  # Proof object total steps             : 42
% 1.32/1.48  # Proof object clause steps            : 21
% 1.32/1.48  # Proof object formula steps           : 21
% 1.32/1.48  # Proof object conjectures             : 9
% 1.32/1.48  # Proof object clause conjectures      : 6
% 1.32/1.48  # Proof object formula conjectures     : 3
% 1.32/1.48  # Proof object initial clauses used    : 11
% 1.32/1.48  # Proof object initial formulas used   : 10
% 1.32/1.48  # Proof object generating inferences   : 3
% 1.32/1.48  # Proof object simplifying inferences  : 52
% 1.32/1.48  # Training examples: 0 positive, 0 negative
% 1.32/1.48  # Parsed axioms                        : 10
% 1.32/1.48  # Removed by relevancy pruning/SinE    : 0
% 1.32/1.48  # Initial clauses                      : 15
% 1.32/1.48  # Removed in clause preprocessing      : 5
% 1.32/1.48  # Initial clauses in saturation        : 10
% 1.32/1.48  # Processed clauses                    : 700
% 1.32/1.48  # ...of these trivial                  : 1
% 1.32/1.48  # ...subsumed                          : 400
% 1.32/1.48  # ...remaining for further processing  : 299
% 1.32/1.48  # Other redundant clauses eliminated   : 3122
% 1.32/1.48  # Clauses deleted for lack of memory   : 0
% 1.32/1.48  # Backward-subsumed                    : 31
% 1.32/1.48  # Backward-rewritten                   : 1
% 1.32/1.48  # Generated clauses                    : 53193
% 1.32/1.48  # ...of the previous two non-trivial   : 49093
% 1.32/1.48  # Contextual simplify-reflections      : 3
% 1.32/1.48  # Paramodulations                      : 49870
% 1.32/1.48  # Factorizations                       : 188
% 1.32/1.48  # Equation resolutions                 : 3136
% 1.32/1.48  # Propositional unsat checks           : 0
% 1.32/1.48  #    Propositional check models        : 0
% 1.32/1.48  #    Propositional check unsatisfiable : 0
% 1.32/1.48  #    Propositional clauses             : 0
% 1.32/1.48  #    Propositional clauses after purity: 0
% 1.32/1.48  #    Propositional unsat core size     : 0
% 1.32/1.48  #    Propositional preprocessing time  : 0.000
% 1.32/1.48  #    Propositional encoding time       : 0.000
% 1.32/1.48  #    Propositional solver time         : 0.000
% 1.32/1.48  #    Success case prop preproc time    : 0.000
% 1.32/1.48  #    Success case prop encoding time   : 0.000
% 1.32/1.48  #    Success case prop solver time     : 0.000
% 1.32/1.48  # Current number of processed clauses  : 255
% 1.32/1.48  #    Positive orientable unit clauses  : 4
% 1.32/1.48  #    Positive unorientable unit clauses: 2
% 1.32/1.48  #    Negative unit clauses             : 2
% 1.32/1.48  #    Non-unit-clauses                  : 247
% 1.32/1.48  # Current number of unprocessed clauses: 48392
% 1.32/1.48  # ...number of literals in the above   : 434074
% 1.32/1.48  # Current number of archived formulas  : 0
% 1.32/1.48  # Current number of archived clauses   : 47
% 1.32/1.48  # Clause-clause subsumption calls (NU) : 17921
% 1.32/1.48  # Rec. Clause-clause subsumption calls : 7192
% 1.32/1.48  # Non-unit clause-clause subsumptions  : 429
% 1.32/1.48  # Unit Clause-clause subsumption calls : 322
% 1.32/1.48  # Rewrite failures with RHS unbound    : 0
% 1.32/1.48  # BW rewrite match attempts            : 33
% 1.32/1.48  # BW rewrite match successes           : 25
% 1.32/1.48  # Condensation attempts                : 0
% 1.32/1.48  # Condensation successes               : 0
% 1.32/1.48  # Termbank termtop insertions          : 2563669
% 1.32/1.48  
% 1.32/1.48  # -------------------------------------------------
% 1.32/1.48  # User time                : 1.109 s
% 1.32/1.48  # System time              : 0.036 s
% 1.32/1.48  # Total time               : 1.145 s
% 1.32/1.48  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:38 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 180 expanded)
%              Number of clauses        :   24 (  68 expanded)
%              Number of leaves         :   11 (  55 expanded)
%              Depth                    :    8
%              Number of atoms          :   85 ( 221 expanded)
%              Number of equality atoms :   58 ( 194 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   2 average)
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

fof(t87_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_xboole_0(X1,X2)
     => k2_xboole_0(k4_xboole_0(X3,X1),X2) = k4_xboole_0(k2_xboole_0(X3,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_xboole_1)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(t65_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,k1_tarski(X2)) = X1
    <=> ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( X1 != X2
       => k4_xboole_0(k2_xboole_0(X3,k1_tarski(X1)),k1_tarski(X2)) = k2_xboole_0(k4_xboole_0(X3,k1_tarski(X2)),k1_tarski(X1)) ) ),
    inference(assume_negation,[status(cth)],[t147_zfmisc_1])).

fof(c_0_12,negated_conjecture,
    ( esk2_0 != esk3_0
    & k4_xboole_0(k2_xboole_0(esk4_0,k1_tarski(esk2_0)),k1_tarski(esk3_0)) != k2_xboole_0(k4_xboole_0(esk4_0,k1_tarski(esk3_0)),k1_tarski(esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

fof(c_0_13,plain,(
    ! [X22] : k2_tarski(X22,X22) = k1_tarski(X22) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_14,plain,(
    ! [X23,X24] : k1_enumset1(X23,X23,X24) = k2_tarski(X23,X24) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_15,plain,(
    ! [X13,X14] : k2_xboole_0(X13,X14) = k5_xboole_0(X13,k4_xboole_0(X14,X13)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_16,plain,(
    ! [X6,X7] : k4_xboole_0(X6,X7) = k5_xboole_0(X6,k3_xboole_0(X6,X7)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_17,plain,(
    ! [X25,X26,X27] : k2_enumset1(X25,X25,X26,X27) = k1_enumset1(X25,X26,X27) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_18,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_19,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk4_0,k1_tarski(esk2_0)),k1_tarski(esk3_0)) != k2_xboole_0(k4_xboole_0(esk4_0,k1_tarski(esk3_0)),k1_tarski(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_26,plain,(
    ! [X10,X11,X12] :
      ( ~ r1_xboole_0(X10,X11)
      | k2_xboole_0(k4_xboole_0(X12,X10),X11) = k4_xboole_0(k2_xboole_0(X12,X11),X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_xboole_1])])).

fof(c_0_27,plain,(
    ! [X8,X9] :
      ( ( ~ r1_xboole_0(X8,X9)
        | k4_xboole_0(X8,X9) = X8 )
      & ( k4_xboole_0(X8,X9) != X8
        | r1_xboole_0(X8,X9) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

fof(c_0_28,plain,(
    ! [X28,X29] :
      ( ( k4_xboole_0(X28,k1_tarski(X29)) != X28
        | ~ r2_hidden(X29,X28) )
      & ( r2_hidden(X29,X28)
        | k4_xboole_0(X28,k1_tarski(X29)) = X28 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).

fof(c_0_29,plain,(
    ! [X15,X16,X17,X18,X19,X20] :
      ( ( ~ r2_hidden(X17,X16)
        | X17 = X15
        | X16 != k1_tarski(X15) )
      & ( X18 != X15
        | r2_hidden(X18,X16)
        | X16 != k1_tarski(X15) )
      & ( ~ r2_hidden(esk1_2(X19,X20),X20)
        | esk1_2(X19,X20) != X19
        | X20 = k1_tarski(X19) )
      & ( r2_hidden(esk1_2(X19,X20),X20)
        | esk1_2(X19,X20) = X19
        | X20 = k1_tarski(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_30,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(esk4_0,k5_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),k3_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk4_0))),k3_xboole_0(k5_xboole_0(esk4_0,k5_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),k3_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk4_0))),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))) != k5_xboole_0(k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))),k5_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),k3_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_20]),c_0_20]),c_0_20]),c_0_20]),c_0_21]),c_0_21]),c_0_21]),c_0_21]),c_0_22]),c_0_22]),c_0_23]),c_0_23]),c_0_23]),c_0_23]),c_0_23]),c_0_24]),c_0_24]),c_0_24]),c_0_24]),c_0_24]),c_0_24]),c_0_24]),c_0_24]),c_0_24])).

cnf(c_0_31,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_22]),c_0_22]),c_0_23]),c_0_23])).

cnf(c_0_32,plain,
    ( k2_xboole_0(k4_xboole_0(X3,X1),X2) = k4_xboole_0(k2_xboole_0(X3,X2),X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,X2)
    | k4_xboole_0(X2,k1_tarski(X1)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(esk4_0,k5_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),k3_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk4_0))),k3_xboole_0(k5_xboole_0(esk4_0,k5_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),k3_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk4_0))),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))) != k5_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),k5_xboole_0(k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))),k3_xboole_0(k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))),k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0)))) ),
    inference(rw,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_37,plain,
    ( k5_xboole_0(k5_xboole_0(X3,k5_xboole_0(X2,k3_xboole_0(X2,X3))),k3_xboole_0(k5_xboole_0(X3,k5_xboole_0(X2,k3_xboole_0(X2,X3))),X1)) = k5_xboole_0(k5_xboole_0(X3,k3_xboole_0(X3,X1)),k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X1)))))
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_22]),c_0_22]),c_0_23]),c_0_23]),c_0_23]),c_0_23]),c_0_23])).

cnf(c_0_38,plain,
    ( r1_xboole_0(X1,X2)
    | k5_xboole_0(X1,k3_xboole_0(X1,X2)) != X1 ),
    inference(rw,[status(thm)],[c_0_33,c_0_23])).

cnf(c_0_39,plain,
    ( k5_xboole_0(X2,k3_xboole_0(X2,k2_enumset1(X1,X1,X1,X1))) = X2
    | r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_20]),c_0_21]),c_0_23]),c_0_24])).

cnf(c_0_40,plain,
    ( X1 = X3
    | X2 != k2_enumset1(X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_20]),c_0_21]),c_0_24])).

cnf(c_0_41,negated_conjecture,
    ( ~ r1_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_31])])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(X2,k2_enumset1(X1,X1,X1,X1)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_43,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k2_enumset1(X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_45,negated_conjecture,
    ( esk2_0 != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_46,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:43:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.027 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t147_zfmisc_1, conjecture, ![X1, X2, X3]:(X1!=X2=>k4_xboole_0(k2_xboole_0(X3,k1_tarski(X1)),k1_tarski(X2))=k2_xboole_0(k4_xboole_0(X3,k1_tarski(X2)),k1_tarski(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_zfmisc_1)).
% 0.13/0.37  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.37  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.37  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.13/0.37  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.13/0.37  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.13/0.37  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.13/0.37  fof(t87_xboole_1, axiom, ![X1, X2, X3]:(r1_xboole_0(X1,X2)=>k2_xboole_0(k4_xboole_0(X3,X1),X2)=k4_xboole_0(k2_xboole_0(X3,X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_xboole_1)).
% 0.13/0.37  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.13/0.37  fof(t65_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(X1,k1_tarski(X2))=X1<=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 0.13/0.37  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.13/0.37  fof(c_0_11, negated_conjecture, ~(![X1, X2, X3]:(X1!=X2=>k4_xboole_0(k2_xboole_0(X3,k1_tarski(X1)),k1_tarski(X2))=k2_xboole_0(k4_xboole_0(X3,k1_tarski(X2)),k1_tarski(X1)))), inference(assume_negation,[status(cth)],[t147_zfmisc_1])).
% 0.13/0.37  fof(c_0_12, negated_conjecture, (esk2_0!=esk3_0&k4_xboole_0(k2_xboole_0(esk4_0,k1_tarski(esk2_0)),k1_tarski(esk3_0))!=k2_xboole_0(k4_xboole_0(esk4_0,k1_tarski(esk3_0)),k1_tarski(esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 0.13/0.37  fof(c_0_13, plain, ![X22]:k2_tarski(X22,X22)=k1_tarski(X22), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.37  fof(c_0_14, plain, ![X23, X24]:k1_enumset1(X23,X23,X24)=k2_tarski(X23,X24), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.37  fof(c_0_15, plain, ![X13, X14]:k2_xboole_0(X13,X14)=k5_xboole_0(X13,k4_xboole_0(X14,X13)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.13/0.37  fof(c_0_16, plain, ![X6, X7]:k4_xboole_0(X6,X7)=k5_xboole_0(X6,k3_xboole_0(X6,X7)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.13/0.37  fof(c_0_17, plain, ![X25, X26, X27]:k2_enumset1(X25,X25,X26,X27)=k1_enumset1(X25,X26,X27), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.13/0.37  fof(c_0_18, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.13/0.37  cnf(c_0_19, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk4_0,k1_tarski(esk2_0)),k1_tarski(esk3_0))!=k2_xboole_0(k4_xboole_0(esk4_0,k1_tarski(esk3_0)),k1_tarski(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.37  cnf(c_0_20, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.37  cnf(c_0_21, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.37  cnf(c_0_22, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.37  cnf(c_0_23, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.37  cnf(c_0_24, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.37  cnf(c_0_25, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.37  fof(c_0_26, plain, ![X10, X11, X12]:(~r1_xboole_0(X10,X11)|k2_xboole_0(k4_xboole_0(X12,X10),X11)=k4_xboole_0(k2_xboole_0(X12,X11),X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_xboole_1])])).
% 0.13/0.37  fof(c_0_27, plain, ![X8, X9]:((~r1_xboole_0(X8,X9)|k4_xboole_0(X8,X9)=X8)&(k4_xboole_0(X8,X9)!=X8|r1_xboole_0(X8,X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.13/0.37  fof(c_0_28, plain, ![X28, X29]:((k4_xboole_0(X28,k1_tarski(X29))!=X28|~r2_hidden(X29,X28))&(r2_hidden(X29,X28)|k4_xboole_0(X28,k1_tarski(X29))=X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).
% 0.13/0.37  fof(c_0_29, plain, ![X15, X16, X17, X18, X19, X20]:(((~r2_hidden(X17,X16)|X17=X15|X16!=k1_tarski(X15))&(X18!=X15|r2_hidden(X18,X16)|X16!=k1_tarski(X15)))&((~r2_hidden(esk1_2(X19,X20),X20)|esk1_2(X19,X20)!=X19|X20=k1_tarski(X19))&(r2_hidden(esk1_2(X19,X20),X20)|esk1_2(X19,X20)=X19|X20=k1_tarski(X19)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.13/0.37  cnf(c_0_30, negated_conjecture, (k5_xboole_0(k5_xboole_0(esk4_0,k5_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),k3_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk4_0))),k3_xboole_0(k5_xboole_0(esk4_0,k5_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),k3_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk4_0))),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)))!=k5_xboole_0(k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))),k5_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),k3_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_20]), c_0_20]), c_0_20]), c_0_20]), c_0_21]), c_0_21]), c_0_21]), c_0_21]), c_0_22]), c_0_22]), c_0_23]), c_0_23]), c_0_23]), c_0_23]), c_0_23]), c_0_24]), c_0_24]), c_0_24]), c_0_24]), c_0_24]), c_0_24]), c_0_24]), c_0_24]), c_0_24])).
% 0.13/0.37  cnf(c_0_31, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_22]), c_0_22]), c_0_23]), c_0_23])).
% 0.13/0.37  cnf(c_0_32, plain, (k2_xboole_0(k4_xboole_0(X3,X1),X2)=k4_xboole_0(k2_xboole_0(X3,X2),X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.37  cnf(c_0_33, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.37  cnf(c_0_34, plain, (r2_hidden(X1,X2)|k4_xboole_0(X2,k1_tarski(X1))=X2), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.37  cnf(c_0_35, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.37  cnf(c_0_36, negated_conjecture, (k5_xboole_0(k5_xboole_0(esk4_0,k5_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),k3_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk4_0))),k3_xboole_0(k5_xboole_0(esk4_0,k5_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),k3_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk4_0))),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)))!=k5_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),k5_xboole_0(k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))),k3_xboole_0(k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))),k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0))))), inference(rw,[status(thm)],[c_0_30, c_0_31])).
% 0.13/0.38  cnf(c_0_37, plain, (k5_xboole_0(k5_xboole_0(X3,k5_xboole_0(X2,k3_xboole_0(X2,X3))),k3_xboole_0(k5_xboole_0(X3,k5_xboole_0(X2,k3_xboole_0(X2,X3))),X1))=k5_xboole_0(k5_xboole_0(X3,k3_xboole_0(X3,X1)),k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X1)))))|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_22]), c_0_22]), c_0_23]), c_0_23]), c_0_23]), c_0_23]), c_0_23])).
% 0.13/0.38  cnf(c_0_38, plain, (r1_xboole_0(X1,X2)|k5_xboole_0(X1,k3_xboole_0(X1,X2))!=X1), inference(rw,[status(thm)],[c_0_33, c_0_23])).
% 0.13/0.38  cnf(c_0_39, plain, (k5_xboole_0(X2,k3_xboole_0(X2,k2_enumset1(X1,X1,X1,X1)))=X2|r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_20]), c_0_21]), c_0_23]), c_0_24])).
% 0.13/0.38  cnf(c_0_40, plain, (X1=X3|X2!=k2_enumset1(X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_20]), c_0_21]), c_0_24])).
% 0.13/0.38  cnf(c_0_41, negated_conjecture, (~r1_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_31])])).
% 0.13/0.38  cnf(c_0_42, plain, (r2_hidden(X1,X2)|r1_xboole_0(X2,k2_enumset1(X1,X1,X1,X1))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.13/0.38  cnf(c_0_43, plain, (X1=X2|~r2_hidden(X1,k2_enumset1(X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_40])).
% 0.13/0.38  cnf(c_0_44, negated_conjecture, (r2_hidden(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.13/0.38  cnf(c_0_45, negated_conjecture, (esk2_0!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_46, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 47
% 0.13/0.38  # Proof object clause steps            : 24
% 0.13/0.38  # Proof object formula steps           : 23
% 0.13/0.38  # Proof object conjectures             : 10
% 0.13/0.38  # Proof object clause conjectures      : 7
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 12
% 0.13/0.38  # Proof object initial formulas used   : 11
% 0.13/0.38  # Proof object generating inferences   : 4
% 0.13/0.38  # Proof object simplifying inferences  : 48
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 11
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 17
% 0.13/0.38  # Removed in clause preprocessing      : 5
% 0.13/0.38  # Initial clauses in saturation        : 12
% 0.13/0.38  # Processed clauses                    : 43
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 4
% 0.13/0.38  # ...remaining for further processing  : 39
% 0.13/0.38  # Other redundant clauses eliminated   : 7
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 2
% 0.13/0.38  # Generated clauses                    : 170
% 0.13/0.38  # ...of the previous two non-trivial   : 161
% 0.13/0.38  # Contextual simplify-reflections      : 0
% 0.13/0.38  # Paramodulations                      : 164
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 7
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 23
% 0.13/0.38  #    Positive orientable unit clauses  : 2
% 0.13/0.38  #    Positive unorientable unit clauses: 1
% 0.13/0.38  #    Negative unit clauses             : 3
% 0.13/0.38  #    Non-unit-clauses                  : 17
% 0.13/0.38  # Current number of unprocessed clauses: 141
% 0.13/0.38  # ...number of literals in the above   : 512
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 19
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 39
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 32
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 4
% 0.13/0.38  # Unit Clause-clause subsumption calls : 7
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 11
% 0.13/0.38  # BW rewrite match successes           : 10
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 5217
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.032 s
% 0.13/0.38  # System time              : 0.004 s
% 0.13/0.38  # Total time               : 0.036 s
% 0.13/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------

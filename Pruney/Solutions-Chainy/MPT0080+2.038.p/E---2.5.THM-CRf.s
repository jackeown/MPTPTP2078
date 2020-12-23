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
% DateTime   : Thu Dec  3 10:33:12 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   53 (  84 expanded)
%              Number of clauses        :   28 (  37 expanded)
%              Number of leaves         :   12 (  22 expanded)
%              Depth                    :   10
%              Number of atoms          :   69 ( 118 expanded)
%              Number of equality atoms :   38 (  64 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t73_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,k2_xboole_0(X2,X3))
        & r1_xboole_0(X1,X3) )
     => r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( r1_tarski(X1,k2_xboole_0(X2,X3))
          & r1_xboole_0(X1,X3) )
       => r1_tarski(X1,X2) ) ),
    inference(assume_negation,[status(cth)],[t73_xboole_1])).

fof(c_0_13,negated_conjecture,
    ( r1_tarski(esk3_0,k2_xboole_0(esk4_0,esk5_0))
    & r1_xboole_0(esk3_0,esk5_0)
    & ~ r1_tarski(esk3_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

fof(c_0_14,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_15,plain,(
    ! [X20,X21] :
      ( ~ r1_tarski(X20,X21)
      | k2_xboole_0(X20,X21) = X21 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_16,negated_conjecture,
    ( r1_tarski(esk3_0,k2_xboole_0(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,plain,(
    ! [X6,X7] :
      ( ( ~ r1_xboole_0(X6,X7)
        | k3_xboole_0(X6,X7) = k1_xboole_0 )
      & ( k3_xboole_0(X6,X7) != k1_xboole_0
        | r1_xboole_0(X6,X7) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_19,plain,(
    ! [X32,X33] : k4_xboole_0(X32,k4_xboole_0(X32,X33)) = k3_xboole_0(X32,X33) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_20,plain,(
    ! [X25,X26] : k4_xboole_0(k2_xboole_0(X25,X26),X26) = k4_xboole_0(X25,X26) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

cnf(c_0_21,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( r1_tarski(esk3_0,k2_xboole_0(esk5_0,esk4_0)) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_25,plain,(
    ! [X24] : k4_xboole_0(X24,k1_xboole_0) = X24 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_26,plain,(
    ! [X34] : r1_xboole_0(X34,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

fof(c_0_27,plain,(
    ! [X22,X23] : k2_xboole_0(X22,k4_xboole_0(X23,X22)) = k2_xboole_0(X22,X23) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

fof(c_0_28,plain,(
    ! [X27,X28,X29] : k4_xboole_0(k4_xboole_0(X27,X28),X29) = k4_xboole_0(X27,k2_xboole_0(X28,X29)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_29,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,negated_conjecture,
    ( k2_xboole_0(esk3_0,k2_xboole_0(esk5_0,esk4_0)) = k2_xboole_0(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_31,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_34,plain,(
    ! [X35,X36] : r1_tarski(X35,k2_xboole_0(X35,X36)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_35,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk5_0,esk4_0),k2_xboole_0(esk5_0,esk4_0)) = k4_xboole_0(esk3_0,k2_xboole_0(esk5_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_38,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])])).

fof(c_0_39,plain,(
    ! [X30,X31] : k4_xboole_0(X30,k3_xboole_0(X30,X31)) = k4_xboole_0(X30,X31) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_41,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1))) = k2_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_42,negated_conjecture,
    ( k4_xboole_0(esk3_0,k2_xboole_0(esk5_0,esk4_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_43,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_29]),c_0_32])).

cnf(c_0_44,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_17])).

cnf(c_0_46,negated_conjecture,
    ( k2_xboole_0(esk4_0,k4_xboole_0(esk3_0,esk5_0)) = esk4_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])).

cnf(c_0_47,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_44,c_0_24])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk3_0,esk5_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_49,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_31]),c_0_32])).

cnf(c_0_50,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_51,negated_conjecture,
    ( ~ r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_52,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50])]),c_0_51]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:58:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.40  # AutoSched0-Mode selected heuristic G_E___208_C48_F1_AE_CS_SP_PS_S0Y
% 0.13/0.40  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.40  #
% 0.13/0.40  # Preprocessing time       : 0.027 s
% 0.13/0.40  # Presaturation interreduction done
% 0.13/0.40  
% 0.13/0.40  # Proof found!
% 0.13/0.40  # SZS status Theorem
% 0.13/0.40  # SZS output start CNFRefutation
% 0.13/0.40  fof(t73_xboole_1, conjecture, ![X1, X2, X3]:((r1_tarski(X1,k2_xboole_0(X2,X3))&r1_xboole_0(X1,X3))=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_xboole_1)).
% 0.13/0.40  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.13/0.40  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.13/0.40  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.13/0.40  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.13/0.40  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 0.13/0.40  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.13/0.40  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.13/0.40  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.13/0.40  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.13/0.40  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.13/0.40  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 0.13/0.40  fof(c_0_12, negated_conjecture, ~(![X1, X2, X3]:((r1_tarski(X1,k2_xboole_0(X2,X3))&r1_xboole_0(X1,X3))=>r1_tarski(X1,X2))), inference(assume_negation,[status(cth)],[t73_xboole_1])).
% 0.13/0.40  fof(c_0_13, negated_conjecture, ((r1_tarski(esk3_0,k2_xboole_0(esk4_0,esk5_0))&r1_xboole_0(esk3_0,esk5_0))&~r1_tarski(esk3_0,esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.13/0.40  fof(c_0_14, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.13/0.40  fof(c_0_15, plain, ![X20, X21]:(~r1_tarski(X20,X21)|k2_xboole_0(X20,X21)=X21), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.13/0.40  cnf(c_0_16, negated_conjecture, (r1_tarski(esk3_0,k2_xboole_0(esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.40  cnf(c_0_17, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.40  fof(c_0_18, plain, ![X6, X7]:((~r1_xboole_0(X6,X7)|k3_xboole_0(X6,X7)=k1_xboole_0)&(k3_xboole_0(X6,X7)!=k1_xboole_0|r1_xboole_0(X6,X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.13/0.40  fof(c_0_19, plain, ![X32, X33]:k4_xboole_0(X32,k4_xboole_0(X32,X33))=k3_xboole_0(X32,X33), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.13/0.40  fof(c_0_20, plain, ![X25, X26]:k4_xboole_0(k2_xboole_0(X25,X26),X26)=k4_xboole_0(X25,X26), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 0.13/0.40  cnf(c_0_21, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.40  cnf(c_0_22, negated_conjecture, (r1_tarski(esk3_0,k2_xboole_0(esk5_0,esk4_0))), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 0.13/0.40  cnf(c_0_23, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.40  cnf(c_0_24, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.40  fof(c_0_25, plain, ![X24]:k4_xboole_0(X24,k1_xboole_0)=X24, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.13/0.40  fof(c_0_26, plain, ![X34]:r1_xboole_0(X34,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.13/0.40  fof(c_0_27, plain, ![X22, X23]:k2_xboole_0(X22,k4_xboole_0(X23,X22))=k2_xboole_0(X22,X23), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.13/0.40  fof(c_0_28, plain, ![X27, X28, X29]:k4_xboole_0(k4_xboole_0(X27,X28),X29)=k4_xboole_0(X27,k2_xboole_0(X28,X29)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.13/0.40  cnf(c_0_29, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.40  cnf(c_0_30, negated_conjecture, (k2_xboole_0(esk3_0,k2_xboole_0(esk5_0,esk4_0))=k2_xboole_0(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.13/0.40  cnf(c_0_31, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 0.13/0.40  cnf(c_0_32, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.40  cnf(c_0_33, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.40  fof(c_0_34, plain, ![X35, X36]:r1_tarski(X35,k2_xboole_0(X35,X36)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.13/0.40  cnf(c_0_35, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.40  cnf(c_0_36, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.40  cnf(c_0_37, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk5_0,esk4_0),k2_xboole_0(esk5_0,esk4_0))=k4_xboole_0(esk3_0,k2_xboole_0(esk5_0,esk4_0))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.13/0.40  cnf(c_0_38, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])])).
% 0.13/0.40  fof(c_0_39, plain, ![X30, X31]:k4_xboole_0(X30,k3_xboole_0(X30,X31))=k4_xboole_0(X30,X31), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 0.13/0.40  cnf(c_0_40, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.40  cnf(c_0_41, plain, (k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1)))=k2_xboole_0(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.13/0.40  cnf(c_0_42, negated_conjecture, (k4_xboole_0(esk3_0,k2_xboole_0(esk5_0,esk4_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_37, c_0_38])).
% 0.13/0.40  cnf(c_0_43, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_29]), c_0_32])).
% 0.13/0.40  cnf(c_0_44, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.13/0.40  cnf(c_0_45, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_40, c_0_17])).
% 0.13/0.40  cnf(c_0_46, negated_conjecture, (k2_xboole_0(esk4_0,k4_xboole_0(esk3_0,esk5_0))=esk4_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43])).
% 0.13/0.40  cnf(c_0_47, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_44, c_0_24])).
% 0.13/0.40  cnf(c_0_48, negated_conjecture, (r1_tarski(k4_xboole_0(esk3_0,esk5_0),esk4_0)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.13/0.40  cnf(c_0_49, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_31]), c_0_32])).
% 0.13/0.40  cnf(c_0_50, negated_conjecture, (r1_xboole_0(esk3_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.40  cnf(c_0_51, negated_conjecture, (~r1_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.40  cnf(c_0_52, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50])]), c_0_51]), ['proof']).
% 0.13/0.40  # SZS output end CNFRefutation
% 0.13/0.40  # Proof object total steps             : 53
% 0.13/0.40  # Proof object clause steps            : 28
% 0.13/0.40  # Proof object formula steps           : 25
% 0.13/0.40  # Proof object conjectures             : 13
% 0.13/0.40  # Proof object clause conjectures      : 10
% 0.13/0.40  # Proof object formula conjectures     : 3
% 0.13/0.40  # Proof object initial clauses used    : 14
% 0.13/0.40  # Proof object initial formulas used   : 12
% 0.13/0.40  # Proof object generating inferences   : 10
% 0.13/0.40  # Proof object simplifying inferences  : 12
% 0.13/0.40  # Training examples: 0 positive, 0 negative
% 0.13/0.40  # Parsed axioms                        : 14
% 0.13/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.40  # Initial clauses                      : 20
% 0.13/0.40  # Removed in clause preprocessing      : 1
% 0.13/0.40  # Initial clauses in saturation        : 19
% 0.13/0.40  # Processed clauses                    : 633
% 0.13/0.40  # ...of these trivial                  : 17
% 0.13/0.40  # ...subsumed                          : 431
% 0.13/0.40  # ...remaining for further processing  : 185
% 0.13/0.40  # Other redundant clauses eliminated   : 0
% 0.13/0.40  # Clauses deleted for lack of memory   : 0
% 0.13/0.40  # Backward-subsumed                    : 22
% 0.13/0.40  # Backward-rewritten                   : 15
% 0.13/0.40  # Generated clauses                    : 2229
% 0.13/0.40  # ...of the previous two non-trivial   : 1693
% 0.13/0.40  # Contextual simplify-reflections      : 1
% 0.13/0.40  # Paramodulations                      : 2229
% 0.13/0.40  # Factorizations                       : 0
% 0.13/0.40  # Equation resolutions                 : 0
% 0.13/0.40  # Propositional unsat checks           : 0
% 0.13/0.40  #    Propositional check models        : 0
% 0.13/0.40  #    Propositional check unsatisfiable : 0
% 0.13/0.40  #    Propositional clauses             : 0
% 0.13/0.40  #    Propositional clauses after purity: 0
% 0.13/0.40  #    Propositional unsat core size     : 0
% 0.13/0.40  #    Propositional preprocessing time  : 0.000
% 0.13/0.40  #    Propositional encoding time       : 0.000
% 0.13/0.40  #    Propositional solver time         : 0.000
% 0.13/0.40  #    Success case prop preproc time    : 0.000
% 0.13/0.40  #    Success case prop encoding time   : 0.000
% 0.13/0.40  #    Success case prop solver time     : 0.000
% 0.13/0.40  # Current number of processed clauses  : 129
% 0.13/0.40  #    Positive orientable unit clauses  : 40
% 0.13/0.40  #    Positive unorientable unit clauses: 1
% 0.13/0.40  #    Negative unit clauses             : 3
% 0.13/0.40  #    Non-unit-clauses                  : 85
% 0.13/0.40  # Current number of unprocessed clauses: 1054
% 0.13/0.40  # ...number of literals in the above   : 2219
% 0.13/0.40  # Current number of archived formulas  : 0
% 0.13/0.40  # Current number of archived clauses   : 57
% 0.13/0.40  # Clause-clause subsumption calls (NU) : 2421
% 0.13/0.40  # Rec. Clause-clause subsumption calls : 1966
% 0.13/0.40  # Non-unit clause-clause subsumptions  : 316
% 0.13/0.40  # Unit Clause-clause subsumption calls : 120
% 0.13/0.40  # Rewrite failures with RHS unbound    : 0
% 0.13/0.40  # BW rewrite match attempts            : 73
% 0.13/0.40  # BW rewrite match successes           : 18
% 0.13/0.40  # Condensation attempts                : 0
% 0.13/0.40  # Condensation successes               : 0
% 0.13/0.40  # Termbank termtop insertions          : 23259
% 0.13/0.40  
% 0.13/0.40  # -------------------------------------------------
% 0.13/0.40  # User time                : 0.059 s
% 0.13/0.40  # System time              : 0.003 s
% 0.13/0.40  # Total time               : 0.062 s
% 0.13/0.40  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------

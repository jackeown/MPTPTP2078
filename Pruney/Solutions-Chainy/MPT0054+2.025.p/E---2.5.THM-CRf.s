%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:32:14 EST 2020

% Result     : Theorem 2.91s
% Output     : CNFRefutation 2.91s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 190 expanded)
%              Number of clauses        :   34 (  85 expanded)
%              Number of leaves         :   12 (  52 expanded)
%              Depth                    :   12
%              Number of atoms          :   62 ( 196 expanded)
%              Number of equality atoms :   55 ( 183 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t22_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(t24_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t47_xboole_1,conjecture,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(c_0_12,plain,(
    ! [X37,X38] :
      ( ~ r1_tarski(X37,X38)
      | k3_xboole_0(X37,X38) = X37 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_13,plain,(
    ! [X29,X30] : r1_tarski(k3_xboole_0(X29,X30),X29) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_14,plain,(
    ! [X7,X8] : k3_xboole_0(X7,X8) = k3_xboole_0(X8,X7) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_15,plain,(
    ! [X31] : k2_xboole_0(X31,k1_xboole_0) = X31 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_16,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_17,plain,(
    ! [X46,X47] : k4_xboole_0(X46,k2_xboole_0(X46,X47)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

fof(c_0_18,plain,(
    ! [X43,X44,X45] : k4_xboole_0(k4_xboole_0(X43,X44),X45) = k4_xboole_0(X43,k2_xboole_0(X44,X45)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_19,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_22,plain,(
    ! [X32,X33] : k2_xboole_0(X32,k3_xboole_0(X32,X33)) = X32 ),
    inference(variable_rename,[status(thm)],[t22_xboole_1])).

cnf(c_0_23,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])).

cnf(c_0_28,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

fof(c_0_30,plain,(
    ! [X41,X42] : k4_xboole_0(k2_xboole_0(X41,X42),X42) = k4_xboole_0(X41,X42) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

cnf(c_0_31,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X1),X2) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_32,plain,(
    ! [X34,X35,X36] : k2_xboole_0(X34,k3_xboole_0(X35,X36)) = k3_xboole_0(k2_xboole_0(X34,X35),k2_xboole_0(X34,X36)) ),
    inference(variable_rename,[status(thm)],[t24_xboole_1])).

cnf(c_0_33,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X1)) = k3_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_21])).

cnf(c_0_34,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_35,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_31,c_0_31])).

cnf(c_0_37,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_38,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

fof(c_0_39,plain,(
    ! [X39,X40] : k2_xboole_0(X39,k4_xboole_0(X40,X39)) = k2_xboole_0(X39,X40) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_40,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X1) = k4_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_24])).

cnf(c_0_41,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X2,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_28,c_0_21])).

cnf(c_0_42,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_29]),c_0_36])).

cnf(c_0_43,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_23]),c_0_21]),c_0_38]),c_0_23])).

cnf(c_0_44,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_45,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),X2) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])).

cnf(c_0_46,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_43,c_0_24])).

cnf(c_0_47,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X2,k4_xboole_0(X3,X1))) = k2_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_44]),c_0_37])).

cnf(c_0_48,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,X1)) = k4_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_44])).

cnf(c_0_49,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_26])).

fof(c_0_50,negated_conjecture,(
    ~ ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(assume_negation,[status(cth)],[t47_xboole_1])).

cnf(c_0_51,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X3,k2_xboole_0(X2,X1))) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X3,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_47])).

cnf(c_0_52,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_49]),c_0_23])).

fof(c_0_53,negated_conjecture,(
    k4_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk4_0)) != k4_xboole_0(esk3_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_50])])])).

cnf(c_0_54,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_46]),c_0_24]),c_0_52])).

cnf(c_0_55,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_41])).

cnf(c_0_56,negated_conjecture,
    ( k4_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk4_0)) != k4_xboole_0(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_57,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_54]),c_0_55])).

cnf(c_0_58,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_57])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:17:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 2.91/3.07  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 2.91/3.07  # and selection function SelectNegativeLiterals.
% 2.91/3.07  #
% 2.91/3.07  # Preprocessing time       : 0.027 s
% 2.91/3.07  # Presaturation interreduction done
% 2.91/3.07  
% 2.91/3.07  # Proof found!
% 2.91/3.07  # SZS status Theorem
% 2.91/3.07  # SZS output start CNFRefutation
% 2.91/3.07  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.91/3.07  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.91/3.07  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.91/3.07  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.91/3.07  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.91/3.07  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.91/3.07  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 2.91/3.07  fof(t22_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 2.91/3.07  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 2.91/3.07  fof(t24_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(X1,k3_xboole_0(X2,X3))=k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_xboole_1)).
% 2.91/3.07  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.91/3.07  fof(t47_xboole_1, conjecture, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 2.91/3.07  fof(c_0_12, plain, ![X37, X38]:(~r1_tarski(X37,X38)|k3_xboole_0(X37,X38)=X37), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 2.91/3.07  fof(c_0_13, plain, ![X29, X30]:r1_tarski(k3_xboole_0(X29,X30),X29), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 2.91/3.07  fof(c_0_14, plain, ![X7, X8]:k3_xboole_0(X7,X8)=k3_xboole_0(X8,X7), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 2.91/3.07  fof(c_0_15, plain, ![X31]:k2_xboole_0(X31,k1_xboole_0)=X31, inference(variable_rename,[status(thm)],[t1_boole])).
% 2.91/3.07  fof(c_0_16, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 2.91/3.07  fof(c_0_17, plain, ![X46, X47]:k4_xboole_0(X46,k2_xboole_0(X46,X47))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 2.91/3.07  fof(c_0_18, plain, ![X43, X44, X45]:k4_xboole_0(k4_xboole_0(X43,X44),X45)=k4_xboole_0(X43,k2_xboole_0(X44,X45)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 2.91/3.07  cnf(c_0_19, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 2.91/3.07  cnf(c_0_20, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 2.91/3.07  cnf(c_0_21, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.91/3.07  fof(c_0_22, plain, ![X32, X33]:k2_xboole_0(X32,k3_xboole_0(X32,X33))=X32, inference(variable_rename,[status(thm)],[t22_xboole_1])).
% 2.91/3.07  cnf(c_0_23, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_15])).
% 2.91/3.07  cnf(c_0_24, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 2.91/3.07  cnf(c_0_25, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 2.91/3.07  cnf(c_0_26, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 2.91/3.07  cnf(c_0_27, plain, (k3_xboole_0(X1,k3_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])).
% 2.91/3.07  cnf(c_0_28, plain, (k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_22])).
% 2.91/3.07  cnf(c_0_29, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 2.91/3.07  fof(c_0_30, plain, ![X41, X42]:k4_xboole_0(k2_xboole_0(X41,X42),X42)=k4_xboole_0(X41,X42), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 2.91/3.07  cnf(c_0_31, plain, (k4_xboole_0(k4_xboole_0(X1,X1),X2)=k1_xboole_0), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 2.91/3.07  fof(c_0_32, plain, ![X34, X35, X36]:k2_xboole_0(X34,k3_xboole_0(X35,X36))=k3_xboole_0(k2_xboole_0(X34,X35),k2_xboole_0(X34,X36)), inference(variable_rename,[status(thm)],[t24_xboole_1])).
% 2.91/3.07  cnf(c_0_33, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X1))=k3_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_27, c_0_21])).
% 2.91/3.07  cnf(c_0_34, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 2.91/3.07  cnf(c_0_35, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 2.91/3.07  cnf(c_0_36, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_31, c_0_31])).
% 2.91/3.07  cnf(c_0_37, plain, (k2_xboole_0(X1,k3_xboole_0(X2,X3))=k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 2.91/3.07  cnf(c_0_38, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 2.91/3.07  fof(c_0_39, plain, ![X39, X40]:k2_xboole_0(X39,k4_xboole_0(X40,X39))=k2_xboole_0(X39,X40), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 2.91/3.07  cnf(c_0_40, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X1)=k4_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_35, c_0_24])).
% 2.91/3.07  cnf(c_0_41, plain, (k2_xboole_0(X1,k3_xboole_0(X2,X1))=X1), inference(spm,[status(thm)],[c_0_28, c_0_21])).
% 2.91/3.07  cnf(c_0_42, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_29]), c_0_36])).
% 2.91/3.07  cnf(c_0_43, plain, (k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_23]), c_0_21]), c_0_38]), c_0_23])).
% 2.91/3.07  cnf(c_0_44, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 2.91/3.07  cnf(c_0_45, plain, (k4_xboole_0(k3_xboole_0(X1,X2),X2)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])).
% 2.91/3.07  cnf(c_0_46, plain, (k3_xboole_0(X1,k2_xboole_0(X2,X1))=X1), inference(spm,[status(thm)],[c_0_43, c_0_24])).
% 2.91/3.07  cnf(c_0_47, plain, (k2_xboole_0(X1,k3_xboole_0(X2,k4_xboole_0(X3,X1)))=k2_xboole_0(X1,k3_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_44]), c_0_37])).
% 2.91/3.07  cnf(c_0_48, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,X1))=k4_xboole_0(X1,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_35, c_0_44])).
% 2.91/3.07  cnf(c_0_49, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_26])).
% 2.91/3.07  fof(c_0_50, negated_conjecture, ~(![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(assume_negation,[status(cth)],[t47_xboole_1])).
% 2.91/3.07  cnf(c_0_51, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X3,k2_xboole_0(X2,X1)))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X3,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_47])).
% 2.91/3.07  cnf(c_0_52, plain, (k2_xboole_0(X1,k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_49]), c_0_23])).
% 2.91/3.07  fof(c_0_53, negated_conjecture, k4_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk4_0))!=k4_xboole_0(esk3_0,esk4_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_50])])])).
% 2.91/3.07  cnf(c_0_54, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_46]), c_0_24]), c_0_52])).
% 2.91/3.07  cnf(c_0_55, plain, (k4_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X3,X2))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_26, c_0_41])).
% 2.91/3.07  cnf(c_0_56, negated_conjecture, (k4_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk4_0))!=k4_xboole_0(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 2.91/3.07  cnf(c_0_57, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_54]), c_0_55])).
% 2.91/3.07  cnf(c_0_58, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_57])]), ['proof']).
% 2.91/3.07  # SZS output end CNFRefutation
% 2.91/3.07  # Proof object total steps             : 59
% 2.91/3.07  # Proof object clause steps            : 34
% 2.91/3.07  # Proof object formula steps           : 25
% 2.91/3.07  # Proof object conjectures             : 5
% 2.91/3.07  # Proof object clause conjectures      : 2
% 2.91/3.07  # Proof object formula conjectures     : 3
% 2.91/3.07  # Proof object initial clauses used    : 12
% 2.91/3.07  # Proof object initial formulas used   : 12
% 2.91/3.07  # Proof object generating inferences   : 20
% 2.91/3.07  # Proof object simplifying inferences  : 16
% 2.91/3.07  # Training examples: 0 positive, 0 negative
% 2.91/3.07  # Parsed axioms                        : 16
% 2.91/3.07  # Removed by relevancy pruning/SinE    : 0
% 2.91/3.07  # Initial clauses                      : 24
% 2.91/3.07  # Removed in clause preprocessing      : 0
% 2.91/3.07  # Initial clauses in saturation        : 24
% 2.91/3.07  # Processed clauses                    : 14747
% 2.91/3.07  # ...of these trivial                  : 870
% 2.91/3.07  # ...subsumed                          : 12703
% 2.91/3.07  # ...remaining for further processing  : 1174
% 2.91/3.07  # Other redundant clauses eliminated   : 6482
% 2.91/3.07  # Clauses deleted for lack of memory   : 0
% 2.91/3.07  # Backward-subsumed                    : 11
% 2.91/3.07  # Backward-rewritten                   : 60
% 2.91/3.07  # Generated clauses                    : 430935
% 2.91/3.07  # ...of the previous two non-trivial   : 317250
% 2.91/3.07  # Contextual simplify-reflections      : 3
% 2.91/3.07  # Paramodulations                      : 424436
% 2.91/3.07  # Factorizations                       : 16
% 2.91/3.07  # Equation resolutions                 : 6483
% 2.91/3.07  # Propositional unsat checks           : 0
% 2.91/3.07  #    Propositional check models        : 0
% 2.91/3.07  #    Propositional check unsatisfiable : 0
% 2.91/3.07  #    Propositional clauses             : 0
% 2.91/3.07  #    Propositional clauses after purity: 0
% 2.91/3.07  #    Propositional unsat core size     : 0
% 2.91/3.07  #    Propositional preprocessing time  : 0.000
% 2.91/3.07  #    Propositional encoding time       : 0.000
% 2.91/3.07  #    Propositional solver time         : 0.000
% 2.91/3.07  #    Success case prop preproc time    : 0.000
% 2.91/3.07  #    Success case prop encoding time   : 0.000
% 2.91/3.07  #    Success case prop solver time     : 0.000
% 2.91/3.07  # Current number of processed clauses  : 1076
% 2.91/3.07  #    Positive orientable unit clauses  : 336
% 2.91/3.07  #    Positive unorientable unit clauses: 7
% 2.91/3.07  #    Negative unit clauses             : 28
% 2.91/3.07  #    Non-unit-clauses                  : 705
% 2.91/3.07  # Current number of unprocessed clauses: 302107
% 2.91/3.07  # ...number of literals in the above   : 948065
% 2.91/3.07  # Current number of archived formulas  : 0
% 2.91/3.07  # Current number of archived clauses   : 95
% 2.91/3.07  # Clause-clause subsumption calls (NU) : 47737
% 2.91/3.07  # Rec. Clause-clause subsumption calls : 39137
% 2.91/3.07  # Non-unit clause-clause subsumptions  : 3491
% 2.91/3.07  # Unit Clause-clause subsumption calls : 5984
% 2.91/3.07  # Rewrite failures with RHS unbound    : 0
% 2.91/3.07  # BW rewrite match attempts            : 1669
% 2.91/3.07  # BW rewrite match successes           : 230
% 2.91/3.07  # Condensation attempts                : 0
% 2.91/3.07  # Condensation successes               : 0
% 2.91/3.07  # Termbank termtop insertions          : 6941539
% 2.91/3.09  
% 2.91/3.09  # -------------------------------------------------
% 2.91/3.09  # User time                : 2.617 s
% 2.91/3.09  # System time              : 0.133 s
% 2.91/3.09  # Total time               : 2.750 s
% 2.91/3.09  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------

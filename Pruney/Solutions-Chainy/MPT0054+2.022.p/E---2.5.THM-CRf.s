%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:32:13 EST 2020

% Result     : Theorem 56.78s
% Output     : CNFRefutation 56.78s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 119 expanded)
%              Number of clauses        :   35 (  54 expanded)
%              Number of leaves         :   13 (  32 expanded)
%              Depth                    :   11
%              Number of atoms          :   72 ( 146 expanded)
%              Number of equality atoms :   52 ( 106 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t22_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t16_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t42_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).

fof(t47_xboole_1,conjecture,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(c_0_13,plain,(
    ! [X49,X50] : r1_tarski(X49,k2_xboole_0(X49,X50)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_14,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_15,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_16,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_17,plain,(
    ! [X33,X34] : k2_xboole_0(X33,k3_xboole_0(X33,X34)) = X33 ),
    inference(variable_rename,[status(thm)],[t22_xboole_1])).

fof(c_0_18,plain,(
    ! [X41,X42,X43] : k4_xboole_0(k4_xboole_0(X41,X42),X43) = k4_xboole_0(X41,k2_xboole_0(X42,X43)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

fof(c_0_19,plain,(
    ! [X32] : k2_xboole_0(X32,k1_xboole_0) = X32 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_20,plain,(
    ! [X27,X28] :
      ( ( k4_xboole_0(X27,X28) != k1_xboole_0
        | r1_tarski(X27,X28) )
      & ( ~ r1_tarski(X27,X28)
        | k4_xboole_0(X27,X28) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_22,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_27,plain,(
    ! [X29,X30,X31] : k3_xboole_0(k3_xboole_0(X29,X30),X31) = k3_xboole_0(X29,k3_xboole_0(X30,X31)) ),
    inference(variable_rename,[status(thm)],[t16_xboole_1])).

fof(c_0_28,plain,(
    ! [X35,X36] :
      ( ~ r1_tarski(X35,X36)
      | k3_xboole_0(X35,X36) = X35 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_29,plain,(
    ! [X37,X38] : r1_tarski(k4_xboole_0(X37,X38),X37) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_30,plain,(
    ! [X7,X8] : k3_xboole_0(X7,X8) = k3_xboole_0(X8,X7) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_32,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(k4_xboole_0(X1,X3),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_16]),c_0_23])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_24])).

cnf(c_0_34,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_35,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | k4_xboole_0(k4_xboole_0(X1,X3),X2) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_40,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_25,c_0_33])).

fof(c_0_41,plain,(
    ! [X39,X40] : k2_xboole_0(X39,k4_xboole_0(X40,X39)) = k2_xboole_0(X39,X40) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_42,plain,
    ( k4_xboole_0(k3_xboole_0(X1,k3_xboole_0(X2,X3)),k3_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_43,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38])).

cnf(c_0_44,plain,
    ( r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

fof(c_0_45,plain,(
    ! [X44,X45,X46] : k4_xboole_0(k2_xboole_0(X44,X45),X46) = k2_xboole_0(k4_xboole_0(X44,X46),k4_xboole_0(X45,X46)) ),
    inference(variable_rename,[status(thm)],[t42_xboole_1])).

cnf(c_0_46,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_47,plain,
    ( k4_xboole_0(k3_xboole_0(X1,k4_xboole_0(X2,X3)),k3_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_48,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_44]),c_0_38])).

cnf(c_0_49,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_50,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X2,X3)) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_22])).

cnf(c_0_51,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_25,c_0_37])).

fof(c_0_52,negated_conjecture,(
    ~ ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(assume_negation,[status(cth)],[t47_xboole_1])).

cnf(c_0_53,plain,
    ( k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X1),X3)) = k2_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_32])).

cnf(c_0_54,plain,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k3_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_55,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,k3_xboole_0(X2,X4))) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X3),k3_xboole_0(X2,X4)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_56,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_51]),c_0_24])).

fof(c_0_57,negated_conjecture,(
    k4_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk4_0)) != k4_xboole_0(esk3_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_52])])])).

cnf(c_0_58,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X2,X1)) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_24]),c_0_55]),c_0_16]),c_0_56])).

cnf(c_0_59,negated_conjecture,
    ( k4_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk4_0)) != k4_xboole_0(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_60,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_58,c_0_38])).

cnf(c_0_61,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_60])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:25:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 56.78/57.02  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 56.78/57.02  # and selection function SelectNegativeLiterals.
% 56.78/57.02  #
% 56.78/57.02  # Preprocessing time       : 0.042 s
% 56.78/57.02  # Presaturation interreduction done
% 56.78/57.02  
% 56.78/57.02  # Proof found!
% 56.78/57.02  # SZS status Theorem
% 56.78/57.02  # SZS output start CNFRefutation
% 56.78/57.02  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 56.78/57.02  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 56.78/57.02  fof(t22_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 56.78/57.02  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 56.78/57.02  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 56.78/57.02  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 56.78/57.02  fof(t16_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 56.78/57.02  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 56.78/57.02  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 56.78/57.02  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 56.78/57.02  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 56.78/57.02  fof(t42_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_xboole_1)).
% 56.78/57.02  fof(t47_xboole_1, conjecture, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 56.78/57.02  fof(c_0_13, plain, ![X49, X50]:r1_tarski(X49,k2_xboole_0(X49,X50)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 56.78/57.02  fof(c_0_14, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 56.78/57.02  cnf(c_0_15, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 56.78/57.02  cnf(c_0_16, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 56.78/57.02  fof(c_0_17, plain, ![X33, X34]:k2_xboole_0(X33,k3_xboole_0(X33,X34))=X33, inference(variable_rename,[status(thm)],[t22_xboole_1])).
% 56.78/57.02  fof(c_0_18, plain, ![X41, X42, X43]:k4_xboole_0(k4_xboole_0(X41,X42),X43)=k4_xboole_0(X41,k2_xboole_0(X42,X43)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 56.78/57.02  fof(c_0_19, plain, ![X32]:k2_xboole_0(X32,k1_xboole_0)=X32, inference(variable_rename,[status(thm)],[t1_boole])).
% 56.78/57.02  fof(c_0_20, plain, ![X27, X28]:((k4_xboole_0(X27,X28)!=k1_xboole_0|r1_tarski(X27,X28))&(~r1_tarski(X27,X28)|k4_xboole_0(X27,X28)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 56.78/57.02  cnf(c_0_21, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 56.78/57.02  cnf(c_0_22, plain, (k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_17])).
% 56.78/57.02  cnf(c_0_23, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 56.78/57.02  cnf(c_0_24, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_19])).
% 56.78/57.02  cnf(c_0_25, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 56.78/57.02  cnf(c_0_26, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 56.78/57.02  fof(c_0_27, plain, ![X29, X30, X31]:k3_xboole_0(k3_xboole_0(X29,X30),X31)=k3_xboole_0(X29,k3_xboole_0(X30,X31)), inference(variable_rename,[status(thm)],[t16_xboole_1])).
% 56.78/57.02  fof(c_0_28, plain, ![X35, X36]:(~r1_tarski(X35,X36)|k3_xboole_0(X35,X36)=X35), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 56.78/57.02  fof(c_0_29, plain, ![X37, X38]:r1_tarski(k4_xboole_0(X37,X38),X37), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 56.78/57.02  fof(c_0_30, plain, ![X7, X8]:k3_xboole_0(X7,X8)=k3_xboole_0(X8,X7), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 56.78/57.02  cnf(c_0_31, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 56.78/57.02  cnf(c_0_32, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(k4_xboole_0(X1,X3),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_16]), c_0_23])).
% 56.78/57.02  cnf(c_0_33, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_15, c_0_24])).
% 56.78/57.02  cnf(c_0_34, plain, (k4_xboole_0(k3_xboole_0(X1,X2),X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 56.78/57.02  cnf(c_0_35, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 56.78/57.02  cnf(c_0_36, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 56.78/57.02  cnf(c_0_37, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 56.78/57.02  cnf(c_0_38, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 56.78/57.02  cnf(c_0_39, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|k4_xboole_0(k4_xboole_0(X1,X3),X2)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 56.78/57.02  cnf(c_0_40, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_25, c_0_33])).
% 56.78/57.02  fof(c_0_41, plain, ![X39, X40]:k2_xboole_0(X39,k4_xboole_0(X40,X39))=k2_xboole_0(X39,X40), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 56.78/57.02  cnf(c_0_42, plain, (k4_xboole_0(k3_xboole_0(X1,k3_xboole_0(X2,X3)),k3_xboole_0(X1,X2))=k1_xboole_0), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 56.78/57.02  cnf(c_0_43, plain, (k3_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38])).
% 56.78/57.02  cnf(c_0_44, plain, (r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 56.78/57.02  fof(c_0_45, plain, ![X44, X45, X46]:k4_xboole_0(k2_xboole_0(X44,X45),X46)=k2_xboole_0(k4_xboole_0(X44,X46),k4_xboole_0(X45,X46)), inference(variable_rename,[status(thm)],[t42_xboole_1])).
% 56.78/57.02  cnf(c_0_46, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 56.78/57.02  cnf(c_0_47, plain, (k4_xboole_0(k3_xboole_0(X1,k4_xboole_0(X2,X3)),k3_xboole_0(X1,X2))=k1_xboole_0), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 56.78/57.02  cnf(c_0_48, plain, (k3_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_44]), c_0_38])).
% 56.78/57.02  cnf(c_0_49, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 56.78/57.02  cnf(c_0_50, plain, (k4_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X2,X3))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_23, c_0_22])).
% 56.78/57.02  cnf(c_0_51, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_25, c_0_37])).
% 56.78/57.02  fof(c_0_52, negated_conjecture, ~(![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(assume_negation,[status(cth)],[t47_xboole_1])).
% 56.78/57.02  cnf(c_0_53, plain, (k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X1),X3))=k2_xboole_0(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_46, c_0_32])).
% 56.78/57.02  cnf(c_0_54, plain, (k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k3_xboole_0(X2,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 56.78/57.02  cnf(c_0_55, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,k3_xboole_0(X2,X4)))=k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X3),k3_xboole_0(X2,X4))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 56.78/57.02  cnf(c_0_56, plain, (k2_xboole_0(X1,k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_51]), c_0_24])).
% 56.78/57.02  fof(c_0_57, negated_conjecture, k4_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk4_0))!=k4_xboole_0(esk3_0,esk4_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_52])])])).
% 56.78/57.02  cnf(c_0_58, plain, (k4_xboole_0(X1,k3_xboole_0(X2,X1))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_24]), c_0_55]), c_0_16]), c_0_56])).
% 56.78/57.02  cnf(c_0_59, negated_conjecture, (k4_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk4_0))!=k4_xboole_0(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 56.78/57.02  cnf(c_0_60, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_58, c_0_38])).
% 56.78/57.02  cnf(c_0_61, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_60])]), ['proof']).
% 56.78/57.02  # SZS output end CNFRefutation
% 56.78/57.02  # Proof object total steps             : 62
% 56.78/57.02  # Proof object clause steps            : 35
% 56.78/57.02  # Proof object formula steps           : 27
% 56.78/57.02  # Proof object conjectures             : 5
% 56.78/57.02  # Proof object clause conjectures      : 2
% 56.78/57.02  # Proof object formula conjectures     : 3
% 56.78/57.02  # Proof object initial clauses used    : 14
% 56.78/57.02  # Proof object initial formulas used   : 13
% 56.78/57.02  # Proof object generating inferences   : 20
% 56.78/57.02  # Proof object simplifying inferences  : 10
% 56.78/57.02  # Training examples: 0 positive, 0 negative
% 56.78/57.02  # Parsed axioms                        : 18
% 56.78/57.02  # Removed by relevancy pruning/SinE    : 0
% 56.78/57.02  # Initial clauses                      : 27
% 56.78/57.02  # Removed in clause preprocessing      : 0
% 56.78/57.02  # Initial clauses in saturation        : 27
% 56.78/57.02  # Processed clauses                    : 42269
% 56.78/57.02  # ...of these trivial                  : 1846
% 56.78/57.02  # ...subsumed                          : 37334
% 56.78/57.02  # ...remaining for further processing  : 3089
% 56.78/57.02  # Other redundant clauses eliminated   : 57503
% 56.78/57.02  # Clauses deleted for lack of memory   : 97835
% 56.78/57.02  # Backward-subsumed                    : 33
% 56.78/57.02  # Backward-rewritten                   : 184
% 56.78/57.02  # Generated clauses                    : 4937447
% 56.78/57.02  # ...of the previous two non-trivial   : 4328965
% 56.78/57.02  # Contextual simplify-reflections      : 31
% 56.78/57.02  # Paramodulations                      : 4879562
% 56.78/57.02  # Factorizations                       : 378
% 56.78/57.02  # Equation resolutions                 : 57507
% 56.78/57.02  # Propositional unsat checks           : 0
% 56.78/57.02  #    Propositional check models        : 0
% 56.78/57.02  #    Propositional check unsatisfiable : 0
% 56.78/57.02  #    Propositional clauses             : 0
% 56.78/57.02  #    Propositional clauses after purity: 0
% 56.78/57.02  #    Propositional unsat core size     : 0
% 56.78/57.02  #    Propositional preprocessing time  : 0.000
% 56.78/57.02  #    Propositional encoding time       : 0.000
% 56.78/57.02  #    Propositional solver time         : 0.000
% 56.78/57.02  #    Success case prop preproc time    : 0.000
% 56.78/57.02  #    Success case prop encoding time   : 0.000
% 56.78/57.02  #    Success case prop solver time     : 0.000
% 56.78/57.02  # Current number of processed clauses  : 2842
% 56.78/57.02  #    Positive orientable unit clauses  : 462
% 56.78/57.02  #    Positive unorientable unit clauses: 19
% 56.78/57.02  #    Negative unit clauses             : 63
% 56.78/57.02  #    Non-unit-clauses                  : 2298
% 56.78/57.02  # Current number of unprocessed clauses: 1087620
% 56.78/57.02  # ...number of literals in the above   : 3278773
% 56.78/57.02  # Current number of archived formulas  : 0
% 56.78/57.02  # Current number of archived clauses   : 244
% 56.78/57.02  # Clause-clause subsumption calls (NU) : 496566
% 56.78/57.02  # Rec. Clause-clause subsumption calls : 204456
% 56.78/57.02  # Non-unit clause-clause subsumptions  : 12571
% 56.78/57.02  # Unit Clause-clause subsumption calls : 36624
% 56.78/57.02  # Rewrite failures with RHS unbound    : 0
% 56.78/57.02  # BW rewrite match attempts            : 2226
% 56.78/57.02  # BW rewrite match successes           : 294
% 56.78/57.02  # Condensation attempts                : 0
% 56.78/57.02  # Condensation successes               : 0
% 56.78/57.02  # Termbank termtop insertions          : 116457259
% 56.87/57.10  
% 56.87/57.10  # -------------------------------------------------
% 56.87/57.10  # User time                : 55.512 s
% 56.87/57.10  # System time              : 1.212 s
% 56.87/57.10  # Total time               : 56.724 s
% 56.87/57.10  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------

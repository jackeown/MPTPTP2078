%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:34:39 EST 2020

% Result     : Theorem 0.48s
% Output     : CNFRefutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 232 expanded)
%              Number of clauses        :   35 ( 103 expanded)
%              Number of leaves         :   13 (  62 expanded)
%              Depth                    :   11
%              Number of atoms          :   86 ( 307 expanded)
%              Number of equality atoms :   48 ( 192 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t106_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k4_xboole_0(X2,X3))
     => ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t50_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_xboole_1)).

fof(t16_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_tarski(X1,k4_xboole_0(X2,X3))
       => ( r1_tarski(X1,X2)
          & r1_xboole_0(X1,X3) ) ) ),
    inference(assume_negation,[status(cth)],[t106_xboole_1])).

fof(c_0_14,negated_conjecture,
    ( r1_tarski(esk1_0,k4_xboole_0(esk2_0,esk3_0))
    & ( ~ r1_tarski(esk1_0,esk2_0)
      | ~ r1_xboole_0(esk1_0,esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

fof(c_0_15,plain,(
    ! [X10,X11] : k4_xboole_0(X10,X11) = k5_xboole_0(X10,k3_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_16,plain,(
    ! [X17,X18] :
      ( ~ r1_tarski(X17,X18)
      | k3_xboole_0(X17,X18) = X17 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_17,negated_conjecture,
    ( r1_tarski(esk1_0,k4_xboole_0(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,plain,(
    ! [X15,X16] : r1_tarski(k3_xboole_0(X15,X16),X15) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_20,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( r1_tarski(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0))) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

fof(c_0_22,plain,(
    ! [X21,X22,X23] : k3_xboole_0(X21,k4_xboole_0(X22,X23)) = k4_xboole_0(k3_xboole_0(X21,X22),k3_xboole_0(X21,X23)) ),
    inference(variable_rename,[status(thm)],[t50_xboole_1])).

cnf(c_0_23,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0))) = esk1_0 ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_26,plain,(
    ! [X12,X13,X14] : k3_xboole_0(k3_xboole_0(X12,X13),X14) = k3_xboole_0(X12,k3_xboole_0(X13,X14)) ),
    inference(variable_rename,[status(thm)],[t16_xboole_1])).

fof(c_0_27,plain,(
    ! [X24,X25] : r1_xboole_0(k4_xboole_0(X24,X25),X25) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

fof(c_0_28,plain,(
    ! [X20] : k4_xboole_0(X20,k1_xboole_0) = X20 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(esk1_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_30,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) = k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_18]),c_0_18])).

cnf(c_0_31,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_32,plain,(
    ! [X26] : k5_xboole_0(X26,X26) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

fof(c_0_33,plain,(
    ! [X6,X7] :
      ( ( ~ r1_xboole_0(X6,X7)
        | k3_xboole_0(X6,X7) = k1_xboole_0 )
      & ( k3_xboole_0(X6,X7) != k1_xboole_0
        | r1_xboole_0(X6,X7) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_34,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_35,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_36,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_37,plain,(
    ! [X19] : k3_xboole_0(X19,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_38,plain,(
    ! [X8,X9] :
      ( ( k4_xboole_0(X8,X9) != k1_xboole_0
        | r1_tarski(X8,X9) )
      & ( ~ r1_tarski(X8,X9)
        | k4_xboole_0(X8,X9) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_39,negated_conjecture,
    ( k3_xboole_0(esk1_0,esk1_0) = esk1_0 ),
    inference(spm,[status(thm)],[c_0_20,c_0_29])).

cnf(c_0_40,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X1,X3)))) = k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_41,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X1)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_23]),c_0_31])).

cnf(c_0_42,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_43,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_44,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2) ),
    inference(rw,[status(thm)],[c_0_34,c_0_18])).

cnf(c_0_45,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_46,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[c_0_36,c_0_18])).

cnf(c_0_47,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_49,negated_conjecture,
    ( k3_xboole_0(esk1_0,k3_xboole_0(esk1_0,X1)) = k3_xboole_0(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_39])).

cnf(c_0_50,negated_conjecture,
    ( ~ r1_tarski(esk1_0,esk2_0)
    | ~ r1_xboole_0(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_51,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_52,negated_conjecture,
    ( k3_xboole_0(esk1_0,k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0))))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_24]),c_0_41]),c_0_42])).

cnf(c_0_53,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])).

cnf(c_0_54,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_55,plain,
    ( r1_tarski(X1,X2)
    | k5_xboole_0(X1,k3_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_48,c_0_18])).

cnf(c_0_56,negated_conjecture,
    ( k3_xboole_0(esk1_0,k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(esk1_0,X2)))) = k3_xboole_0(esk1_0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_49]),c_0_40])).

cnf(c_0_57,negated_conjecture,
    ( k3_xboole_0(esk1_0,esk3_0) != k1_xboole_0
    | ~ r1_tarski(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_58,negated_conjecture,
    ( k3_xboole_0(esk1_0,esk3_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(esk1_0,k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(esk1_0,X2))))
    | k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_60,negated_conjecture,
    ( ~ r1_tarski(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_58])])).

cnf(c_0_61,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_24]),c_0_58]),c_0_47]),c_0_54]),c_0_42])]),c_0_60]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n019.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:52:52 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.33  # No SInE strategy applied
% 0.13/0.33  # Trying AutoSched0 for 299 seconds
% 0.48/0.68  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.48/0.68  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.48/0.68  #
% 0.48/0.68  # Preprocessing time       : 0.025 s
% 0.48/0.68  # Presaturation interreduction done
% 0.48/0.68  
% 0.48/0.68  # Proof found!
% 0.48/0.68  # SZS status Theorem
% 0.48/0.68  # SZS output start CNFRefutation
% 0.48/0.68  fof(t106_xboole_1, conjecture, ![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 0.48/0.68  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.48/0.68  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.48/0.68  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.48/0.68  fof(t50_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_xboole_1)).
% 0.48/0.68  fof(t16_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 0.48/0.68  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.48/0.68  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 0.48/0.68  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.48/0.68  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.48/0.68  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.48/0.68  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 0.48/0.68  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.48/0.68  fof(c_0_13, negated_conjecture, ~(![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3)))), inference(assume_negation,[status(cth)],[t106_xboole_1])).
% 0.48/0.68  fof(c_0_14, negated_conjecture, (r1_tarski(esk1_0,k4_xboole_0(esk2_0,esk3_0))&(~r1_tarski(esk1_0,esk2_0)|~r1_xboole_0(esk1_0,esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.48/0.68  fof(c_0_15, plain, ![X10, X11]:k4_xboole_0(X10,X11)=k5_xboole_0(X10,k3_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.48/0.68  fof(c_0_16, plain, ![X17, X18]:(~r1_tarski(X17,X18)|k3_xboole_0(X17,X18)=X17), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.48/0.68  cnf(c_0_17, negated_conjecture, (r1_tarski(esk1_0,k4_xboole_0(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.48/0.68  cnf(c_0_18, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.48/0.68  fof(c_0_19, plain, ![X15, X16]:r1_tarski(k3_xboole_0(X15,X16),X15), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.48/0.68  cnf(c_0_20, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.48/0.68  cnf(c_0_21, negated_conjecture, (r1_tarski(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0)))), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.48/0.68  fof(c_0_22, plain, ![X21, X22, X23]:k3_xboole_0(X21,k4_xboole_0(X22,X23))=k4_xboole_0(k3_xboole_0(X21,X22),k3_xboole_0(X21,X23)), inference(variable_rename,[status(thm)],[t50_xboole_1])).
% 0.48/0.68  cnf(c_0_23, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.48/0.68  cnf(c_0_24, negated_conjecture, (k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0)))=esk1_0), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.48/0.68  cnf(c_0_25, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.48/0.68  fof(c_0_26, plain, ![X12, X13, X14]:k3_xboole_0(k3_xboole_0(X12,X13),X14)=k3_xboole_0(X12,k3_xboole_0(X13,X14)), inference(variable_rename,[status(thm)],[t16_xboole_1])).
% 0.48/0.68  fof(c_0_27, plain, ![X24, X25]:r1_xboole_0(k4_xboole_0(X24,X25),X25), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.48/0.68  fof(c_0_28, plain, ![X20]:k4_xboole_0(X20,k1_xboole_0)=X20, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.48/0.68  cnf(c_0_29, negated_conjecture, (r1_tarski(esk1_0,esk1_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.48/0.68  cnf(c_0_30, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))=k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_18]), c_0_18])).
% 0.48/0.68  cnf(c_0_31, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.48/0.68  fof(c_0_32, plain, ![X26]:k5_xboole_0(X26,X26)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.48/0.68  fof(c_0_33, plain, ![X6, X7]:((~r1_xboole_0(X6,X7)|k3_xboole_0(X6,X7)=k1_xboole_0)&(k3_xboole_0(X6,X7)!=k1_xboole_0|r1_xboole_0(X6,X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.48/0.68  cnf(c_0_34, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.48/0.68  fof(c_0_35, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.48/0.68  cnf(c_0_36, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.48/0.68  fof(c_0_37, plain, ![X19]:k3_xboole_0(X19,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.48/0.68  fof(c_0_38, plain, ![X8, X9]:((k4_xboole_0(X8,X9)!=k1_xboole_0|r1_tarski(X8,X9))&(~r1_tarski(X8,X9)|k4_xboole_0(X8,X9)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.48/0.68  cnf(c_0_39, negated_conjecture, (k3_xboole_0(esk1_0,esk1_0)=esk1_0), inference(spm,[status(thm)],[c_0_20, c_0_29])).
% 0.48/0.68  cnf(c_0_40, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X1,X3))))=k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_30, c_0_31])).
% 0.48/0.68  cnf(c_0_41, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X1))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_23]), c_0_31])).
% 0.48/0.68  cnf(c_0_42, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.48/0.68  cnf(c_0_43, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.48/0.68  cnf(c_0_44, plain, (r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2)), inference(rw,[status(thm)],[c_0_34, c_0_18])).
% 0.48/0.68  cnf(c_0_45, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.48/0.68  cnf(c_0_46, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[c_0_36, c_0_18])).
% 0.48/0.68  cnf(c_0_47, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.48/0.68  cnf(c_0_48, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.48/0.68  cnf(c_0_49, negated_conjecture, (k3_xboole_0(esk1_0,k3_xboole_0(esk1_0,X1))=k3_xboole_0(esk1_0,X1)), inference(spm,[status(thm)],[c_0_31, c_0_39])).
% 0.48/0.68  cnf(c_0_50, negated_conjecture, (~r1_tarski(esk1_0,esk2_0)|~r1_xboole_0(esk1_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.48/0.68  cnf(c_0_51, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.48/0.68  cnf(c_0_52, negated_conjecture, (k3_xboole_0(esk1_0,k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0)))))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_24]), c_0_41]), c_0_42])).
% 0.48/0.68  cnf(c_0_53, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45])).
% 0.48/0.68  cnf(c_0_54, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_46, c_0_47])).
% 0.48/0.68  cnf(c_0_55, plain, (r1_tarski(X1,X2)|k5_xboole_0(X1,k3_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_48, c_0_18])).
% 0.48/0.68  cnf(c_0_56, negated_conjecture, (k3_xboole_0(esk1_0,k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(esk1_0,X2))))=k3_xboole_0(esk1_0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_49]), c_0_40])).
% 0.48/0.68  cnf(c_0_57, negated_conjecture, (k3_xboole_0(esk1_0,esk3_0)!=k1_xboole_0|~r1_tarski(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.48/0.68  cnf(c_0_58, negated_conjecture, (k3_xboole_0(esk1_0,esk3_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54])).
% 0.48/0.68  cnf(c_0_59, negated_conjecture, (r1_tarski(esk1_0,k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(esk1_0,X2))))|k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,k5_xboole_0(X1,k3_xboole_0(X1,X2))))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.48/0.68  cnf(c_0_60, negated_conjecture, (~r1_tarski(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_58])])).
% 0.48/0.68  cnf(c_0_61, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_24]), c_0_58]), c_0_47]), c_0_54]), c_0_42])]), c_0_60]), ['proof']).
% 0.48/0.68  # SZS output end CNFRefutation
% 0.48/0.68  # Proof object total steps             : 62
% 0.48/0.68  # Proof object clause steps            : 35
% 0.48/0.68  # Proof object formula steps           : 27
% 0.48/0.68  # Proof object conjectures             : 17
% 0.48/0.68  # Proof object clause conjectures      : 14
% 0.48/0.68  # Proof object formula conjectures     : 3
% 0.48/0.68  # Proof object initial clauses used    : 15
% 0.48/0.68  # Proof object initial formulas used   : 13
% 0.48/0.68  # Proof object generating inferences   : 12
% 0.48/0.68  # Proof object simplifying inferences  : 22
% 0.48/0.68  # Training examples: 0 positive, 0 negative
% 0.48/0.68  # Parsed axioms                        : 13
% 0.48/0.68  # Removed by relevancy pruning/SinE    : 0
% 0.48/0.68  # Initial clauses                      : 16
% 0.48/0.68  # Removed in clause preprocessing      : 1
% 0.48/0.68  # Initial clauses in saturation        : 15
% 0.48/0.68  # Processed clauses                    : 6276
% 0.48/0.68  # ...of these trivial                  : 312
% 0.48/0.68  # ...subsumed                          : 5343
% 0.48/0.68  # ...remaining for further processing  : 621
% 0.48/0.68  # Other redundant clauses eliminated   : 185
% 0.48/0.68  # Clauses deleted for lack of memory   : 0
% 0.48/0.68  # Backward-subsumed                    : 16
% 0.48/0.68  # Backward-rewritten                   : 30
% 0.48/0.68  # Generated clauses                    : 35640
% 0.48/0.68  # ...of the previous two non-trivial   : 25025
% 0.48/0.68  # Contextual simplify-reflections      : 3
% 0.48/0.68  # Paramodulations                      : 35455
% 0.48/0.68  # Factorizations                       : 0
% 0.48/0.68  # Equation resolutions                 : 185
% 0.48/0.68  # Propositional unsat checks           : 0
% 0.48/0.68  #    Propositional check models        : 0
% 0.48/0.68  #    Propositional check unsatisfiable : 0
% 0.48/0.68  #    Propositional clauses             : 0
% 0.48/0.68  #    Propositional clauses after purity: 0
% 0.48/0.68  #    Propositional unsat core size     : 0
% 0.48/0.68  #    Propositional preprocessing time  : 0.000
% 0.48/0.68  #    Propositional encoding time       : 0.000
% 0.48/0.68  #    Propositional solver time         : 0.000
% 0.48/0.68  #    Success case prop preproc time    : 0.000
% 0.48/0.68  #    Success case prop encoding time   : 0.000
% 0.48/0.68  #    Success case prop solver time     : 0.000
% 0.48/0.68  # Current number of processed clauses  : 560
% 0.48/0.68  #    Positive orientable unit clauses  : 185
% 0.48/0.68  #    Positive unorientable unit clauses: 4
% 0.48/0.68  #    Negative unit clauses             : 77
% 0.48/0.68  #    Non-unit-clauses                  : 294
% 0.48/0.68  # Current number of unprocessed clauses: 18006
% 0.48/0.68  # ...number of literals in the above   : 29536
% 0.48/0.68  # Current number of archived formulas  : 0
% 0.48/0.68  # Current number of archived clauses   : 62
% 0.48/0.68  # Clause-clause subsumption calls (NU) : 13189
% 0.48/0.68  # Rec. Clause-clause subsumption calls : 13189
% 0.48/0.68  # Non-unit clause-clause subsumptions  : 1512
% 0.48/0.68  # Unit Clause-clause subsumption calls : 1124
% 0.48/0.68  # Rewrite failures with RHS unbound    : 0
% 0.48/0.68  # BW rewrite match attempts            : 490
% 0.48/0.68  # BW rewrite match successes           : 144
% 0.48/0.68  # Condensation attempts                : 0
% 0.48/0.68  # Condensation successes               : 0
% 0.48/0.68  # Termbank termtop insertions          : 516449
% 0.48/0.68  
% 0.48/0.68  # -------------------------------------------------
% 0.48/0.68  # User time                : 0.335 s
% 0.48/0.68  # System time              : 0.017 s
% 0.48/0.68  # Total time               : 0.353 s
% 0.48/0.68  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------

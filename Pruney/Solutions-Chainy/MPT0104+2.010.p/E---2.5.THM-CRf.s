%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:34:08 EST 2020

% Result     : Theorem 0.50s
% Output     : CNFRefutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 209 expanded)
%              Number of clauses        :   35 (  96 expanded)
%              Number of leaves         :   10 (  55 expanded)
%              Depth                    :   10
%              Number of atoms          :   68 ( 242 expanded)
%              Number of equality atoms :   46 ( 195 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(l98_xboole_1,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t97_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(k4_xboole_0(X1,X2),X3)
        & r1_tarski(k4_xboole_0(X2,X1),X3) )
     => r1_tarski(k5_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_xboole_1)).

fof(t42_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t55_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_xboole_1)).

fof(c_0_10,plain,(
    ! [X8] : k4_xboole_0(X8,k1_xboole_0) = X8 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_11,plain,(
    ! [X9,X10,X11] : k4_xboole_0(k4_xboole_0(X9,X10),X11) = k4_xboole_0(X9,k2_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

fof(c_0_12,plain,(
    ! [X15,X16] : k4_xboole_0(X15,k2_xboole_0(X15,X16)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

cnf(c_0_13,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k1_xboole_0)) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

fof(c_0_17,plain,(
    ! [X6,X7] : k5_xboole_0(X6,X7) = k4_xboole_0(k2_xboole_0(X6,X7),k3_xboole_0(X6,X7)) ),
    inference(variable_rename,[status(thm)],[l98_xboole_1])).

fof(c_0_18,plain,(
    ! [X17,X18] : k4_xboole_0(X17,k4_xboole_0(X17,X18)) = k3_xboole_0(X17,X18) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( r1_tarski(k4_xboole_0(X1,X2),X3)
          & r1_tarski(k4_xboole_0(X2,X1),X3) )
       => r1_tarski(k5_xboole_0(X1,X2),X3) ) ),
    inference(assume_negation,[status(cth)],[t97_xboole_1])).

fof(c_0_20,plain,(
    ! [X12,X13,X14] : k4_xboole_0(k2_xboole_0(X12,X13),X14) = k2_xboole_0(k4_xboole_0(X12,X14),k4_xboole_0(X13,X14)) ),
    inference(variable_rename,[status(thm)],[t42_xboole_1])).

cnf(c_0_21,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_22,plain,(
    ! [X21] : k5_xboole_0(X21,k1_xboole_0) = X21 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

cnf(c_0_23,plain,
    ( k5_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_25,plain,(
    ! [X4,X5] :
      ( ( k4_xboole_0(X4,X5) != k1_xboole_0
        | r1_tarski(X4,X5) )
      & ( ~ r1_tarski(X4,X5)
        | k4_xboole_0(X4,X5) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_26,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk1_0,esk2_0),esk3_0)
    & r1_tarski(k4_xboole_0(esk2_0,esk1_0),esk3_0)
    & ~ r1_tarski(k5_xboole_0(esk1_0,esk2_0),esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

cnf(c_0_27,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_21]),c_0_15])).

cnf(c_0_29,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( k5_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_31,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk1_0,esk2_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,plain,
    ( k4_xboole_0(k2_xboole_0(X1,k1_xboole_0),k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))) = X1 ),
    inference(rw,[status(thm)],[c_0_29,c_0_30])).

fof(c_0_35,plain,(
    ! [X19,X20] : k4_xboole_0(k2_xboole_0(X19,X20),k3_xboole_0(X19,X20)) = k2_xboole_0(k4_xboole_0(X19,X20),k4_xboole_0(X20,X19)) ),
    inference(variable_rename,[status(thm)],[t55_xboole_1])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_14,c_0_21])).

cnf(c_0_38,plain,
    ( k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k4_xboole_0(X4,X3)) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X4),X3) ),
    inference(spm,[status(thm)],[c_0_27,c_0_14])).

cnf(c_0_39,negated_conjecture,
    ( k4_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_14])).

cnf(c_0_40,plain,
    ( k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),X2) = k4_xboole_0(k2_xboole_0(X2,X1),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_21]),c_0_33])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk2_0,esk1_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_42,plain,
    ( k4_xboole_0(k2_xboole_0(X1,k1_xboole_0),k4_xboole_0(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_34,c_0_13])).

cnf(c_0_43,negated_conjecture,
    ( ~ r1_tarski(k5_xboole_0(esk1_0,esk2_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_44,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_46,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),X1),esk3_0) = k4_xboole_0(k2_xboole_0(esk3_0,X1),esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_33]),c_0_40])).

cnf(c_0_47,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,k2_xboole_0(X4,X2))) = k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(X3,X4)),X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_14])).

cnf(c_0_48,negated_conjecture,
    ( k4_xboole_0(esk2_0,k2_xboole_0(esk1_0,esk3_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_41]),c_0_14])).

cnf(c_0_49,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_21]),c_0_13])).

cnf(c_0_50,negated_conjecture,
    ( ~ r1_tarski(k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0))),esk3_0) ),
    inference(rw,[status(thm)],[c_0_43,c_0_30])).

cnf(c_0_51,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_44,c_0_24])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),X1),k2_xboole_0(esk3_0,k4_xboole_0(k2_xboole_0(esk3_0,X1),esk3_0))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_53,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(esk2_0,esk1_0)),esk3_0) = k4_xboole_0(X1,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk2_0,esk1_0)),esk3_0) ),
    inference(rw,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_55,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_21]),c_0_49]),c_0_54]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n005.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:30:17 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.50/0.67  # AutoSched0-Mode selected heuristic G_____Y1346__C12_02_nc_F1_AE_CS_SP_S2S
% 0.50/0.67  # and selection function SelectNewComplexAHP.
% 0.50/0.67  #
% 0.50/0.67  # Preprocessing time       : 0.027 s
% 0.50/0.67  # Presaturation interreduction done
% 0.50/0.67  
% 0.50/0.67  # Proof found!
% 0.50/0.67  # SZS status Theorem
% 0.50/0.67  # SZS output start CNFRefutation
% 0.50/0.67  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.50/0.67  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.50/0.67  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 0.50/0.67  fof(l98_xboole_1, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l98_xboole_1)).
% 0.50/0.67  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.50/0.67  fof(t97_xboole_1, conjecture, ![X1, X2, X3]:((r1_tarski(k4_xboole_0(X1,X2),X3)&r1_tarski(k4_xboole_0(X2,X1),X3))=>r1_tarski(k5_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_xboole_1)).
% 0.50/0.67  fof(t42_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_xboole_1)).
% 0.50/0.67  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 0.50/0.67  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.50/0.67  fof(t55_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_xboole_1)).
% 0.50/0.67  fof(c_0_10, plain, ![X8]:k4_xboole_0(X8,k1_xboole_0)=X8, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.50/0.67  fof(c_0_11, plain, ![X9, X10, X11]:k4_xboole_0(k4_xboole_0(X9,X10),X11)=k4_xboole_0(X9,k2_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.50/0.67  fof(c_0_12, plain, ![X15, X16]:k4_xboole_0(X15,k2_xboole_0(X15,X16))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 0.50/0.67  cnf(c_0_13, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.50/0.67  cnf(c_0_14, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.50/0.67  cnf(c_0_15, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.50/0.67  cnf(c_0_16, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k1_xboole_0))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.50/0.67  fof(c_0_17, plain, ![X6, X7]:k5_xboole_0(X6,X7)=k4_xboole_0(k2_xboole_0(X6,X7),k3_xboole_0(X6,X7)), inference(variable_rename,[status(thm)],[l98_xboole_1])).
% 0.50/0.67  fof(c_0_18, plain, ![X17, X18]:k4_xboole_0(X17,k4_xboole_0(X17,X18))=k3_xboole_0(X17,X18), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.50/0.67  fof(c_0_19, negated_conjecture, ~(![X1, X2, X3]:((r1_tarski(k4_xboole_0(X1,X2),X3)&r1_tarski(k4_xboole_0(X2,X1),X3))=>r1_tarski(k5_xboole_0(X1,X2),X3))), inference(assume_negation,[status(cth)],[t97_xboole_1])).
% 0.50/0.67  fof(c_0_20, plain, ![X12, X13, X14]:k4_xboole_0(k2_xboole_0(X12,X13),X14)=k2_xboole_0(k4_xboole_0(X12,X14),k4_xboole_0(X13,X14)), inference(variable_rename,[status(thm)],[t42_xboole_1])).
% 0.50/0.67  cnf(c_0_21, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.50/0.67  fof(c_0_22, plain, ![X21]:k5_xboole_0(X21,k1_xboole_0)=X21, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.50/0.67  cnf(c_0_23, plain, (k5_xboole_0(X1,X2)=k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.50/0.67  cnf(c_0_24, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.50/0.67  fof(c_0_25, plain, ![X4, X5]:((k4_xboole_0(X4,X5)!=k1_xboole_0|r1_tarski(X4,X5))&(~r1_tarski(X4,X5)|k4_xboole_0(X4,X5)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.50/0.67  fof(c_0_26, negated_conjecture, ((r1_tarski(k4_xboole_0(esk1_0,esk2_0),esk3_0)&r1_tarski(k4_xboole_0(esk2_0,esk1_0),esk3_0))&~r1_tarski(k5_xboole_0(esk1_0,esk2_0),esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 0.50/0.67  cnf(c_0_27, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.50/0.67  cnf(c_0_28, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_21]), c_0_15])).
% 0.50/0.67  cnf(c_0_29, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.50/0.67  cnf(c_0_30, plain, (k5_xboole_0(X1,X2)=k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 0.50/0.67  cnf(c_0_31, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.50/0.67  cnf(c_0_32, negated_conjecture, (r1_tarski(k4_xboole_0(esk1_0,esk2_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.50/0.67  cnf(c_0_33, plain, (k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))=k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),X2)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.50/0.67  cnf(c_0_34, plain, (k4_xboole_0(k2_xboole_0(X1,k1_xboole_0),k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)))=X1), inference(rw,[status(thm)],[c_0_29, c_0_30])).
% 0.50/0.67  fof(c_0_35, plain, ![X19, X20]:k4_xboole_0(k2_xboole_0(X19,X20),k3_xboole_0(X19,X20))=k2_xboole_0(k4_xboole_0(X19,X20),k4_xboole_0(X20,X19)), inference(variable_rename,[status(thm)],[t55_xboole_1])).
% 0.50/0.67  cnf(c_0_36, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.50/0.67  cnf(c_0_37, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_14, c_0_21])).
% 0.50/0.67  cnf(c_0_38, plain, (k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k4_xboole_0(X4,X3))=k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X4),X3)), inference(spm,[status(thm)],[c_0_27, c_0_14])).
% 0.50/0.67  cnf(c_0_39, negated_conjecture, (k4_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_14])).
% 0.50/0.67  cnf(c_0_40, plain, (k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),X2)=k4_xboole_0(k2_xboole_0(X2,X1),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_21]), c_0_33])).
% 0.50/0.67  cnf(c_0_41, negated_conjecture, (r1_tarski(k4_xboole_0(esk2_0,esk1_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.50/0.67  cnf(c_0_42, plain, (k4_xboole_0(k2_xboole_0(X1,k1_xboole_0),k4_xboole_0(X1,X1))=X1), inference(rw,[status(thm)],[c_0_34, c_0_13])).
% 0.50/0.67  cnf(c_0_43, negated_conjecture, (~r1_tarski(k5_xboole_0(esk1_0,esk2_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.50/0.67  cnf(c_0_44, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.50/0.67  cnf(c_0_45, plain, (r1_tarski(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.50/0.67  cnf(c_0_46, negated_conjecture, (k4_xboole_0(k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),X1),esk3_0)=k4_xboole_0(k2_xboole_0(esk3_0,X1),esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_33]), c_0_40])).
% 0.50/0.67  cnf(c_0_47, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,k2_xboole_0(X4,X2)))=k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(X3,X4)),X2)), inference(spm,[status(thm)],[c_0_27, c_0_14])).
% 0.50/0.67  cnf(c_0_48, negated_conjecture, (k4_xboole_0(esk2_0,k2_xboole_0(esk1_0,esk3_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_41]), c_0_14])).
% 0.50/0.67  cnf(c_0_49, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_21]), c_0_13])).
% 0.50/0.67  cnf(c_0_50, negated_conjecture, (~r1_tarski(k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0))),esk3_0)), inference(rw,[status(thm)],[c_0_43, c_0_30])).
% 0.50/0.67  cnf(c_0_51, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))=k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(rw,[status(thm)],[c_0_44, c_0_24])).
% 0.50/0.67  cnf(c_0_52, negated_conjecture, (r1_tarski(k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),X1),k2_xboole_0(esk3_0,k4_xboole_0(k2_xboole_0(esk3_0,X1),esk3_0)))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.50/0.67  cnf(c_0_53, negated_conjecture, (k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(esk2_0,esk1_0)),esk3_0)=k4_xboole_0(X1,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49])).
% 0.50/0.67  cnf(c_0_54, negated_conjecture, (~r1_tarski(k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk2_0,esk1_0)),esk3_0)), inference(rw,[status(thm)],[c_0_50, c_0_51])).
% 0.50/0.67  cnf(c_0_55, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_21]), c_0_49]), c_0_54]), ['proof']).
% 0.50/0.67  # SZS output end CNFRefutation
% 0.50/0.67  # Proof object total steps             : 56
% 0.50/0.67  # Proof object clause steps            : 35
% 0.50/0.67  # Proof object formula steps           : 21
% 0.50/0.67  # Proof object conjectures             : 14
% 0.50/0.67  # Proof object clause conjectures      : 11
% 0.50/0.67  # Proof object formula conjectures     : 3
% 0.50/0.67  # Proof object initial clauses used    : 13
% 0.50/0.67  # Proof object initial formulas used   : 10
% 0.50/0.67  # Proof object generating inferences   : 15
% 0.50/0.67  # Proof object simplifying inferences  : 18
% 0.50/0.67  # Training examples: 0 positive, 0 negative
% 0.50/0.67  # Parsed axioms                        : 10
% 0.50/0.67  # Removed by relevancy pruning/SinE    : 0
% 0.50/0.67  # Initial clauses                      : 13
% 0.50/0.67  # Removed in clause preprocessing      : 2
% 0.50/0.67  # Initial clauses in saturation        : 11
% 0.50/0.67  # Processed clauses                    : 1236
% 0.50/0.67  # ...of these trivial                  : 437
% 0.50/0.67  # ...subsumed                          : 55
% 0.50/0.67  # ...remaining for further processing  : 744
% 0.50/0.67  # Other redundant clauses eliminated   : 0
% 0.50/0.67  # Clauses deleted for lack of memory   : 0
% 0.50/0.67  # Backward-subsumed                    : 0
% 0.50/0.67  # Backward-rewritten                   : 96
% 0.50/0.67  # Generated clauses                    : 32766
% 0.50/0.67  # ...of the previous two non-trivial   : 20179
% 0.50/0.67  # Contextual simplify-reflections      : 0
% 0.50/0.67  # Paramodulations                      : 32765
% 0.50/0.67  # Factorizations                       : 0
% 0.50/0.67  # Equation resolutions                 : 1
% 0.50/0.67  # Propositional unsat checks           : 0
% 0.50/0.67  #    Propositional check models        : 0
% 0.50/0.67  #    Propositional check unsatisfiable : 0
% 0.50/0.67  #    Propositional clauses             : 0
% 0.50/0.67  #    Propositional clauses after purity: 0
% 0.50/0.67  #    Propositional unsat core size     : 0
% 0.50/0.67  #    Propositional preprocessing time  : 0.000
% 0.50/0.67  #    Propositional encoding time       : 0.000
% 0.50/0.67  #    Propositional solver time         : 0.000
% 0.50/0.67  #    Success case prop preproc time    : 0.000
% 0.50/0.67  #    Success case prop encoding time   : 0.000
% 0.50/0.67  #    Success case prop solver time     : 0.000
% 0.50/0.67  # Current number of processed clauses  : 637
% 0.50/0.67  #    Positive orientable unit clauses  : 616
% 0.50/0.67  #    Positive unorientable unit clauses: 4
% 0.50/0.67  #    Negative unit clauses             : 1
% 0.50/0.67  #    Non-unit-clauses                  : 16
% 0.50/0.67  # Current number of unprocessed clauses: 18733
% 0.50/0.67  # ...number of literals in the above   : 19826
% 0.50/0.67  # Current number of archived formulas  : 0
% 0.50/0.67  # Current number of archived clauses   : 109
% 0.50/0.67  # Clause-clause subsumption calls (NU) : 74
% 0.50/0.67  # Rec. Clause-clause subsumption calls : 74
% 0.50/0.67  # Non-unit clause-clause subsumptions  : 26
% 0.50/0.67  # Unit Clause-clause subsumption calls : 19
% 0.50/0.67  # Rewrite failures with RHS unbound    : 0
% 0.50/0.67  # BW rewrite match attempts            : 4155
% 0.50/0.67  # BW rewrite match successes           : 135
% 0.50/0.67  # Condensation attempts                : 0
% 0.50/0.67  # Condensation successes               : 0
% 0.50/0.67  # Termbank termtop insertions          : 533212
% 0.50/0.68  
% 0.50/0.68  # -------------------------------------------------
% 0.50/0.68  # User time                : 0.304 s
% 0.50/0.68  # System time              : 0.025 s
% 0.50/0.68  # Total time               : 0.329 s
% 0.50/0.68  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------

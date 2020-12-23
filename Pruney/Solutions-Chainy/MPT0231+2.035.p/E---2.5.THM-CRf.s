%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:38:52 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 152 expanded)
%              Number of clauses        :   31 (  64 expanded)
%              Number of leaves         :   12 (  43 expanded)
%              Depth                    :   11
%              Number of atoms          :   69 ( 186 expanded)
%              Number of equality atoms :   33 ( 113 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t26_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_tarski(X1,X2),k1_tarski(X3))
     => X1 = X3 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(t10_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(X1,k2_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(t12_zfmisc_1,axiom,(
    ! [X1,X2] : r1_tarski(k1_tarski(X1),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t6_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),k1_tarski(X2))
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_tarski(k2_tarski(X1,X2),k1_tarski(X3))
       => X1 = X3 ) ),
    inference(assume_negation,[status(cth)],[t26_zfmisc_1])).

fof(c_0_13,negated_conjecture,
    ( r1_tarski(k2_tarski(esk1_0,esk2_0),k1_tarski(esk3_0))
    & esk1_0 != esk3_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

fof(c_0_14,plain,(
    ! [X16] : k2_tarski(X16,X16) = k1_tarski(X16) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_15,plain,(
    ! [X17,X18] : k1_enumset1(X17,X17,X18) = k2_tarski(X17,X18) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_16,plain,(
    ! [X19,X20,X21] : k2_enumset1(X19,X19,X20,X21) = k1_enumset1(X19,X20,X21) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_17,plain,(
    ! [X14,X15] : r1_tarski(X14,k2_xboole_0(X14,X15)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_18,plain,(
    ! [X9] : k2_xboole_0(X9,k1_xboole_0) = X9 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_19,plain,(
    ! [X4,X5,X6] :
      ( ~ r1_tarski(X4,X5)
      | r1_tarski(X4,k2_xboole_0(X6,X5)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).

cnf(c_0_20,negated_conjecture,
    ( r1_tarski(k2_tarski(esk1_0,esk2_0),k1_tarski(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_26,plain,(
    ! [X10,X11] : k2_xboole_0(X10,k4_xboole_0(X11,X10)) = k2_xboole_0(X10,X11) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

fof(c_0_27,plain,(
    ! [X12,X13] : k4_xboole_0(k2_xboole_0(X12,X13),X13) = k4_xboole_0(X12,X13) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,k2_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_22]),c_0_23]),c_0_23])).

fof(c_0_30,plain,(
    ! [X22,X23] : r1_tarski(k1_tarski(X22),k2_tarski(X22,X23)) ),
    inference(variable_rename,[status(thm)],[t12_zfmisc_1])).

fof(c_0_31,plain,(
    ! [X7,X8] :
      ( ~ r1_tarski(X7,X8)
      | k2_xboole_0(X7,X8) = X8 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_33,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0),k2_xboole_0(X1,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_36,plain,
    ( r1_tarski(k1_tarski(X1),k2_tarski(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_32])).

cnf(c_0_39,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0),k2_xboole_0(X1,k2_xboole_0(X2,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_35])).

cnf(c_0_41,plain,
    ( r1_tarski(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_21]),c_0_22]),c_0_22]),c_0_23]),c_0_23])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,k2_xboole_0(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_24])).

cnf(c_0_43,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0),k2_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),X1)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_39])).

cnf(c_0_45,plain,
    ( k2_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X2)) = k2_enumset1(X1,X1,X1,X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_41])).

fof(c_0_46,plain,(
    ! [X24,X25] :
      ( ~ r1_tarski(k1_tarski(X24),k1_tarski(X25))
      | X24 = X25 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_zfmisc_1])])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,k2_xboole_0(k2_xboole_0(X1,X2),X3)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0),k2_enumset1(esk3_0,esk3_0,esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_49,plain,
    ( X1 = X2
    | ~ r1_tarski(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_50,plain,
    ( r1_tarski(k2_enumset1(X1,X1,X1,X1),k2_xboole_0(k2_enumset1(X1,X1,X1,X2),X3)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_45])).

cnf(c_0_51,negated_conjecture,
    ( k2_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0),k2_enumset1(esk3_0,esk3_0,esk3_0,X1)) = k2_enumset1(esk3_0,esk3_0,esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_48])).

cnf(c_0_52,plain,
    ( X1 = X2
    | ~ r1_tarski(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_21]),c_0_21]),c_0_22]),c_0_22]),c_0_23]),c_0_23])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k2_enumset1(esk3_0,esk3_0,esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_54,negated_conjecture,
    ( esk1_0 != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_55,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:45:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.41  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S081N
% 0.20/0.41  # and selection function SelectCQArNTNp.
% 0.20/0.41  #
% 0.20/0.41  # Preprocessing time       : 0.027 s
% 0.20/0.41  # Presaturation interreduction done
% 0.20/0.41  
% 0.20/0.41  # Proof found!
% 0.20/0.41  # SZS status Theorem
% 0.20/0.41  # SZS output start CNFRefutation
% 0.20/0.41  fof(t26_zfmisc_1, conjecture, ![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),k1_tarski(X3))=>X1=X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_zfmisc_1)).
% 0.20/0.41  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.41  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.41  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.41  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.20/0.41  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 0.20/0.41  fof(t10_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(X1,k2_xboole_0(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 0.20/0.41  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.20/0.41  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 0.20/0.41  fof(t12_zfmisc_1, axiom, ![X1, X2]:r1_tarski(k1_tarski(X1),k2_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 0.20/0.41  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.20/0.41  fof(t6_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),k1_tarski(X2))=>X1=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 0.20/0.41  fof(c_0_12, negated_conjecture, ~(![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),k1_tarski(X3))=>X1=X3)), inference(assume_negation,[status(cth)],[t26_zfmisc_1])).
% 0.20/0.41  fof(c_0_13, negated_conjecture, (r1_tarski(k2_tarski(esk1_0,esk2_0),k1_tarski(esk3_0))&esk1_0!=esk3_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.20/0.41  fof(c_0_14, plain, ![X16]:k2_tarski(X16,X16)=k1_tarski(X16), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.41  fof(c_0_15, plain, ![X17, X18]:k1_enumset1(X17,X17,X18)=k2_tarski(X17,X18), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.41  fof(c_0_16, plain, ![X19, X20, X21]:k2_enumset1(X19,X19,X20,X21)=k1_enumset1(X19,X20,X21), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.41  fof(c_0_17, plain, ![X14, X15]:r1_tarski(X14,k2_xboole_0(X14,X15)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.20/0.41  fof(c_0_18, plain, ![X9]:k2_xboole_0(X9,k1_xboole_0)=X9, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.20/0.41  fof(c_0_19, plain, ![X4, X5, X6]:(~r1_tarski(X4,X5)|r1_tarski(X4,k2_xboole_0(X6,X5))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).
% 0.20/0.41  cnf(c_0_20, negated_conjecture, (r1_tarski(k2_tarski(esk1_0,esk2_0),k1_tarski(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.41  cnf(c_0_21, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  cnf(c_0_22, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  cnf(c_0_23, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.41  cnf(c_0_24, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.41  cnf(c_0_25, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.41  fof(c_0_26, plain, ![X10, X11]:k2_xboole_0(X10,k4_xboole_0(X11,X10))=k2_xboole_0(X10,X11), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.20/0.41  fof(c_0_27, plain, ![X12, X13]:k4_xboole_0(k2_xboole_0(X12,X13),X13)=k4_xboole_0(X12,X13), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 0.20/0.41  cnf(c_0_28, plain, (r1_tarski(X1,k2_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.41  cnf(c_0_29, negated_conjecture, (r1_tarski(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_21]), c_0_22]), c_0_22]), c_0_23]), c_0_23])).
% 0.20/0.41  fof(c_0_30, plain, ![X22, X23]:r1_tarski(k1_tarski(X22),k2_tarski(X22,X23)), inference(variable_rename,[status(thm)],[t12_zfmisc_1])).
% 0.20/0.41  fof(c_0_31, plain, ![X7, X8]:(~r1_tarski(X7,X8)|k2_xboole_0(X7,X8)=X8), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.20/0.41  cnf(c_0_32, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.20/0.41  cnf(c_0_33, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.41  cnf(c_0_34, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.41  cnf(c_0_35, negated_conjecture, (r1_tarski(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0),k2_xboole_0(X1,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.20/0.41  cnf(c_0_36, plain, (r1_tarski(k1_tarski(X1),k2_tarski(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.41  cnf(c_0_37, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.41  cnf(c_0_38, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_28, c_0_32])).
% 0.20/0.41  cnf(c_0_39, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_33])).
% 0.20/0.41  cnf(c_0_40, negated_conjecture, (r1_tarski(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0),k2_xboole_0(X1,k2_xboole_0(X2,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))))), inference(spm,[status(thm)],[c_0_28, c_0_35])).
% 0.20/0.41  cnf(c_0_41, plain, (r1_tarski(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_21]), c_0_22]), c_0_22]), c_0_23]), c_0_23])).
% 0.20/0.41  cnf(c_0_42, plain, (r1_tarski(X1,k2_xboole_0(X2,k2_xboole_0(X1,X3)))), inference(spm,[status(thm)],[c_0_28, c_0_24])).
% 0.20/0.41  cnf(c_0_43, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])).
% 0.20/0.41  cnf(c_0_44, negated_conjecture, (r1_tarski(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0),k2_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),X1))), inference(spm,[status(thm)],[c_0_40, c_0_39])).
% 0.20/0.41  cnf(c_0_45, plain, (k2_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X2))=k2_enumset1(X1,X1,X1,X2)), inference(spm,[status(thm)],[c_0_37, c_0_41])).
% 0.20/0.41  fof(c_0_46, plain, ![X24, X25]:(~r1_tarski(k1_tarski(X24),k1_tarski(X25))|X24=X25), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_zfmisc_1])])).
% 0.20/0.41  cnf(c_0_47, plain, (r1_tarski(X1,k2_xboole_0(k2_xboole_0(X1,X2),X3))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.20/0.41  cnf(c_0_48, negated_conjecture, (r1_tarski(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0),k2_enumset1(esk3_0,esk3_0,esk3_0,X1))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.20/0.41  cnf(c_0_49, plain, (X1=X2|~r1_tarski(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.20/0.41  cnf(c_0_50, plain, (r1_tarski(k2_enumset1(X1,X1,X1,X1),k2_xboole_0(k2_enumset1(X1,X1,X1,X2),X3))), inference(spm,[status(thm)],[c_0_47, c_0_45])).
% 0.20/0.41  cnf(c_0_51, negated_conjecture, (k2_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0),k2_enumset1(esk3_0,esk3_0,esk3_0,X1))=k2_enumset1(esk3_0,esk3_0,esk3_0,X1)), inference(spm,[status(thm)],[c_0_37, c_0_48])).
% 0.20/0.41  cnf(c_0_52, plain, (X1=X2|~r1_tarski(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_21]), c_0_21]), c_0_22]), c_0_22]), c_0_23]), c_0_23])).
% 0.20/0.41  cnf(c_0_53, negated_conjecture, (r1_tarski(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k2_enumset1(esk3_0,esk3_0,esk3_0,X1))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.20/0.41  cnf(c_0_54, negated_conjecture, (esk1_0!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.41  cnf(c_0_55, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54]), ['proof']).
% 0.20/0.41  # SZS output end CNFRefutation
% 0.20/0.41  # Proof object total steps             : 56
% 0.20/0.41  # Proof object clause steps            : 31
% 0.20/0.41  # Proof object formula steps           : 25
% 0.20/0.41  # Proof object conjectures             : 13
% 0.20/0.41  # Proof object clause conjectures      : 10
% 0.20/0.41  # Proof object formula conjectures     : 3
% 0.20/0.41  # Proof object initial clauses used    : 13
% 0.20/0.41  # Proof object initial formulas used   : 12
% 0.20/0.41  # Proof object generating inferences   : 15
% 0.20/0.41  # Proof object simplifying inferences  : 19
% 0.20/0.41  # Training examples: 0 positive, 0 negative
% 0.20/0.41  # Parsed axioms                        : 12
% 0.20/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.41  # Initial clauses                      : 13
% 0.20/0.41  # Removed in clause preprocessing      : 3
% 0.20/0.41  # Initial clauses in saturation        : 10
% 0.20/0.41  # Processed clauses                    : 436
% 0.20/0.41  # ...of these trivial                  : 210
% 0.20/0.41  # ...subsumed                          : 41
% 0.20/0.41  # ...remaining for further processing  : 185
% 0.20/0.41  # Other redundant clauses eliminated   : 0
% 0.20/0.41  # Clauses deleted for lack of memory   : 0
% 0.20/0.41  # Backward-subsumed                    : 0
% 0.20/0.41  # Backward-rewritten                   : 28
% 0.20/0.41  # Generated clauses                    : 4381
% 0.20/0.41  # ...of the previous two non-trivial   : 1718
% 0.20/0.41  # Contextual simplify-reflections      : 0
% 0.20/0.41  # Paramodulations                      : 4381
% 0.20/0.41  # Factorizations                       : 0
% 0.20/0.41  # Equation resolutions                 : 0
% 0.20/0.41  # Propositional unsat checks           : 0
% 0.20/0.41  #    Propositional check models        : 0
% 0.20/0.41  #    Propositional check unsatisfiable : 0
% 0.20/0.41  #    Propositional clauses             : 0
% 0.20/0.41  #    Propositional clauses after purity: 0
% 0.20/0.41  #    Propositional unsat core size     : 0
% 0.20/0.41  #    Propositional preprocessing time  : 0.000
% 0.20/0.41  #    Propositional encoding time       : 0.000
% 0.20/0.41  #    Propositional solver time         : 0.000
% 0.20/0.41  #    Success case prop preproc time    : 0.000
% 0.20/0.41  #    Success case prop encoding time   : 0.000
% 0.20/0.41  #    Success case prop solver time     : 0.000
% 0.20/0.41  # Current number of processed clauses  : 147
% 0.20/0.41  #    Positive orientable unit clauses  : 139
% 0.20/0.41  #    Positive unorientable unit clauses: 4
% 0.20/0.41  #    Negative unit clauses             : 1
% 0.20/0.41  #    Non-unit-clauses                  : 3
% 0.20/0.41  # Current number of unprocessed clauses: 1278
% 0.20/0.41  # ...number of literals in the above   : 1278
% 0.20/0.41  # Current number of archived formulas  : 0
% 0.20/0.41  # Current number of archived clauses   : 41
% 0.20/0.41  # Clause-clause subsumption calls (NU) : 2
% 0.20/0.41  # Rec. Clause-clause subsumption calls : 2
% 0.20/0.41  # Non-unit clause-clause subsumptions  : 0
% 0.20/0.41  # Unit Clause-clause subsumption calls : 18
% 0.20/0.41  # Rewrite failures with RHS unbound    : 0
% 0.20/0.41  # BW rewrite match attempts            : 395
% 0.20/0.41  # BW rewrite match successes           : 67
% 0.20/0.41  # Condensation attempts                : 0
% 0.20/0.41  # Condensation successes               : 0
% 0.20/0.41  # Termbank termtop insertions          : 53650
% 0.20/0.41  
% 0.20/0.41  # -------------------------------------------------
% 0.20/0.41  # User time                : 0.065 s
% 0.20/0.41  # System time              : 0.006 s
% 0.20/0.41  # Total time               : 0.071 s
% 0.20/0.41  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------

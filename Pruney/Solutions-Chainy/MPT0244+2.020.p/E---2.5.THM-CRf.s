%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:39:33 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 859 expanded)
%              Number of clauses        :   35 ( 334 expanded)
%              Number of leaves         :   11 ( 260 expanded)
%              Depth                    :    8
%              Number of atoms          :   97 ( 970 expanded)
%              Number of equality atoms :   66 ( 897 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(t76_enumset1,axiom,(
    ! [X1] : k1_enumset1(X1,X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_enumset1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t78_enumset1,axiom,(
    ! [X1,X2,X3] : k3_enumset1(X1,X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(t55_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).

fof(t39_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( r1_tarski(X1,k1_tarski(X2))
    <=> ( X1 = k1_xboole_0
        | X1 = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_zfmisc_1)).

fof(l3_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k1_tarski(X2))
    <=> ( X1 = k1_xboole_0
        | X1 = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(t95_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t21_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(c_0_11,plain,(
    ! [X13,X14] : k2_tarski(X13,X14) = k2_xboole_0(k1_tarski(X13),k1_tarski(X14)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

fof(c_0_12,plain,(
    ! [X26] : k1_enumset1(X26,X26,X26) = k1_tarski(X26) ),
    inference(variable_rename,[status(thm)],[t76_enumset1])).

fof(c_0_13,plain,(
    ! [X32,X33] : k3_tarski(k2_tarski(X32,X33)) = k2_xboole_0(X32,X33) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_14,plain,(
    ! [X27,X28,X29] : k3_enumset1(X27,X27,X27,X28,X29) = k1_enumset1(X27,X28,X29) ),
    inference(variable_rename,[status(thm)],[t78_enumset1])).

fof(c_0_15,plain,(
    ! [X21,X22,X23,X24,X25] : k4_enumset1(X21,X21,X22,X23,X24,X25) = k3_enumset1(X21,X22,X23,X24,X25) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_16,plain,(
    ! [X15,X16,X17,X18,X19,X20] : k4_enumset1(X15,X16,X17,X18,X19,X20) = k2_xboole_0(k3_enumset1(X15,X16,X17,X18,X19),k1_tarski(X20)) ),
    inference(variable_rename,[status(thm)],[t55_enumset1])).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r1_tarski(X1,k1_tarski(X2))
      <=> ( X1 = k1_xboole_0
          | X1 = k1_tarski(X2) ) ) ),
    inference(assume_negation,[status(cth)],[t39_zfmisc_1])).

fof(c_0_18,plain,(
    ! [X30,X31] :
      ( ( ~ r1_tarski(X30,k1_tarski(X31))
        | X30 = k1_xboole_0
        | X30 = k1_tarski(X31) )
      & ( X30 != k1_xboole_0
        | r1_tarski(X30,k1_tarski(X31)) )
      & ( X30 != k1_tarski(X31)
        | r1_tarski(X30,k1_tarski(X31)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).

cnf(c_0_19,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,plain,
    ( k1_enumset1(X1,X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( k3_enumset1(X1,X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_25,negated_conjecture,
    ( ( esk1_0 != k1_xboole_0
      | ~ r1_tarski(esk1_0,k1_tarski(esk2_0)) )
    & ( esk1_0 != k1_tarski(esk2_0)
      | ~ r1_tarski(esk1_0,k1_tarski(esk2_0)) )
    & ( r1_tarski(esk1_0,k1_tarski(esk2_0))
      | esk1_0 = k1_xboole_0
      | esk1_0 = k1_tarski(esk2_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])])).

fof(c_0_26,plain,(
    ! [X11,X12] : k3_xboole_0(X11,X12) = k5_xboole_0(k5_xboole_0(X11,X12),k2_xboole_0(X11,X12)) ),
    inference(variable_rename,[status(thm)],[t95_xboole_1])).

cnf(c_0_27,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | ~ r1_tarski(X1,k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( k2_tarski(X1,X2) = k3_tarski(k2_tarski(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X2,X2,X2,X2,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_20]),c_0_20]),c_0_21]),c_0_22]),c_0_22]),c_0_23]),c_0_23])).

cnf(c_0_29,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k3_tarski(k2_tarski(k4_enumset1(X1,X1,X2,X3,X4,X5),k4_enumset1(X6,X6,X6,X6,X6,X6))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(esk1_0,k1_tarski(esk2_0))
    | esk1_0 = k1_xboole_0
    | esk1_0 = k1_tarski(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_31,plain,(
    ! [X7,X8] : r1_tarski(k3_xboole_0(X7,X8),X7) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_32,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_33,plain,(
    ! [X9,X10] : k3_xboole_0(X9,k2_xboole_0(X9,X10)) = X9 ),
    inference(variable_rename,[status(thm)],[t21_xboole_1])).

cnf(c_0_34,negated_conjecture,
    ( esk1_0 != k1_tarski(esk2_0)
    | ~ r1_tarski(esk1_0,k1_tarski(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( X1 = k1_xboole_0
    | X1 = k4_enumset1(X2,X2,X2,X2,X2,X2)
    | ~ r1_tarski(X1,k4_enumset1(X2,X2,X2,X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_20]),c_0_20]),c_0_22]),c_0_22]),c_0_23]),c_0_23])).

cnf(c_0_36,plain,
    ( k4_enumset1(X1,X1,X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_37,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | esk1_0 = k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)
    | r1_tarski(esk1_0,k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_20]),c_0_20]),c_0_22]),c_0_22]),c_0_23]),c_0_23])).

cnf(c_0_38,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_32,c_0_21])).

cnf(c_0_40,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,k1_tarski(X2))
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_42,negated_conjecture,
    ( esk1_0 != k1_xboole_0
    | ~ r1_tarski(esk1_0,k1_tarski(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_43,negated_conjecture,
    ( esk1_0 != k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)
    | ~ r1_tarski(esk1_0,k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_20]),c_0_20]),c_0_22]),c_0_22]),c_0_23]),c_0_23])).

cnf(c_0_44,plain,
    ( X1 = k2_tarski(X2,X2)
    | X1 = k1_xboole_0
    | ~ r1_tarski(X1,k2_tarski(X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36]),c_0_36])).

cnf(c_0_45,negated_conjecture,
    ( k2_tarski(esk2_0,esk2_0) = esk1_0
    | esk1_0 = k1_xboole_0
    | r1_tarski(esk1_0,k2_tarski(esk2_0,esk2_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_36]),c_0_36])).

cnf(c_0_46,plain,
    ( r1_tarski(k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k2_tarski(X1,X2))),X1) ),
    inference(rw,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_47,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k3_tarski(k2_tarski(X1,X2))),k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(X1,X2))))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_21]),c_0_39])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,k4_enumset1(X2,X2,X2,X2,X2,X2))
    | X1 != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_20]),c_0_22]),c_0_23])).

cnf(c_0_49,negated_conjecture,
    ( esk1_0 != k1_xboole_0
    | ~ r1_tarski(esk1_0,k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_20]),c_0_22]),c_0_23])).

cnf(c_0_50,negated_conjecture,
    ( k2_tarski(esk2_0,esk2_0) != esk1_0
    | ~ r1_tarski(esk1_0,k2_tarski(esk2_0,esk2_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_36]),c_0_36])).

cnf(c_0_51,negated_conjecture,
    ( k2_tarski(esk2_0,esk2_0) = esk1_0
    | esk1_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_53,plain,
    ( r1_tarski(k1_xboole_0,k4_enumset1(X1,X1,X1,X1,X1,X1)) ),
    inference(er,[status(thm)],[c_0_48])).

cnf(c_0_54,negated_conjecture,
    ( esk1_0 != k1_xboole_0
    | ~ r1_tarski(esk1_0,k2_tarski(esk2_0,esk2_0)) ),
    inference(rw,[status(thm)],[c_0_49,c_0_36])).

cnf(c_0_55,negated_conjecture,
    ( esk1_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])])).

cnf(c_0_56,plain,
    ( r1_tarski(k1_xboole_0,k2_tarski(X1,X1)) ),
    inference(rw,[status(thm)],[c_0_53,c_0_36])).

cnf(c_0_57,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_55]),c_0_55]),c_0_56])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:19:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S078N
% 0.20/0.38  # and selection function SelectCQIArNpEqFirst.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.027 s
% 0.20/0.38  # Presaturation interreduction done
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 0.20/0.38  fof(t76_enumset1, axiom, ![X1]:k1_enumset1(X1,X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_enumset1)).
% 0.20/0.38  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.20/0.38  fof(t78_enumset1, axiom, ![X1, X2, X3]:k3_enumset1(X1,X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_enumset1)).
% 0.20/0.38  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.20/0.38  fof(t55_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_enumset1)).
% 0.20/0.38  fof(t39_zfmisc_1, conjecture, ![X1, X2]:(r1_tarski(X1,k1_tarski(X2))<=>(X1=k1_xboole_0|X1=k1_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_zfmisc_1)).
% 0.20/0.38  fof(l3_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,k1_tarski(X2))<=>(X1=k1_xboole_0|X1=k1_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 0.20/0.38  fof(t95_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 0.20/0.38  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.20/0.38  fof(t21_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 0.20/0.38  fof(c_0_11, plain, ![X13, X14]:k2_tarski(X13,X14)=k2_xboole_0(k1_tarski(X13),k1_tarski(X14)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 0.20/0.38  fof(c_0_12, plain, ![X26]:k1_enumset1(X26,X26,X26)=k1_tarski(X26), inference(variable_rename,[status(thm)],[t76_enumset1])).
% 0.20/0.38  fof(c_0_13, plain, ![X32, X33]:k3_tarski(k2_tarski(X32,X33))=k2_xboole_0(X32,X33), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.20/0.38  fof(c_0_14, plain, ![X27, X28, X29]:k3_enumset1(X27,X27,X27,X28,X29)=k1_enumset1(X27,X28,X29), inference(variable_rename,[status(thm)],[t78_enumset1])).
% 0.20/0.38  fof(c_0_15, plain, ![X21, X22, X23, X24, X25]:k4_enumset1(X21,X21,X22,X23,X24,X25)=k3_enumset1(X21,X22,X23,X24,X25), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.20/0.38  fof(c_0_16, plain, ![X15, X16, X17, X18, X19, X20]:k4_enumset1(X15,X16,X17,X18,X19,X20)=k2_xboole_0(k3_enumset1(X15,X16,X17,X18,X19),k1_tarski(X20)), inference(variable_rename,[status(thm)],[t55_enumset1])).
% 0.20/0.38  fof(c_0_17, negated_conjecture, ~(![X1, X2]:(r1_tarski(X1,k1_tarski(X2))<=>(X1=k1_xboole_0|X1=k1_tarski(X2)))), inference(assume_negation,[status(cth)],[t39_zfmisc_1])).
% 0.20/0.38  fof(c_0_18, plain, ![X30, X31]:((~r1_tarski(X30,k1_tarski(X31))|(X30=k1_xboole_0|X30=k1_tarski(X31)))&((X30!=k1_xboole_0|r1_tarski(X30,k1_tarski(X31)))&(X30!=k1_tarski(X31)|r1_tarski(X30,k1_tarski(X31))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).
% 0.20/0.38  cnf(c_0_19, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.38  cnf(c_0_20, plain, (k1_enumset1(X1,X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  cnf(c_0_21, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  cnf(c_0_22, plain, (k3_enumset1(X1,X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.38  cnf(c_0_23, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.38  cnf(c_0_24, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.38  fof(c_0_25, negated_conjecture, (((esk1_0!=k1_xboole_0|~r1_tarski(esk1_0,k1_tarski(esk2_0)))&(esk1_0!=k1_tarski(esk2_0)|~r1_tarski(esk1_0,k1_tarski(esk2_0))))&(r1_tarski(esk1_0,k1_tarski(esk2_0))|(esk1_0=k1_xboole_0|esk1_0=k1_tarski(esk2_0)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])])).
% 0.20/0.38  fof(c_0_26, plain, ![X11, X12]:k3_xboole_0(X11,X12)=k5_xboole_0(k5_xboole_0(X11,X12),k2_xboole_0(X11,X12)), inference(variable_rename,[status(thm)],[t95_xboole_1])).
% 0.20/0.38  cnf(c_0_27, plain, (X1=k1_xboole_0|X1=k1_tarski(X2)|~r1_tarski(X1,k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.38  cnf(c_0_28, plain, (k2_tarski(X1,X2)=k3_tarski(k2_tarski(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X2,X2,X2,X2,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_20]), c_0_20]), c_0_21]), c_0_22]), c_0_22]), c_0_23]), c_0_23])).
% 0.20/0.38  cnf(c_0_29, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k3_tarski(k2_tarski(k4_enumset1(X1,X1,X2,X3,X4,X5),k4_enumset1(X6,X6,X6,X6,X6,X6)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_20]), c_0_21]), c_0_22]), c_0_23]), c_0_23])).
% 0.20/0.38  cnf(c_0_30, negated_conjecture, (r1_tarski(esk1_0,k1_tarski(esk2_0))|esk1_0=k1_xboole_0|esk1_0=k1_tarski(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.38  fof(c_0_31, plain, ![X7, X8]:r1_tarski(k3_xboole_0(X7,X8),X7), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.20/0.38  cnf(c_0_32, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.38  fof(c_0_33, plain, ![X9, X10]:k3_xboole_0(X9,k2_xboole_0(X9,X10))=X9, inference(variable_rename,[status(thm)],[t21_xboole_1])).
% 0.20/0.38  cnf(c_0_34, negated_conjecture, (esk1_0!=k1_tarski(esk2_0)|~r1_tarski(esk1_0,k1_tarski(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.38  cnf(c_0_35, plain, (X1=k1_xboole_0|X1=k4_enumset1(X2,X2,X2,X2,X2,X2)|~r1_tarski(X1,k4_enumset1(X2,X2,X2,X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_20]), c_0_20]), c_0_22]), c_0_22]), c_0_23]), c_0_23])).
% 0.20/0.38  cnf(c_0_36, plain, (k4_enumset1(X1,X1,X1,X1,X1,X2)=k2_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_28, c_0_29])).
% 0.20/0.38  cnf(c_0_37, negated_conjecture, (esk1_0=k1_xboole_0|esk1_0=k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)|r1_tarski(esk1_0,k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_20]), c_0_20]), c_0_22]), c_0_22]), c_0_23]), c_0_23])).
% 0.20/0.38  cnf(c_0_38, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.38  cnf(c_0_39, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_32, c_0_21])).
% 0.20/0.38  cnf(c_0_40, plain, (k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.38  cnf(c_0_41, plain, (r1_tarski(X1,k1_tarski(X2))|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.38  cnf(c_0_42, negated_conjecture, (esk1_0!=k1_xboole_0|~r1_tarski(esk1_0,k1_tarski(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.38  cnf(c_0_43, negated_conjecture, (esk1_0!=k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)|~r1_tarski(esk1_0,k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_20]), c_0_20]), c_0_22]), c_0_22]), c_0_23]), c_0_23])).
% 0.20/0.38  cnf(c_0_44, plain, (X1=k2_tarski(X2,X2)|X1=k1_xboole_0|~r1_tarski(X1,k2_tarski(X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_36]), c_0_36])).
% 0.20/0.38  cnf(c_0_45, negated_conjecture, (k2_tarski(esk2_0,esk2_0)=esk1_0|esk1_0=k1_xboole_0|r1_tarski(esk1_0,k2_tarski(esk2_0,esk2_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_36]), c_0_36])).
% 0.20/0.38  cnf(c_0_46, plain, (r1_tarski(k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k2_tarski(X1,X2))),X1)), inference(rw,[status(thm)],[c_0_38, c_0_39])).
% 0.20/0.38  cnf(c_0_47, plain, (k5_xboole_0(k5_xboole_0(X1,k3_tarski(k2_tarski(X1,X2))),k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(X1,X2)))))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_21]), c_0_39])).
% 0.20/0.38  cnf(c_0_48, plain, (r1_tarski(X1,k4_enumset1(X2,X2,X2,X2,X2,X2))|X1!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_20]), c_0_22]), c_0_23])).
% 0.20/0.38  cnf(c_0_49, negated_conjecture, (esk1_0!=k1_xboole_0|~r1_tarski(esk1_0,k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_20]), c_0_22]), c_0_23])).
% 0.20/0.38  cnf(c_0_50, negated_conjecture, (k2_tarski(esk2_0,esk2_0)!=esk1_0|~r1_tarski(esk1_0,k2_tarski(esk2_0,esk2_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_36]), c_0_36])).
% 0.20/0.38  cnf(c_0_51, negated_conjecture, (k2_tarski(esk2_0,esk2_0)=esk1_0|esk1_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.20/0.38  cnf(c_0_52, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.20/0.38  cnf(c_0_53, plain, (r1_tarski(k1_xboole_0,k4_enumset1(X1,X1,X1,X1,X1,X1))), inference(er,[status(thm)],[c_0_48])).
% 0.20/0.38  cnf(c_0_54, negated_conjecture, (esk1_0!=k1_xboole_0|~r1_tarski(esk1_0,k2_tarski(esk2_0,esk2_0))), inference(rw,[status(thm)],[c_0_49, c_0_36])).
% 0.20/0.38  cnf(c_0_55, negated_conjecture, (esk1_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52])])).
% 0.20/0.38  cnf(c_0_56, plain, (r1_tarski(k1_xboole_0,k2_tarski(X1,X1))), inference(rw,[status(thm)],[c_0_53, c_0_36])).
% 0.20/0.38  cnf(c_0_57, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_55]), c_0_55]), c_0_56])]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 58
% 0.20/0.38  # Proof object clause steps            : 35
% 0.20/0.38  # Proof object formula steps           : 23
% 0.20/0.38  # Proof object conjectures             : 15
% 0.20/0.38  # Proof object clause conjectures      : 12
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 14
% 0.20/0.38  # Proof object initial formulas used   : 11
% 0.20/0.38  # Proof object generating inferences   : 3
% 0.20/0.38  # Proof object simplifying inferences  : 56
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 11
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 15
% 0.20/0.38  # Removed in clause preprocessing      : 5
% 0.20/0.38  # Initial clauses in saturation        : 10
% 0.20/0.38  # Processed clauses                    : 31
% 0.20/0.38  # ...of these trivial                  : 0
% 0.20/0.38  # ...subsumed                          : 0
% 0.20/0.38  # ...remaining for further processing  : 31
% 0.20/0.38  # Other redundant clauses eliminated   : 2
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 1
% 0.20/0.38  # Backward-rewritten                   : 12
% 0.20/0.38  # Generated clauses                    : 11
% 0.20/0.38  # ...of the previous two non-trivial   : 20
% 0.20/0.38  # Contextual simplify-reflections      : 0
% 0.20/0.38  # Paramodulations                      : 9
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 2
% 0.20/0.38  # Propositional unsat checks           : 0
% 0.20/0.38  #    Propositional check models        : 0
% 0.20/0.38  #    Propositional check unsatisfiable : 0
% 0.20/0.38  #    Propositional clauses             : 0
% 0.20/0.38  #    Propositional clauses after purity: 0
% 0.20/0.38  #    Propositional unsat core size     : 0
% 0.20/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 6
% 0.20/0.38  #    Positive orientable unit clauses  : 5
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 0
% 0.20/0.38  #    Non-unit-clauses                  : 1
% 0.20/0.38  # Current number of unprocessed clauses: 8
% 0.20/0.38  # ...number of literals in the above   : 15
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 28
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 1
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 1
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 1
% 0.20/0.38  # Unit Clause-clause subsumption calls : 7
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 13
% 0.20/0.38  # BW rewrite match successes           : 7
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 1032
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.028 s
% 0.20/0.38  # System time              : 0.003 s
% 0.20/0.38  # Total time               : 0.032 s
% 0.20/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------

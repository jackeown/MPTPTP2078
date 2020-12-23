%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:38:52 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 126 expanded)
%              Number of clauses        :   28 (  54 expanded)
%              Number of leaves         :   11 (  35 expanded)
%              Depth                    :   12
%              Number of atoms          :   64 ( 154 expanded)
%              Number of equality atoms :   32 (  97 expanded)
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

fof(t77_enumset1,axiom,(
    ! [X1,X2] : k2_enumset1(X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).

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

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(t24_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),k1_tarski(X2))
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_zfmisc_1)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_tarski(k2_tarski(X1,X2),k1_tarski(X3))
       => X1 = X3 ) ),
    inference(assume_negation,[status(cth)],[t26_zfmisc_1])).

fof(c_0_12,negated_conjecture,
    ( r1_tarski(k2_tarski(esk1_0,esk2_0),k1_tarski(esk3_0))
    & esk1_0 != esk3_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

fof(c_0_13,plain,(
    ! [X15] : k2_tarski(X15,X15) = k1_tarski(X15) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_14,plain,(
    ! [X16,X17] : k2_enumset1(X16,X16,X16,X17) = k2_tarski(X16,X17) ),
    inference(variable_rename,[status(thm)],[t77_enumset1])).

fof(c_0_15,plain,(
    ! [X4,X5,X6] :
      ( ~ r1_tarski(X4,X5)
      | r1_tarski(X4,k2_xboole_0(X6,X5)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).

cnf(c_0_16,negated_conjecture,
    ( r1_tarski(k2_tarski(esk1_0,esk2_0),k1_tarski(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,k2_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( r1_tarski(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_18])).

fof(c_0_21,plain,(
    ! [X11,X12] : k2_xboole_0(X11,k4_xboole_0(X12,X11)) = k2_xboole_0(X11,X12) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

fof(c_0_22,plain,(
    ! [X13,X14] : k4_xboole_0(k2_xboole_0(X13,X14),X14) = k4_xboole_0(X13,X14) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

fof(c_0_23,plain,(
    ! [X18,X19] : r1_tarski(k1_tarski(X18),k2_tarski(X18,X19)) ),
    inference(variable_rename,[status(thm)],[t12_zfmisc_1])).

cnf(c_0_24,negated_conjecture,
    ( r1_tarski(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0),k2_xboole_0(X1,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_25,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_27,plain,(
    ! [X7,X8] :
      ( ~ r1_tarski(X7,X8)
      | k2_xboole_0(X7,X8) = X8 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_28,plain,
    ( r1_tarski(k1_tarski(X1),k2_tarski(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0),k2_xboole_0(X1,k2_xboole_0(X2,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_24])).

cnf(c_0_30,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_25])).

cnf(c_0_31,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,plain,
    ( r1_tarski(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_17]),c_0_18]),c_0_18])).

fof(c_0_33,plain,(
    ! [X10] : r1_tarski(k1_xboole_0,X10) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0),k2_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),X1)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,plain,
    ( k2_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X2)) = k2_enumset1(X1,X1,X1,X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_36,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_37,plain,(
    ! [X9] : k2_xboole_0(X9,k1_xboole_0) = X9 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0),k2_enumset1(esk3_0,esk3_0,esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_39,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_31,c_0_36])).

cnf(c_0_40,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_41,plain,(
    ! [X20,X21] :
      ( ~ r1_tarski(k1_tarski(X20),k1_tarski(X21))
      | X20 = X21 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_zfmisc_1])])).

cnf(c_0_42,negated_conjecture,
    ( k2_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0),k2_enumset1(esk3_0,esk3_0,esk3_0,X1)) = k2_enumset1(esk3_0,esk3_0,esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_38])).

cnf(c_0_43,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_39]),c_0_40])).

cnf(c_0_44,plain,
    ( X1 = X2
    | ~ r1_tarski(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_45,plain,
    ( r1_tarski(k2_enumset1(X1,X1,X1,X1),k2_xboole_0(X2,k2_enumset1(X1,X1,X1,X3))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_32])).

cnf(c_0_46,negated_conjecture,
    ( k2_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,X1),k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0)) = k2_enumset1(esk3_0,esk3_0,esk3_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_42]),c_0_43])).

cnf(c_0_47,plain,
    ( X1 = X2
    | ~ r1_tarski(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_17]),c_0_17]),c_0_18]),c_0_18])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k2_enumset1(esk3_0,esk3_0,esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_49,negated_conjecture,
    ( esk1_0 != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_50,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:36:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S081N
% 0.12/0.36  # and selection function SelectCQArNTNp.
% 0.12/0.36  #
% 0.12/0.36  # Preprocessing time       : 0.019 s
% 0.12/0.36  # Presaturation interreduction done
% 0.12/0.36  
% 0.12/0.36  # Proof found!
% 0.12/0.36  # SZS status Theorem
% 0.12/0.36  # SZS output start CNFRefutation
% 0.12/0.36  fof(t26_zfmisc_1, conjecture, ![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),k1_tarski(X3))=>X1=X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_zfmisc_1)).
% 0.12/0.36  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.12/0.36  fof(t77_enumset1, axiom, ![X1, X2]:k2_enumset1(X1,X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_enumset1)).
% 0.12/0.36  fof(t10_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(X1,k2_xboole_0(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 0.12/0.36  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.12/0.36  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 0.12/0.36  fof(t12_zfmisc_1, axiom, ![X1, X2]:r1_tarski(k1_tarski(X1),k2_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 0.12/0.36  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.12/0.36  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.12/0.36  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 0.12/0.36  fof(t24_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),k1_tarski(X2))=>X1=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_zfmisc_1)).
% 0.12/0.36  fof(c_0_11, negated_conjecture, ~(![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),k1_tarski(X3))=>X1=X3)), inference(assume_negation,[status(cth)],[t26_zfmisc_1])).
% 0.12/0.36  fof(c_0_12, negated_conjecture, (r1_tarski(k2_tarski(esk1_0,esk2_0),k1_tarski(esk3_0))&esk1_0!=esk3_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 0.12/0.36  fof(c_0_13, plain, ![X15]:k2_tarski(X15,X15)=k1_tarski(X15), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.12/0.36  fof(c_0_14, plain, ![X16, X17]:k2_enumset1(X16,X16,X16,X17)=k2_tarski(X16,X17), inference(variable_rename,[status(thm)],[t77_enumset1])).
% 0.12/0.36  fof(c_0_15, plain, ![X4, X5, X6]:(~r1_tarski(X4,X5)|r1_tarski(X4,k2_xboole_0(X6,X5))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).
% 0.12/0.36  cnf(c_0_16, negated_conjecture, (r1_tarski(k2_tarski(esk1_0,esk2_0),k1_tarski(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.36  cnf(c_0_17, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.36  cnf(c_0_18, plain, (k2_enumset1(X1,X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.36  cnf(c_0_19, plain, (r1_tarski(X1,k2_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.36  cnf(c_0_20, negated_conjecture, (r1_tarski(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16, c_0_17]), c_0_18]), c_0_18])).
% 0.12/0.36  fof(c_0_21, plain, ![X11, X12]:k2_xboole_0(X11,k4_xboole_0(X12,X11))=k2_xboole_0(X11,X12), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.12/0.36  fof(c_0_22, plain, ![X13, X14]:k4_xboole_0(k2_xboole_0(X13,X14),X14)=k4_xboole_0(X13,X14), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 0.12/0.36  fof(c_0_23, plain, ![X18, X19]:r1_tarski(k1_tarski(X18),k2_tarski(X18,X19)), inference(variable_rename,[status(thm)],[t12_zfmisc_1])).
% 0.12/0.36  cnf(c_0_24, negated_conjecture, (r1_tarski(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0),k2_xboole_0(X1,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.12/0.36  cnf(c_0_25, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.12/0.36  cnf(c_0_26, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.36  fof(c_0_27, plain, ![X7, X8]:(~r1_tarski(X7,X8)|k2_xboole_0(X7,X8)=X8), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.12/0.36  cnf(c_0_28, plain, (r1_tarski(k1_tarski(X1),k2_tarski(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.12/0.36  cnf(c_0_29, negated_conjecture, (r1_tarski(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0),k2_xboole_0(X1,k2_xboole_0(X2,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))))), inference(spm,[status(thm)],[c_0_19, c_0_24])).
% 0.12/0.36  cnf(c_0_30, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_25])).
% 0.12/0.36  cnf(c_0_31, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.12/0.36  cnf(c_0_32, plain, (r1_tarski(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_17]), c_0_18]), c_0_18])).
% 0.12/0.36  fof(c_0_33, plain, ![X10]:r1_tarski(k1_xboole_0,X10), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.12/0.36  cnf(c_0_34, negated_conjecture, (r1_tarski(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0),k2_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),X1))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.12/0.36  cnf(c_0_35, plain, (k2_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X2))=k2_enumset1(X1,X1,X1,X2)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.12/0.36  cnf(c_0_36, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.12/0.36  fof(c_0_37, plain, ![X9]:k2_xboole_0(X9,k1_xboole_0)=X9, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.12/0.36  cnf(c_0_38, negated_conjecture, (r1_tarski(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0),k2_enumset1(esk3_0,esk3_0,esk3_0,X1))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.12/0.36  cnf(c_0_39, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_31, c_0_36])).
% 0.12/0.36  cnf(c_0_40, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.12/0.36  fof(c_0_41, plain, ![X20, X21]:(~r1_tarski(k1_tarski(X20),k1_tarski(X21))|X20=X21), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_zfmisc_1])])).
% 0.12/0.36  cnf(c_0_42, negated_conjecture, (k2_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0),k2_enumset1(esk3_0,esk3_0,esk3_0,X1))=k2_enumset1(esk3_0,esk3_0,esk3_0,X1)), inference(spm,[status(thm)],[c_0_31, c_0_38])).
% 0.12/0.36  cnf(c_0_43, plain, (k2_xboole_0(X1,X1)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_39]), c_0_40])).
% 0.12/0.36  cnf(c_0_44, plain, (X1=X2|~r1_tarski(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.12/0.36  cnf(c_0_45, plain, (r1_tarski(k2_enumset1(X1,X1,X1,X1),k2_xboole_0(X2,k2_enumset1(X1,X1,X1,X3)))), inference(spm,[status(thm)],[c_0_19, c_0_32])).
% 0.12/0.36  cnf(c_0_46, negated_conjecture, (k2_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,X1),k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0))=k2_enumset1(esk3_0,esk3_0,esk3_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_42]), c_0_43])).
% 0.12/0.36  cnf(c_0_47, plain, (X1=X2|~r1_tarski(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_17]), c_0_17]), c_0_18]), c_0_18])).
% 0.12/0.36  cnf(c_0_48, negated_conjecture, (r1_tarski(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k2_enumset1(esk3_0,esk3_0,esk3_0,X1))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.12/0.36  cnf(c_0_49, negated_conjecture, (esk1_0!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.36  cnf(c_0_50, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49]), ['proof']).
% 0.12/0.36  # SZS output end CNFRefutation
% 0.12/0.36  # Proof object total steps             : 51
% 0.12/0.36  # Proof object clause steps            : 28
% 0.12/0.36  # Proof object formula steps           : 23
% 0.12/0.36  # Proof object conjectures             : 14
% 0.12/0.36  # Proof object clause conjectures      : 11
% 0.12/0.36  # Proof object formula conjectures     : 3
% 0.12/0.36  # Proof object initial clauses used    : 12
% 0.12/0.36  # Proof object initial formulas used   : 11
% 0.12/0.36  # Proof object generating inferences   : 13
% 0.12/0.36  # Proof object simplifying inferences  : 14
% 0.12/0.36  # Training examples: 0 positive, 0 negative
% 0.12/0.36  # Parsed axioms                        : 11
% 0.12/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.36  # Initial clauses                      : 12
% 0.12/0.36  # Removed in clause preprocessing      : 2
% 0.12/0.36  # Initial clauses in saturation        : 10
% 0.12/0.36  # Processed clauses                    : 51
% 0.12/0.36  # ...of these trivial                  : 1
% 0.12/0.36  # ...subsumed                          : 5
% 0.12/0.36  # ...remaining for further processing  : 45
% 0.12/0.36  # Other redundant clauses eliminated   : 0
% 0.12/0.36  # Clauses deleted for lack of memory   : 0
% 0.12/0.36  # Backward-subsumed                    : 0
% 0.12/0.36  # Backward-rewritten                   : 8
% 0.12/0.36  # Generated clauses                    : 123
% 0.12/0.36  # ...of the previous two non-trivial   : 68
% 0.12/0.36  # Contextual simplify-reflections      : 0
% 0.12/0.36  # Paramodulations                      : 123
% 0.12/0.36  # Factorizations                       : 0
% 0.12/0.36  # Equation resolutions                 : 0
% 0.12/0.36  # Propositional unsat checks           : 0
% 0.12/0.36  #    Propositional check models        : 0
% 0.12/0.36  #    Propositional check unsatisfiable : 0
% 0.12/0.36  #    Propositional clauses             : 0
% 0.12/0.36  #    Propositional clauses after purity: 0
% 0.12/0.36  #    Propositional unsat core size     : 0
% 0.12/0.36  #    Propositional preprocessing time  : 0.000
% 0.12/0.36  #    Propositional encoding time       : 0.000
% 0.12/0.36  #    Propositional solver time         : 0.000
% 0.12/0.36  #    Success case prop preproc time    : 0.000
% 0.12/0.36  #    Success case prop encoding time   : 0.000
% 0.12/0.36  #    Success case prop solver time     : 0.000
% 0.12/0.36  # Current number of processed clauses  : 27
% 0.12/0.36  #    Positive orientable unit clauses  : 22
% 0.12/0.36  #    Positive unorientable unit clauses: 1
% 0.12/0.36  #    Negative unit clauses             : 1
% 0.12/0.36  #    Non-unit-clauses                  : 3
% 0.12/0.36  # Current number of unprocessed clauses: 31
% 0.12/0.36  # ...number of literals in the above   : 31
% 0.12/0.36  # Current number of archived formulas  : 0
% 0.12/0.36  # Current number of archived clauses   : 20
% 0.12/0.36  # Clause-clause subsumption calls (NU) : 2
% 0.12/0.36  # Rec. Clause-clause subsumption calls : 2
% 0.12/0.36  # Non-unit clause-clause subsumptions  : 0
% 0.12/0.36  # Unit Clause-clause subsumption calls : 2
% 0.12/0.36  # Rewrite failures with RHS unbound    : 0
% 0.12/0.36  # BW rewrite match attempts            : 32
% 0.12/0.36  # BW rewrite match successes           : 8
% 0.12/0.36  # Condensation attempts                : 0
% 0.12/0.36  # Condensation successes               : 0
% 0.12/0.36  # Termbank termtop insertions          : 2769
% 0.12/0.36  
% 0.12/0.36  # -------------------------------------------------
% 0.12/0.36  # User time                : 0.019 s
% 0.12/0.36  # System time              : 0.005 s
% 0.12/0.36  # Total time               : 0.024 s
% 0.12/0.36  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------

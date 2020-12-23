%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:37:12 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   37 ( 379 expanded)
%              Number of clauses        :   22 ( 158 expanded)
%              Number of leaves         :    7 ( 105 expanded)
%              Depth                    :   12
%              Number of atoms          :   48 ( 459 expanded)
%              Number of equality atoms :   47 ( 458 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t9_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ( k1_tarski(X1) = k2_tarski(X2,X3)
     => X2 = X3 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_zfmisc_1)).

fof(t8_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k1_tarski(X1) = k2_tarski(X2,X3)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t77_enumset1,axiom,(
    ! [X1,X2] : k2_enumset1(X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).

fof(t45_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_enumset1)).

fof(t111_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X2,X3,X4,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_enumset1)).

fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( k1_tarski(X1) = k2_tarski(X2,X3)
       => X2 = X3 ) ),
    inference(assume_negation,[status(cth)],[t9_zfmisc_1])).

fof(c_0_8,plain,(
    ! [X34,X35,X36] :
      ( k1_tarski(X34) != k2_tarski(X35,X36)
      | X34 = X35 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_zfmisc_1])])).

fof(c_0_9,plain,(
    ! [X23] : k2_tarski(X23,X23) = k1_tarski(X23) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_10,plain,(
    ! [X27,X28] : k2_enumset1(X27,X27,X27,X28) = k2_tarski(X27,X28) ),
    inference(variable_rename,[status(thm)],[t77_enumset1])).

fof(c_0_11,negated_conjecture,
    ( k1_tarski(esk1_0) = k2_tarski(esk2_0,esk3_0)
    & esk2_0 != esk3_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

cnf(c_0_12,plain,
    ( X1 = X2
    | k1_tarski(X1) != k2_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( k1_tarski(esk1_0) = k2_tarski(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( X1 = X2
    | k2_enumset1(X1,X1,X1,X1) != k2_enumset1(X2,X2,X2,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_12,c_0_13]),c_0_14]),c_0_14])).

cnf(c_0_17,negated_conjecture,
    ( k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0) = k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_13]),c_0_14]),c_0_14])).

fof(c_0_18,plain,(
    ! [X19,X20,X21,X22] : k2_enumset1(X19,X20,X21,X22) = k2_xboole_0(k2_tarski(X19,X20),k2_tarski(X21,X22)) ),
    inference(variable_rename,[status(thm)],[t45_enumset1])).

cnf(c_0_19,negated_conjecture,
    ( esk1_0 = X1
    | k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0) != k2_enumset1(X1,X1,X1,X2) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_20,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_21,negated_conjecture,
    ( esk1_0 = esk2_0 ),
    inference(er,[status(thm)],[c_0_19])).

fof(c_0_22,plain,(
    ! [X7,X8,X9,X10] : k2_enumset1(X7,X8,X9,X10) = k2_enumset1(X8,X9,X10,X7) ),
    inference(variable_rename,[status(thm)],[t111_enumset1])).

cnf(c_0_23,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X3,X3,X3,X4)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_14]),c_0_14])).

cnf(c_0_24,negated_conjecture,
    ( k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0) = k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_21]),c_0_21]),c_0_21]),c_0_21])).

fof(c_0_25,plain,(
    ! [X14,X15] : k2_tarski(X14,X15) = k2_xboole_0(k1_tarski(X14),k1_tarski(X15)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

cnf(c_0_26,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X2,X3,X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( k2_enumset1(X1,X2,esk2_0,esk3_0) = k2_enumset1(X1,X2,esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_23])).

cnf(c_0_28,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_29,plain,
    ( X1 = X2
    | k2_enumset1(X1,X1,X1,X1) != k2_enumset1(X3,X2,X2,X2) ),
    inference(spm,[status(thm)],[c_0_16,c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( k2_enumset1(esk2_0,esk3_0,X1,X2) = k2_enumset1(esk2_0,esk2_0,X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_27]),c_0_23])).

cnf(c_0_31,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k2_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_13]),c_0_13]),c_0_14]),c_0_14]),c_0_14])).

cnf(c_0_32,negated_conjecture,
    ( X1 = esk3_0
    | k2_enumset1(X1,X1,X1,X1) != k2_enumset1(esk2_0,esk2_0,esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_33,plain,
    ( k2_enumset1(X1,X1,X2,X2) = k2_enumset1(X1,X1,X1,X2) ),
    inference(rw,[status(thm)],[c_0_31,c_0_23])).

cnf(c_0_34,negated_conjecture,
    ( X1 = esk3_0
    | k2_enumset1(X1,X1,X1,X1) != k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_33]),c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( esk2_0 != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_36,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_34]),c_0_35]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:04:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.027 s
% 0.19/0.37  # Presaturation interreduction done
% 0.19/0.37  
% 0.19/0.37  # Proof found!
% 0.19/0.37  # SZS status Theorem
% 0.19/0.37  # SZS output start CNFRefutation
% 0.19/0.37  fof(t9_zfmisc_1, conjecture, ![X1, X2, X3]:(k1_tarski(X1)=k2_tarski(X2,X3)=>X2=X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_zfmisc_1)).
% 0.19/0.37  fof(t8_zfmisc_1, axiom, ![X1, X2, X3]:(k1_tarski(X1)=k2_tarski(X2,X3)=>X1=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_zfmisc_1)).
% 0.19/0.37  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.37  fof(t77_enumset1, axiom, ![X1, X2]:k2_enumset1(X1,X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_enumset1)).
% 0.19/0.37  fof(t45_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_enumset1)).
% 0.19/0.37  fof(t111_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X2,X3,X4,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t111_enumset1)).
% 0.19/0.37  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 0.19/0.37  fof(c_0_7, negated_conjecture, ~(![X1, X2, X3]:(k1_tarski(X1)=k2_tarski(X2,X3)=>X2=X3)), inference(assume_negation,[status(cth)],[t9_zfmisc_1])).
% 0.19/0.37  fof(c_0_8, plain, ![X34, X35, X36]:(k1_tarski(X34)!=k2_tarski(X35,X36)|X34=X35), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_zfmisc_1])])).
% 0.19/0.37  fof(c_0_9, plain, ![X23]:k2_tarski(X23,X23)=k1_tarski(X23), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.37  fof(c_0_10, plain, ![X27, X28]:k2_enumset1(X27,X27,X27,X28)=k2_tarski(X27,X28), inference(variable_rename,[status(thm)],[t77_enumset1])).
% 0.19/0.37  fof(c_0_11, negated_conjecture, (k1_tarski(esk1_0)=k2_tarski(esk2_0,esk3_0)&esk2_0!=esk3_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.19/0.37  cnf(c_0_12, plain, (X1=X2|k1_tarski(X1)!=k2_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.37  cnf(c_0_13, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.37  cnf(c_0_14, plain, (k2_enumset1(X1,X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.37  cnf(c_0_15, negated_conjecture, (k1_tarski(esk1_0)=k2_tarski(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.37  cnf(c_0_16, plain, (X1=X2|k2_enumset1(X1,X1,X1,X1)!=k2_enumset1(X2,X2,X2,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_12, c_0_13]), c_0_14]), c_0_14])).
% 0.19/0.37  cnf(c_0_17, negated_conjecture, (k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0)=k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15, c_0_13]), c_0_14]), c_0_14])).
% 0.19/0.37  fof(c_0_18, plain, ![X19, X20, X21, X22]:k2_enumset1(X19,X20,X21,X22)=k2_xboole_0(k2_tarski(X19,X20),k2_tarski(X21,X22)), inference(variable_rename,[status(thm)],[t45_enumset1])).
% 0.19/0.37  cnf(c_0_19, negated_conjecture, (esk1_0=X1|k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0)!=k2_enumset1(X1,X1,X1,X2)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.19/0.37  cnf(c_0_20, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.37  cnf(c_0_21, negated_conjecture, (esk1_0=esk2_0), inference(er,[status(thm)],[c_0_19])).
% 0.19/0.37  fof(c_0_22, plain, ![X7, X8, X9, X10]:k2_enumset1(X7,X8,X9,X10)=k2_enumset1(X8,X9,X10,X7), inference(variable_rename,[status(thm)],[t111_enumset1])).
% 0.19/0.37  cnf(c_0_23, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X3,X3,X3,X4))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_14]), c_0_14])).
% 0.19/0.37  cnf(c_0_24, negated_conjecture, (k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0)=k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17, c_0_21]), c_0_21]), c_0_21]), c_0_21])).
% 0.19/0.37  fof(c_0_25, plain, ![X14, X15]:k2_tarski(X14,X15)=k2_xboole_0(k1_tarski(X14),k1_tarski(X15)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 0.19/0.37  cnf(c_0_26, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X2,X3,X4,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.37  cnf(c_0_27, negated_conjecture, (k2_enumset1(X1,X2,esk2_0,esk3_0)=k2_enumset1(X1,X2,esk2_0,esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_23])).
% 0.19/0.37  cnf(c_0_28, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.37  cnf(c_0_29, plain, (X1=X2|k2_enumset1(X1,X1,X1,X1)!=k2_enumset1(X3,X2,X2,X2)), inference(spm,[status(thm)],[c_0_16, c_0_26])).
% 0.19/0.37  cnf(c_0_30, negated_conjecture, (k2_enumset1(esk2_0,esk3_0,X1,X2)=k2_enumset1(esk2_0,esk2_0,X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_27]), c_0_23])).
% 0.19/0.37  cnf(c_0_31, plain, (k2_enumset1(X1,X1,X1,X2)=k2_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_13]), c_0_13]), c_0_14]), c_0_14]), c_0_14])).
% 0.19/0.37  cnf(c_0_32, negated_conjecture, (X1=esk3_0|k2_enumset1(X1,X1,X1,X1)!=k2_enumset1(esk2_0,esk2_0,esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.19/0.37  cnf(c_0_33, plain, (k2_enumset1(X1,X1,X2,X2)=k2_enumset1(X1,X1,X1,X2)), inference(rw,[status(thm)],[c_0_31, c_0_23])).
% 0.19/0.37  cnf(c_0_34, negated_conjecture, (X1=esk3_0|k2_enumset1(X1,X1,X1,X1)!=k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_33]), c_0_27])).
% 0.19/0.37  cnf(c_0_35, negated_conjecture, (esk2_0!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.37  cnf(c_0_36, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_34]), c_0_35]), ['proof']).
% 0.19/0.37  # SZS output end CNFRefutation
% 0.19/0.37  # Proof object total steps             : 37
% 0.19/0.37  # Proof object clause steps            : 22
% 0.19/0.37  # Proof object formula steps           : 15
% 0.19/0.37  # Proof object conjectures             : 14
% 0.19/0.37  # Proof object clause conjectures      : 11
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 8
% 0.19/0.37  # Proof object initial formulas used   : 7
% 0.19/0.37  # Proof object generating inferences   : 7
% 0.19/0.37  # Proof object simplifying inferences  : 23
% 0.19/0.37  # Training examples: 0 positive, 0 negative
% 0.19/0.37  # Parsed axioms                        : 14
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 17
% 0.19/0.37  # Removed in clause preprocessing      : 4
% 0.19/0.37  # Initial clauses in saturation        : 13
% 0.19/0.37  # Processed clauses                    : 50
% 0.19/0.37  # ...of these trivial                  : 1
% 0.19/0.37  # ...subsumed                          : 7
% 0.19/0.37  # ...remaining for further processing  : 42
% 0.19/0.37  # Other redundant clauses eliminated   : 2
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 1
% 0.19/0.37  # Backward-rewritten                   : 5
% 0.19/0.37  # Generated clauses                    : 324
% 0.19/0.37  # ...of the previous two non-trivial   : 251
% 0.19/0.37  # Contextual simplify-reflections      : 0
% 0.19/0.37  # Paramodulations                      : 316
% 0.19/0.37  # Factorizations                       : 0
% 0.19/0.37  # Equation resolutions                 : 8
% 0.19/0.37  # Propositional unsat checks           : 0
% 0.19/0.37  #    Propositional check models        : 0
% 0.19/0.37  #    Propositional check unsatisfiable : 0
% 0.19/0.37  #    Propositional clauses             : 0
% 0.19/0.37  #    Propositional clauses after purity: 0
% 0.19/0.37  #    Propositional unsat core size     : 0
% 0.19/0.37  #    Propositional preprocessing time  : 0.000
% 0.19/0.37  #    Propositional encoding time       : 0.000
% 0.19/0.37  #    Propositional solver time         : 0.000
% 0.19/0.37  #    Success case prop preproc time    : 0.000
% 0.19/0.37  #    Success case prop encoding time   : 0.000
% 0.19/0.37  #    Success case prop solver time     : 0.000
% 0.19/0.37  # Current number of processed clauses  : 22
% 0.19/0.37  #    Positive orientable unit clauses  : 7
% 0.19/0.37  #    Positive unorientable unit clauses: 6
% 0.19/0.37  #    Negative unit clauses             : 1
% 0.19/0.37  #    Non-unit-clauses                  : 8
% 0.19/0.37  # Current number of unprocessed clauses: 220
% 0.19/0.37  # ...number of literals in the above   : 449
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 21
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 43
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 43
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 6
% 0.19/0.37  # Unit Clause-clause subsumption calls : 15
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 123
% 0.19/0.37  # BW rewrite match successes           : 42
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 3623
% 0.19/0.37  
% 0.19/0.37  # -------------------------------------------------
% 0.19/0.37  # User time                : 0.029 s
% 0.19/0.37  # System time              : 0.005 s
% 0.19/0.37  # Total time               : 0.035 s
% 0.19/0.37  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------

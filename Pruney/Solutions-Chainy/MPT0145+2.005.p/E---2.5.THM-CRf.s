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
% DateTime   : Thu Dec  3 10:35:19 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   30 (  78 expanded)
%              Number of clauses        :   15 (  33 expanded)
%              Number of leaves         :    7 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :   30 (  78 expanded)
%              Number of equality atoms :   29 (  77 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    8 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t42_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(t44_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

fof(t61_enumset1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_enumset1)).

fof(t54_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_enumset1)).

fof(t58_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_enumset1(X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_enumset1)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(c_0_7,plain,(
    ! [X29,X30,X31] : k1_enumset1(X29,X30,X31) = k2_xboole_0(k1_tarski(X29),k2_tarski(X30,X31)) ),
    inference(variable_rename,[status(thm)],[t42_enumset1])).

fof(c_0_8,plain,(
    ! [X27,X28] : k2_tarski(X27,X28) = k2_xboole_0(k1_tarski(X27),k1_tarski(X28)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

fof(c_0_9,plain,(
    ! [X32,X33,X34,X35] : k2_enumset1(X32,X33,X34,X35) = k2_xboole_0(k1_tarski(X32),k1_enumset1(X33,X34,X35)) ),
    inference(variable_rename,[status(thm)],[t44_enumset1])).

cnf(c_0_10,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    inference(assume_negation,[status(cth)],[t61_enumset1])).

fof(c_0_13,plain,(
    ! [X49,X50,X51,X52,X53,X54] : k4_enumset1(X49,X50,X51,X52,X53,X54) = k2_xboole_0(k2_enumset1(X49,X50,X51,X52),k2_tarski(X53,X54)) ),
    inference(variable_rename,[status(thm)],[t54_enumset1])).

cnf(c_0_14,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k1_tarski(X3))) ),
    inference(rw,[status(thm)],[c_0_10,c_0_11])).

fof(c_0_16,negated_conjecture,(
    k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0) != k2_xboole_0(k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_tarski(esk7_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

cnf(c_0_17,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k2_xboole_0(k1_tarski(X3),k1_tarski(X4)))) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

fof(c_0_19,plain,(
    ! [X61,X62,X63,X64,X65,X66,X67] : k5_enumset1(X61,X62,X63,X64,X65,X66,X67) = k2_xboole_0(k1_enumset1(X61,X62,X63),k2_enumset1(X64,X65,X66,X67)) ),
    inference(variable_rename,[status(thm)],[t58_enumset1])).

cnf(c_0_20,negated_conjecture,
    ( k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0) != k2_xboole_0(k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_tarski(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k2_xboole_0(k1_tarski(X3),k1_tarski(X4)))),k2_xboole_0(k1_tarski(X5),k1_tarski(X6))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_11]),c_0_18])).

fof(c_0_22,plain,(
    ! [X12,X13,X14] : k2_xboole_0(k2_xboole_0(X12,X13),X14) = k2_xboole_0(X12,k2_xboole_0(X13,X14)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

cnf(c_0_23,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_enumset1(X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(esk1_0),k2_xboole_0(k1_tarski(esk2_0),k2_xboole_0(k1_tarski(esk3_0),k1_tarski(esk4_0)))),k2_xboole_0(k1_tarski(esk5_0),k1_tarski(esk6_0))),k1_tarski(esk7_0)) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_26,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k1_tarski(X3))),k2_xboole_0(k1_tarski(X4),k2_xboole_0(k1_tarski(X5),k2_xboole_0(k1_tarski(X6),k1_tarski(X7))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_15]),c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( k2_xboole_0(k1_tarski(esk1_0),k2_xboole_0(k1_tarski(esk2_0),k2_xboole_0(k1_tarski(esk3_0),k2_xboole_0(k1_tarski(esk4_0),k2_xboole_0(k1_tarski(esk5_0),k2_xboole_0(k1_tarski(esk6_0),k1_tarski(esk7_0))))))) != k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25]),c_0_25]),c_0_25]),c_0_25]),c_0_25]),c_0_25]),c_0_25]),c_0_25])).

cnf(c_0_28,plain,
    ( k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k2_xboole_0(k1_tarski(X3),k2_xboole_0(k1_tarski(X4),k2_xboole_0(k1_tarski(X5),k2_xboole_0(k1_tarski(X6),k1_tarski(X7))))))) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_25]),c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_28])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:44:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.39  #
% 0.20/0.39  # Preprocessing time       : 0.039 s
% 0.20/0.39  # Presaturation interreduction done
% 0.20/0.39  
% 0.20/0.39  # Proof found!
% 0.20/0.39  # SZS status Theorem
% 0.20/0.39  # SZS output start CNFRefutation
% 0.20/0.39  fof(t42_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 0.20/0.39  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 0.20/0.39  fof(t44_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 0.20/0.39  fof(t61_enumset1, conjecture, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X7)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_enumset1)).
% 0.20/0.39  fof(t54_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_tarski(X5,X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_enumset1)).
% 0.20/0.39  fof(t58_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k1_enumset1(X1,X2,X3),k2_enumset1(X4,X5,X6,X7)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_enumset1)).
% 0.20/0.39  fof(t4_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 0.20/0.39  fof(c_0_7, plain, ![X29, X30, X31]:k1_enumset1(X29,X30,X31)=k2_xboole_0(k1_tarski(X29),k2_tarski(X30,X31)), inference(variable_rename,[status(thm)],[t42_enumset1])).
% 0.20/0.39  fof(c_0_8, plain, ![X27, X28]:k2_tarski(X27,X28)=k2_xboole_0(k1_tarski(X27),k1_tarski(X28)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 0.20/0.39  fof(c_0_9, plain, ![X32, X33, X34, X35]:k2_enumset1(X32,X33,X34,X35)=k2_xboole_0(k1_tarski(X32),k1_enumset1(X33,X34,X35)), inference(variable_rename,[status(thm)],[t44_enumset1])).
% 0.20/0.39  cnf(c_0_10, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.39  cnf(c_0_11, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.39  fof(c_0_12, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X7))), inference(assume_negation,[status(cth)],[t61_enumset1])).
% 0.20/0.39  fof(c_0_13, plain, ![X49, X50, X51, X52, X53, X54]:k4_enumset1(X49,X50,X51,X52,X53,X54)=k2_xboole_0(k2_enumset1(X49,X50,X51,X52),k2_tarski(X53,X54)), inference(variable_rename,[status(thm)],[t54_enumset1])).
% 0.20/0.39  cnf(c_0_14, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.39  cnf(c_0_15, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k1_tarski(X3)))), inference(rw,[status(thm)],[c_0_10, c_0_11])).
% 0.20/0.39  fof(c_0_16, negated_conjecture, k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0)!=k2_xboole_0(k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_tarski(esk7_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.20/0.39  cnf(c_0_17, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_tarski(X5,X6))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.39  cnf(c_0_18, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k2_xboole_0(k1_tarski(X3),k1_tarski(X4))))), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.20/0.39  fof(c_0_19, plain, ![X61, X62, X63, X64, X65, X66, X67]:k5_enumset1(X61,X62,X63,X64,X65,X66,X67)=k2_xboole_0(k1_enumset1(X61,X62,X63),k2_enumset1(X64,X65,X66,X67)), inference(variable_rename,[status(thm)],[t58_enumset1])).
% 0.20/0.39  cnf(c_0_20, negated_conjecture, (k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0)!=k2_xboole_0(k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_tarski(esk7_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.39  cnf(c_0_21, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k2_xboole_0(k1_tarski(X3),k1_tarski(X4)))),k2_xboole_0(k1_tarski(X5),k1_tarski(X6)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17, c_0_11]), c_0_18])).
% 0.20/0.39  fof(c_0_22, plain, ![X12, X13, X14]:k2_xboole_0(k2_xboole_0(X12,X13),X14)=k2_xboole_0(X12,k2_xboole_0(X13,X14)), inference(variable_rename,[status(thm)],[t4_xboole_1])).
% 0.20/0.39  cnf(c_0_23, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k1_enumset1(X1,X2,X3),k2_enumset1(X4,X5,X6,X7))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.39  cnf(c_0_24, negated_conjecture, (k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0)!=k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(esk1_0),k2_xboole_0(k1_tarski(esk2_0),k2_xboole_0(k1_tarski(esk3_0),k1_tarski(esk4_0)))),k2_xboole_0(k1_tarski(esk5_0),k1_tarski(esk6_0))),k1_tarski(esk7_0))), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 0.20/0.39  cnf(c_0_25, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.39  cnf(c_0_26, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k1_tarski(X3))),k2_xboole_0(k1_tarski(X4),k2_xboole_0(k1_tarski(X5),k2_xboole_0(k1_tarski(X6),k1_tarski(X7)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_15]), c_0_18])).
% 0.20/0.39  cnf(c_0_27, negated_conjecture, (k2_xboole_0(k1_tarski(esk1_0),k2_xboole_0(k1_tarski(esk2_0),k2_xboole_0(k1_tarski(esk3_0),k2_xboole_0(k1_tarski(esk4_0),k2_xboole_0(k1_tarski(esk5_0),k2_xboole_0(k1_tarski(esk6_0),k1_tarski(esk7_0)))))))!=k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_25]), c_0_25]), c_0_25]), c_0_25]), c_0_25]), c_0_25]), c_0_25]), c_0_25])).
% 0.20/0.39  cnf(c_0_28, plain, (k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k2_xboole_0(k1_tarski(X3),k2_xboole_0(k1_tarski(X4),k2_xboole_0(k1_tarski(X5),k2_xboole_0(k1_tarski(X6),k1_tarski(X7)))))))=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_25]), c_0_25])).
% 0.20/0.39  cnf(c_0_29, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_28])]), ['proof']).
% 0.20/0.39  # SZS output end CNFRefutation
% 0.20/0.39  # Proof object total steps             : 30
% 0.20/0.39  # Proof object clause steps            : 15
% 0.20/0.39  # Proof object formula steps           : 15
% 0.20/0.39  # Proof object conjectures             : 7
% 0.20/0.39  # Proof object clause conjectures      : 4
% 0.20/0.39  # Proof object formula conjectures     : 3
% 0.20/0.39  # Proof object initial clauses used    : 7
% 0.20/0.39  # Proof object initial formulas used   : 7
% 0.20/0.39  # Proof object generating inferences   : 0
% 0.20/0.39  # Proof object simplifying inferences  : 19
% 0.20/0.39  # Training examples: 0 positive, 0 negative
% 0.20/0.39  # Parsed axioms                        : 14
% 0.20/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.39  # Initial clauses                      : 14
% 0.20/0.39  # Removed in clause preprocessing      : 5
% 0.20/0.39  # Initial clauses in saturation        : 9
% 0.20/0.39  # Processed clauses                    : 7
% 0.20/0.39  # ...of these trivial                  : 4
% 0.20/0.39  # ...subsumed                          : 0
% 0.20/0.39  # ...remaining for further processing  : 3
% 0.20/0.39  # Other redundant clauses eliminated   : 0
% 0.20/0.39  # Clauses deleted for lack of memory   : 0
% 0.20/0.39  # Backward-subsumed                    : 0
% 0.20/0.39  # Backward-rewritten                   : 1
% 0.20/0.39  # Generated clauses                    : 0
% 0.20/0.39  # ...of the previous two non-trivial   : 0
% 0.20/0.39  # Contextual simplify-reflections      : 0
% 0.20/0.39  # Paramodulations                      : 0
% 0.20/0.39  # Factorizations                       : 0
% 0.20/0.39  # Equation resolutions                 : 0
% 0.20/0.39  # Propositional unsat checks           : 0
% 0.20/0.39  #    Propositional check models        : 0
% 0.20/0.39  #    Propositional check unsatisfiable : 0
% 0.20/0.39  #    Propositional clauses             : 0
% 0.20/0.39  #    Propositional clauses after purity: 0
% 0.20/0.39  #    Propositional unsat core size     : 0
% 0.20/0.39  #    Propositional preprocessing time  : 0.000
% 0.20/0.39  #    Propositional encoding time       : 0.000
% 0.20/0.39  #    Propositional solver time         : 0.000
% 0.20/0.39  #    Success case prop preproc time    : 0.000
% 0.20/0.39  #    Success case prop encoding time   : 0.000
% 0.20/0.39  #    Success case prop solver time     : 0.000
% 0.20/0.39  # Current number of processed clauses  : 2
% 0.20/0.39  #    Positive orientable unit clauses  : 2
% 0.20/0.39  #    Positive unorientable unit clauses: 0
% 0.20/0.39  #    Negative unit clauses             : 0
% 0.20/0.39  #    Non-unit-clauses                  : 0
% 0.20/0.39  # Current number of unprocessed clauses: 2
% 0.20/0.39  # ...number of literals in the above   : 2
% 0.20/0.39  # Current number of archived formulas  : 0
% 0.20/0.39  # Current number of archived clauses   : 6
% 0.20/0.39  # Clause-clause subsumption calls (NU) : 0
% 0.20/0.39  # Rec. Clause-clause subsumption calls : 0
% 0.20/0.39  # Non-unit clause-clause subsumptions  : 0
% 0.20/0.39  # Unit Clause-clause subsumption calls : 0
% 0.20/0.39  # Rewrite failures with RHS unbound    : 0
% 0.20/0.39  # BW rewrite match attempts            : 4
% 0.20/0.39  # BW rewrite match successes           : 1
% 0.20/0.39  # Condensation attempts                : 0
% 0.20/0.39  # Condensation successes               : 0
% 0.20/0.39  # Termbank termtop insertions          : 1153
% 0.20/0.39  
% 0.20/0.39  # -------------------------------------------------
% 0.20/0.39  # User time                : 0.043 s
% 0.20/0.39  # System time              : 0.001 s
% 0.20/0.39  # Total time               : 0.044 s
% 0.20/0.39  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------

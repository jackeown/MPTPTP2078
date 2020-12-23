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
% DateTime   : Thu Dec  3 10:36:36 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   33 ( 145 expanded)
%              Number of clauses        :   16 (  54 expanded)
%              Number of leaves         :    8 (  45 expanded)
%              Depth                    :    7
%              Number of atoms          :   33 ( 145 expanded)
%              Number of equality atoms :   32 ( 144 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t125_enumset1,conjecture,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X4,X3,X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(t123_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X4,X2,X3,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_enumset1)).

fof(t105_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X3,X4,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_enumset1)).

fof(t107_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X4,X3,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X4,X3,X2,X1) ),
    inference(assume_negation,[status(cth)],[t125_enumset1])).

fof(c_0_9,negated_conjecture,(
    k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0) != k2_enumset1(esk4_0,esk3_0,esk2_0,esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_10,plain,(
    ! [X24,X25,X26,X27] : k3_enumset1(X24,X24,X25,X26,X27) = k2_enumset1(X24,X25,X26,X27) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_11,plain,(
    ! [X28,X29,X30,X31,X32] : k4_enumset1(X28,X28,X29,X30,X31,X32) = k3_enumset1(X28,X29,X30,X31,X32) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_12,plain,(
    ! [X33,X34,X35,X36,X37,X38] : k5_enumset1(X33,X33,X34,X35,X36,X37,X38) = k4_enumset1(X33,X34,X35,X36,X37,X38) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_13,plain,(
    ! [X39,X40,X41,X42,X43,X44,X45] : k6_enumset1(X39,X39,X40,X41,X42,X43,X44,X45) = k5_enumset1(X39,X40,X41,X42,X43,X44,X45) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_14,plain,(
    ! [X20,X21,X22,X23] : k2_enumset1(X20,X21,X22,X23) = k2_enumset1(X23,X21,X22,X20) ),
    inference(variable_rename,[status(thm)],[t123_enumset1])).

cnf(c_0_15,negated_conjecture,
    ( k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0) != k2_enumset1(esk4_0,esk3_0,esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X4,X2,X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_21,plain,(
    ! [X8,X9,X10,X11] : k2_enumset1(X8,X9,X10,X11) = k2_enumset1(X8,X10,X11,X9) ),
    inference(variable_rename,[status(thm)],[t105_enumset1])).

fof(c_0_22,plain,(
    ! [X12,X13,X14,X15] : k2_enumset1(X12,X13,X14,X15) = k2_enumset1(X12,X15,X14,X13) ),
    inference(variable_rename,[status(thm)],[t107_enumset1])).

cnf(c_0_23,negated_conjecture,
    ( k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk3_0,esk2_0,esk1_0) != k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_16]),c_0_16]),c_0_17]),c_0_17]),c_0_18]),c_0_18]),c_0_19]),c_0_19])).

cnf(c_0_24,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4) = k6_enumset1(X4,X4,X4,X4,X4,X2,X3,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_16]),c_0_16]),c_0_17]),c_0_17]),c_0_18]),c_0_18]),c_0_19]),c_0_19])).

cnf(c_0_25,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X3,X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X4,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk2_0,esk3_0,esk1_0) != k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk3_0,esk2_0,esk1_0) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_28,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4) = k6_enumset1(X1,X1,X1,X1,X1,X3,X4,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_16]),c_0_16]),c_0_17]),c_0_17]),c_0_18]),c_0_18]),c_0_19]),c_0_19])).

cnf(c_0_29,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4) = k6_enumset1(X1,X1,X1,X1,X1,X4,X3,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_16]),c_0_16]),c_0_17]),c_0_17]),c_0_18]),c_0_18]),c_0_19]),c_0_19])).

cnf(c_0_30,negated_conjecture,
    ( k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk3_0,esk1_0,esk2_0) != k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk3_0,esk2_0,esk1_0) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_31,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4) = k6_enumset1(X1,X1,X1,X1,X1,X2,X4,X3) ),
    inference(spm,[status(thm)],[c_0_29,c_0_28])).

cnf(c_0_32,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_31])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.08  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.09  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.08/0.28  % Computer   : n020.cluster.edu
% 0.08/0.28  % Model      : x86_64 x86_64
% 0.08/0.28  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.08/0.28  % Memory     : 8042.1875MB
% 0.08/0.28  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.08/0.28  % CPULimit   : 60
% 0.08/0.28  % WCLimit    : 600
% 0.08/0.28  % DateTime   : Tue Dec  1 13:44:52 EST 2020
% 0.08/0.28  % CPUTime    : 
% 0.08/0.28  # Version: 2.5pre002
% 0.08/0.28  # No SInE strategy applied
% 0.08/0.28  # Trying AutoSched0 for 299 seconds
% 0.12/0.31  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.12/0.31  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.12/0.31  #
% 0.12/0.31  # Preprocessing time       : 0.026 s
% 0.12/0.31  # Presaturation interreduction done
% 0.12/0.31  
% 0.12/0.31  # Proof found!
% 0.12/0.31  # SZS status Theorem
% 0.12/0.31  # SZS output start CNFRefutation
% 0.12/0.31  fof(t125_enumset1, conjecture, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X4,X3,X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_enumset1)).
% 0.12/0.31  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.12/0.31  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.12/0.31  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.12/0.31  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 0.12/0.31  fof(t123_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X4,X2,X3,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_enumset1)).
% 0.12/0.31  fof(t105_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X1,X3,X4,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t105_enumset1)).
% 0.12/0.31  fof(t107_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X1,X4,X3,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t107_enumset1)).
% 0.12/0.31  fof(c_0_8, negated_conjecture, ~(![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X4,X3,X2,X1)), inference(assume_negation,[status(cth)],[t125_enumset1])).
% 0.12/0.31  fof(c_0_9, negated_conjecture, k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0)!=k2_enumset1(esk4_0,esk3_0,esk2_0,esk1_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.12/0.31  fof(c_0_10, plain, ![X24, X25, X26, X27]:k3_enumset1(X24,X24,X25,X26,X27)=k2_enumset1(X24,X25,X26,X27), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.12/0.31  fof(c_0_11, plain, ![X28, X29, X30, X31, X32]:k4_enumset1(X28,X28,X29,X30,X31,X32)=k3_enumset1(X28,X29,X30,X31,X32), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.12/0.31  fof(c_0_12, plain, ![X33, X34, X35, X36, X37, X38]:k5_enumset1(X33,X33,X34,X35,X36,X37,X38)=k4_enumset1(X33,X34,X35,X36,X37,X38), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.12/0.31  fof(c_0_13, plain, ![X39, X40, X41, X42, X43, X44, X45]:k6_enumset1(X39,X39,X40,X41,X42,X43,X44,X45)=k5_enumset1(X39,X40,X41,X42,X43,X44,X45), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.12/0.31  fof(c_0_14, plain, ![X20, X21, X22, X23]:k2_enumset1(X20,X21,X22,X23)=k2_enumset1(X23,X21,X22,X20), inference(variable_rename,[status(thm)],[t123_enumset1])).
% 0.12/0.31  cnf(c_0_15, negated_conjecture, (k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0)!=k2_enumset1(esk4_0,esk3_0,esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.31  cnf(c_0_16, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.31  cnf(c_0_17, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.31  cnf(c_0_18, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.31  cnf(c_0_19, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.31  cnf(c_0_20, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X4,X2,X3,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.31  fof(c_0_21, plain, ![X8, X9, X10, X11]:k2_enumset1(X8,X9,X10,X11)=k2_enumset1(X8,X10,X11,X9), inference(variable_rename,[status(thm)],[t105_enumset1])).
% 0.12/0.31  fof(c_0_22, plain, ![X12, X13, X14, X15]:k2_enumset1(X12,X13,X14,X15)=k2_enumset1(X12,X15,X14,X13), inference(variable_rename,[status(thm)],[t107_enumset1])).
% 0.12/0.31  cnf(c_0_23, negated_conjecture, (k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk3_0,esk2_0,esk1_0)!=k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15, c_0_16]), c_0_16]), c_0_17]), c_0_17]), c_0_18]), c_0_18]), c_0_19]), c_0_19])).
% 0.12/0.31  cnf(c_0_24, plain, (k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4)=k6_enumset1(X4,X4,X4,X4,X4,X2,X3,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_16]), c_0_16]), c_0_17]), c_0_17]), c_0_18]), c_0_18]), c_0_19]), c_0_19])).
% 0.12/0.31  cnf(c_0_25, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X1,X3,X4,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.12/0.31  cnf(c_0_26, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X1,X4,X3,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.31  cnf(c_0_27, negated_conjecture, (k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk2_0,esk3_0,esk1_0)!=k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk3_0,esk2_0,esk1_0)), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 0.12/0.31  cnf(c_0_28, plain, (k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4)=k6_enumset1(X1,X1,X1,X1,X1,X3,X4,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_16]), c_0_16]), c_0_17]), c_0_17]), c_0_18]), c_0_18]), c_0_19]), c_0_19])).
% 0.12/0.31  cnf(c_0_29, plain, (k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4)=k6_enumset1(X1,X1,X1,X1,X1,X4,X3,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_16]), c_0_16]), c_0_17]), c_0_17]), c_0_18]), c_0_18]), c_0_19]), c_0_19])).
% 0.12/0.31  cnf(c_0_30, negated_conjecture, (k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk3_0,esk1_0,esk2_0)!=k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk3_0,esk2_0,esk1_0)), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 0.12/0.31  cnf(c_0_31, plain, (k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4)=k6_enumset1(X1,X1,X1,X1,X1,X2,X4,X3)), inference(spm,[status(thm)],[c_0_29, c_0_28])).
% 0.12/0.31  cnf(c_0_32, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_31])]), ['proof']).
% 0.12/0.31  # SZS output end CNFRefutation
% 0.12/0.31  # Proof object total steps             : 33
% 0.12/0.31  # Proof object clause steps            : 16
% 0.12/0.31  # Proof object formula steps           : 17
% 0.12/0.31  # Proof object conjectures             : 8
% 0.12/0.31  # Proof object clause conjectures      : 5
% 0.12/0.31  # Proof object formula conjectures     : 3
% 0.12/0.31  # Proof object initial clauses used    : 8
% 0.12/0.31  # Proof object initial formulas used   : 8
% 0.12/0.31  # Proof object generating inferences   : 1
% 0.12/0.31  # Proof object simplifying inferences  : 36
% 0.12/0.31  # Training examples: 0 positive, 0 negative
% 0.12/0.31  # Parsed axioms                        : 9
% 0.12/0.31  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.31  # Initial clauses                      : 9
% 0.12/0.31  # Removed in clause preprocessing      : 4
% 0.12/0.31  # Initial clauses in saturation        : 5
% 0.12/0.31  # Processed clauses                    : 29
% 0.12/0.31  # ...of these trivial                  : 0
% 0.12/0.31  # ...subsumed                          : 11
% 0.12/0.31  # ...remaining for further processing  : 18
% 0.12/0.31  # Other redundant clauses eliminated   : 0
% 0.12/0.31  # Clauses deleted for lack of memory   : 0
% 0.12/0.31  # Backward-subsumed                    : 0
% 0.12/0.31  # Backward-rewritten                   : 3
% 0.12/0.31  # Generated clauses                    : 192
% 0.12/0.31  # ...of the previous two non-trivial   : 158
% 0.12/0.31  # Contextual simplify-reflections      : 0
% 0.12/0.31  # Paramodulations                      : 192
% 0.12/0.31  # Factorizations                       : 0
% 0.12/0.31  # Equation resolutions                 : 0
% 0.12/0.31  # Propositional unsat checks           : 0
% 0.12/0.31  #    Propositional check models        : 0
% 0.12/0.31  #    Propositional check unsatisfiable : 0
% 0.12/0.31  #    Propositional clauses             : 0
% 0.12/0.31  #    Propositional clauses after purity: 0
% 0.12/0.31  #    Propositional unsat core size     : 0
% 0.12/0.31  #    Propositional preprocessing time  : 0.000
% 0.12/0.31  #    Propositional encoding time       : 0.000
% 0.12/0.31  #    Propositional solver time         : 0.000
% 0.12/0.31  #    Success case prop preproc time    : 0.000
% 0.12/0.31  #    Success case prop encoding time   : 0.000
% 0.12/0.31  #    Success case prop solver time     : 0.000
% 0.12/0.31  # Current number of processed clauses  : 10
% 0.12/0.31  #    Positive orientable unit clauses  : 0
% 0.12/0.31  #    Positive unorientable unit clauses: 10
% 0.12/0.31  #    Negative unit clauses             : 0
% 0.12/0.31  #    Non-unit-clauses                  : 0
% 0.12/0.31  # Current number of unprocessed clauses: 139
% 0.12/0.31  # ...number of literals in the above   : 139
% 0.12/0.31  # Current number of archived formulas  : 0
% 0.12/0.31  # Current number of archived clauses   : 12
% 0.12/0.31  # Clause-clause subsumption calls (NU) : 0
% 0.12/0.31  # Rec. Clause-clause subsumption calls : 0
% 0.12/0.31  # Non-unit clause-clause subsumptions  : 0
% 0.12/0.31  # Unit Clause-clause subsumption calls : 51
% 0.12/0.31  # Rewrite failures with RHS unbound    : 0
% 0.12/0.31  # BW rewrite match attempts            : 182
% 0.12/0.31  # BW rewrite match successes           : 182
% 0.12/0.31  # Condensation attempts                : 0
% 0.12/0.31  # Condensation successes               : 0
% 0.12/0.31  # Termbank termtop insertions          : 975
% 0.12/0.31  
% 0.12/0.31  # -------------------------------------------------
% 0.12/0.31  # User time                : 0.026 s
% 0.12/0.31  # System time              : 0.004 s
% 0.12/0.31  # Total time               : 0.030 s
% 0.12/0.31  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------

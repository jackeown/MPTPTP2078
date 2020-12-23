%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:54 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   37 (  95 expanded)
%              Number of clauses        :   18 (  36 expanded)
%              Number of leaves         :    9 (  28 expanded)
%              Depth                    :    8
%              Number of atoms          :   62 ( 142 expanded)
%              Number of equality atoms :   61 ( 141 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t130_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( X1 != k1_xboole_0
     => ( k2_zfmisc_1(k1_tarski(X2),X1) != k1_xboole_0
        & k2_zfmisc_1(X1,k1_tarski(X2)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t20_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
    <=> X1 != X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2] :
        ( X1 != k1_xboole_0
       => ( k2_zfmisc_1(k1_tarski(X2),X1) != k1_xboole_0
          & k2_zfmisc_1(X1,k1_tarski(X2)) != k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t130_zfmisc_1])).

fof(c_0_10,negated_conjecture,
    ( esk1_0 != k1_xboole_0
    & ( k2_zfmisc_1(k1_tarski(esk2_0),esk1_0) = k1_xboole_0
      | k2_zfmisc_1(esk1_0,k1_tarski(esk2_0)) = k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_11,plain,(
    ! [X8] : k2_tarski(X8,X8) = k1_tarski(X8) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_12,plain,(
    ! [X9,X10] : k1_enumset1(X9,X9,X10) = k2_tarski(X9,X10) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_13,plain,(
    ! [X11,X12,X13] : k2_enumset1(X11,X11,X12,X13) = k1_enumset1(X11,X12,X13) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_14,plain,(
    ! [X14,X15,X16,X17] : k3_enumset1(X14,X14,X15,X16,X17) = k2_enumset1(X14,X15,X16,X17) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_15,plain,(
    ! [X20,X21] :
      ( ( k4_xboole_0(k1_tarski(X20),k1_tarski(X21)) != k1_tarski(X20)
        | X20 != X21 )
      & ( X20 = X21
        | k4_xboole_0(k1_tarski(X20),k1_tarski(X21)) = k1_tarski(X20) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_zfmisc_1])])).

fof(c_0_16,plain,(
    ! [X18,X19] :
      ( ( k2_zfmisc_1(X18,X19) != k1_xboole_0
        | X18 = k1_xboole_0
        | X19 = k1_xboole_0 )
      & ( X18 != k1_xboole_0
        | k2_zfmisc_1(X18,X19) = k1_xboole_0 )
      & ( X19 != k1_xboole_0
        | k2_zfmisc_1(X18,X19) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_17,negated_conjecture,
    ( k2_zfmisc_1(k1_tarski(esk2_0),esk1_0) = k1_xboole_0
    | k2_zfmisc_1(esk1_0,k1_tarski(esk2_0)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) != k1_tarski(X1)
    | X1 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k2_zfmisc_1(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)) = k1_xboole_0
    | k2_zfmisc_1(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),esk1_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_18]),c_0_18]),c_0_19]),c_0_19]),c_0_20]),c_0_20]),c_0_21]),c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_26,plain,
    ( X1 != X2
    | k4_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X2,X2,X2,X2,X2)) != k3_enumset1(X1,X1,X1,X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_18]),c_0_18]),c_0_18]),c_0_19]),c_0_19]),c_0_19]),c_0_20]),c_0_20]),c_0_20]),c_0_21]),c_0_21]),c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)) = k1_xboole_0
    | k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])).

fof(c_0_28,plain,(
    ! [X6,X7] : k4_xboole_0(X6,k2_xboole_0(X6,X7)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

fof(c_0_29,plain,(
    ! [X5] : k2_xboole_0(X5,k1_xboole_0) = X5 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_30,plain,
    ( k4_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1)) != k3_enumset1(X1,X1,X1,X1,X1) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_27]),c_0_25])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_33,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_35,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_36,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_35])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.32  % Computer   : n002.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 13:59:52 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  # Version: 2.5pre002
% 0.12/0.32  # No SInE strategy applied
% 0.12/0.32  # Trying AutoSched0 for 299 seconds
% 0.18/0.35  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.18/0.35  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.18/0.35  #
% 0.18/0.35  # Preprocessing time       : 0.028 s
% 0.18/0.35  # Presaturation interreduction done
% 0.18/0.35  
% 0.18/0.35  # Proof found!
% 0.18/0.35  # SZS status Theorem
% 0.18/0.35  # SZS output start CNFRefutation
% 0.18/0.35  fof(t130_zfmisc_1, conjecture, ![X1, X2]:(X1!=k1_xboole_0=>(k2_zfmisc_1(k1_tarski(X2),X1)!=k1_xboole_0&k2_zfmisc_1(X1,k1_tarski(X2))!=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t130_zfmisc_1)).
% 0.18/0.35  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.18/0.35  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.18/0.35  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.18/0.35  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.18/0.35  fof(t20_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)<=>X1!=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 0.18/0.35  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.18/0.35  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 0.18/0.35  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 0.18/0.35  fof(c_0_9, negated_conjecture, ~(![X1, X2]:(X1!=k1_xboole_0=>(k2_zfmisc_1(k1_tarski(X2),X1)!=k1_xboole_0&k2_zfmisc_1(X1,k1_tarski(X2))!=k1_xboole_0))), inference(assume_negation,[status(cth)],[t130_zfmisc_1])).
% 0.18/0.35  fof(c_0_10, negated_conjecture, (esk1_0!=k1_xboole_0&(k2_zfmisc_1(k1_tarski(esk2_0),esk1_0)=k1_xboole_0|k2_zfmisc_1(esk1_0,k1_tarski(esk2_0))=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.18/0.35  fof(c_0_11, plain, ![X8]:k2_tarski(X8,X8)=k1_tarski(X8), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.18/0.35  fof(c_0_12, plain, ![X9, X10]:k1_enumset1(X9,X9,X10)=k2_tarski(X9,X10), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.18/0.35  fof(c_0_13, plain, ![X11, X12, X13]:k2_enumset1(X11,X11,X12,X13)=k1_enumset1(X11,X12,X13), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.18/0.35  fof(c_0_14, plain, ![X14, X15, X16, X17]:k3_enumset1(X14,X14,X15,X16,X17)=k2_enumset1(X14,X15,X16,X17), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.18/0.35  fof(c_0_15, plain, ![X20, X21]:((k4_xboole_0(k1_tarski(X20),k1_tarski(X21))!=k1_tarski(X20)|X20!=X21)&(X20=X21|k4_xboole_0(k1_tarski(X20),k1_tarski(X21))=k1_tarski(X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_zfmisc_1])])).
% 0.18/0.35  fof(c_0_16, plain, ![X18, X19]:((k2_zfmisc_1(X18,X19)!=k1_xboole_0|(X18=k1_xboole_0|X19=k1_xboole_0))&((X18!=k1_xboole_0|k2_zfmisc_1(X18,X19)=k1_xboole_0)&(X19!=k1_xboole_0|k2_zfmisc_1(X18,X19)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.18/0.35  cnf(c_0_17, negated_conjecture, (k2_zfmisc_1(k1_tarski(esk2_0),esk1_0)=k1_xboole_0|k2_zfmisc_1(esk1_0,k1_tarski(esk2_0))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.35  cnf(c_0_18, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.35  cnf(c_0_19, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.35  cnf(c_0_20, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.35  cnf(c_0_21, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.35  cnf(c_0_22, plain, (k4_xboole_0(k1_tarski(X1),k1_tarski(X2))!=k1_tarski(X1)|X1!=X2), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.35  cnf(c_0_23, plain, (X1=k1_xboole_0|X2=k1_xboole_0|k2_zfmisc_1(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.35  cnf(c_0_24, negated_conjecture, (k2_zfmisc_1(esk1_0,k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))=k1_xboole_0|k2_zfmisc_1(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),esk1_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17, c_0_18]), c_0_18]), c_0_19]), c_0_19]), c_0_20]), c_0_20]), c_0_21]), c_0_21])).
% 0.18/0.35  cnf(c_0_25, negated_conjecture, (esk1_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.35  cnf(c_0_26, plain, (X1!=X2|k4_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X2,X2,X2,X2,X2))!=k3_enumset1(X1,X1,X1,X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_18]), c_0_18]), c_0_18]), c_0_19]), c_0_19]), c_0_19]), c_0_20]), c_0_20]), c_0_20]), c_0_21]), c_0_21]), c_0_21])).
% 0.18/0.35  cnf(c_0_27, negated_conjecture, (k2_zfmisc_1(esk1_0,k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))=k1_xboole_0|k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])).
% 0.18/0.35  fof(c_0_28, plain, ![X6, X7]:k4_xboole_0(X6,k2_xboole_0(X6,X7))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 0.18/0.35  fof(c_0_29, plain, ![X5]:k2_xboole_0(X5,k1_xboole_0)=X5, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.18/0.35  cnf(c_0_30, plain, (k4_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1))!=k3_enumset1(X1,X1,X1,X1,X1)), inference(er,[status(thm)],[c_0_26])).
% 0.18/0.35  cnf(c_0_31, negated_conjecture, (k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_27]), c_0_25])).
% 0.18/0.35  cnf(c_0_32, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.18/0.35  cnf(c_0_33, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.18/0.35  cnf(c_0_34, negated_conjecture, (k4_xboole_0(k1_xboole_0,k1_xboole_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.18/0.35  cnf(c_0_35, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.18/0.35  cnf(c_0_36, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_35])]), ['proof']).
% 0.18/0.35  # SZS output end CNFRefutation
% 0.18/0.35  # Proof object total steps             : 37
% 0.18/0.35  # Proof object clause steps            : 18
% 0.18/0.35  # Proof object formula steps           : 19
% 0.18/0.35  # Proof object conjectures             : 10
% 0.18/0.35  # Proof object clause conjectures      : 7
% 0.18/0.35  # Proof object formula conjectures     : 3
% 0.18/0.35  # Proof object initial clauses used    : 10
% 0.18/0.35  # Proof object initial formulas used   : 9
% 0.18/0.35  # Proof object generating inferences   : 4
% 0.18/0.35  # Proof object simplifying inferences  : 25
% 0.18/0.35  # Training examples: 0 positive, 0 negative
% 0.18/0.35  # Parsed axioms                        : 9
% 0.18/0.35  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.35  # Initial clauses                      : 13
% 0.18/0.35  # Removed in clause preprocessing      : 4
% 0.18/0.35  # Initial clauses in saturation        : 9
% 0.18/0.35  # Processed clauses                    : 25
% 0.18/0.35  # ...of these trivial                  : 0
% 0.18/0.35  # ...subsumed                          : 0
% 0.18/0.35  # ...remaining for further processing  : 25
% 0.18/0.35  # Other redundant clauses eliminated   : 3
% 0.18/0.35  # Clauses deleted for lack of memory   : 0
% 0.18/0.35  # Backward-subsumed                    : 0
% 0.18/0.35  # Backward-rewritten                   : 4
% 0.18/0.35  # Generated clauses                    : 9
% 0.18/0.35  # ...of the previous two non-trivial   : 9
% 0.18/0.35  # Contextual simplify-reflections      : 0
% 0.18/0.35  # Paramodulations                      : 6
% 0.18/0.35  # Factorizations                       : 0
% 0.18/0.35  # Equation resolutions                 : 3
% 0.18/0.35  # Propositional unsat checks           : 0
% 0.18/0.35  #    Propositional check models        : 0
% 0.18/0.35  #    Propositional check unsatisfiable : 0
% 0.18/0.35  #    Propositional clauses             : 0
% 0.18/0.35  #    Propositional clauses after purity: 0
% 0.18/0.35  #    Propositional unsat core size     : 0
% 0.18/0.35  #    Propositional preprocessing time  : 0.000
% 0.18/0.35  #    Propositional encoding time       : 0.000
% 0.18/0.35  #    Propositional solver time         : 0.000
% 0.18/0.35  #    Success case prop preproc time    : 0.000
% 0.18/0.35  #    Success case prop encoding time   : 0.000
% 0.18/0.35  #    Success case prop solver time     : 0.000
% 0.18/0.35  # Current number of processed clauses  : 9
% 0.18/0.35  #    Positive orientable unit clauses  : 6
% 0.18/0.35  #    Positive unorientable unit clauses: 0
% 0.18/0.35  #    Negative unit clauses             : 1
% 0.18/0.35  #    Non-unit-clauses                  : 2
% 0.18/0.35  # Current number of unprocessed clauses: 2
% 0.18/0.35  # ...number of literals in the above   : 4
% 0.18/0.35  # Current number of archived formulas  : 0
% 0.18/0.35  # Current number of archived clauses   : 17
% 0.18/0.35  # Clause-clause subsumption calls (NU) : 1
% 0.18/0.35  # Rec. Clause-clause subsumption calls : 1
% 0.18/0.35  # Non-unit clause-clause subsumptions  : 0
% 0.18/0.35  # Unit Clause-clause subsumption calls : 2
% 0.18/0.35  # Rewrite failures with RHS unbound    : 0
% 0.18/0.35  # BW rewrite match attempts            : 5
% 0.18/0.35  # BW rewrite match successes           : 3
% 0.18/0.35  # Condensation attempts                : 0
% 0.18/0.35  # Condensation successes               : 0
% 0.18/0.35  # Termbank termtop insertions          : 707
% 0.18/0.35  
% 0.18/0.35  # -------------------------------------------------
% 0.18/0.35  # User time                : 0.029 s
% 0.18/0.35  # System time              : 0.003 s
% 0.18/0.35  # Total time               : 0.032 s
% 0.18/0.35  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------

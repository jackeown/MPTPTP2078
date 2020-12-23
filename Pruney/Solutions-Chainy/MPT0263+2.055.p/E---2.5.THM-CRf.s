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
% DateTime   : Thu Dec  3 10:42:03 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   37 ( 124 expanded)
%              Number of clauses        :   22 (  54 expanded)
%              Number of leaves         :    7 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :   59 ( 188 expanded)
%              Number of equality atoms :   32 ( 124 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t58_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( r1_xboole_0(k1_tarski(X1),X2)
      | k3_xboole_0(k1_tarski(X1),X2) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(l33_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),X2) = k1_tarski(X1)
    <=> ~ r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

fof(l35_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),X2) = k1_xboole_0
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l35_zfmisc_1)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r1_xboole_0(k1_tarski(X1),X2)
        | k3_xboole_0(k1_tarski(X1),X2) = k1_tarski(X1) ) ),
    inference(assume_negation,[status(cth)],[t58_zfmisc_1])).

fof(c_0_8,negated_conjecture,
    ( ~ r1_xboole_0(k1_tarski(esk1_0),esk2_0)
    & k3_xboole_0(k1_tarski(esk1_0),esk2_0) != k1_tarski(esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_9,plain,(
    ! [X8] : k2_tarski(X8,X8) = k1_tarski(X8) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_10,plain,(
    ! [X4,X5] : k4_xboole_0(X4,k4_xboole_0(X4,X5)) = k3_xboole_0(X4,X5) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_11,plain,(
    ! [X9,X10] :
      ( ( k4_xboole_0(k1_tarski(X9),X10) != k1_tarski(X9)
        | ~ r2_hidden(X9,X10) )
      & ( r2_hidden(X9,X10)
        | k4_xboole_0(k1_tarski(X9),X10) = k1_tarski(X9) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l33_zfmisc_1])])])).

fof(c_0_12,plain,(
    ! [X11,X12] :
      ( ( k4_xboole_0(k1_tarski(X11),X12) != k1_xboole_0
        | r2_hidden(X11,X12) )
      & ( ~ r2_hidden(X11,X12)
        | k4_xboole_0(k1_tarski(X11),X12) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l35_zfmisc_1])])).

cnf(c_0_13,negated_conjecture,
    ( k3_xboole_0(k1_tarski(esk1_0),esk2_0) != k1_tarski(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X2)
    | k4_xboole_0(k1_tarski(X1),X2) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( k4_xboole_0(k1_tarski(X1),X2) = k1_xboole_0
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk1_0,esk1_0),k4_xboole_0(k2_tarski(esk1_0,esk1_0),esk2_0)) != k2_tarski(esk1_0,esk1_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_14]),c_0_14]),c_0_15])).

cnf(c_0_19,plain,
    ( k4_xboole_0(k2_tarski(X1,X1),X2) = k2_tarski(X1,X1)
    | r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_14]),c_0_14])).

fof(c_0_20,plain,(
    ! [X6,X7] :
      ( ( ~ r1_xboole_0(X6,X7)
        | k4_xboole_0(X6,X7) = X6 )
      & ( k4_xboole_0(X6,X7) != X6
        | r1_xboole_0(X6,X7) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_21,plain,
    ( k4_xboole_0(k2_tarski(X1,X1),X2) = k1_xboole_0
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_17,c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk1_0,k4_xboole_0(k2_tarski(esk1_0,esk1_0),esk2_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( ~ r1_xboole_0(k1_tarski(esk1_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_24,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk1_0,esk1_0),k4_xboole_0(k2_tarski(esk1_0,esk1_0),esk2_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( ~ r1_xboole_0(k2_tarski(esk1_0,esk1_0),esk2_0) ),
    inference(rw,[status(thm)],[c_0_23,c_0_14])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k2_tarski(X1,X1),X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_19])).

fof(c_0_28,plain,(
    ! [X3] : k4_xboole_0(X3,k1_xboole_0) = X3 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_29,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,negated_conjecture,
    ( k2_tarski(esk1_0,esk1_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_18,c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( ~ r1_xboole_0(k2_tarski(esk1_0,esk1_0),k4_xboole_0(k2_tarski(esk1_0,esk1_0),esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_25]),c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk1_0,esk1_0),esk2_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_21,c_0_31])).

cnf(c_0_35,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_34]),c_0_35])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:46:59 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S053N
% 0.12/0.37  # and selection function HSelectMinInfpos.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.027 s
% 0.12/0.37  # Presaturation interreduction done
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(t58_zfmisc_1, conjecture, ![X1, X2]:(r1_xboole_0(k1_tarski(X1),X2)|k3_xboole_0(k1_tarski(X1),X2)=k1_tarski(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_zfmisc_1)).
% 0.12/0.37  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.12/0.37  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.12/0.37  fof(l33_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),X2)=k1_tarski(X1)<=>~(r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 0.12/0.37  fof(l35_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),X2)=k1_xboole_0<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l35_zfmisc_1)).
% 0.12/0.37  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.12/0.37  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 0.12/0.37  fof(c_0_7, negated_conjecture, ~(![X1, X2]:(r1_xboole_0(k1_tarski(X1),X2)|k3_xboole_0(k1_tarski(X1),X2)=k1_tarski(X1))), inference(assume_negation,[status(cth)],[t58_zfmisc_1])).
% 0.12/0.37  fof(c_0_8, negated_conjecture, (~r1_xboole_0(k1_tarski(esk1_0),esk2_0)&k3_xboole_0(k1_tarski(esk1_0),esk2_0)!=k1_tarski(esk1_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.12/0.37  fof(c_0_9, plain, ![X8]:k2_tarski(X8,X8)=k1_tarski(X8), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.12/0.37  fof(c_0_10, plain, ![X4, X5]:k4_xboole_0(X4,k4_xboole_0(X4,X5))=k3_xboole_0(X4,X5), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.12/0.37  fof(c_0_11, plain, ![X9, X10]:((k4_xboole_0(k1_tarski(X9),X10)!=k1_tarski(X9)|~r2_hidden(X9,X10))&(r2_hidden(X9,X10)|k4_xboole_0(k1_tarski(X9),X10)=k1_tarski(X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l33_zfmisc_1])])])).
% 0.12/0.37  fof(c_0_12, plain, ![X11, X12]:((k4_xboole_0(k1_tarski(X11),X12)!=k1_xboole_0|r2_hidden(X11,X12))&(~r2_hidden(X11,X12)|k4_xboole_0(k1_tarski(X11),X12)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l35_zfmisc_1])])).
% 0.12/0.37  cnf(c_0_13, negated_conjecture, (k3_xboole_0(k1_tarski(esk1_0),esk2_0)!=k1_tarski(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  cnf(c_0_14, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.37  cnf(c_0_15, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.37  cnf(c_0_16, plain, (r2_hidden(X1,X2)|k4_xboole_0(k1_tarski(X1),X2)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  cnf(c_0_17, plain, (k4_xboole_0(k1_tarski(X1),X2)=k1_xboole_0|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.37  cnf(c_0_18, negated_conjecture, (k4_xboole_0(k2_tarski(esk1_0,esk1_0),k4_xboole_0(k2_tarski(esk1_0,esk1_0),esk2_0))!=k2_tarski(esk1_0,esk1_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13, c_0_14]), c_0_14]), c_0_15])).
% 0.12/0.37  cnf(c_0_19, plain, (k4_xboole_0(k2_tarski(X1,X1),X2)=k2_tarski(X1,X1)|r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16, c_0_14]), c_0_14])).
% 0.12/0.37  fof(c_0_20, plain, ![X6, X7]:((~r1_xboole_0(X6,X7)|k4_xboole_0(X6,X7)=X6)&(k4_xboole_0(X6,X7)!=X6|r1_xboole_0(X6,X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.12/0.37  cnf(c_0_21, plain, (k4_xboole_0(k2_tarski(X1,X1),X2)=k1_xboole_0|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_17, c_0_14])).
% 0.12/0.37  cnf(c_0_22, negated_conjecture, (r2_hidden(esk1_0,k4_xboole_0(k2_tarski(esk1_0,esk1_0),esk2_0))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.12/0.37  cnf(c_0_23, negated_conjecture, (~r1_xboole_0(k1_tarski(esk1_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  cnf(c_0_24, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.37  cnf(c_0_25, negated_conjecture, (k4_xboole_0(k2_tarski(esk1_0,esk1_0),k4_xboole_0(k2_tarski(esk1_0,esk1_0),esk2_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.12/0.37  cnf(c_0_26, negated_conjecture, (~r1_xboole_0(k2_tarski(esk1_0,esk1_0),esk2_0)), inference(rw,[status(thm)],[c_0_23, c_0_14])).
% 0.12/0.37  cnf(c_0_27, plain, (r2_hidden(X1,X2)|r1_xboole_0(k2_tarski(X1,X1),X2)), inference(spm,[status(thm)],[c_0_24, c_0_19])).
% 0.12/0.37  fof(c_0_28, plain, ![X3]:k4_xboole_0(X3,k1_xboole_0)=X3, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.12/0.37  cnf(c_0_29, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.37  cnf(c_0_30, negated_conjecture, (k2_tarski(esk1_0,esk1_0)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_18, c_0_25])).
% 0.12/0.37  cnf(c_0_31, negated_conjecture, (r2_hidden(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.12/0.37  cnf(c_0_32, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.12/0.37  cnf(c_0_33, negated_conjecture, (~r1_xboole_0(k2_tarski(esk1_0,esk1_0),k4_xboole_0(k2_tarski(esk1_0,esk1_0),esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_25]), c_0_30])).
% 0.12/0.37  cnf(c_0_34, negated_conjecture, (k4_xboole_0(k2_tarski(esk1_0,esk1_0),esk2_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_21, c_0_31])).
% 0.12/0.37  cnf(c_0_35, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_24, c_0_32])).
% 0.12/0.37  cnf(c_0_36, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_34]), c_0_35])]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 37
% 0.12/0.37  # Proof object clause steps            : 22
% 0.12/0.37  # Proof object formula steps           : 15
% 0.12/0.37  # Proof object conjectures             : 14
% 0.12/0.37  # Proof object clause conjectures      : 11
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 9
% 0.12/0.37  # Proof object initial formulas used   : 7
% 0.12/0.37  # Proof object generating inferences   : 7
% 0.12/0.37  # Proof object simplifying inferences  : 12
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 7
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 11
% 0.12/0.37  # Removed in clause preprocessing      : 2
% 0.12/0.37  # Initial clauses in saturation        : 9
% 0.12/0.37  # Processed clauses                    : 42
% 0.12/0.37  # ...of these trivial                  : 0
% 0.12/0.37  # ...subsumed                          : 10
% 0.12/0.37  # ...remaining for further processing  : 32
% 0.12/0.37  # Other redundant clauses eliminated   : 0
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 0
% 0.12/0.37  # Backward-rewritten                   : 9
% 0.12/0.37  # Generated clauses                    : 36
% 0.12/0.37  # ...of the previous two non-trivial   : 28
% 0.12/0.37  # Contextual simplify-reflections      : 0
% 0.12/0.37  # Paramodulations                      : 36
% 0.12/0.37  # Factorizations                       : 0
% 0.12/0.37  # Equation resolutions                 : 0
% 0.12/0.37  # Propositional unsat checks           : 0
% 0.12/0.37  #    Propositional check models        : 0
% 0.12/0.37  #    Propositional check unsatisfiable : 0
% 0.12/0.37  #    Propositional clauses             : 0
% 0.12/0.37  #    Propositional clauses after purity: 0
% 0.12/0.37  #    Propositional unsat core size     : 0
% 0.12/0.37  #    Propositional preprocessing time  : 0.000
% 0.12/0.37  #    Propositional encoding time       : 0.000
% 0.12/0.37  #    Propositional solver time         : 0.000
% 0.12/0.37  #    Success case prop preproc time    : 0.000
% 0.12/0.37  #    Success case prop encoding time   : 0.000
% 0.12/0.37  #    Success case prop solver time     : 0.000
% 0.12/0.37  # Current number of processed clauses  : 14
% 0.12/0.37  #    Positive orientable unit clauses  : 4
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 2
% 0.12/0.37  #    Non-unit-clauses                  : 8
% 0.12/0.37  # Current number of unprocessed clauses: 3
% 0.12/0.37  # ...number of literals in the above   : 6
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 20
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 18
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 18
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 6
% 0.12/0.37  # Unit Clause-clause subsumption calls : 1
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 3
% 0.12/0.37  # BW rewrite match successes           : 3
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 923
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.025 s
% 0.12/0.37  # System time              : 0.006 s
% 0.12/0.37  # Total time               : 0.032 s
% 0.12/0.37  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------

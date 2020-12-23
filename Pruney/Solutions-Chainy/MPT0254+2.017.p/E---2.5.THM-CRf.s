%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:41:01 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 286 expanded)
%              Number of clauses        :   26 ( 118 expanded)
%              Number of leaves         :   11 (  82 expanded)
%              Depth                    :    9
%              Number of atoms          :   74 ( 319 expanded)
%              Number of equality atoms :   53 ( 298 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t49_zfmisc_1,conjecture,(
    ! [X1,X2] : k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t15_xboole_1,axiom,(
    ! [X1,X2] :
      ( k2_xboole_0(X1,X2) = k1_xboole_0
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(l24_zfmisc_1,axiom,(
    ! [X1,X2] :
      ~ ( r1_xboole_0(k1_tarski(X1),X2)
        & r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2] : k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    inference(assume_negation,[status(cth)],[t49_zfmisc_1])).

fof(c_0_12,plain,(
    ! [X25,X26] : k3_tarski(k2_tarski(X25,X26)) = k2_xboole_0(X25,X26) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_13,plain,(
    ! [X18,X19] : k1_enumset1(X18,X18,X19) = k2_tarski(X18,X19) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_14,negated_conjecture,(
    k2_xboole_0(k1_tarski(esk2_0),esk3_0) = k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

fof(c_0_15,plain,(
    ! [X17] : k2_tarski(X17,X17) = k1_tarski(X17) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_16,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_18,plain,(
    ! [X20,X21,X22] : k2_enumset1(X20,X20,X21,X22) = k1_enumset1(X20,X21,X22) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_19,plain,(
    ! [X8,X9] : k2_tarski(X8,X9) = k2_tarski(X9,X8) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

fof(c_0_20,plain,(
    ! [X4,X5] :
      ( k2_xboole_0(X4,X5) != k1_xboole_0
      | X4 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_xboole_1])])).

cnf(c_0_21,negated_conjecture,
    ( k2_xboole_0(k1_tarski(esk2_0),esk3_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_24,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( X1 = k1_xboole_0
    | k2_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( k3_tarski(k2_enumset1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk3_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_22]),c_0_17]),c_0_23]),c_0_24]),c_0_24]),c_0_24])).

cnf(c_0_28,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k2_enumset1(X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_17]),c_0_17]),c_0_24]),c_0_24])).

fof(c_0_29,plain,(
    ! [X6] : k2_xboole_0(X6,k1_xboole_0) = X6 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_30,plain,(
    ! [X10,X11,X12,X13,X14,X15] :
      ( ( ~ r2_hidden(X12,X11)
        | X12 = X10
        | X11 != k1_tarski(X10) )
      & ( X13 != X10
        | r2_hidden(X13,X11)
        | X11 != k1_tarski(X10) )
      & ( ~ r2_hidden(esk1_2(X14,X15),X15)
        | esk1_2(X14,X15) != X14
        | X15 = k1_tarski(X14) )
      & ( r2_hidden(esk1_2(X14,X15),X15)
        | esk1_2(X14,X15) = X14
        | X15 = k1_tarski(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_31,plain,
    ( X1 = k1_xboole_0
    | k3_tarski(k2_enumset1(X1,X1,X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_23]),c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( k3_tarski(k2_enumset1(esk3_0,esk3_0,esk3_0,k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_34,plain,(
    ! [X23,X24] :
      ( ~ r1_xboole_0(k1_tarski(X23),X24)
      | ~ r2_hidden(X23,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l24_zfmisc_1])])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_37,plain,
    ( k3_tarski(k2_enumset1(X1,X1,X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_23]),c_0_24])).

cnf(c_0_38,plain,
    ( ~ r1_xboole_0(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_39,plain,(
    ! [X7] : r1_xboole_0(X7,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X2,X2,X2,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_22]),c_0_17]),c_0_24])).

cnf(c_0_41,negated_conjecture,
    ( k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_36]),c_0_36]),c_0_36])).

cnf(c_0_42,plain,
    ( k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_37,c_0_28])).

cnf(c_0_43,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_xboole_0(k2_enumset1(X1,X1,X1,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_22]),c_0_17]),c_0_24])).

cnf(c_0_44,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,k2_enumset1(X1,X1,X1,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_40])])).

cnf(c_0_46,negated_conjecture,
    ( k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_47,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_48,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.33  % Computer   : n023.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 13:58:50 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  # Version: 2.5pre002
% 0.11/0.34  # No SInE strategy applied
% 0.11/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S078N
% 0.19/0.36  # and selection function SelectCQIArNpEqFirst.
% 0.19/0.36  #
% 0.19/0.36  # Preprocessing time       : 0.027 s
% 0.19/0.36  # Presaturation interreduction done
% 0.19/0.36  
% 0.19/0.36  # Proof found!
% 0.19/0.36  # SZS status Theorem
% 0.19/0.36  # SZS output start CNFRefutation
% 0.19/0.36  fof(t49_zfmisc_1, conjecture, ![X1, X2]:k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 0.19/0.36  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.19/0.36  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.36  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.36  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.36  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.19/0.36  fof(t15_xboole_1, axiom, ![X1, X2]:(k2_xboole_0(X1,X2)=k1_xboole_0=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_xboole_1)).
% 0.19/0.36  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 0.19/0.36  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.19/0.36  fof(l24_zfmisc_1, axiom, ![X1, X2]:~((r1_xboole_0(k1_tarski(X1),X2)&r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 0.19/0.36  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.19/0.36  fof(c_0_11, negated_conjecture, ~(![X1, X2]:k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0), inference(assume_negation,[status(cth)],[t49_zfmisc_1])).
% 0.19/0.36  fof(c_0_12, plain, ![X25, X26]:k3_tarski(k2_tarski(X25,X26))=k2_xboole_0(X25,X26), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.19/0.36  fof(c_0_13, plain, ![X18, X19]:k1_enumset1(X18,X18,X19)=k2_tarski(X18,X19), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.36  fof(c_0_14, negated_conjecture, k2_xboole_0(k1_tarski(esk2_0),esk3_0)=k1_xboole_0, inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 0.19/0.36  fof(c_0_15, plain, ![X17]:k2_tarski(X17,X17)=k1_tarski(X17), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.36  cnf(c_0_16, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.36  cnf(c_0_17, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.36  fof(c_0_18, plain, ![X20, X21, X22]:k2_enumset1(X20,X20,X21,X22)=k1_enumset1(X20,X21,X22), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.36  fof(c_0_19, plain, ![X8, X9]:k2_tarski(X8,X9)=k2_tarski(X9,X8), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.19/0.36  fof(c_0_20, plain, ![X4, X5]:(k2_xboole_0(X4,X5)!=k1_xboole_0|X4=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_xboole_1])])).
% 0.19/0.36  cnf(c_0_21, negated_conjecture, (k2_xboole_0(k1_tarski(esk2_0),esk3_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.36  cnf(c_0_22, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.36  cnf(c_0_23, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 0.19/0.36  cnf(c_0_24, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.36  cnf(c_0_25, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.36  cnf(c_0_26, plain, (X1=k1_xboole_0|k2_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.36  cnf(c_0_27, negated_conjecture, (k3_tarski(k2_enumset1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk3_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_22]), c_0_17]), c_0_23]), c_0_24]), c_0_24]), c_0_24])).
% 0.19/0.36  cnf(c_0_28, plain, (k2_enumset1(X1,X1,X1,X2)=k2_enumset1(X2,X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_17]), c_0_17]), c_0_24]), c_0_24])).
% 0.19/0.36  fof(c_0_29, plain, ![X6]:k2_xboole_0(X6,k1_xboole_0)=X6, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.19/0.36  fof(c_0_30, plain, ![X10, X11, X12, X13, X14, X15]:(((~r2_hidden(X12,X11)|X12=X10|X11!=k1_tarski(X10))&(X13!=X10|r2_hidden(X13,X11)|X11!=k1_tarski(X10)))&((~r2_hidden(esk1_2(X14,X15),X15)|esk1_2(X14,X15)!=X14|X15=k1_tarski(X14))&(r2_hidden(esk1_2(X14,X15),X15)|esk1_2(X14,X15)=X14|X15=k1_tarski(X14)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.19/0.36  cnf(c_0_31, plain, (X1=k1_xboole_0|k3_tarski(k2_enumset1(X1,X1,X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_23]), c_0_24])).
% 0.19/0.36  cnf(c_0_32, negated_conjecture, (k3_tarski(k2_enumset1(esk3_0,esk3_0,esk3_0,k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0)))=k1_xboole_0), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 0.19/0.36  cnf(c_0_33, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.36  fof(c_0_34, plain, ![X23, X24]:(~r1_xboole_0(k1_tarski(X23),X24)|~r2_hidden(X23,X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l24_zfmisc_1])])).
% 0.19/0.36  cnf(c_0_35, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.36  cnf(c_0_36, negated_conjecture, (esk3_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.19/0.36  cnf(c_0_37, plain, (k3_tarski(k2_enumset1(X1,X1,X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_23]), c_0_24])).
% 0.19/0.36  cnf(c_0_38, plain, (~r1_xboole_0(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.36  fof(c_0_39, plain, ![X7]:r1_xboole_0(X7,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.19/0.36  cnf(c_0_40, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X2,X2,X2,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_22]), c_0_17]), c_0_24])).
% 0.19/0.36  cnf(c_0_41, negated_conjecture, (k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0)))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_36]), c_0_36]), c_0_36])).
% 0.19/0.36  cnf(c_0_42, plain, (k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X1))=X1), inference(spm,[status(thm)],[c_0_37, c_0_28])).
% 0.19/0.36  cnf(c_0_43, plain, (~r2_hidden(X1,X2)|~r1_xboole_0(k2_enumset1(X1,X1,X1,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_22]), c_0_17]), c_0_24])).
% 0.19/0.36  cnf(c_0_44, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.36  cnf(c_0_45, plain, (r2_hidden(X1,k2_enumset1(X1,X1,X1,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_40])])).
% 0.19/0.36  cnf(c_0_46, negated_conjecture, (k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0)=k1_xboole_0), inference(rw,[status(thm)],[c_0_41, c_0_42])).
% 0.19/0.36  cnf(c_0_47, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.19/0.36  cnf(c_0_48, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47]), ['proof']).
% 0.19/0.36  # SZS output end CNFRefutation
% 0.19/0.36  # Proof object total steps             : 49
% 0.19/0.36  # Proof object clause steps            : 26
% 0.19/0.36  # Proof object formula steps           : 23
% 0.19/0.36  # Proof object conjectures             : 10
% 0.19/0.36  # Proof object clause conjectures      : 7
% 0.19/0.36  # Proof object formula conjectures     : 3
% 0.19/0.36  # Proof object initial clauses used    : 11
% 0.19/0.36  # Proof object initial formulas used   : 11
% 0.19/0.36  # Proof object generating inferences   : 4
% 0.19/0.36  # Proof object simplifying inferences  : 29
% 0.19/0.36  # Training examples: 0 positive, 0 negative
% 0.19/0.36  # Parsed axioms                        : 11
% 0.19/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.36  # Initial clauses                      : 14
% 0.19/0.36  # Removed in clause preprocessing      : 4
% 0.19/0.36  # Initial clauses in saturation        : 10
% 0.19/0.36  # Processed clauses                    : 26
% 0.19/0.36  # ...of these trivial                  : 0
% 0.19/0.36  # ...subsumed                          : 0
% 0.19/0.36  # ...remaining for further processing  : 26
% 0.19/0.36  # Other redundant clauses eliminated   : 3
% 0.19/0.36  # Clauses deleted for lack of memory   : 0
% 0.19/0.36  # Backward-subsumed                    : 0
% 0.19/0.36  # Backward-rewritten                   : 3
% 0.19/0.36  # Generated clauses                    : 25
% 0.19/0.36  # ...of the previous two non-trivial   : 16
% 0.19/0.36  # Contextual simplify-reflections      : 0
% 0.19/0.36  # Paramodulations                      : 23
% 0.19/0.36  # Factorizations                       : 0
% 0.19/0.36  # Equation resolutions                 : 3
% 0.19/0.36  # Propositional unsat checks           : 0
% 0.19/0.36  #    Propositional check models        : 0
% 0.19/0.36  #    Propositional check unsatisfiable : 0
% 0.19/0.36  #    Propositional clauses             : 0
% 0.19/0.36  #    Propositional clauses after purity: 0
% 0.19/0.36  #    Propositional unsat core size     : 0
% 0.19/0.36  #    Propositional preprocessing time  : 0.000
% 0.19/0.36  #    Propositional encoding time       : 0.000
% 0.19/0.36  #    Propositional solver time         : 0.000
% 0.19/0.36  #    Success case prop preproc time    : 0.000
% 0.19/0.36  #    Success case prop encoding time   : 0.000
% 0.19/0.36  #    Success case prop solver time     : 0.000
% 0.19/0.36  # Current number of processed clauses  : 11
% 0.19/0.36  #    Positive orientable unit clauses  : 6
% 0.19/0.36  #    Positive unorientable unit clauses: 1
% 0.19/0.36  #    Negative unit clauses             : 1
% 0.19/0.36  #    Non-unit-clauses                  : 3
% 0.19/0.36  # Current number of unprocessed clauses: 9
% 0.19/0.36  # ...number of literals in the above   : 19
% 0.19/0.36  # Current number of archived formulas  : 0
% 0.19/0.36  # Current number of archived clauses   : 17
% 0.19/0.36  # Clause-clause subsumption calls (NU) : 0
% 0.19/0.36  # Rec. Clause-clause subsumption calls : 0
% 0.19/0.36  # Non-unit clause-clause subsumptions  : 0
% 0.19/0.36  # Unit Clause-clause subsumption calls : 2
% 0.19/0.36  # Rewrite failures with RHS unbound    : 0
% 0.19/0.36  # BW rewrite match attempts            : 28
% 0.19/0.36  # BW rewrite match successes           : 22
% 0.19/0.36  # Condensation attempts                : 0
% 0.19/0.36  # Condensation successes               : 0
% 0.19/0.36  # Termbank termtop insertions          : 877
% 0.19/0.36  
% 0.19/0.36  # -------------------------------------------------
% 0.19/0.36  # User time                : 0.028 s
% 0.19/0.36  # System time              : 0.003 s
% 0.19/0.36  # Total time               : 0.031 s
% 0.19/0.36  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------

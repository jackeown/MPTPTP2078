%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:39:16 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   38 ( 116 expanded)
%              Number of clauses        :   19 (  44 expanded)
%              Number of leaves         :    9 (  35 expanded)
%              Depth                    :    7
%              Number of atoms          :   78 ( 159 expanded)
%              Number of equality atoms :   60 ( 141 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t29_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( X1 != X2
     => k5_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k2_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_zfmisc_1)).

fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(l33_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),X2) = k1_tarski(X1)
    <=> ~ r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(c_0_9,plain,(
    ! [X7,X8] : k2_xboole_0(X7,X8) = k5_xboole_0(X7,k4_xboole_0(X8,X7)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_10,plain,(
    ! [X5,X6] : k4_xboole_0(X5,X6) = k5_xboole_0(X5,k3_xboole_0(X5,X6)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2] :
        ( X1 != X2
       => k5_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k2_tarski(X1,X2) ) ),
    inference(assume_negation,[status(cth)],[t29_zfmisc_1])).

fof(c_0_12,plain,(
    ! [X18,X19] : k2_tarski(X18,X19) = k2_xboole_0(k1_tarski(X18),k1_tarski(X19)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

fof(c_0_13,plain,(
    ! [X20] : k2_tarski(X20,X20) = k1_tarski(X20) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_14,plain,(
    ! [X21,X22] : k1_enumset1(X21,X21,X22) = k2_tarski(X21,X22) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_15,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_17,plain,(
    ! [X23,X24,X25] : k2_enumset1(X23,X23,X24,X25) = k1_enumset1(X23,X24,X25) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_18,plain,(
    ! [X26,X27] :
      ( ( k4_xboole_0(k1_tarski(X26),X27) != k1_tarski(X26)
        | ~ r2_hidden(X26,X27) )
      & ( r2_hidden(X26,X27)
        | k4_xboole_0(k1_tarski(X26),X27) = k1_tarski(X26) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l33_zfmisc_1])])])).

fof(c_0_19,plain,(
    ! [X9,X10,X11,X12,X13,X14,X15,X16] :
      ( ( ~ r2_hidden(X12,X11)
        | X12 = X9
        | X12 = X10
        | X11 != k2_tarski(X9,X10) )
      & ( X13 != X9
        | r2_hidden(X13,X11)
        | X11 != k2_tarski(X9,X10) )
      & ( X13 != X10
        | r2_hidden(X13,X11)
        | X11 != k2_tarski(X9,X10) )
      & ( esk1_3(X14,X15,X16) != X14
        | ~ r2_hidden(esk1_3(X14,X15,X16),X16)
        | X16 = k2_tarski(X14,X15) )
      & ( esk1_3(X14,X15,X16) != X15
        | ~ r2_hidden(esk1_3(X14,X15,X16),X16)
        | X16 = k2_tarski(X14,X15) )
      & ( r2_hidden(esk1_3(X14,X15,X16),X16)
        | esk1_3(X14,X15,X16) = X14
        | esk1_3(X14,X15,X16) = X15
        | X16 = k2_tarski(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

fof(c_0_20,negated_conjecture,
    ( esk2_0 != esk3_0
    & k5_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)) != k2_tarski(esk2_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

cnf(c_0_21,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_25,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,X2)
    | k4_xboole_0(k1_tarski(X1),X2) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,negated_conjecture,
    ( k5_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)) != k2_tarski(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k5_xboole_0(k2_enumset1(X2,X2,X2,X2),k3_xboole_0(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X1,X1,X1,X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_22]),c_0_22]),c_0_23]),c_0_23]),c_0_23]),c_0_24]),c_0_25]),c_0_25]),c_0_25]),c_0_25]),c_0_25])).

cnf(c_0_30,plain,
    ( k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k3_xboole_0(k2_enumset1(X1,X1,X1,X1),X2)) = k2_enumset1(X1,X1,X1,X1)
    | r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_22]),c_0_22]),c_0_23]),c_0_23]),c_0_16]),c_0_25]),c_0_25]),c_0_25])).

cnf(c_0_31,plain,
    ( X1 = X4
    | X1 = X3
    | X2 != k2_enumset1(X3,X3,X3,X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_23]),c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( k5_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)) != k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_22]),c_0_22]),c_0_23]),c_0_23]),c_0_23]),c_0_25]),c_0_25]),c_0_25])).

cnf(c_0_33,plain,
    ( k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)) = k2_enumset1(X1,X1,X1,X2)
    | r2_hidden(X2,k2_enumset1(X1,X1,X1,X1)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_34,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k2_enumset1(X3,X3,X3,X2)) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk3_0,k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_36,negated_conjecture,
    ( esk2_0 != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_37,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:41:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.21/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S078N
% 0.21/0.40  # and selection function SelectCQIArNpEqFirst.
% 0.21/0.40  #
% 0.21/0.40  # Preprocessing time       : 0.027 s
% 0.21/0.40  # Presaturation interreduction done
% 0.21/0.40  
% 0.21/0.40  # Proof found!
% 0.21/0.40  # SZS status Theorem
% 0.21/0.40  # SZS output start CNFRefutation
% 0.21/0.40  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.21/0.40  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.21/0.40  fof(t29_zfmisc_1, conjecture, ![X1, X2]:(X1!=X2=>k5_xboole_0(k1_tarski(X1),k1_tarski(X2))=k2_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_zfmisc_1)).
% 0.21/0.40  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 0.21/0.40  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.21/0.40  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.21/0.40  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.21/0.40  fof(l33_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),X2)=k1_tarski(X1)<=>~(r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 0.21/0.40  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 0.21/0.40  fof(c_0_9, plain, ![X7, X8]:k2_xboole_0(X7,X8)=k5_xboole_0(X7,k4_xboole_0(X8,X7)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.21/0.40  fof(c_0_10, plain, ![X5, X6]:k4_xboole_0(X5,X6)=k5_xboole_0(X5,k3_xboole_0(X5,X6)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.21/0.40  fof(c_0_11, negated_conjecture, ~(![X1, X2]:(X1!=X2=>k5_xboole_0(k1_tarski(X1),k1_tarski(X2))=k2_tarski(X1,X2))), inference(assume_negation,[status(cth)],[t29_zfmisc_1])).
% 0.21/0.40  fof(c_0_12, plain, ![X18, X19]:k2_tarski(X18,X19)=k2_xboole_0(k1_tarski(X18),k1_tarski(X19)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 0.21/0.40  fof(c_0_13, plain, ![X20]:k2_tarski(X20,X20)=k1_tarski(X20), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.21/0.40  fof(c_0_14, plain, ![X21, X22]:k1_enumset1(X21,X21,X22)=k2_tarski(X21,X22), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.21/0.40  cnf(c_0_15, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.40  cnf(c_0_16, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.40  fof(c_0_17, plain, ![X23, X24, X25]:k2_enumset1(X23,X23,X24,X25)=k1_enumset1(X23,X24,X25), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.21/0.40  fof(c_0_18, plain, ![X26, X27]:((k4_xboole_0(k1_tarski(X26),X27)!=k1_tarski(X26)|~r2_hidden(X26,X27))&(r2_hidden(X26,X27)|k4_xboole_0(k1_tarski(X26),X27)=k1_tarski(X26))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l33_zfmisc_1])])])).
% 0.21/0.40  fof(c_0_19, plain, ![X9, X10, X11, X12, X13, X14, X15, X16]:(((~r2_hidden(X12,X11)|(X12=X9|X12=X10)|X11!=k2_tarski(X9,X10))&((X13!=X9|r2_hidden(X13,X11)|X11!=k2_tarski(X9,X10))&(X13!=X10|r2_hidden(X13,X11)|X11!=k2_tarski(X9,X10))))&(((esk1_3(X14,X15,X16)!=X14|~r2_hidden(esk1_3(X14,X15,X16),X16)|X16=k2_tarski(X14,X15))&(esk1_3(X14,X15,X16)!=X15|~r2_hidden(esk1_3(X14,X15,X16),X16)|X16=k2_tarski(X14,X15)))&(r2_hidden(esk1_3(X14,X15,X16),X16)|(esk1_3(X14,X15,X16)=X14|esk1_3(X14,X15,X16)=X15)|X16=k2_tarski(X14,X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.21/0.40  fof(c_0_20, negated_conjecture, (esk2_0!=esk3_0&k5_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0))!=k2_tarski(esk2_0,esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 0.21/0.41  cnf(c_0_21, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.41  cnf(c_0_22, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.41  cnf(c_0_23, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.41  cnf(c_0_24, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 0.21/0.41  cnf(c_0_25, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.41  cnf(c_0_26, plain, (r2_hidden(X1,X2)|k4_xboole_0(k1_tarski(X1),X2)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.41  cnf(c_0_27, plain, (X1=X3|X1=X4|~r2_hidden(X1,X2)|X2!=k2_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.41  cnf(c_0_28, negated_conjecture, (k5_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0))!=k2_tarski(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.41  cnf(c_0_29, plain, (k2_enumset1(X1,X1,X1,X2)=k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k5_xboole_0(k2_enumset1(X2,X2,X2,X2),k3_xboole_0(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X1,X1,X1,X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_22]), c_0_22]), c_0_23]), c_0_23]), c_0_23]), c_0_24]), c_0_25]), c_0_25]), c_0_25]), c_0_25]), c_0_25])).
% 0.21/0.41  cnf(c_0_30, plain, (k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k3_xboole_0(k2_enumset1(X1,X1,X1,X1),X2))=k2_enumset1(X1,X1,X1,X1)|r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_22]), c_0_22]), c_0_23]), c_0_23]), c_0_16]), c_0_25]), c_0_25]), c_0_25])).
% 0.21/0.41  cnf(c_0_31, plain, (X1=X4|X1=X3|X2!=k2_enumset1(X3,X3,X3,X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_23]), c_0_25])).
% 0.21/0.41  cnf(c_0_32, negated_conjecture, (k5_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))!=k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_22]), c_0_22]), c_0_23]), c_0_23]), c_0_23]), c_0_25]), c_0_25]), c_0_25])).
% 0.21/0.41  cnf(c_0_33, plain, (k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))=k2_enumset1(X1,X1,X1,X2)|r2_hidden(X2,k2_enumset1(X1,X1,X1,X1))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.21/0.41  cnf(c_0_34, plain, (X1=X2|X1=X3|~r2_hidden(X1,k2_enumset1(X3,X3,X3,X2))), inference(er,[status(thm)],[c_0_31])).
% 0.21/0.41  cnf(c_0_35, negated_conjecture, (r2_hidden(esk3_0,k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.21/0.41  cnf(c_0_36, negated_conjecture, (esk2_0!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.41  cnf(c_0_37, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36]), ['proof']).
% 0.21/0.41  # SZS output end CNFRefutation
% 0.21/0.41  # Proof object total steps             : 38
% 0.21/0.41  # Proof object clause steps            : 19
% 0.21/0.41  # Proof object formula steps           : 19
% 0.21/0.41  # Proof object conjectures             : 8
% 0.21/0.41  # Proof object clause conjectures      : 5
% 0.21/0.41  # Proof object formula conjectures     : 3
% 0.21/0.41  # Proof object initial clauses used    : 10
% 0.21/0.41  # Proof object initial formulas used   : 9
% 0.21/0.41  # Proof object generating inferences   : 3
% 0.21/0.41  # Proof object simplifying inferences  : 32
% 0.21/0.41  # Training examples: 0 positive, 0 negative
% 0.21/0.41  # Parsed axioms                        : 9
% 0.21/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.41  # Initial clauses                      : 16
% 0.21/0.41  # Removed in clause preprocessing      : 5
% 0.21/0.41  # Initial clauses in saturation        : 11
% 0.21/0.41  # Processed clauses                    : 63
% 0.21/0.41  # ...of these trivial                  : 0
% 0.21/0.41  # ...subsumed                          : 4
% 0.21/0.41  # ...remaining for further processing  : 59
% 0.21/0.41  # Other redundant clauses eliminated   : 126
% 0.21/0.41  # Clauses deleted for lack of memory   : 0
% 0.21/0.41  # Backward-subsumed                    : 6
% 0.21/0.41  # Backward-rewritten                   : 0
% 0.21/0.41  # Generated clauses                    : 1051
% 0.21/0.41  # ...of the previous two non-trivial   : 868
% 0.21/0.41  # Contextual simplify-reflections      : 1
% 0.21/0.41  # Paramodulations                      : 897
% 0.21/0.41  # Factorizations                       : 29
% 0.21/0.41  # Equation resolutions                 : 127
% 0.21/0.41  # Propositional unsat checks           : 0
% 0.21/0.41  #    Propositional check models        : 0
% 0.21/0.41  #    Propositional check unsatisfiable : 0
% 0.21/0.41  #    Propositional clauses             : 0
% 0.21/0.41  #    Propositional clauses after purity: 0
% 0.21/0.41  #    Propositional unsat core size     : 0
% 0.21/0.41  #    Propositional preprocessing time  : 0.000
% 0.21/0.41  #    Propositional encoding time       : 0.000
% 0.21/0.41  #    Propositional solver time         : 0.000
% 0.21/0.41  #    Success case prop preproc time    : 0.000
% 0.21/0.41  #    Success case prop encoding time   : 0.000
% 0.21/0.41  #    Success case prop solver time     : 0.000
% 0.21/0.41  # Current number of processed clauses  : 39
% 0.21/0.41  #    Positive orientable unit clauses  : 4
% 0.21/0.41  #    Positive unorientable unit clauses: 0
% 0.21/0.41  #    Negative unit clauses             : 2
% 0.21/0.41  #    Non-unit-clauses                  : 33
% 0.21/0.41  # Current number of unprocessed clauses: 813
% 0.21/0.41  # ...number of literals in the above   : 5727
% 0.21/0.41  # Current number of archived formulas  : 0
% 0.21/0.41  # Current number of archived clauses   : 22
% 0.21/0.41  # Clause-clause subsumption calls (NU) : 236
% 0.21/0.41  # Rec. Clause-clause subsumption calls : 110
% 0.21/0.41  # Non-unit clause-clause subsumptions  : 11
% 0.21/0.41  # Unit Clause-clause subsumption calls : 14
% 0.21/0.41  # Rewrite failures with RHS unbound    : 0
% 0.21/0.41  # BW rewrite match attempts            : 2
% 0.21/0.41  # BW rewrite match successes           : 0
% 0.21/0.41  # Condensation attempts                : 0
% 0.21/0.41  # Condensation successes               : 0
% 0.21/0.41  # Termbank termtop insertions          : 26044
% 0.21/0.41  
% 0.21/0.41  # -------------------------------------------------
% 0.21/0.41  # User time                : 0.062 s
% 0.21/0.41  # System time              : 0.004 s
% 0.21/0.41  # Total time               : 0.067 s
% 0.21/0.41  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------

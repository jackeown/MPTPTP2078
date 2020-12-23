%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:41:04 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 323 expanded)
%              Number of clauses        :   29 ( 137 expanded)
%              Number of leaves         :   13 (  91 expanded)
%              Depth                    :   10
%              Number of atoms          :  100 ( 387 expanded)
%              Number of equality atoms :   57 ( 309 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   1 average)
%              Maximal term depth       :    4 (   1 average)

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

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(l24_zfmisc_1,axiom,(
    ! [X1,X2] :
      ~ ( r1_xboole_0(k1_tarski(X1),X2)
        & r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2] : k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    inference(assume_negation,[status(cth)],[t49_zfmisc_1])).

fof(c_0_14,plain,(
    ! [X32,X33] : k3_tarski(k2_tarski(X32,X33)) = k2_xboole_0(X32,X33) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_15,plain,(
    ! [X25,X26] : k1_enumset1(X25,X25,X26) = k2_tarski(X25,X26) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_16,negated_conjecture,(
    k2_xboole_0(k1_tarski(esk2_0),esk3_0) = k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

fof(c_0_17,plain,(
    ! [X24] : k2_tarski(X24,X24) = k1_tarski(X24) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_18,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_20,plain,(
    ! [X27,X28,X29] : k2_enumset1(X27,X27,X28,X29) = k1_enumset1(X27,X28,X29) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_21,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_22,plain,(
    ! [X13,X14] : r1_tarski(X13,k2_xboole_0(X13,X14)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_23,negated_conjecture,
    ( k2_xboole_0(k1_tarski(esk2_0),esk3_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_26,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( k3_tarski(k2_enumset1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk3_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24]),c_0_19]),c_0_25]),c_0_26]),c_0_26]),c_0_26])).

cnf(c_0_30,plain,
    ( k3_tarski(k2_enumset1(X1,X1,X1,X2)) = k3_tarski(k2_enumset1(X2,X2,X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_25]),c_0_25]),c_0_26]),c_0_26])).

fof(c_0_31,plain,(
    ! [X7,X8] :
      ( ( r1_tarski(X7,X8)
        | X7 != X8 )
      & ( r1_tarski(X8,X7)
        | X7 != X8 )
      & ( ~ r1_tarski(X7,X8)
        | ~ r1_tarski(X8,X7)
        | X7 = X8 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,k3_tarski(k2_enumset1(X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_25]),c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( k3_tarski(k2_enumset1(esk3_0,esk3_0,esk3_0,k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_29,c_0_30])).

fof(c_0_34,plain,(
    ! [X11] : r1_tarski(k1_xboole_0,X11) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_35,plain,(
    ! [X9,X10] :
      ( ~ r1_tarski(X9,X10)
      | k2_xboole_0(X9,X10) = X10 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_36,plain,(
    ! [X15,X16,X17,X18,X19,X20,X21,X22] :
      ( ( ~ r2_hidden(X18,X17)
        | X18 = X15
        | X18 = X16
        | X17 != k2_tarski(X15,X16) )
      & ( X19 != X15
        | r2_hidden(X19,X17)
        | X17 != k2_tarski(X15,X16) )
      & ( X19 != X16
        | r2_hidden(X19,X17)
        | X17 != k2_tarski(X15,X16) )
      & ( esk1_3(X20,X21,X22) != X20
        | ~ r2_hidden(esk1_3(X20,X21,X22),X22)
        | X22 = k2_tarski(X20,X21) )
      & ( esk1_3(X20,X21,X22) != X21
        | ~ r2_hidden(esk1_3(X20,X21,X22),X22)
        | X22 = k2_tarski(X20,X21) )
      & ( r2_hidden(esk1_3(X20,X21,X22),X22)
        | esk1_3(X20,X21,X22) = X20
        | esk1_3(X20,X21,X22) = X21
        | X22 = k2_tarski(X20,X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

cnf(c_0_37,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(esk3_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_39,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_40,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_41,plain,(
    ! [X30,X31] :
      ( ~ r1_xboole_0(k1_tarski(X30),X31)
      | ~ r2_hidden(X30,X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l24_zfmisc_1])])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])])).

cnf(c_0_44,plain,
    ( k3_tarski(k2_enumset1(X1,X1,X1,X2)) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_25]),c_0_26])).

cnf(c_0_45,plain,
    ( ~ r1_xboole_0(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_46,plain,(
    ! [X12] : r1_xboole_0(X12,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X4,X4,X4,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_19]),c_0_26])).

cnf(c_0_48,negated_conjecture,
    ( k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_43]),c_0_43]),c_0_43])).

cnf(c_0_49,plain,
    ( k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_44,c_0_39])).

cnf(c_0_50,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_xboole_0(k2_enumset1(X1,X1,X1,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_24]),c_0_19]),c_0_26])).

cnf(c_0_51,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,k2_enumset1(X2,X2,X2,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_47])])).

cnf(c_0_53,negated_conjecture,
    ( k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_54,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_55,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:50:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S078N
% 0.13/0.37  # and selection function SelectCQIArNpEqFirst.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.022 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t49_zfmisc_1, conjecture, ![X1, X2]:k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 0.13/0.37  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.13/0.37  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.37  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.37  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.13/0.37  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.13/0.37  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.13/0.37  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.13/0.37  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.13/0.37  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.13/0.37  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 0.13/0.37  fof(l24_zfmisc_1, axiom, ![X1, X2]:~((r1_xboole_0(k1_tarski(X1),X2)&r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 0.13/0.37  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.13/0.37  fof(c_0_13, negated_conjecture, ~(![X1, X2]:k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0), inference(assume_negation,[status(cth)],[t49_zfmisc_1])).
% 0.13/0.37  fof(c_0_14, plain, ![X32, X33]:k3_tarski(k2_tarski(X32,X33))=k2_xboole_0(X32,X33), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.13/0.37  fof(c_0_15, plain, ![X25, X26]:k1_enumset1(X25,X25,X26)=k2_tarski(X25,X26), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.37  fof(c_0_16, negated_conjecture, k2_xboole_0(k1_tarski(esk2_0),esk3_0)=k1_xboole_0, inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.13/0.37  fof(c_0_17, plain, ![X24]:k2_tarski(X24,X24)=k1_tarski(X24), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.37  cnf(c_0_18, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.37  cnf(c_0_19, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.37  fof(c_0_20, plain, ![X27, X28, X29]:k2_enumset1(X27,X27,X28,X29)=k1_enumset1(X27,X28,X29), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.13/0.37  fof(c_0_21, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.13/0.37  fof(c_0_22, plain, ![X13, X14]:r1_tarski(X13,k2_xboole_0(X13,X14)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.13/0.37  cnf(c_0_23, negated_conjecture, (k2_xboole_0(k1_tarski(esk2_0),esk3_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.37  cnf(c_0_24, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.37  cnf(c_0_25, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 0.13/0.37  cnf(c_0_26, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.37  cnf(c_0_27, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.37  cnf(c_0_28, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.37  cnf(c_0_29, negated_conjecture, (k3_tarski(k2_enumset1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk3_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_24]), c_0_19]), c_0_25]), c_0_26]), c_0_26]), c_0_26])).
% 0.13/0.37  cnf(c_0_30, plain, (k3_tarski(k2_enumset1(X1,X1,X1,X2))=k3_tarski(k2_enumset1(X2,X2,X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_25]), c_0_25]), c_0_26]), c_0_26])).
% 0.13/0.37  fof(c_0_31, plain, ![X7, X8]:(((r1_tarski(X7,X8)|X7!=X8)&(r1_tarski(X8,X7)|X7!=X8))&(~r1_tarski(X7,X8)|~r1_tarski(X8,X7)|X7=X8)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.13/0.37  cnf(c_0_32, plain, (r1_tarski(X1,k3_tarski(k2_enumset1(X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_25]), c_0_26])).
% 0.13/0.37  cnf(c_0_33, negated_conjecture, (k3_tarski(k2_enumset1(esk3_0,esk3_0,esk3_0,k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0)))=k1_xboole_0), inference(rw,[status(thm)],[c_0_29, c_0_30])).
% 0.13/0.37  fof(c_0_34, plain, ![X11]:r1_tarski(k1_xboole_0,X11), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.13/0.37  fof(c_0_35, plain, ![X9, X10]:(~r1_tarski(X9,X10)|k2_xboole_0(X9,X10)=X10), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.13/0.37  fof(c_0_36, plain, ![X15, X16, X17, X18, X19, X20, X21, X22]:(((~r2_hidden(X18,X17)|(X18=X15|X18=X16)|X17!=k2_tarski(X15,X16))&((X19!=X15|r2_hidden(X19,X17)|X17!=k2_tarski(X15,X16))&(X19!=X16|r2_hidden(X19,X17)|X17!=k2_tarski(X15,X16))))&(((esk1_3(X20,X21,X22)!=X20|~r2_hidden(esk1_3(X20,X21,X22),X22)|X22=k2_tarski(X20,X21))&(esk1_3(X20,X21,X22)!=X21|~r2_hidden(esk1_3(X20,X21,X22),X22)|X22=k2_tarski(X20,X21)))&(r2_hidden(esk1_3(X20,X21,X22),X22)|(esk1_3(X20,X21,X22)=X20|esk1_3(X20,X21,X22)=X21)|X22=k2_tarski(X20,X21)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.13/0.37  cnf(c_0_37, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.37  cnf(c_0_38, negated_conjecture, (r1_tarski(esk3_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.13/0.37  cnf(c_0_39, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.37  cnf(c_0_40, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.37  fof(c_0_41, plain, ![X30, X31]:(~r1_xboole_0(k1_tarski(X30),X31)|~r2_hidden(X30,X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l24_zfmisc_1])])).
% 0.13/0.37  cnf(c_0_42, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.13/0.37  cnf(c_0_43, negated_conjecture, (esk3_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])])).
% 0.13/0.37  cnf(c_0_44, plain, (k3_tarski(k2_enumset1(X1,X1,X1,X2))=X2|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_25]), c_0_26])).
% 0.13/0.37  cnf(c_0_45, plain, (~r1_xboole_0(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.13/0.37  fof(c_0_46, plain, ![X12]:r1_xboole_0(X12,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.13/0.37  cnf(c_0_47, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X4,X4,X4,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_19]), c_0_26])).
% 0.13/0.37  cnf(c_0_48, negated_conjecture, (k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0)))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_43]), c_0_43]), c_0_43])).
% 0.13/0.37  cnf(c_0_49, plain, (k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X1))=X1), inference(spm,[status(thm)],[c_0_44, c_0_39])).
% 0.13/0.37  cnf(c_0_50, plain, (~r2_hidden(X1,X2)|~r1_xboole_0(k2_enumset1(X1,X1,X1,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_24]), c_0_19]), c_0_26])).
% 0.13/0.37  cnf(c_0_51, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.13/0.37  cnf(c_0_52, plain, (r2_hidden(X1,k2_enumset1(X2,X2,X2,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_47])])).
% 0.13/0.37  cnf(c_0_53, negated_conjecture, (k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0)=k1_xboole_0), inference(rw,[status(thm)],[c_0_48, c_0_49])).
% 0.13/0.37  cnf(c_0_54, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.13/0.37  cnf(c_0_55, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 56
% 0.13/0.37  # Proof object clause steps            : 29
% 0.13/0.37  # Proof object formula steps           : 27
% 0.13/0.37  # Proof object conjectures             : 11
% 0.13/0.37  # Proof object clause conjectures      : 8
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 13
% 0.13/0.37  # Proof object initial formulas used   : 13
% 0.13/0.37  # Proof object generating inferences   : 5
% 0.13/0.37  # Proof object simplifying inferences  : 30
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 13
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 20
% 0.13/0.37  # Removed in clause preprocessing      : 4
% 0.13/0.37  # Initial clauses in saturation        : 16
% 0.13/0.37  # Processed clauses                    : 38
% 0.13/0.37  # ...of these trivial                  : 0
% 0.13/0.37  # ...subsumed                          : 0
% 0.13/0.37  # ...remaining for further processing  : 38
% 0.13/0.37  # Other redundant clauses eliminated   : 7
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 0
% 0.13/0.37  # Backward-rewritten                   : 4
% 0.13/0.37  # Generated clauses                    : 21
% 0.13/0.37  # ...of the previous two non-trivial   : 17
% 0.13/0.37  # Contextual simplify-reflections      : 0
% 0.13/0.37  # Paramodulations                      : 16
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 7
% 0.13/0.37  # Propositional unsat checks           : 0
% 0.13/0.37  #    Propositional check models        : 0
% 0.13/0.37  #    Propositional check unsatisfiable : 0
% 0.13/0.37  #    Propositional clauses             : 0
% 0.13/0.37  #    Propositional clauses after purity: 0
% 0.13/0.37  #    Propositional unsat core size     : 0
% 0.13/0.37  #    Propositional preprocessing time  : 0.000
% 0.13/0.37  #    Propositional encoding time       : 0.000
% 0.13/0.37  #    Propositional solver time         : 0.000
% 0.13/0.37  #    Success case prop preproc time    : 0.000
% 0.13/0.37  #    Success case prop encoding time   : 0.000
% 0.13/0.37  #    Success case prop solver time     : 0.000
% 0.13/0.37  # Current number of processed clauses  : 14
% 0.13/0.37  #    Positive orientable unit clauses  : 9
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 1
% 0.13/0.37  #    Non-unit-clauses                  : 4
% 0.13/0.37  # Current number of unprocessed clauses: 8
% 0.13/0.37  # ...number of literals in the above   : 17
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 23
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 2
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 2
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.37  # Unit Clause-clause subsumption calls : 1
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 11
% 0.13/0.37  # BW rewrite match successes           : 6
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 1149
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.021 s
% 0.13/0.37  # System time              : 0.005 s
% 0.13/0.37  # Total time               : 0.026 s
% 0.13/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------

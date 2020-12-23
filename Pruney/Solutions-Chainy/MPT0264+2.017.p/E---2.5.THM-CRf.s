%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:42:05 EST 2020

% Result     : Theorem 0.36s
% Output     : CNFRefutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 158 expanded)
%              Number of clauses        :   29 (  63 expanded)
%              Number of leaves         :   10 (  46 expanded)
%              Depth                    :    9
%              Number of atoms          :  113 ( 268 expanded)
%              Number of equality atoms :   80 ( 216 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(l29_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k3_xboole_0(X1,k1_tarski(X2)) = k1_tarski(X2)
     => r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l29_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(l31_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => k3_xboole_0(X2,k1_tarski(X1)) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).

fof(t59_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( k3_xboole_0(k2_tarski(X1,X2),X3) = k1_tarski(X1)
        & r2_hidden(X2,X3)
        & X1 != X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_zfmisc_1)).

fof(t16_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(c_0_10,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17,X18,X19,X20] :
      ( ( ~ r2_hidden(X15,X14)
        | X15 = X11
        | X15 = X12
        | X15 = X13
        | X14 != k1_enumset1(X11,X12,X13) )
      & ( X16 != X11
        | r2_hidden(X16,X14)
        | X14 != k1_enumset1(X11,X12,X13) )
      & ( X16 != X12
        | r2_hidden(X16,X14)
        | X14 != k1_enumset1(X11,X12,X13) )
      & ( X16 != X13
        | r2_hidden(X16,X14)
        | X14 != k1_enumset1(X11,X12,X13) )
      & ( esk1_4(X17,X18,X19,X20) != X17
        | ~ r2_hidden(esk1_4(X17,X18,X19,X20),X20)
        | X20 = k1_enumset1(X17,X18,X19) )
      & ( esk1_4(X17,X18,X19,X20) != X18
        | ~ r2_hidden(esk1_4(X17,X18,X19,X20),X20)
        | X20 = k1_enumset1(X17,X18,X19) )
      & ( esk1_4(X17,X18,X19,X20) != X19
        | ~ r2_hidden(esk1_4(X17,X18,X19,X20),X20)
        | X20 = k1_enumset1(X17,X18,X19) )
      & ( r2_hidden(esk1_4(X17,X18,X19,X20),X20)
        | esk1_4(X17,X18,X19,X20) = X17
        | esk1_4(X17,X18,X19,X20) = X18
        | esk1_4(X17,X18,X19,X20) = X19
        | X20 = k1_enumset1(X17,X18,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

fof(c_0_11,plain,(
    ! [X25,X26,X27] : k2_enumset1(X25,X25,X26,X27) = k1_enumset1(X25,X26,X27) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_12,plain,(
    ! [X28,X29,X30,X31] : k3_enumset1(X28,X28,X29,X30,X31) = k2_enumset1(X28,X29,X30,X31) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_13,plain,(
    ! [X32,X33] :
      ( k3_xboole_0(X32,k1_tarski(X33)) != k1_tarski(X33)
      | r2_hidden(X33,X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l29_zfmisc_1])])).

fof(c_0_14,plain,(
    ! [X22] : k2_tarski(X22,X22) = k1_tarski(X22) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_15,plain,(
    ! [X23,X24] : k1_enumset1(X23,X23,X24) = k2_tarski(X23,X24) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_16,plain,(
    ! [X34,X35] :
      ( ~ r2_hidden(X34,X35)
      | k3_xboole_0(X35,k1_tarski(X34)) = k1_tarski(X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l31_zfmisc_1])])).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( k3_xboole_0(k2_tarski(X1,X2),X3) = k1_tarski(X1)
          & r2_hidden(X2,X3)
          & X1 != X2 ) ),
    inference(assume_negation,[status(cth)],[t59_zfmisc_1])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,plain,
    ( r2_hidden(X2,X1)
    | k3_xboole_0(X1,k1_tarski(X2)) != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_24,plain,(
    ! [X8,X9,X10] : k3_xboole_0(k3_xboole_0(X8,X9),X10) = k3_xboole_0(X8,k3_xboole_0(X9,X10)) ),
    inference(variable_rename,[status(thm)],[t16_xboole_1])).

cnf(c_0_25,plain,
    ( k3_xboole_0(X2,k1_tarski(X1)) = k1_tarski(X1)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_26,negated_conjecture,
    ( k3_xboole_0(k2_tarski(esk2_0,esk3_0),esk4_0) = k1_tarski(esk2_0)
    & r2_hidden(esk3_0,esk4_0)
    & esk2_0 != esk3_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k3_enumset1(X4,X4,X4,X5,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_19]),c_0_20])).

cnf(c_0_28,plain,
    ( r2_hidden(X2,X1)
    | k3_xboole_0(X1,k3_enumset1(X2,X2,X2,X2,X2)) != k3_enumset1(X2,X2,X2,X2,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_22]),c_0_22]),c_0_23]),c_0_23]),c_0_19]),c_0_19]),c_0_20]),c_0_20])).

cnf(c_0_29,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,plain,
    ( k3_xboole_0(X2,k3_enumset1(X1,X1,X1,X1,X1)) = k3_enumset1(X1,X1,X1,X1,X1)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_22]),c_0_22]),c_0_23]),c_0_23]),c_0_19]),c_0_19]),c_0_20]),c_0_20])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,X2)
    | X2 != k3_enumset1(X3,X3,X3,X4,X1) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,X3))
    | k3_xboole_0(X2,k3_xboole_0(X3,k3_enumset1(X1,X1,X1,X1,X1))) != k3_enumset1(X1,X1,X1,X1,X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( k3_xboole_0(esk4_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)) = k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,k3_enumset1(X2,X2,X2,X3,X1)) ),
    inference(er,[status(thm)],[c_0_32])).

fof(c_0_36,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k3_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_37,negated_conjecture,
    ( k3_xboole_0(k2_tarski(esk2_0,esk3_0),esk4_0) = k1_tarski(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_38,plain,
    ( X1 = X3
    | X1 = X4
    | X1 = X5
    | ~ r2_hidden(X1,X2)
    | X2 != k1_enumset1(X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk3_0,k3_xboole_0(X1,esk4_0))
    | k3_xboole_0(X1,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)) != k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_40,plain,
    ( k3_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),k3_enumset1(X3,X3,X3,X3,X3)) = k3_enumset1(X3,X3,X3,X3,X3) ),
    inference(spm,[status(thm)],[c_0_30,c_0_35])).

cnf(c_0_41,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_42,negated_conjecture,
    ( k3_xboole_0(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0),esk4_0) = k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_22]),c_0_23]),c_0_23]),c_0_19]),c_0_19]),c_0_20]),c_0_20])).

cnf(c_0_43,plain,
    ( X1 = X5
    | X1 = X4
    | X1 = X3
    | X2 != k3_enumset1(X3,X3,X3,X4,X5)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_19]),c_0_20])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk3_0,k3_xboole_0(esk4_0,k3_enumset1(X1,X1,X1,X2,esk3_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])).

cnf(c_0_45,negated_conjecture,
    ( k3_xboole_0(esk4_0,k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0)) = k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_42,c_0_41])).

cnf(c_0_46,plain,
    ( X1 = X2
    | X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,k3_enumset1(X4,X4,X4,X3,X2)) ),
    inference(er,[status(thm)],[c_0_43])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk3_0,k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_48,negated_conjecture,
    ( esk2_0 != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_49,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 17:32:10 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.36/0.54  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_S0a
% 0.36/0.54  # and selection function SelectNegativeLiterals.
% 0.36/0.54  #
% 0.36/0.54  # Preprocessing time       : 0.026 s
% 0.36/0.54  
% 0.36/0.54  # Proof found!
% 0.36/0.54  # SZS status Theorem
% 0.36/0.54  # SZS output start CNFRefutation
% 0.36/0.54  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 0.36/0.54  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.36/0.54  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.36/0.54  fof(l29_zfmisc_1, axiom, ![X1, X2]:(k3_xboole_0(X1,k1_tarski(X2))=k1_tarski(X2)=>r2_hidden(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l29_zfmisc_1)).
% 0.36/0.54  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.36/0.54  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.36/0.54  fof(l31_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>k3_xboole_0(X2,k1_tarski(X1))=k1_tarski(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 0.36/0.54  fof(t59_zfmisc_1, conjecture, ![X1, X2, X3]:~(((k3_xboole_0(k2_tarski(X1,X2),X3)=k1_tarski(X1)&r2_hidden(X2,X3))&X1!=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_zfmisc_1)).
% 0.36/0.54  fof(t16_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 0.36/0.54  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.36/0.54  fof(c_0_10, plain, ![X11, X12, X13, X14, X15, X16, X17, X18, X19, X20]:(((~r2_hidden(X15,X14)|(X15=X11|X15=X12|X15=X13)|X14!=k1_enumset1(X11,X12,X13))&(((X16!=X11|r2_hidden(X16,X14)|X14!=k1_enumset1(X11,X12,X13))&(X16!=X12|r2_hidden(X16,X14)|X14!=k1_enumset1(X11,X12,X13)))&(X16!=X13|r2_hidden(X16,X14)|X14!=k1_enumset1(X11,X12,X13))))&((((esk1_4(X17,X18,X19,X20)!=X17|~r2_hidden(esk1_4(X17,X18,X19,X20),X20)|X20=k1_enumset1(X17,X18,X19))&(esk1_4(X17,X18,X19,X20)!=X18|~r2_hidden(esk1_4(X17,X18,X19,X20),X20)|X20=k1_enumset1(X17,X18,X19)))&(esk1_4(X17,X18,X19,X20)!=X19|~r2_hidden(esk1_4(X17,X18,X19,X20),X20)|X20=k1_enumset1(X17,X18,X19)))&(r2_hidden(esk1_4(X17,X18,X19,X20),X20)|(esk1_4(X17,X18,X19,X20)=X17|esk1_4(X17,X18,X19,X20)=X18|esk1_4(X17,X18,X19,X20)=X19)|X20=k1_enumset1(X17,X18,X19)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 0.36/0.54  fof(c_0_11, plain, ![X25, X26, X27]:k2_enumset1(X25,X25,X26,X27)=k1_enumset1(X25,X26,X27), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.36/0.54  fof(c_0_12, plain, ![X28, X29, X30, X31]:k3_enumset1(X28,X28,X29,X30,X31)=k2_enumset1(X28,X29,X30,X31), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.36/0.54  fof(c_0_13, plain, ![X32, X33]:(k3_xboole_0(X32,k1_tarski(X33))!=k1_tarski(X33)|r2_hidden(X33,X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l29_zfmisc_1])])).
% 0.36/0.54  fof(c_0_14, plain, ![X22]:k2_tarski(X22,X22)=k1_tarski(X22), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.36/0.54  fof(c_0_15, plain, ![X23, X24]:k1_enumset1(X23,X23,X24)=k2_tarski(X23,X24), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.36/0.54  fof(c_0_16, plain, ![X34, X35]:(~r2_hidden(X34,X35)|k3_xboole_0(X35,k1_tarski(X34))=k1_tarski(X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l31_zfmisc_1])])).
% 0.36/0.54  fof(c_0_17, negated_conjecture, ~(![X1, X2, X3]:~(((k3_xboole_0(k2_tarski(X1,X2),X3)=k1_tarski(X1)&r2_hidden(X2,X3))&X1!=X2))), inference(assume_negation,[status(cth)],[t59_zfmisc_1])).
% 0.36/0.54  cnf(c_0_18, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X5,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.36/0.54  cnf(c_0_19, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.36/0.54  cnf(c_0_20, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.36/0.54  cnf(c_0_21, plain, (r2_hidden(X2,X1)|k3_xboole_0(X1,k1_tarski(X2))!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.36/0.54  cnf(c_0_22, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.36/0.54  cnf(c_0_23, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.36/0.54  fof(c_0_24, plain, ![X8, X9, X10]:k3_xboole_0(k3_xboole_0(X8,X9),X10)=k3_xboole_0(X8,k3_xboole_0(X9,X10)), inference(variable_rename,[status(thm)],[t16_xboole_1])).
% 0.36/0.54  cnf(c_0_25, plain, (k3_xboole_0(X2,k1_tarski(X1))=k1_tarski(X1)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.36/0.54  fof(c_0_26, negated_conjecture, ((k3_xboole_0(k2_tarski(esk2_0,esk3_0),esk4_0)=k1_tarski(esk2_0)&r2_hidden(esk3_0,esk4_0))&esk2_0!=esk3_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 0.36/0.54  cnf(c_0_27, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k3_enumset1(X4,X4,X4,X5,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_19]), c_0_20])).
% 0.36/0.54  cnf(c_0_28, plain, (r2_hidden(X2,X1)|k3_xboole_0(X1,k3_enumset1(X2,X2,X2,X2,X2))!=k3_enumset1(X2,X2,X2,X2,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_22]), c_0_22]), c_0_23]), c_0_23]), c_0_19]), c_0_19]), c_0_20]), c_0_20])).
% 0.36/0.54  cnf(c_0_29, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.36/0.54  cnf(c_0_30, plain, (k3_xboole_0(X2,k3_enumset1(X1,X1,X1,X1,X1))=k3_enumset1(X1,X1,X1,X1,X1)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_22]), c_0_22]), c_0_23]), c_0_23]), c_0_19]), c_0_19]), c_0_20]), c_0_20])).
% 0.36/0.54  cnf(c_0_31, negated_conjecture, (r2_hidden(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.36/0.54  cnf(c_0_32, plain, (r2_hidden(X1,X2)|X2!=k3_enumset1(X3,X3,X3,X4,X1)), inference(er,[status(thm)],[c_0_27])).
% 0.36/0.54  cnf(c_0_33, plain, (r2_hidden(X1,k3_xboole_0(X2,X3))|k3_xboole_0(X2,k3_xboole_0(X3,k3_enumset1(X1,X1,X1,X1,X1)))!=k3_enumset1(X1,X1,X1,X1,X1)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.36/0.54  cnf(c_0_34, negated_conjecture, (k3_xboole_0(esk4_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))=k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.36/0.54  cnf(c_0_35, plain, (r2_hidden(X1,k3_enumset1(X2,X2,X2,X3,X1))), inference(er,[status(thm)],[c_0_32])).
% 0.36/0.54  fof(c_0_36, plain, ![X6, X7]:k3_xboole_0(X6,X7)=k3_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.36/0.54  cnf(c_0_37, negated_conjecture, (k3_xboole_0(k2_tarski(esk2_0,esk3_0),esk4_0)=k1_tarski(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.36/0.54  cnf(c_0_38, plain, (X1=X3|X1=X4|X1=X5|~r2_hidden(X1,X2)|X2!=k1_enumset1(X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.36/0.54  cnf(c_0_39, negated_conjecture, (r2_hidden(esk3_0,k3_xboole_0(X1,esk4_0))|k3_xboole_0(X1,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))!=k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.36/0.54  cnf(c_0_40, plain, (k3_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),k3_enumset1(X3,X3,X3,X3,X3))=k3_enumset1(X3,X3,X3,X3,X3)), inference(spm,[status(thm)],[c_0_30, c_0_35])).
% 0.36/0.54  cnf(c_0_41, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.36/0.54  cnf(c_0_42, negated_conjecture, (k3_xboole_0(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0),esk4_0)=k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_22]), c_0_23]), c_0_23]), c_0_19]), c_0_19]), c_0_20]), c_0_20])).
% 0.36/0.54  cnf(c_0_43, plain, (X1=X5|X1=X4|X1=X3|X2!=k3_enumset1(X3,X3,X3,X4,X5)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_19]), c_0_20])).
% 0.36/0.54  cnf(c_0_44, negated_conjecture, (r2_hidden(esk3_0,k3_xboole_0(esk4_0,k3_enumset1(X1,X1,X1,X2,esk3_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41])).
% 0.36/0.54  cnf(c_0_45, negated_conjecture, (k3_xboole_0(esk4_0,k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0))=k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)), inference(rw,[status(thm)],[c_0_42, c_0_41])).
% 0.36/0.54  cnf(c_0_46, plain, (X1=X2|X1=X3|X1=X4|~r2_hidden(X1,k3_enumset1(X4,X4,X4,X3,X2))), inference(er,[status(thm)],[c_0_43])).
% 0.36/0.54  cnf(c_0_47, negated_conjecture, (r2_hidden(esk3_0,k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.36/0.54  cnf(c_0_48, negated_conjecture, (esk2_0!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.36/0.54  cnf(c_0_49, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48]), ['proof']).
% 0.36/0.54  # SZS output end CNFRefutation
% 0.36/0.54  # Proof object total steps             : 50
% 0.36/0.54  # Proof object clause steps            : 29
% 0.36/0.54  # Proof object formula steps           : 21
% 0.36/0.54  # Proof object conjectures             : 13
% 0.36/0.54  # Proof object clause conjectures      : 10
% 0.36/0.54  # Proof object formula conjectures     : 3
% 0.36/0.54  # Proof object initial clauses used    : 13
% 0.36/0.54  # Proof object initial formulas used   : 10
% 0.36/0.54  # Proof object generating inferences   : 9
% 0.36/0.54  # Proof object simplifying inferences  : 31
% 0.36/0.54  # Training examples: 0 positive, 0 negative
% 0.36/0.54  # Parsed axioms                        : 10
% 0.36/0.54  # Removed by relevancy pruning/SinE    : 0
% 0.36/0.54  # Initial clauses                      : 19
% 0.36/0.54  # Removed in clause preprocessing      : 4
% 0.36/0.54  # Initial clauses in saturation        : 15
% 0.36/0.54  # Processed clauses                    : 382
% 0.36/0.54  # ...of these trivial                  : 39
% 0.36/0.54  # ...subsumed                          : 229
% 0.36/0.54  # ...remaining for further processing  : 114
% 0.36/0.54  # Other redundant clauses eliminated   : 124
% 0.36/0.54  # Clauses deleted for lack of memory   : 0
% 0.36/0.54  # Backward-subsumed                    : 0
% 0.36/0.54  # Backward-rewritten                   : 2
% 0.36/0.54  # Generated clauses                    : 4118
% 0.36/0.54  # ...of the previous two non-trivial   : 3838
% 0.36/0.54  # Contextual simplify-reflections      : 0
% 0.36/0.54  # Paramodulations                      : 3949
% 0.36/0.54  # Factorizations                       : 28
% 0.36/0.54  # Equation resolutions                 : 141
% 0.36/0.54  # Propositional unsat checks           : 0
% 0.36/0.54  #    Propositional check models        : 0
% 0.36/0.54  #    Propositional check unsatisfiable : 0
% 0.36/0.54  #    Propositional clauses             : 0
% 0.36/0.54  #    Propositional clauses after purity: 0
% 0.36/0.54  #    Propositional unsat core size     : 0
% 0.36/0.54  #    Propositional preprocessing time  : 0.000
% 0.36/0.54  #    Propositional encoding time       : 0.000
% 0.36/0.54  #    Propositional solver time         : 0.000
% 0.36/0.54  #    Success case prop preproc time    : 0.000
% 0.36/0.54  #    Success case prop encoding time   : 0.000
% 0.36/0.54  #    Success case prop solver time     : 0.000
% 0.36/0.54  # Current number of processed clauses  : 109
% 0.36/0.54  #    Positive orientable unit clauses  : 21
% 0.36/0.54  #    Positive unorientable unit clauses: 4
% 0.36/0.54  #    Negative unit clauses             : 1
% 0.36/0.54  #    Non-unit-clauses                  : 83
% 0.36/0.54  # Current number of unprocessed clauses: 3467
% 0.36/0.54  # ...number of literals in the above   : 28152
% 0.36/0.54  # Current number of archived formulas  : 0
% 0.36/0.54  # Current number of archived clauses   : 6
% 0.36/0.54  # Clause-clause subsumption calls (NU) : 3517
% 0.36/0.54  # Rec. Clause-clause subsumption calls : 3201
% 0.36/0.54  # Non-unit clause-clause subsumptions  : 192
% 0.36/0.54  # Unit Clause-clause subsumption calls : 27
% 0.36/0.54  # Rewrite failures with RHS unbound    : 0
% 0.36/0.54  # BW rewrite match attempts            : 53
% 0.36/0.54  # BW rewrite match successes           : 39
% 0.36/0.54  # Condensation attempts                : 0
% 0.36/0.54  # Condensation successes               : 0
% 0.36/0.54  # Termbank termtop insertions          : 108770
% 0.36/0.54  
% 0.36/0.54  # -------------------------------------------------
% 0.36/0.54  # User time                : 0.193 s
% 0.36/0.54  # System time              : 0.008 s
% 0.36/0.54  # Total time               : 0.201 s
% 0.36/0.54  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------

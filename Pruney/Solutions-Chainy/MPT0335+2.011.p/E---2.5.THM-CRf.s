%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:41 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 228 expanded)
%              Number of clauses        :   38 ( 100 expanded)
%              Number of leaves         :   13 (  61 expanded)
%              Depth                    :    9
%              Number of atoms          :   92 ( 347 expanded)
%              Number of equality atoms :   67 ( 252 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t148_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(X1,X2)
        & k3_xboole_0(X2,X3) = k1_tarski(X4)
        & r2_hidden(X4,X1) )
     => k3_xboole_0(X1,X3) = k1_tarski(X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_zfmisc_1)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t16_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t21_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(l22_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => k2_xboole_0(k1_tarski(X1),X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_zfmisc_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(c_0_13,plain,(
    ! [X8,X9] :
      ( ( r1_tarski(X8,X9)
        | X8 != X9 )
      & ( r1_tarski(X9,X8)
        | X8 != X9 )
      & ( ~ r1_tarski(X8,X9)
        | ~ r1_tarski(X9,X8)
        | X8 = X9 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( r1_tarski(X1,X2)
          & k3_xboole_0(X2,X3) = k1_tarski(X4)
          & r2_hidden(X4,X1) )
       => k3_xboole_0(X1,X3) = k1_tarski(X4) ) ),
    inference(assume_negation,[status(cth)],[t148_zfmisc_1])).

fof(c_0_15,plain,(
    ! [X17,X18] : k4_xboole_0(X17,k3_xboole_0(X17,X18)) = k4_xboole_0(X17,X18) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

fof(c_0_16,plain,(
    ! [X19,X20] : k4_xboole_0(X19,k4_xboole_0(X19,X20)) = k3_xboole_0(X19,X20) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_17,plain,(
    ! [X12,X13,X14] : k3_xboole_0(k3_xboole_0(X12,X13),X14) = k3_xboole_0(X12,k3_xboole_0(X13,X14)) ),
    inference(variable_rename,[status(thm)],[t16_xboole_1])).

fof(c_0_18,plain,(
    ! [X7] : k3_xboole_0(X7,X7) = X7 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

fof(c_0_19,plain,(
    ! [X10,X11] :
      ( ( k4_xboole_0(X10,X11) != k1_xboole_0
        | r1_tarski(X10,X11) )
      & ( ~ r1_tarski(X10,X11)
        | k4_xboole_0(X10,X11) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_21,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0)
    & k3_xboole_0(esk2_0,esk3_0) = k1_tarski(esk4_0)
    & r2_hidden(esk4_0,esk1_0)
    & k3_xboole_0(esk1_0,esk3_0) != k1_tarski(esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_22,plain,(
    ! [X21] : k2_tarski(X21,X21) = k1_tarski(X21) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_23,plain,(
    ! [X22,X23] : k1_enumset1(X22,X22,X23) = k2_tarski(X22,X23) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_24,plain,(
    ! [X24,X25,X26] : k2_enumset1(X24,X24,X25,X26) = k1_enumset1(X24,X25,X26) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_31,negated_conjecture,
    ( k3_xboole_0(esk2_0,esk3_0) = k1_tarski(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_35,plain,(
    ! [X15,X16] : k3_xboole_0(X15,k2_xboole_0(X15,X16)) = X15 ),
    inference(variable_rename,[status(thm)],[t21_xboole_1])).

fof(c_0_36,plain,(
    ! [X27,X28] :
      ( ~ r2_hidden(X27,X28)
      | k2_xboole_0(k1_tarski(X27),X28) = X28 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l22_zfmisc_1])])).

cnf(c_0_37,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_38,plain,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_26]),c_0_26]),c_0_26]),c_0_26])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_40,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_28,c_0_26])).

cnf(c_0_41,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_42,negated_conjecture,
    ( k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)) = k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34]),c_0_26])).

cnf(c_0_43,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,plain,
    ( k2_xboole_0(k1_tarski(X1),X2) = X2
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_45,plain,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_46,negated_conjecture,
    ( k4_xboole_0(esk1_0,esk2_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_29,c_0_39])).

cnf(c_0_47,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_48,negated_conjecture,
    ( k4_xboole_0(esk2_0,esk3_0) = k4_xboole_0(esk2_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_42])).

fof(c_0_49,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_50,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[c_0_43,c_0_26])).

cnf(c_0_51,plain,
    ( k2_xboole_0(k2_enumset1(X1,X1,X1,X1),X2) = X2
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_32]),c_0_33]),c_0_34])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_53,negated_conjecture,
    ( k3_xboole_0(esk1_0,esk3_0) != k1_tarski(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_54,negated_conjecture,
    ( k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,X1))) = k4_xboole_0(esk1_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47]),c_0_37]),c_0_47])).

cnf(c_0_55,negated_conjecture,
    ( k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))) = k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_42,c_0_48])).

cnf(c_0_56,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_57,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_50]),c_0_41])).

cnf(c_0_58,negated_conjecture,
    ( k2_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk1_0) = esk1_0 ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_59,negated_conjecture,
    ( k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk3_0)) != k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_32]),c_0_33]),c_0_34]),c_0_26])).

cnf(c_0_60,negated_conjecture,
    ( k4_xboole_0(esk1_0,esk3_0) = k4_xboole_0(esk1_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_48]),c_0_55])).

cnf(c_0_61,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_26]),c_0_26])).

cnf(c_0_62,negated_conjecture,
    ( k4_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk1_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_63,negated_conjecture,
    ( k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))) != k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_64,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_47]),c_0_63]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.19/0.34  % CPULimit   : 60
% 0.19/0.34  % WCLimit    : 600
% 0.19/0.34  % DateTime   : Tue Dec  1 16:27:57 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  # Version: 2.5pre002
% 0.19/0.34  # No SInE strategy applied
% 0.19/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.43  # AutoSched0-Mode selected heuristic G_E___107_B00_00_F1_PI_AE_Q4_CS_SP_PS_S064A
% 0.19/0.43  # and selection function SelectComplexG.
% 0.19/0.43  #
% 0.19/0.43  # Preprocessing time       : 0.027 s
% 0.19/0.43  # Presaturation interreduction done
% 0.19/0.43  
% 0.19/0.43  # Proof found!
% 0.19/0.43  # SZS status Theorem
% 0.19/0.43  # SZS output start CNFRefutation
% 0.19/0.43  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.43  fof(t148_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(((r1_tarski(X1,X2)&k3_xboole_0(X2,X3)=k1_tarski(X4))&r2_hidden(X4,X1))=>k3_xboole_0(X1,X3)=k1_tarski(X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_zfmisc_1)).
% 0.19/0.43  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 0.19/0.43  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.19/0.43  fof(t16_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 0.19/0.43  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.19/0.43  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.19/0.43  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.43  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.43  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.43  fof(t21_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 0.19/0.43  fof(l22_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>k2_xboole_0(k1_tarski(X1),X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 0.19/0.43  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.19/0.43  fof(c_0_13, plain, ![X8, X9]:(((r1_tarski(X8,X9)|X8!=X9)&(r1_tarski(X9,X8)|X8!=X9))&(~r1_tarski(X8,X9)|~r1_tarski(X9,X8)|X8=X9)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.43  fof(c_0_14, negated_conjecture, ~(![X1, X2, X3, X4]:(((r1_tarski(X1,X2)&k3_xboole_0(X2,X3)=k1_tarski(X4))&r2_hidden(X4,X1))=>k3_xboole_0(X1,X3)=k1_tarski(X4))), inference(assume_negation,[status(cth)],[t148_zfmisc_1])).
% 0.19/0.43  fof(c_0_15, plain, ![X17, X18]:k4_xboole_0(X17,k3_xboole_0(X17,X18))=k4_xboole_0(X17,X18), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 0.19/0.43  fof(c_0_16, plain, ![X19, X20]:k4_xboole_0(X19,k4_xboole_0(X19,X20))=k3_xboole_0(X19,X20), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.19/0.43  fof(c_0_17, plain, ![X12, X13, X14]:k3_xboole_0(k3_xboole_0(X12,X13),X14)=k3_xboole_0(X12,k3_xboole_0(X13,X14)), inference(variable_rename,[status(thm)],[t16_xboole_1])).
% 0.19/0.43  fof(c_0_18, plain, ![X7]:k3_xboole_0(X7,X7)=X7, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.19/0.43  fof(c_0_19, plain, ![X10, X11]:((k4_xboole_0(X10,X11)!=k1_xboole_0|r1_tarski(X10,X11))&(~r1_tarski(X10,X11)|k4_xboole_0(X10,X11)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.19/0.43  cnf(c_0_20, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.43  fof(c_0_21, negated_conjecture, (((r1_tarski(esk1_0,esk2_0)&k3_xboole_0(esk2_0,esk3_0)=k1_tarski(esk4_0))&r2_hidden(esk4_0,esk1_0))&k3_xboole_0(esk1_0,esk3_0)!=k1_tarski(esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.19/0.43  fof(c_0_22, plain, ![X21]:k2_tarski(X21,X21)=k1_tarski(X21), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.43  fof(c_0_23, plain, ![X22, X23]:k1_enumset1(X22,X22,X23)=k2_tarski(X22,X23), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.43  fof(c_0_24, plain, ![X24, X25, X26]:k2_enumset1(X24,X24,X25,X26)=k1_enumset1(X24,X25,X26), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.43  cnf(c_0_25, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.43  cnf(c_0_26, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.43  cnf(c_0_27, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.43  cnf(c_0_28, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.43  cnf(c_0_29, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.43  cnf(c_0_30, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_20])).
% 0.19/0.43  cnf(c_0_31, negated_conjecture, (k3_xboole_0(esk2_0,esk3_0)=k1_tarski(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.43  cnf(c_0_32, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.43  cnf(c_0_33, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.43  cnf(c_0_34, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.43  fof(c_0_35, plain, ![X15, X16]:k3_xboole_0(X15,k2_xboole_0(X15,X16))=X15, inference(variable_rename,[status(thm)],[t21_xboole_1])).
% 0.19/0.43  fof(c_0_36, plain, ![X27, X28]:(~r2_hidden(X27,X28)|k2_xboole_0(k1_tarski(X27),X28)=X28), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l22_zfmisc_1])])).
% 0.19/0.43  cnf(c_0_37, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 0.19/0.43  cnf(c_0_38, plain, (k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3))=k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_26]), c_0_26]), c_0_26]), c_0_26])).
% 0.19/0.43  cnf(c_0_39, negated_conjecture, (r1_tarski(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.43  cnf(c_0_40, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X1))=X1), inference(rw,[status(thm)],[c_0_28, c_0_26])).
% 0.19/0.43  cnf(c_0_41, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.19/0.43  cnf(c_0_42, negated_conjecture, (k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0))=k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_32]), c_0_33]), c_0_34]), c_0_26])).
% 0.19/0.43  cnf(c_0_43, plain, (k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.43  cnf(c_0_44, plain, (k2_xboole_0(k1_tarski(X1),X2)=X2|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.43  cnf(c_0_45, plain, (k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))))=k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.19/0.43  cnf(c_0_46, negated_conjecture, (k4_xboole_0(esk1_0,esk2_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_29, c_0_39])).
% 0.19/0.43  cnf(c_0_47, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_40, c_0_41])).
% 0.19/0.43  cnf(c_0_48, negated_conjecture, (k4_xboole_0(esk2_0,esk3_0)=k4_xboole_0(esk2_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_37, c_0_42])).
% 0.19/0.43  fof(c_0_49, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.19/0.43  cnf(c_0_50, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X1,X2)))=X1), inference(rw,[status(thm)],[c_0_43, c_0_26])).
% 0.19/0.43  cnf(c_0_51, plain, (k2_xboole_0(k2_enumset1(X1,X1,X1,X1),X2)=X2|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_32]), c_0_33]), c_0_34])).
% 0.19/0.43  cnf(c_0_52, negated_conjecture, (r2_hidden(esk4_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.43  cnf(c_0_53, negated_conjecture, (k3_xboole_0(esk1_0,esk3_0)!=k1_tarski(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.43  cnf(c_0_54, negated_conjecture, (k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,X1)))=k4_xboole_0(esk1_0,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47]), c_0_37]), c_0_47])).
% 0.19/0.43  cnf(c_0_55, negated_conjecture, (k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)))=k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)), inference(rw,[status(thm)],[c_0_42, c_0_48])).
% 0.19/0.43  cnf(c_0_56, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.19/0.43  cnf(c_0_57, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_50]), c_0_41])).
% 0.19/0.43  cnf(c_0_58, negated_conjecture, (k2_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk1_0)=esk1_0), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.19/0.43  cnf(c_0_59, negated_conjecture, (k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk3_0))!=k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_32]), c_0_33]), c_0_34]), c_0_26])).
% 0.19/0.43  cnf(c_0_60, negated_conjecture, (k4_xboole_0(esk1_0,esk3_0)=k4_xboole_0(esk1_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_48]), c_0_55])).
% 0.19/0.43  cnf(c_0_61, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_26]), c_0_26])).
% 0.19/0.43  cnf(c_0_62, negated_conjecture, (k4_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk1_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.19/0.43  cnf(c_0_63, negated_conjecture, (k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)))!=k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)), inference(rw,[status(thm)],[c_0_59, c_0_60])).
% 0.19/0.43  cnf(c_0_64, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_47]), c_0_63]), ['proof']).
% 0.19/0.43  # SZS output end CNFRefutation
% 0.19/0.43  # Proof object total steps             : 65
% 0.19/0.43  # Proof object clause steps            : 38
% 0.19/0.43  # Proof object formula steps           : 27
% 0.19/0.43  # Proof object conjectures             : 18
% 0.19/0.43  # Proof object clause conjectures      : 15
% 0.19/0.43  # Proof object formula conjectures     : 3
% 0.19/0.43  # Proof object initial clauses used    : 16
% 0.19/0.43  # Proof object initial formulas used   : 13
% 0.19/0.43  # Proof object generating inferences   : 10
% 0.19/0.43  # Proof object simplifying inferences  : 31
% 0.19/0.43  # Training examples: 0 positive, 0 negative
% 0.19/0.43  # Parsed axioms                        : 13
% 0.19/0.43  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.43  # Initial clauses                      : 19
% 0.19/0.43  # Removed in clause preprocessing      : 4
% 0.19/0.43  # Initial clauses in saturation        : 15
% 0.19/0.43  # Processed clauses                    : 330
% 0.19/0.43  # ...of these trivial                  : 81
% 0.19/0.43  # ...subsumed                          : 101
% 0.19/0.43  # ...remaining for further processing  : 147
% 0.19/0.43  # Other redundant clauses eliminated   : 2
% 0.19/0.43  # Clauses deleted for lack of memory   : 0
% 0.19/0.43  # Backward-subsumed                    : 1
% 0.19/0.43  # Backward-rewritten                   : 14
% 0.19/0.43  # Generated clauses                    : 4130
% 0.19/0.43  # ...of the previous two non-trivial   : 2198
% 0.19/0.43  # Contextual simplify-reflections      : 0
% 0.19/0.43  # Paramodulations                      : 4127
% 0.19/0.43  # Factorizations                       : 0
% 0.19/0.43  # Equation resolutions                 : 3
% 0.19/0.43  # Propositional unsat checks           : 0
% 0.19/0.43  #    Propositional check models        : 0
% 0.19/0.43  #    Propositional check unsatisfiable : 0
% 0.19/0.43  #    Propositional clauses             : 0
% 0.19/0.43  #    Propositional clauses after purity: 0
% 0.19/0.43  #    Propositional unsat core size     : 0
% 0.19/0.43  #    Propositional preprocessing time  : 0.000
% 0.19/0.43  #    Propositional encoding time       : 0.000
% 0.19/0.43  #    Propositional solver time         : 0.000
% 0.19/0.43  #    Success case prop preproc time    : 0.000
% 0.19/0.43  #    Success case prop encoding time   : 0.000
% 0.19/0.43  #    Success case prop solver time     : 0.000
% 0.19/0.43  # Current number of processed clauses  : 116
% 0.19/0.43  #    Positive orientable unit clauses  : 83
% 0.19/0.43  #    Positive unorientable unit clauses: 3
% 0.19/0.43  #    Negative unit clauses             : 1
% 0.19/0.43  #    Non-unit-clauses                  : 29
% 0.19/0.43  # Current number of unprocessed clauses: 1871
% 0.19/0.43  # ...number of literals in the above   : 2139
% 0.19/0.43  # Current number of archived formulas  : 0
% 0.19/0.43  # Current number of archived clauses   : 33
% 0.19/0.43  # Clause-clause subsumption calls (NU) : 222
% 0.19/0.43  # Rec. Clause-clause subsumption calls : 222
% 0.19/0.43  # Non-unit clause-clause subsumptions  : 83
% 0.19/0.43  # Unit Clause-clause subsumption calls : 34
% 0.19/0.43  # Rewrite failures with RHS unbound    : 0
% 0.19/0.43  # BW rewrite match attempts            : 242
% 0.19/0.43  # BW rewrite match successes           : 65
% 0.19/0.43  # Condensation attempts                : 0
% 0.19/0.43  # Condensation successes               : 0
% 0.19/0.43  # Termbank termtop insertions          : 66160
% 0.19/0.43  
% 0.19/0.43  # -------------------------------------------------
% 0.19/0.43  # User time                : 0.084 s
% 0.19/0.43  # System time              : 0.004 s
% 0.19/0.43  # Total time               : 0.089 s
% 0.19/0.43  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------

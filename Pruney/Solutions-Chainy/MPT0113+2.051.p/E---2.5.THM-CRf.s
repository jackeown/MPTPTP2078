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
% DateTime   : Thu Dec  3 10:34:42 EST 2020

% Result     : Theorem 0.40s
% Output     : CNFRefutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 252 expanded)
%              Number of clauses        :   40 ( 113 expanded)
%              Number of leaves         :   13 (  68 expanded)
%              Depth                    :   11
%              Number of atoms          :   98 ( 319 expanded)
%              Number of equality atoms :   50 ( 212 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t106_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k4_xboole_0(X2,X3))
     => ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(t16_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(c_0_13,plain,(
    ! [X24,X25] : r1_tarski(k4_xboole_0(X24,X25),X24) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_14,plain,(
    ! [X16,X17] : k4_xboole_0(X16,X17) = k5_xboole_0(X16,k3_xboole_0(X16,X17)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_15,plain,(
    ! [X27,X28] : k4_xboole_0(X27,k4_xboole_0(X27,X28)) = k3_xboole_0(X27,X28) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_16,plain,(
    ! [X21,X22] :
      ( ~ r1_tarski(X21,X22)
      | k3_xboole_0(X21,X22) = X21 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_17,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_20,plain,(
    ! [X26] : k4_xboole_0(X26,k1_xboole_0) = X26 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_21,plain,(
    ! [X14,X15] :
      ( ( k4_xboole_0(X14,X15) != k1_xboole_0
        | r1_tarski(X14,X15) )
      & ( ~ r1_tarski(X14,X15)
        | k4_xboole_0(X14,X15) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_25,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_26,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_tarski(X1,k4_xboole_0(X2,X3))
       => ( r1_tarski(X1,X2)
          & r1_xboole_0(X1,X3) ) ) ),
    inference(assume_negation,[status(cth)],[t106_xboole_1])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_28,plain,(
    ! [X23] : k3_xboole_0(X23,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_18]),c_0_18])).

cnf(c_0_31,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])).

fof(c_0_32,plain,(
    ! [X18,X19,X20] : k3_xboole_0(k3_xboole_0(X18,X19),X20) = k3_xboole_0(X18,k3_xboole_0(X19,X20)) ),
    inference(variable_rename,[status(thm)],[t16_xboole_1])).

fof(c_0_33,negated_conjecture,
    ( r1_tarski(esk3_0,k4_xboole_0(esk4_0,esk5_0))
    & ( ~ r1_tarski(esk3_0,esk4_0)
      | ~ r1_xboole_0(esk3_0,esk5_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])).

cnf(c_0_34,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[c_0_27,c_0_18])).

cnf(c_0_35,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_36,plain,(
    ! [X29,X30] : r1_xboole_0(k4_xboole_0(X29,X30),X30) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,X2)
    | k5_xboole_0(X1,k3_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_29,c_0_18])).

cnf(c_0_38,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_39,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(esk3_0,k4_xboole_0(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_42,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_31]),c_0_38])).

cnf(c_0_44,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(X2,k3_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_25]),c_0_39])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(esk3_0,k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk5_0))) ),
    inference(rw,[status(thm)],[c_0_40,c_0_18])).

cnf(c_0_46,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_35]),c_0_41])).

fof(c_0_47,plain,(
    ! [X6,X7,X9,X10,X11] :
      ( ( r1_xboole_0(X6,X7)
        | r2_hidden(esk1_2(X6,X7),k3_xboole_0(X6,X7)) )
      & ( ~ r2_hidden(X11,k3_xboole_0(X9,X10))
        | ~ r1_xboole_0(X9,X10) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_48,plain,(
    ! [X12] :
      ( X12 = k1_xboole_0
      | r2_hidden(esk2_1(X12),X12) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_49,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2) ),
    inference(rw,[status(thm)],[c_0_42,c_0_18])).

cnf(c_0_50,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = X1
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_43]),c_0_31])).

cnf(c_0_51,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X3)))) = k3_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_31])).

cnf(c_0_52,negated_conjecture,
    ( k3_xboole_0(esk3_0,k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk5_0))) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_45])).

cnf(c_0_53,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_46]),c_0_35]),c_0_41])).

cnf(c_0_54,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_55,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_56,negated_conjecture,
    ( ~ r1_tarski(esk3_0,esk4_0)
    | ~ r1_xboole_0(esk3_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_57,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_58,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk4_0) = esk3_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_25])).

cnf(c_0_59,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_46,c_0_53])).

cnf(c_0_60,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_61,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk5_0) != k1_xboole_0
    | ~ r1_tarski(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_58]),c_0_59])])).

cnf(c_0_63,negated_conjecture,
    ( k3_xboole_0(esk3_0,k3_xboole_0(X1,k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk5_0)))) = k3_xboole_0(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_52])).

cnf(c_0_64,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_49]),c_0_25])).

cnf(c_0_65,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk5_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_62])])).

cnf(c_0_66,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_35]),c_0_25]),c_0_65]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:25:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.40/0.57  # AutoSched0-Mode selected heuristic G_E___103_C18_F1_PI_AE_Q4_CS_SP_S0Y
% 0.40/0.57  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.40/0.57  #
% 0.40/0.57  # Preprocessing time       : 0.027 s
% 0.40/0.57  
% 0.40/0.57  # Proof found!
% 0.40/0.57  # SZS status Theorem
% 0.40/0.57  # SZS output start CNFRefutation
% 0.40/0.57  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.40/0.57  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.40/0.57  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.40/0.57  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.40/0.57  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.40/0.57  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.40/0.57  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.40/0.57  fof(t106_xboole_1, conjecture, ![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 0.40/0.57  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 0.40/0.57  fof(t16_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 0.40/0.57  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.40/0.57  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.40/0.57  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.40/0.57  fof(c_0_13, plain, ![X24, X25]:r1_tarski(k4_xboole_0(X24,X25),X24), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.40/0.57  fof(c_0_14, plain, ![X16, X17]:k4_xboole_0(X16,X17)=k5_xboole_0(X16,k3_xboole_0(X16,X17)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.40/0.57  fof(c_0_15, plain, ![X27, X28]:k4_xboole_0(X27,k4_xboole_0(X27,X28))=k3_xboole_0(X27,X28), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.40/0.57  fof(c_0_16, plain, ![X21, X22]:(~r1_tarski(X21,X22)|k3_xboole_0(X21,X22)=X21), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.40/0.57  cnf(c_0_17, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.40/0.57  cnf(c_0_18, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.40/0.57  fof(c_0_19, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.40/0.57  fof(c_0_20, plain, ![X26]:k4_xboole_0(X26,k1_xboole_0)=X26, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.40/0.57  fof(c_0_21, plain, ![X14, X15]:((k4_xboole_0(X14,X15)!=k1_xboole_0|r1_tarski(X14,X15))&(~r1_tarski(X14,X15)|k4_xboole_0(X14,X15)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.40/0.57  cnf(c_0_22, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.40/0.57  cnf(c_0_23, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.40/0.57  cnf(c_0_24, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.40/0.57  cnf(c_0_25, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.40/0.57  fof(c_0_26, negated_conjecture, ~(![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3)))), inference(assume_negation,[status(cth)],[t106_xboole_1])).
% 0.40/0.57  cnf(c_0_27, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.40/0.57  fof(c_0_28, plain, ![X23]:k3_xboole_0(X23,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.40/0.57  cnf(c_0_29, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.40/0.57  cnf(c_0_30, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_18]), c_0_18])).
% 0.40/0.57  cnf(c_0_31, plain, (k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])).
% 0.40/0.57  fof(c_0_32, plain, ![X18, X19, X20]:k3_xboole_0(k3_xboole_0(X18,X19),X20)=k3_xboole_0(X18,k3_xboole_0(X19,X20)), inference(variable_rename,[status(thm)],[t16_xboole_1])).
% 0.40/0.57  fof(c_0_33, negated_conjecture, (r1_tarski(esk3_0,k4_xboole_0(esk4_0,esk5_0))&(~r1_tarski(esk3_0,esk4_0)|~r1_xboole_0(esk3_0,esk5_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])).
% 0.40/0.57  cnf(c_0_34, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[c_0_27, c_0_18])).
% 0.40/0.57  cnf(c_0_35, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.40/0.57  fof(c_0_36, plain, ![X29, X30]:r1_xboole_0(k4_xboole_0(X29,X30),X30), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.40/0.57  cnf(c_0_37, plain, (r1_tarski(X1,X2)|k5_xboole_0(X1,k3_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_29, c_0_18])).
% 0.40/0.57  cnf(c_0_38, plain, (k5_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_30, c_0_31])).
% 0.40/0.57  cnf(c_0_39, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.40/0.57  cnf(c_0_40, negated_conjecture, (r1_tarski(esk3_0,k4_xboole_0(esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.40/0.57  cnf(c_0_41, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_34, c_0_35])).
% 0.40/0.57  cnf(c_0_42, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.40/0.57  cnf(c_0_43, plain, (r1_tarski(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_31]), c_0_38])).
% 0.40/0.57  cnf(c_0_44, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X3))=k3_xboole_0(X2,k3_xboole_0(X1,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_25]), c_0_39])).
% 0.40/0.57  cnf(c_0_45, negated_conjecture, (r1_tarski(esk3_0,k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk5_0)))), inference(rw,[status(thm)],[c_0_40, c_0_18])).
% 0.40/0.57  cnf(c_0_46, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X1))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_35]), c_0_41])).
% 0.40/0.57  fof(c_0_47, plain, ![X6, X7, X9, X10, X11]:((r1_xboole_0(X6,X7)|r2_hidden(esk1_2(X6,X7),k3_xboole_0(X6,X7)))&(~r2_hidden(X11,k3_xboole_0(X9,X10))|~r1_xboole_0(X9,X10))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.40/0.57  fof(c_0_48, plain, ![X12]:(X12=k1_xboole_0|r2_hidden(esk2_1(X12),X12)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.40/0.57  cnf(c_0_49, plain, (r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2)), inference(rw,[status(thm)],[c_0_42, c_0_18])).
% 0.40/0.57  cnf(c_0_50, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=X1|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_43]), c_0_31])).
% 0.40/0.57  cnf(c_0_51, plain, (k3_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X3))))=k3_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X3)))), inference(spm,[status(thm)],[c_0_44, c_0_31])).
% 0.40/0.57  cnf(c_0_52, negated_conjecture, (k3_xboole_0(esk3_0,k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk5_0)))=esk3_0), inference(spm,[status(thm)],[c_0_23, c_0_45])).
% 0.40/0.57  cnf(c_0_53, plain, (k3_xboole_0(X1,X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_46]), c_0_35]), c_0_41])).
% 0.40/0.57  cnf(c_0_54, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.40/0.57  cnf(c_0_55, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.40/0.57  cnf(c_0_56, negated_conjecture, (~r1_tarski(esk3_0,esk4_0)|~r1_xboole_0(esk3_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.40/0.57  cnf(c_0_57, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.40/0.57  cnf(c_0_58, negated_conjecture, (k3_xboole_0(esk3_0,esk4_0)=esk3_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_25])).
% 0.40/0.57  cnf(c_0_59, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_46, c_0_53])).
% 0.40/0.57  cnf(c_0_60, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.40/0.57  cnf(c_0_61, negated_conjecture, (k3_xboole_0(esk3_0,esk5_0)!=k1_xboole_0|~r1_tarski(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.40/0.57  cnf(c_0_62, negated_conjecture, (r1_tarski(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_58]), c_0_59])])).
% 0.40/0.57  cnf(c_0_63, negated_conjecture, (k3_xboole_0(esk3_0,k3_xboole_0(X1,k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk5_0))))=k3_xboole_0(X1,esk3_0)), inference(spm,[status(thm)],[c_0_44, c_0_52])).
% 0.40/0.57  cnf(c_0_64, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_49]), c_0_25])).
% 0.40/0.57  cnf(c_0_65, negated_conjecture, (k3_xboole_0(esk3_0,esk5_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_62])])).
% 0.40/0.57  cnf(c_0_66, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_35]), c_0_25]), c_0_65]), ['proof']).
% 0.40/0.57  # SZS output end CNFRefutation
% 0.40/0.57  # Proof object total steps             : 67
% 0.40/0.57  # Proof object clause steps            : 40
% 0.40/0.57  # Proof object formula steps           : 27
% 0.40/0.57  # Proof object conjectures             : 13
% 0.40/0.57  # Proof object clause conjectures      : 10
% 0.40/0.57  # Proof object formula conjectures     : 3
% 0.40/0.57  # Proof object initial clauses used    : 14
% 0.40/0.57  # Proof object initial formulas used   : 13
% 0.40/0.57  # Proof object generating inferences   : 16
% 0.40/0.57  # Proof object simplifying inferences  : 26
% 0.40/0.57  # Training examples: 0 positive, 0 negative
% 0.40/0.57  # Parsed axioms                        : 13
% 0.40/0.57  # Removed by relevancy pruning/SinE    : 0
% 0.40/0.57  # Initial clauses                      : 16
% 0.40/0.57  # Removed in clause preprocessing      : 1
% 0.40/0.57  # Initial clauses in saturation        : 15
% 0.40/0.57  # Processed clauses                    : 3126
% 0.40/0.57  # ...of these trivial                  : 167
% 0.40/0.57  # ...subsumed                          : 2506
% 0.40/0.57  # ...remaining for further processing  : 453
% 0.40/0.57  # Other redundant clauses eliminated   : 0
% 0.40/0.57  # Clauses deleted for lack of memory   : 0
% 0.40/0.57  # Backward-subsumed                    : 9
% 0.40/0.57  # Backward-rewritten                   : 11
% 0.40/0.57  # Generated clauses                    : 25104
% 0.40/0.57  # ...of the previous two non-trivial   : 19840
% 0.40/0.57  # Contextual simplify-reflections      : 0
% 0.40/0.57  # Paramodulations                      : 25104
% 0.40/0.57  # Factorizations                       : 0
% 0.40/0.57  # Equation resolutions                 : 0
% 0.40/0.57  # Propositional unsat checks           : 0
% 0.40/0.57  #    Propositional check models        : 0
% 0.40/0.57  #    Propositional check unsatisfiable : 0
% 0.40/0.57  #    Propositional clauses             : 0
% 0.40/0.57  #    Propositional clauses after purity: 0
% 0.40/0.57  #    Propositional unsat core size     : 0
% 0.40/0.57  #    Propositional preprocessing time  : 0.000
% 0.40/0.57  #    Propositional encoding time       : 0.000
% 0.40/0.57  #    Propositional solver time         : 0.000
% 0.40/0.57  #    Success case prop preproc time    : 0.000
% 0.40/0.57  #    Success case prop encoding time   : 0.000
% 0.40/0.57  #    Success case prop solver time     : 0.000
% 0.40/0.57  # Current number of processed clauses  : 433
% 0.40/0.57  #    Positive orientable unit clauses  : 94
% 0.40/0.57  #    Positive unorientable unit clauses: 4
% 0.40/0.57  #    Negative unit clauses             : 4
% 0.40/0.57  #    Non-unit-clauses                  : 331
% 0.40/0.57  # Current number of unprocessed clauses: 16117
% 0.40/0.57  # ...number of literals in the above   : 28065
% 0.40/0.57  # Current number of archived formulas  : 0
% 0.40/0.57  # Current number of archived clauses   : 21
% 0.40/0.57  # Clause-clause subsumption calls (NU) : 37799
% 0.40/0.57  # Rec. Clause-clause subsumption calls : 37390
% 0.40/0.57  # Non-unit clause-clause subsumptions  : 2272
% 0.40/0.57  # Unit Clause-clause subsumption calls : 72
% 0.40/0.57  # Rewrite failures with RHS unbound    : 0
% 0.40/0.57  # BW rewrite match attempts            : 292
% 0.40/0.57  # BW rewrite match successes           : 50
% 0.40/0.57  # Condensation attempts                : 0
% 0.40/0.57  # Condensation successes               : 0
% 0.40/0.57  # Termbank termtop insertions          : 265432
% 0.40/0.57  
% 0.40/0.57  # -------------------------------------------------
% 0.40/0.57  # User time                : 0.209 s
% 0.40/0.57  # System time              : 0.015 s
% 0.40/0.57  # Total time               : 0.224 s
% 0.40/0.57  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------

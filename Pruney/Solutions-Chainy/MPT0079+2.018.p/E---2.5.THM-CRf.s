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
% DateTime   : Thu Dec  3 10:33:02 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 483 expanded)
%              Number of clauses        :   42 ( 216 expanded)
%              Number of leaves         :    9 ( 126 expanded)
%              Depth                    :   11
%              Number of atoms          :   81 ( 734 expanded)
%              Number of equality atoms :   60 ( 531 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t72_xboole_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( k2_xboole_0(X1,X2) = k2_xboole_0(X3,X4)
        & r1_xboole_0(X3,X1)
        & r1_xboole_0(X4,X2) )
     => X3 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(c_0_9,plain,(
    ! [X9,X10] :
      ( ( ~ r1_xboole_0(X9,X10)
        | k3_xboole_0(X9,X10) = k1_xboole_0 )
      & ( k3_xboole_0(X9,X10) != k1_xboole_0
        | r1_xboole_0(X9,X10) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_10,plain,(
    ! [X19,X20] : k4_xboole_0(X19,k4_xboole_0(X19,X20)) = k3_xboole_0(X19,X20) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( k2_xboole_0(X1,X2) = k2_xboole_0(X3,X4)
          & r1_xboole_0(X3,X1)
          & r1_xboole_0(X4,X2) )
       => X3 = X2 ) ),
    inference(assume_negation,[status(cth)],[t72_xboole_1])).

fof(c_0_12,plain,(
    ! [X7,X8] : k3_xboole_0(X7,X8) = k3_xboole_0(X8,X7) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_13,plain,(
    ! [X17,X18] : k4_xboole_0(X17,k3_xboole_0(X17,X18)) = k4_xboole_0(X17,X18) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

cnf(c_0_14,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_16,negated_conjecture,
    ( k2_xboole_0(esk1_0,esk2_0) = k2_xboole_0(esk3_0,esk4_0)
    & r1_xboole_0(esk3_0,esk1_0)
    & r1_xboole_0(esk4_0,esk2_0)
    & esk3_0 != esk2_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

cnf(c_0_17,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_22,plain,(
    ! [X11] : k4_xboole_0(X11,k1_xboole_0) = X11 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_23,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,k4_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_17,c_0_15])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_15]),c_0_15])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_19,c_0_15])).

cnf(c_0_26,negated_conjecture,
    ( k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk2_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X2,k4_xboole_0(X2,X1)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_30,negated_conjecture,
    ( k4_xboole_0(esk4_0,esk2_0) = esk4_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])).

fof(c_0_31,plain,(
    ! [X12,X13] : k4_xboole_0(k2_xboole_0(X12,X13),X13) = k4_xboole_0(X12,X13) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

fof(c_0_32,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_33,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X1)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_28,c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk1_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_20,c_0_29])).

cnf(c_0_35,plain,
    ( r1_xboole_0(k1_xboole_0,X1)
    | k4_xboole_0(X1,X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_28,c_0_27])).

cnf(c_0_36,negated_conjecture,
    ( k4_xboole_0(esk4_0,esk4_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_26,c_0_30])).

fof(c_0_37,plain,(
    ! [X14,X15,X16] : k4_xboole_0(k4_xboole_0(X14,X15),X16) = k4_xboole_0(X14,k2_xboole_0(X15,X16)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_38,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_24])).

cnf(c_0_39,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_40,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_41,negated_conjecture,
    ( r1_xboole_0(k1_xboole_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_42,negated_conjecture,
    ( r1_xboole_0(k1_xboole_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_43,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( k4_xboole_0(esk2_0,esk4_0) = esk2_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_30]),c_0_36]),c_0_27])).

cnf(c_0_45,negated_conjecture,
    ( k2_xboole_0(esk1_0,esk2_0) = k2_xboole_0(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_46,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X1) = k4_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_47,negated_conjecture,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,esk3_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_20,c_0_41])).

cnf(c_0_48,negated_conjecture,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,esk4_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_20,c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( k4_xboole_0(esk2_0,k2_xboole_0(esk4_0,X1)) = k4_xboole_0(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_50,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(X1,esk1_0),esk2_0) = k4_xboole_0(X1,k2_xboole_0(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_45])).

cnf(c_0_51,negated_conjecture,
    ( k4_xboole_0(esk2_0,esk1_0) = k4_xboole_0(k2_xboole_0(esk3_0,esk4_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_45])).

cnf(c_0_52,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)) = k4_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_27])).

cnf(c_0_53,negated_conjecture,
    ( k4_xboole_0(k1_xboole_0,esk3_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_47]),c_0_27])).

cnf(c_0_54,negated_conjecture,
    ( k4_xboole_0(k1_xboole_0,esk4_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_48]),c_0_27])).

cnf(c_0_55,negated_conjecture,
    ( k4_xboole_0(esk2_0,k2_xboole_0(X1,esk4_0)) = k4_xboole_0(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_40])).

cnf(c_0_56,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk1_0) = esk3_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_34]),c_0_27])).

cnf(c_0_57,negated_conjecture,
    ( k4_xboole_0(esk2_0,esk3_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_50]),c_0_52]),c_0_43]),c_0_53]),c_0_54]),c_0_27]),c_0_55])).

cnf(c_0_58,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk2_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_56]),c_0_43]),c_0_52]),c_0_53]),c_0_27]),c_0_54])).

cnf(c_0_59,negated_conjecture,
    ( esk3_0 != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_60,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_57]),c_0_27]),c_0_58]),c_0_27]),c_0_59]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.32  % Computer   : n022.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 17:02:56 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  # Version: 2.5pre002
% 0.12/0.32  # No SInE strategy applied
% 0.12/0.32  # Trying AutoSched0 for 299 seconds
% 0.12/0.35  # AutoSched0-Mode selected heuristic G_E___200_B02_F1_AE_CS_SP_PI_S0S
% 0.12/0.35  # and selection function SelectComplexG.
% 0.12/0.35  #
% 0.12/0.35  # Preprocessing time       : 0.013 s
% 0.12/0.35  
% 0.12/0.35  # Proof found!
% 0.12/0.35  # SZS status Theorem
% 0.12/0.35  # SZS output start CNFRefutation
% 0.12/0.35  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.12/0.35  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.12/0.35  fof(t72_xboole_1, conjecture, ![X1, X2, X3, X4]:(((k2_xboole_0(X1,X2)=k2_xboole_0(X3,X4)&r1_xboole_0(X3,X1))&r1_xboole_0(X4,X2))=>X3=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_xboole_1)).
% 0.12/0.35  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.12/0.35  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 0.12/0.35  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 0.12/0.35  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 0.12/0.35  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.12/0.35  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.12/0.35  fof(c_0_9, plain, ![X9, X10]:((~r1_xboole_0(X9,X10)|k3_xboole_0(X9,X10)=k1_xboole_0)&(k3_xboole_0(X9,X10)!=k1_xboole_0|r1_xboole_0(X9,X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.12/0.35  fof(c_0_10, plain, ![X19, X20]:k4_xboole_0(X19,k4_xboole_0(X19,X20))=k3_xboole_0(X19,X20), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.12/0.35  fof(c_0_11, negated_conjecture, ~(![X1, X2, X3, X4]:(((k2_xboole_0(X1,X2)=k2_xboole_0(X3,X4)&r1_xboole_0(X3,X1))&r1_xboole_0(X4,X2))=>X3=X2)), inference(assume_negation,[status(cth)],[t72_xboole_1])).
% 0.12/0.35  fof(c_0_12, plain, ![X7, X8]:k3_xboole_0(X7,X8)=k3_xboole_0(X8,X7), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.12/0.35  fof(c_0_13, plain, ![X17, X18]:k4_xboole_0(X17,k3_xboole_0(X17,X18))=k4_xboole_0(X17,X18), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 0.12/0.35  cnf(c_0_14, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.35  cnf(c_0_15, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.35  fof(c_0_16, negated_conjecture, (((k2_xboole_0(esk1_0,esk2_0)=k2_xboole_0(esk3_0,esk4_0)&r1_xboole_0(esk3_0,esk1_0))&r1_xboole_0(esk4_0,esk2_0))&esk3_0!=esk2_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 0.12/0.35  cnf(c_0_17, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.35  cnf(c_0_18, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.35  cnf(c_0_19, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.35  cnf(c_0_20, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.12/0.35  cnf(c_0_21, negated_conjecture, (r1_xboole_0(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.35  fof(c_0_22, plain, ![X11]:k4_xboole_0(X11,k1_xboole_0)=X11, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.12/0.35  cnf(c_0_23, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,k4_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_17, c_0_15])).
% 0.12/0.35  cnf(c_0_24, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_15]), c_0_15])).
% 0.12/0.35  cnf(c_0_25, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_19, c_0_15])).
% 0.12/0.35  cnf(c_0_26, negated_conjecture, (k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk2_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.12/0.35  cnf(c_0_27, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.35  cnf(c_0_28, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X2,k4_xboole_0(X2,X1))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.12/0.35  cnf(c_0_29, negated_conjecture, (r1_xboole_0(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.35  cnf(c_0_30, negated_conjecture, (k4_xboole_0(esk4_0,esk2_0)=esk4_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27])).
% 0.12/0.35  fof(c_0_31, plain, ![X12, X13]:k4_xboole_0(k2_xboole_0(X12,X13),X13)=k4_xboole_0(X12,X13), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 0.12/0.35  fof(c_0_32, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.12/0.35  cnf(c_0_33, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X1)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_28, c_0_25])).
% 0.12/0.35  cnf(c_0_34, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk1_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_20, c_0_29])).
% 0.12/0.35  cnf(c_0_35, plain, (r1_xboole_0(k1_xboole_0,X1)|k4_xboole_0(X1,X1)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_28, c_0_27])).
% 0.12/0.35  cnf(c_0_36, negated_conjecture, (k4_xboole_0(esk4_0,esk4_0)=k1_xboole_0), inference(rw,[status(thm)],[c_0_26, c_0_30])).
% 0.12/0.35  fof(c_0_37, plain, ![X14, X15, X16]:k4_xboole_0(k4_xboole_0(X14,X15),X16)=k4_xboole_0(X14,k2_xboole_0(X15,X16)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.12/0.35  cnf(c_0_38, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_25, c_0_24])).
% 0.12/0.35  cnf(c_0_39, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.12/0.35  cnf(c_0_40, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.12/0.35  cnf(c_0_41, negated_conjecture, (r1_xboole_0(k1_xboole_0,esk3_0)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.12/0.35  cnf(c_0_42, negated_conjecture, (r1_xboole_0(k1_xboole_0,esk4_0)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.12/0.35  cnf(c_0_43, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.12/0.35  cnf(c_0_44, negated_conjecture, (k4_xboole_0(esk2_0,esk4_0)=esk2_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_30]), c_0_36]), c_0_27])).
% 0.12/0.35  cnf(c_0_45, negated_conjecture, (k2_xboole_0(esk1_0,esk2_0)=k2_xboole_0(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.35  cnf(c_0_46, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X1)=k4_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.12/0.35  cnf(c_0_47, negated_conjecture, (k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,esk3_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_20, c_0_41])).
% 0.12/0.35  cnf(c_0_48, negated_conjecture, (k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,esk4_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_20, c_0_42])).
% 0.12/0.35  cnf(c_0_49, negated_conjecture, (k4_xboole_0(esk2_0,k2_xboole_0(esk4_0,X1))=k4_xboole_0(esk2_0,X1)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.12/0.35  cnf(c_0_50, negated_conjecture, (k4_xboole_0(k4_xboole_0(X1,esk1_0),esk2_0)=k4_xboole_0(X1,k2_xboole_0(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_43, c_0_45])).
% 0.12/0.35  cnf(c_0_51, negated_conjecture, (k4_xboole_0(esk2_0,esk1_0)=k4_xboole_0(k2_xboole_0(esk3_0,esk4_0),esk1_0)), inference(spm,[status(thm)],[c_0_46, c_0_45])).
% 0.12/0.35  cnf(c_0_52, plain, (k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))=k4_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_24, c_0_27])).
% 0.12/0.35  cnf(c_0_53, negated_conjecture, (k4_xboole_0(k1_xboole_0,esk3_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_47]), c_0_27])).
% 0.12/0.35  cnf(c_0_54, negated_conjecture, (k4_xboole_0(k1_xboole_0,esk4_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_48]), c_0_27])).
% 0.12/0.35  cnf(c_0_55, negated_conjecture, (k4_xboole_0(esk2_0,k2_xboole_0(X1,esk4_0))=k4_xboole_0(esk2_0,X1)), inference(spm,[status(thm)],[c_0_49, c_0_40])).
% 0.12/0.35  cnf(c_0_56, negated_conjecture, (k4_xboole_0(esk3_0,esk1_0)=esk3_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_34]), c_0_27])).
% 0.12/0.35  cnf(c_0_57, negated_conjecture, (k4_xboole_0(esk2_0,esk3_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_50]), c_0_52]), c_0_43]), c_0_53]), c_0_54]), c_0_27]), c_0_55])).
% 0.12/0.35  cnf(c_0_58, negated_conjecture, (k4_xboole_0(esk3_0,esk2_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_56]), c_0_43]), c_0_52]), c_0_53]), c_0_27]), c_0_54])).
% 0.12/0.35  cnf(c_0_59, negated_conjecture, (esk3_0!=esk2_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.35  cnf(c_0_60, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_57]), c_0_27]), c_0_58]), c_0_27]), c_0_59]), ['proof']).
% 0.12/0.35  # SZS output end CNFRefutation
% 0.12/0.35  # Proof object total steps             : 61
% 0.12/0.35  # Proof object clause steps            : 42
% 0.12/0.35  # Proof object formula steps           : 19
% 0.12/0.35  # Proof object conjectures             : 26
% 0.12/0.35  # Proof object clause conjectures      : 23
% 0.12/0.35  # Proof object formula conjectures     : 3
% 0.12/0.35  # Proof object initial clauses used    : 13
% 0.12/0.35  # Proof object initial formulas used   : 9
% 0.12/0.35  # Proof object generating inferences   : 24
% 0.12/0.35  # Proof object simplifying inferences  : 28
% 0.12/0.35  # Training examples: 0 positive, 0 negative
% 0.12/0.35  # Parsed axioms                        : 9
% 0.12/0.35  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.35  # Initial clauses                      : 13
% 0.12/0.35  # Removed in clause preprocessing      : 1
% 0.12/0.35  # Initial clauses in saturation        : 12
% 0.12/0.35  # Processed clauses                    : 361
% 0.12/0.35  # ...of these trivial                  : 20
% 0.12/0.35  # ...subsumed                          : 173
% 0.12/0.35  # ...remaining for further processing  : 167
% 0.12/0.35  # Other redundant clauses eliminated   : 0
% 0.12/0.35  # Clauses deleted for lack of memory   : 0
% 0.12/0.35  # Backward-subsumed                    : 2
% 0.12/0.35  # Backward-rewritten                   : 32
% 0.12/0.35  # Generated clauses                    : 2060
% 0.12/0.35  # ...of the previous two non-trivial   : 1654
% 0.12/0.35  # Contextual simplify-reflections      : 0
% 0.12/0.35  # Paramodulations                      : 2057
% 0.12/0.35  # Factorizations                       : 0
% 0.12/0.35  # Equation resolutions                 : 3
% 0.12/0.35  # Propositional unsat checks           : 0
% 0.12/0.35  #    Propositional check models        : 0
% 0.12/0.35  #    Propositional check unsatisfiable : 0
% 0.12/0.35  #    Propositional clauses             : 0
% 0.12/0.35  #    Propositional clauses after purity: 0
% 0.12/0.35  #    Propositional unsat core size     : 0
% 0.12/0.35  #    Propositional preprocessing time  : 0.000
% 0.12/0.35  #    Propositional encoding time       : 0.000
% 0.12/0.35  #    Propositional solver time         : 0.000
% 0.12/0.35  #    Success case prop preproc time    : 0.000
% 0.12/0.35  #    Success case prop encoding time   : 0.000
% 0.12/0.35  #    Success case prop solver time     : 0.000
% 0.12/0.35  # Current number of processed clauses  : 133
% 0.12/0.35  #    Positive orientable unit clauses  : 54
% 0.12/0.35  #    Positive unorientable unit clauses: 9
% 0.12/0.35  #    Negative unit clauses             : 1
% 0.12/0.35  #    Non-unit-clauses                  : 69
% 0.12/0.35  # Current number of unprocessed clauses: 1276
% 0.12/0.35  # ...number of literals in the above   : 1763
% 0.12/0.35  # Current number of archived formulas  : 0
% 0.12/0.35  # Current number of archived clauses   : 35
% 0.12/0.35  # Clause-clause subsumption calls (NU) : 931
% 0.12/0.35  # Rec. Clause-clause subsumption calls : 927
% 0.12/0.35  # Non-unit clause-clause subsumptions  : 169
% 0.12/0.35  # Unit Clause-clause subsumption calls : 11
% 0.12/0.35  # Rewrite failures with RHS unbound    : 0
% 0.12/0.35  # BW rewrite match attempts            : 103
% 0.12/0.35  # BW rewrite match successes           : 40
% 0.12/0.35  # Condensation attempts                : 0
% 0.12/0.35  # Condensation successes               : 0
% 0.12/0.35  # Termbank termtop insertions          : 21286
% 0.12/0.35  
% 0.12/0.35  # -------------------------------------------------
% 0.12/0.35  # User time                : 0.029 s
% 0.12/0.35  # System time              : 0.002 s
% 0.12/0.35  # Total time               : 0.031 s
% 0.12/0.35  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------

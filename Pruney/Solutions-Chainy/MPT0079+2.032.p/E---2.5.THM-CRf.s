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
% DateTime   : Thu Dec  3 10:33:04 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 281 expanded)
%              Number of clauses        :   43 ( 121 expanded)
%              Number of leaves         :   12 (  74 expanded)
%              Depth                    :   19
%              Number of atoms          :  115 ( 527 expanded)
%              Number of equality atoms :   53 ( 247 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t72_xboole_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( k2_xboole_0(X1,X2) = k2_xboole_0(X3,X4)
        & r1_xboole_0(X3,X1)
        & r1_xboole_0(X4,X2) )
     => X3 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(t70_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ~ ( ~ r1_xboole_0(X1,k2_xboole_0(X2,X3))
          & r1_xboole_0(X1,X2)
          & r1_xboole_0(X1,X3) )
      & ~ ( ~ ( r1_xboole_0(X1,X2)
              & r1_xboole_0(X1,X3) )
          & r1_xboole_0(X1,k2_xboole_0(X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t71_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( k2_xboole_0(X1,X2) = k2_xboole_0(X3,X2)
        & r1_xboole_0(X1,X2)
        & r1_xboole_0(X3,X2) )
     => X1 = X3 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_xboole_1)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(c_0_12,plain,(
    ! [X19,X20] : k4_xboole_0(X19,k2_xboole_0(X19,X20)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

fof(c_0_13,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( k2_xboole_0(X1,X2) = k2_xboole_0(X3,X4)
          & r1_xboole_0(X3,X1)
          & r1_xboole_0(X4,X2) )
       => X3 = X2 ) ),
    inference(assume_negation,[status(cth)],[t72_xboole_1])).

fof(c_0_15,plain,(
    ! [X14,X15] : k2_xboole_0(X14,k4_xboole_0(X15,X14)) = k2_xboole_0(X14,X15) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

fof(c_0_16,plain,(
    ! [X16,X17,X18] : k4_xboole_0(k4_xboole_0(X16,X17),X18) = k4_xboole_0(X16,k2_xboole_0(X17,X18)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_17,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_19,negated_conjecture,
    ( k2_xboole_0(esk1_0,esk2_0) = k2_xboole_0(esk3_0,esk4_0)
    & r1_xboole_0(esk3_0,esk1_0)
    & r1_xboole_0(esk4_0,esk2_0)
    & esk3_0 != esk2_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

cnf(c_0_20,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( k2_xboole_0(esk1_0,esk2_0) = k2_xboole_0(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_24,plain,(
    ! [X13] : k2_xboole_0(X13,k1_xboole_0) = X13 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_25,plain,(
    ! [X26,X27,X28] :
      ( ( r1_xboole_0(X26,k2_xboole_0(X27,X28))
        | ~ r1_xboole_0(X26,X27)
        | ~ r1_xboole_0(X26,X28) )
      & ( r1_xboole_0(X26,X27)
        | ~ r1_xboole_0(X26,k2_xboole_0(X27,X28)) )
      & ( r1_xboole_0(X26,X28)
        | ~ r1_xboole_0(X26,k2_xboole_0(X27,X28)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).

cnf(c_0_26,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1))) = k2_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( k4_xboole_0(esk2_0,k2_xboole_0(esk3_0,esk4_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_29,plain,(
    ! [X9,X10] :
      ( ~ r1_xboole_0(X9,X10)
      | r1_xboole_0(X10,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_30,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,k2_xboole_0(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( k2_xboole_0(esk4_0,k4_xboole_0(esk2_0,esk3_0)) = esk4_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])).

cnf(c_0_32,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_34,plain,(
    ! [X7,X8] :
      ( ( ~ r1_xboole_0(X7,X8)
        | k3_xboole_0(X7,X8) = k1_xboole_0 )
      & ( k3_xboole_0(X7,X8) != k1_xboole_0
        | r1_xboole_0(X7,X8) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_35,plain,(
    ! [X21,X22] : k4_xboole_0(X21,k4_xboole_0(X21,X22)) = k3_xboole_0(X21,X22) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_36,negated_conjecture,
    ( r1_xboole_0(X1,k4_xboole_0(esk2_0,esk3_0))
    | ~ r1_xboole_0(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( r1_xboole_0(esk2_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_38,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_39,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_40,negated_conjecture,
    ( r1_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_41,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_42,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk2_0,esk3_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_40])).

cnf(c_0_43,negated_conjecture,
    ( k4_xboole_0(esk2_0,esk3_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_21]),c_0_22]),c_0_21]),c_0_28])).

cnf(c_0_44,negated_conjecture,
    ( k2_xboole_0(esk3_0,esk2_0) = esk3_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_43]),c_0_28])).

cnf(c_0_45,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_46,negated_conjecture,
    ( r1_xboole_0(X1,esk2_0)
    | ~ r1_xboole_0(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_44])).

cnf(c_0_47,negated_conjecture,
    ( r1_xboole_0(esk1_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_45])).

cnf(c_0_48,plain,
    ( r1_xboole_0(X1,k2_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_49,negated_conjecture,
    ( r1_xboole_0(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_50,negated_conjecture,
    ( r1_xboole_0(esk2_0,k2_xboole_0(X1,esk4_0))
    | ~ r1_xboole_0(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_37])).

cnf(c_0_51,negated_conjecture,
    ( r1_xboole_0(esk2_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_49])).

cnf(c_0_52,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,k2_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_20])).

cnf(c_0_53,negated_conjecture,
    ( r1_xboole_0(esk2_0,k2_xboole_0(esk1_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_54,negated_conjecture,
    ( r1_xboole_0(esk2_0,k4_xboole_0(esk4_0,esk1_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

fof(c_0_55,plain,(
    ! [X29,X30,X31] :
      ( k2_xboole_0(X29,X30) != k2_xboole_0(X31,X30)
      | ~ r1_xboole_0(X29,X30)
      | ~ r1_xboole_0(X31,X30)
      | X29 = X31 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t71_xboole_1])])).

fof(c_0_56,plain,(
    ! [X23,X24,X25] : k2_xboole_0(k2_xboole_0(X23,X24),X25) = k2_xboole_0(X23,k2_xboole_0(X24,X25)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

cnf(c_0_57,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk4_0,esk1_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_54])).

cnf(c_0_58,plain,
    ( X1 = X3
    | k2_xboole_0(X1,X2) != k2_xboole_0(X3,X2)
    | ~ r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_59,negated_conjecture,
    ( k4_xboole_0(esk1_0,k2_xboole_0(esk3_0,esk4_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_17,c_0_23])).

cnf(c_0_60,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_61,negated_conjecture,
    ( k4_xboole_0(esk4_0,esk1_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_57]),c_0_21]),c_0_23]),c_0_22]),c_0_21]),c_0_28])).

cnf(c_0_62,negated_conjecture,
    ( X1 = esk3_0
    | k2_xboole_0(X1,esk1_0) != k2_xboole_0(esk3_0,esk1_0)
    | ~ r1_xboole_0(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_45])).

cnf(c_0_63,negated_conjecture,
    ( esk3_0 != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_64,negated_conjecture,
    ( k2_xboole_0(esk3_0,k2_xboole_0(esk1_0,esk4_0)) = k2_xboole_0(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_59]),c_0_60]),c_0_28]),c_0_60]),c_0_18])).

cnf(c_0_65,negated_conjecture,
    ( k2_xboole_0(esk1_0,esk4_0) = esk1_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_61]),c_0_28])).

cnf(c_0_66,negated_conjecture,
    ( k2_xboole_0(esk3_0,esk4_0) != k2_xboole_0(esk3_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_51]),c_0_18]),c_0_23]),c_0_63])).

cnf(c_0_67,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_65]),c_0_66]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:33:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.40  # AutoSched0-Mode selected heuristic G_E___200_B02_F1_AE_CS_SP_PI_S0S
% 0.13/0.40  # and selection function SelectComplexG.
% 0.13/0.40  #
% 0.13/0.40  # Preprocessing time       : 0.028 s
% 0.13/0.40  
% 0.13/0.40  # Proof found!
% 0.13/0.40  # SZS status Theorem
% 0.13/0.40  # SZS output start CNFRefutation
% 0.13/0.40  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 0.13/0.40  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.13/0.40  fof(t72_xboole_1, conjecture, ![X1, X2, X3, X4]:(((k2_xboole_0(X1,X2)=k2_xboole_0(X3,X4)&r1_xboole_0(X3,X1))&r1_xboole_0(X4,X2))=>X3=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_xboole_1)).
% 0.13/0.40  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.13/0.40  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.13/0.40  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 0.13/0.40  fof(t70_xboole_1, axiom, ![X1, X2, X3]:(~(((~(r1_xboole_0(X1,k2_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))&r1_xboole_0(X1,X3)))&~((~((r1_xboole_0(X1,X2)&r1_xboole_0(X1,X3)))&r1_xboole_0(X1,k2_xboole_0(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 0.13/0.40  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.13/0.40  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.13/0.40  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.13/0.40  fof(t71_xboole_1, axiom, ![X1, X2, X3]:(((k2_xboole_0(X1,X2)=k2_xboole_0(X3,X2)&r1_xboole_0(X1,X2))&r1_xboole_0(X3,X2))=>X1=X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_xboole_1)).
% 0.13/0.40  fof(t4_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 0.13/0.40  fof(c_0_12, plain, ![X19, X20]:k4_xboole_0(X19,k2_xboole_0(X19,X20))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 0.13/0.40  fof(c_0_13, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.13/0.40  fof(c_0_14, negated_conjecture, ~(![X1, X2, X3, X4]:(((k2_xboole_0(X1,X2)=k2_xboole_0(X3,X4)&r1_xboole_0(X3,X1))&r1_xboole_0(X4,X2))=>X3=X2)), inference(assume_negation,[status(cth)],[t72_xboole_1])).
% 0.13/0.40  fof(c_0_15, plain, ![X14, X15]:k2_xboole_0(X14,k4_xboole_0(X15,X14))=k2_xboole_0(X14,X15), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.13/0.40  fof(c_0_16, plain, ![X16, X17, X18]:k4_xboole_0(k4_xboole_0(X16,X17),X18)=k4_xboole_0(X16,k2_xboole_0(X17,X18)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.13/0.40  cnf(c_0_17, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.40  cnf(c_0_18, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.40  fof(c_0_19, negated_conjecture, (((k2_xboole_0(esk1_0,esk2_0)=k2_xboole_0(esk3_0,esk4_0)&r1_xboole_0(esk3_0,esk1_0))&r1_xboole_0(esk4_0,esk2_0))&esk3_0!=esk2_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.13/0.40  cnf(c_0_20, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.40  cnf(c_0_21, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.40  cnf(c_0_22, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.13/0.40  cnf(c_0_23, negated_conjecture, (k2_xboole_0(esk1_0,esk2_0)=k2_xboole_0(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.40  fof(c_0_24, plain, ![X13]:k2_xboole_0(X13,k1_xboole_0)=X13, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.13/0.40  fof(c_0_25, plain, ![X26, X27, X28]:((r1_xboole_0(X26,k2_xboole_0(X27,X28))|~r1_xboole_0(X26,X27)|~r1_xboole_0(X26,X28))&((r1_xboole_0(X26,X27)|~r1_xboole_0(X26,k2_xboole_0(X27,X28)))&(r1_xboole_0(X26,X28)|~r1_xboole_0(X26,k2_xboole_0(X27,X28))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).
% 0.13/0.40  cnf(c_0_26, plain, (k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1)))=k2_xboole_0(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.13/0.40  cnf(c_0_27, negated_conjecture, (k4_xboole_0(esk2_0,k2_xboole_0(esk3_0,esk4_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.13/0.40  cnf(c_0_28, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.40  fof(c_0_29, plain, ![X9, X10]:(~r1_xboole_0(X9,X10)|r1_xboole_0(X10,X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.13/0.40  cnf(c_0_30, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X1,k2_xboole_0(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.40  cnf(c_0_31, negated_conjecture, (k2_xboole_0(esk4_0,k4_xboole_0(esk2_0,esk3_0))=esk4_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])).
% 0.13/0.40  cnf(c_0_32, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.40  cnf(c_0_33, negated_conjecture, (r1_xboole_0(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.40  fof(c_0_34, plain, ![X7, X8]:((~r1_xboole_0(X7,X8)|k3_xboole_0(X7,X8)=k1_xboole_0)&(k3_xboole_0(X7,X8)!=k1_xboole_0|r1_xboole_0(X7,X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.13/0.40  fof(c_0_35, plain, ![X21, X22]:k4_xboole_0(X21,k4_xboole_0(X21,X22))=k3_xboole_0(X21,X22), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.13/0.40  cnf(c_0_36, negated_conjecture, (r1_xboole_0(X1,k4_xboole_0(esk2_0,esk3_0))|~r1_xboole_0(X1,esk4_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.13/0.40  cnf(c_0_37, negated_conjecture, (r1_xboole_0(esk2_0,esk4_0)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.13/0.40  cnf(c_0_38, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.40  cnf(c_0_39, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.40  cnf(c_0_40, negated_conjecture, (r1_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.13/0.40  cnf(c_0_41, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_38, c_0_39])).
% 0.13/0.40  cnf(c_0_42, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk2_0,esk3_0),esk2_0)), inference(spm,[status(thm)],[c_0_32, c_0_40])).
% 0.13/0.40  cnf(c_0_43, negated_conjecture, (k4_xboole_0(esk2_0,esk3_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_21]), c_0_22]), c_0_21]), c_0_28])).
% 0.13/0.40  cnf(c_0_44, negated_conjecture, (k2_xboole_0(esk3_0,esk2_0)=esk3_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_43]), c_0_28])).
% 0.13/0.40  cnf(c_0_45, negated_conjecture, (r1_xboole_0(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.40  cnf(c_0_46, negated_conjecture, (r1_xboole_0(X1,esk2_0)|~r1_xboole_0(X1,esk3_0)), inference(spm,[status(thm)],[c_0_30, c_0_44])).
% 0.13/0.40  cnf(c_0_47, negated_conjecture, (r1_xboole_0(esk1_0,esk3_0)), inference(spm,[status(thm)],[c_0_32, c_0_45])).
% 0.13/0.40  cnf(c_0_48, plain, (r1_xboole_0(X1,k2_xboole_0(X2,X3))|~r1_xboole_0(X1,X2)|~r1_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.40  cnf(c_0_49, negated_conjecture, (r1_xboole_0(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.13/0.40  cnf(c_0_50, negated_conjecture, (r1_xboole_0(esk2_0,k2_xboole_0(X1,esk4_0))|~r1_xboole_0(esk2_0,X1)), inference(spm,[status(thm)],[c_0_48, c_0_37])).
% 0.13/0.40  cnf(c_0_51, negated_conjecture, (r1_xboole_0(esk2_0,esk1_0)), inference(spm,[status(thm)],[c_0_32, c_0_49])).
% 0.13/0.40  cnf(c_0_52, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X3))|~r1_xboole_0(X1,k2_xboole_0(X3,X2))), inference(spm,[status(thm)],[c_0_30, c_0_20])).
% 0.13/0.40  cnf(c_0_53, negated_conjecture, (r1_xboole_0(esk2_0,k2_xboole_0(esk1_0,esk4_0))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.13/0.40  cnf(c_0_54, negated_conjecture, (r1_xboole_0(esk2_0,k4_xboole_0(esk4_0,esk1_0))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.13/0.40  fof(c_0_55, plain, ![X29, X30, X31]:(k2_xboole_0(X29,X30)!=k2_xboole_0(X31,X30)|~r1_xboole_0(X29,X30)|~r1_xboole_0(X31,X30)|X29=X31), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t71_xboole_1])])).
% 0.13/0.40  fof(c_0_56, plain, ![X23, X24, X25]:k2_xboole_0(k2_xboole_0(X23,X24),X25)=k2_xboole_0(X23,k2_xboole_0(X24,X25)), inference(variable_rename,[status(thm)],[t4_xboole_1])).
% 0.13/0.40  cnf(c_0_57, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk4_0,esk1_0),esk2_0)), inference(spm,[status(thm)],[c_0_32, c_0_54])).
% 0.13/0.40  cnf(c_0_58, plain, (X1=X3|k2_xboole_0(X1,X2)!=k2_xboole_0(X3,X2)|~r1_xboole_0(X1,X2)|~r1_xboole_0(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.13/0.40  cnf(c_0_59, negated_conjecture, (k4_xboole_0(esk1_0,k2_xboole_0(esk3_0,esk4_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_17, c_0_23])).
% 0.13/0.40  cnf(c_0_60, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.13/0.40  cnf(c_0_61, negated_conjecture, (k4_xboole_0(esk4_0,esk1_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_57]), c_0_21]), c_0_23]), c_0_22]), c_0_21]), c_0_28])).
% 0.13/0.40  cnf(c_0_62, negated_conjecture, (X1=esk3_0|k2_xboole_0(X1,esk1_0)!=k2_xboole_0(esk3_0,esk1_0)|~r1_xboole_0(X1,esk1_0)), inference(spm,[status(thm)],[c_0_58, c_0_45])).
% 0.13/0.40  cnf(c_0_63, negated_conjecture, (esk3_0!=esk2_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.40  cnf(c_0_64, negated_conjecture, (k2_xboole_0(esk3_0,k2_xboole_0(esk1_0,esk4_0))=k2_xboole_0(esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_59]), c_0_60]), c_0_28]), c_0_60]), c_0_18])).
% 0.13/0.40  cnf(c_0_65, negated_conjecture, (k2_xboole_0(esk1_0,esk4_0)=esk1_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_61]), c_0_28])).
% 0.13/0.40  cnf(c_0_66, negated_conjecture, (k2_xboole_0(esk3_0,esk4_0)!=k2_xboole_0(esk3_0,esk1_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_51]), c_0_18]), c_0_23]), c_0_63])).
% 0.13/0.40  cnf(c_0_67, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_65]), c_0_66]), ['proof']).
% 0.13/0.40  # SZS output end CNFRefutation
% 0.13/0.40  # Proof object total steps             : 68
% 0.13/0.40  # Proof object clause steps            : 43
% 0.13/0.40  # Proof object formula steps           : 25
% 0.13/0.40  # Proof object conjectures             : 30
% 0.13/0.40  # Proof object clause conjectures      : 27
% 0.13/0.40  # Proof object formula conjectures     : 3
% 0.13/0.40  # Proof object initial clauses used    : 16
% 0.13/0.40  # Proof object initial formulas used   : 12
% 0.13/0.40  # Proof object generating inferences   : 25
% 0.13/0.40  # Proof object simplifying inferences  : 22
% 0.13/0.40  # Training examples: 0 positive, 0 negative
% 0.13/0.40  # Parsed axioms                        : 14
% 0.13/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.40  # Initial clauses                      : 20
% 0.13/0.40  # Removed in clause preprocessing      : 1
% 0.13/0.40  # Initial clauses in saturation        : 19
% 0.13/0.40  # Processed clauses                    : 410
% 0.13/0.40  # ...of these trivial                  : 21
% 0.13/0.40  # ...subsumed                          : 190
% 0.13/0.40  # ...remaining for further processing  : 199
% 0.13/0.40  # Other redundant clauses eliminated   : 0
% 0.13/0.40  # Clauses deleted for lack of memory   : 0
% 0.13/0.40  # Backward-subsumed                    : 4
% 0.13/0.40  # Backward-rewritten                   : 51
% 0.13/0.40  # Generated clauses                    : 1889
% 0.13/0.40  # ...of the previous two non-trivial   : 1354
% 0.13/0.40  # Contextual simplify-reflections      : 0
% 0.13/0.40  # Paramodulations                      : 1886
% 0.13/0.40  # Factorizations                       : 0
% 0.13/0.40  # Equation resolutions                 : 3
% 0.13/0.40  # Propositional unsat checks           : 0
% 0.13/0.40  #    Propositional check models        : 0
% 0.13/0.40  #    Propositional check unsatisfiable : 0
% 0.13/0.40  #    Propositional clauses             : 0
% 0.13/0.40  #    Propositional clauses after purity: 0
% 0.13/0.40  #    Propositional unsat core size     : 0
% 0.13/0.40  #    Propositional preprocessing time  : 0.000
% 0.13/0.40  #    Propositional encoding time       : 0.000
% 0.13/0.40  #    Propositional solver time         : 0.000
% 0.13/0.40  #    Success case prop preproc time    : 0.000
% 0.13/0.40  #    Success case prop encoding time   : 0.000
% 0.13/0.40  #    Success case prop solver time     : 0.000
% 0.13/0.40  # Current number of processed clauses  : 144
% 0.13/0.40  #    Positive orientable unit clauses  : 65
% 0.13/0.40  #    Positive unorientable unit clauses: 3
% 0.13/0.40  #    Negative unit clauses             : 2
% 0.13/0.40  #    Non-unit-clauses                  : 74
% 0.13/0.40  # Current number of unprocessed clauses: 902
% 0.13/0.40  # ...number of literals in the above   : 1299
% 0.13/0.40  # Current number of archived formulas  : 0
% 0.13/0.40  # Current number of archived clauses   : 56
% 0.13/0.40  # Clause-clause subsumption calls (NU) : 1261
% 0.13/0.40  # Rec. Clause-clause subsumption calls : 1259
% 0.13/0.40  # Non-unit clause-clause subsumptions  : 190
% 0.13/0.40  # Unit Clause-clause subsumption calls : 42
% 0.13/0.40  # Rewrite failures with RHS unbound    : 0
% 0.13/0.40  # BW rewrite match attempts            : 148
% 0.13/0.40  # BW rewrite match successes           : 92
% 0.13/0.40  # Condensation attempts                : 0
% 0.13/0.40  # Condensation successes               : 0
% 0.13/0.40  # Termbank termtop insertions          : 18260
% 0.13/0.40  
% 0.13/0.40  # -------------------------------------------------
% 0.13/0.40  # User time                : 0.048 s
% 0.13/0.40  # System time              : 0.009 s
% 0.13/0.40  # Total time               : 0.058 s
% 0.13/0.40  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------

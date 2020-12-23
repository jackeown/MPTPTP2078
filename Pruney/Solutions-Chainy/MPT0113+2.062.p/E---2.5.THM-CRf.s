%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:34:43 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   48 (  98 expanded)
%              Number of clauses        :   27 (  44 expanded)
%              Number of leaves         :   10 (  25 expanded)
%              Depth                    :    9
%              Number of atoms          :   82 ( 182 expanded)
%              Number of equality atoms :   22 (  46 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t106_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k4_xboole_0(X2,X3))
     => ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t84_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( ~ r1_xboole_0(X1,X2)
        & r1_xboole_0(X1,X3)
        & r1_xboole_0(X1,k4_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_xboole_1)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(t80_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X1,k4_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_xboole_1)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_tarski(X1,k4_xboole_0(X2,X3))
       => ( r1_tarski(X1,X2)
          & r1_xboole_0(X1,X3) ) ) ),
    inference(assume_negation,[status(cth)],[t106_xboole_1])).

fof(c_0_11,plain,(
    ! [X6,X7] :
      ( ( k4_xboole_0(X6,X7) != k1_xboole_0
        | r1_tarski(X6,X7) )
      & ( ~ r1_tarski(X6,X7)
        | k4_xboole_0(X6,X7) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_12,negated_conjecture,
    ( r1_tarski(esk1_0,k4_xboole_0(esk2_0,esk3_0))
    & ( ~ r1_tarski(esk1_0,esk2_0)
      | ~ r1_xboole_0(esk1_0,esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

fof(c_0_13,plain,(
    ! [X20,X21,X22] :
      ( r1_xboole_0(X20,X21)
      | ~ r1_xboole_0(X20,X22)
      | ~ r1_xboole_0(X20,k4_xboole_0(X21,X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t84_xboole_1])])])).

cnf(c_0_14,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( r1_tarski(esk1_0,k4_xboole_0(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X12] : r1_xboole_0(X12,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

fof(c_0_17,plain,(
    ! [X4,X5] :
      ( ~ r1_xboole_0(X4,X5)
      | r1_xboole_0(X5,X4) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

fof(c_0_18,plain,(
    ! [X13,X14] : r1_xboole_0(k4_xboole_0(X13,X14),X14) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

cnf(c_0_19,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,X3)
    | ~ r1_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_21,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_22,plain,(
    ! [X15,X16,X17] :
      ( ~ r1_xboole_0(X15,X16)
      | r1_xboole_0(X15,k4_xboole_0(X16,X17)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_xboole_1])])).

fof(c_0_23,plain,(
    ! [X8,X9] : k4_xboole_0(X8,k3_xboole_0(X8,X9)) = k4_xboole_0(X8,X9) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

fof(c_0_24,plain,(
    ! [X10,X11] : k4_xboole_0(X10,k4_xboole_0(X10,X11)) = k3_xboole_0(X10,X11) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_25,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( r1_xboole_0(X1,esk1_0)
    | ~ r1_xboole_0(X1,k4_xboole_0(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])])).

cnf(c_0_28,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_32,plain,(
    ! [X18,X19] :
      ( ( ~ r1_xboole_0(X18,X19)
        | k4_xboole_0(X18,X19) = X18 )
      & ( k4_xboole_0(X18,X19) != X18
        | r1_xboole_0(X18,X19) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_33,negated_conjecture,
    ( r1_xboole_0(X1,esk1_0)
    | ~ r1_xboole_0(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( ~ r1_tarski(esk1_0,esk2_0)
    | ~ r1_xboole_0(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_37,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_31])).

cnf(c_0_38,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(X1,esk2_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_26])).

cnf(c_0_40,negated_conjecture,
    ( k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_34,c_0_20])).

cnf(c_0_41,negated_conjecture,
    ( k4_xboole_0(esk1_0,esk2_0) != k1_xboole_0
    | ~ r1_xboole_0(esk1_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_42,negated_conjecture,
    ( r1_xboole_0(esk1_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_37])).

cnf(c_0_43,plain,
    ( k4_xboole_0(X1,X1) = k4_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_38])).

cnf(c_0_44,negated_conjecture,
    ( r1_xboole_0(esk1_0,k4_xboole_0(X1,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_39])).

cnf(c_0_45,negated_conjecture,
    ( k4_xboole_0(esk1_0,esk1_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_38]),c_0_21])])).

cnf(c_0_46,negated_conjecture,
    ( k4_xboole_0(esk1_0,esk2_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_42])])).

cnf(c_0_47,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45]),c_0_46]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:33:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.028 s
% 0.20/0.38  # Presaturation interreduction done
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(t106_xboole_1, conjecture, ![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 0.20/0.38  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.20/0.38  fof(t84_xboole_1, axiom, ![X1, X2, X3]:~(((~(r1_xboole_0(X1,X2))&r1_xboole_0(X1,X3))&r1_xboole_0(X1,k4_xboole_0(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_xboole_1)).
% 0.20/0.38  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.20/0.38  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.20/0.38  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.20/0.38  fof(t80_xboole_1, axiom, ![X1, X2, X3]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X1,k4_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_xboole_1)).
% 0.20/0.38  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 0.20/0.38  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.20/0.38  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.20/0.38  fof(c_0_10, negated_conjecture, ~(![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3)))), inference(assume_negation,[status(cth)],[t106_xboole_1])).
% 0.20/0.38  fof(c_0_11, plain, ![X6, X7]:((k4_xboole_0(X6,X7)!=k1_xboole_0|r1_tarski(X6,X7))&(~r1_tarski(X6,X7)|k4_xboole_0(X6,X7)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.20/0.38  fof(c_0_12, negated_conjecture, (r1_tarski(esk1_0,k4_xboole_0(esk2_0,esk3_0))&(~r1_tarski(esk1_0,esk2_0)|~r1_xboole_0(esk1_0,esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 0.20/0.38  fof(c_0_13, plain, ![X20, X21, X22]:(r1_xboole_0(X20,X21)|~r1_xboole_0(X20,X22)|~r1_xboole_0(X20,k4_xboole_0(X21,X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t84_xboole_1])])])).
% 0.20/0.38  cnf(c_0_14, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.38  cnf(c_0_15, negated_conjecture, (r1_tarski(esk1_0,k4_xboole_0(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  fof(c_0_16, plain, ![X12]:r1_xboole_0(X12,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.20/0.38  fof(c_0_17, plain, ![X4, X5]:(~r1_xboole_0(X4,X5)|r1_xboole_0(X5,X4)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.20/0.38  fof(c_0_18, plain, ![X13, X14]:r1_xboole_0(k4_xboole_0(X13,X14),X14), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.20/0.38  cnf(c_0_19, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X1,X3)|~r1_xboole_0(X1,k4_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  cnf(c_0_20, negated_conjecture, (k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.20/0.38  cnf(c_0_21, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.38  fof(c_0_22, plain, ![X15, X16, X17]:(~r1_xboole_0(X15,X16)|r1_xboole_0(X15,k4_xboole_0(X16,X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_xboole_1])])).
% 0.20/0.38  fof(c_0_23, plain, ![X8, X9]:k4_xboole_0(X8,k3_xboole_0(X8,X9))=k4_xboole_0(X8,X9), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 0.20/0.38  fof(c_0_24, plain, ![X10, X11]:k4_xboole_0(X10,k4_xboole_0(X10,X11))=k3_xboole_0(X10,X11), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.20/0.38  cnf(c_0_25, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.38  cnf(c_0_26, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.38  cnf(c_0_27, negated_conjecture, (r1_xboole_0(X1,esk1_0)|~r1_xboole_0(X1,k4_xboole_0(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])])).
% 0.20/0.38  cnf(c_0_28, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X3))|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.38  cnf(c_0_29, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.38  cnf(c_0_30, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.38  cnf(c_0_31, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.20/0.38  fof(c_0_32, plain, ![X18, X19]:((~r1_xboole_0(X18,X19)|k4_xboole_0(X18,X19)=X18)&(k4_xboole_0(X18,X19)!=X18|r1_xboole_0(X18,X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.20/0.38  cnf(c_0_33, negated_conjecture, (r1_xboole_0(X1,esk1_0)|~r1_xboole_0(X1,esk2_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.20/0.38  cnf(c_0_34, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_29, c_0_30])).
% 0.20/0.38  cnf(c_0_35, negated_conjecture, (~r1_tarski(esk1_0,esk2_0)|~r1_xboole_0(esk1_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  cnf(c_0_36, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.38  cnf(c_0_37, negated_conjecture, (r1_xboole_0(esk3_0,esk1_0)), inference(spm,[status(thm)],[c_0_27, c_0_31])).
% 0.20/0.38  cnf(c_0_38, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.38  cnf(c_0_39, negated_conjecture, (r1_xboole_0(k4_xboole_0(X1,esk2_0),esk1_0)), inference(spm,[status(thm)],[c_0_33, c_0_26])).
% 0.20/0.38  cnf(c_0_40, negated_conjecture, (k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,k1_xboole_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_34, c_0_20])).
% 0.20/0.38  cnf(c_0_41, negated_conjecture, (k4_xboole_0(esk1_0,esk2_0)!=k1_xboole_0|~r1_xboole_0(esk1_0,esk3_0)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.20/0.38  cnf(c_0_42, negated_conjecture, (r1_xboole_0(esk1_0,esk3_0)), inference(spm,[status(thm)],[c_0_25, c_0_37])).
% 0.20/0.38  cnf(c_0_43, plain, (k4_xboole_0(X1,X1)=k4_xboole_0(X1,X2)|~r1_xboole_0(X1,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_34, c_0_38])).
% 0.20/0.38  cnf(c_0_44, negated_conjecture, (r1_xboole_0(esk1_0,k4_xboole_0(X1,esk2_0))), inference(spm,[status(thm)],[c_0_25, c_0_39])).
% 0.20/0.38  cnf(c_0_45, negated_conjecture, (k4_xboole_0(esk1_0,esk1_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_38]), c_0_21])])).
% 0.20/0.38  cnf(c_0_46, negated_conjecture, (k4_xboole_0(esk1_0,esk2_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_42])])).
% 0.20/0.38  cnf(c_0_47, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45]), c_0_46]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 48
% 0.20/0.38  # Proof object clause steps            : 27
% 0.20/0.38  # Proof object formula steps           : 21
% 0.20/0.38  # Proof object conjectures             : 17
% 0.20/0.38  # Proof object clause conjectures      : 14
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 12
% 0.20/0.38  # Proof object initial formulas used   : 10
% 0.20/0.38  # Proof object generating inferences   : 13
% 0.20/0.38  # Proof object simplifying inferences  : 9
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 10
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 13
% 0.20/0.38  # Removed in clause preprocessing      : 1
% 0.20/0.38  # Initial clauses in saturation        : 12
% 0.20/0.38  # Processed clauses                    : 111
% 0.20/0.38  # ...of these trivial                  : 5
% 0.20/0.38  # ...subsumed                          : 37
% 0.20/0.38  # ...remaining for further processing  : 69
% 0.20/0.38  # Other redundant clauses eliminated   : 0
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 6
% 0.20/0.38  # Backward-rewritten                   : 8
% 0.20/0.38  # Generated clauses                    : 212
% 0.20/0.38  # ...of the previous two non-trivial   : 127
% 0.20/0.38  # Contextual simplify-reflections      : 1
% 0.20/0.38  # Paramodulations                      : 212
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 0
% 0.20/0.38  # Propositional unsat checks           : 0
% 0.20/0.38  #    Propositional check models        : 0
% 0.20/0.38  #    Propositional check unsatisfiable : 0
% 0.20/0.38  #    Propositional clauses             : 0
% 0.20/0.38  #    Propositional clauses after purity: 0
% 0.20/0.38  #    Propositional unsat core size     : 0
% 0.20/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 43
% 0.20/0.38  #    Positive orientable unit clauses  : 15
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 5
% 0.20/0.38  #    Non-unit-clauses                  : 23
% 0.20/0.38  # Current number of unprocessed clauses: 29
% 0.20/0.38  # ...number of literals in the above   : 54
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 27
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 203
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 197
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 24
% 0.20/0.38  # Unit Clause-clause subsumption calls : 24
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 8
% 0.20/0.38  # BW rewrite match successes           : 5
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 2267
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.032 s
% 0.20/0.38  # System time              : 0.003 s
% 0.20/0.38  # Total time               : 0.035 s
% 0.20/0.38  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------

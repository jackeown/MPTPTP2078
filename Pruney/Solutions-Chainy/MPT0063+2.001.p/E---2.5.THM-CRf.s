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
% DateTime   : Thu Dec  3 10:32:27 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   38 (  57 expanded)
%              Number of clauses        :   21 (  24 expanded)
%              Number of leaves         :    8 (  14 expanded)
%              Depth                    :   11
%              Number of atoms          :   76 ( 136 expanded)
%              Number of equality atoms :   22 (  28 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(d8_xboole_0,axiom,(
    ! [X1,X2] :
      ( r2_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        & X1 != X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t11_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X1,X2),X3)
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(t56_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( r2_xboole_0(X1,X2)
        & r2_xboole_0(X2,X3) )
     => r2_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_xboole_1)).

fof(antisymmetry_r2_xboole_0,axiom,(
    ! [X1,X2] :
      ( r2_xboole_0(X1,X2)
     => ~ r2_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_xboole_0)).

fof(c_0_8,plain,(
    ! [X16,X17] : k2_xboole_0(X16,k4_xboole_0(X17,X16)) = k2_xboole_0(X16,X17) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

fof(c_0_9,plain,(
    ! [X10,X11] :
      ( ( k4_xboole_0(X10,X11) != k1_xboole_0
        | r1_tarski(X10,X11) )
      & ( ~ r1_tarski(X10,X11)
        | k4_xboole_0(X10,X11) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_10,plain,(
    ! [X15] : k2_xboole_0(X15,k1_xboole_0) = X15 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_11,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,plain,(
    ! [X8,X9] :
      ( ( r1_tarski(X8,X9)
        | ~ r2_xboole_0(X8,X9) )
      & ( X8 != X9
        | ~ r2_xboole_0(X8,X9) )
      & ( ~ r1_tarski(X8,X9)
        | X8 = X9
        | r2_xboole_0(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).

fof(c_0_15,plain,(
    ! [X6,X7] : k2_xboole_0(X6,X7) = k2_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_16,plain,
    ( k2_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,plain,(
    ! [X12,X13,X14] :
      ( ~ r1_tarski(k2_xboole_0(X12,X13),X14)
      | r1_tarski(X12,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

cnf(c_0_19,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( k2_xboole_0(X1,X2) = X1
    | ~ r2_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r2_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

fof(c_0_23,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( r2_xboole_0(X1,X2)
          & r2_xboole_0(X2,X3) )
       => r2_xboole_0(X1,X3) ) ),
    inference(assume_negation,[status(cth)],[t56_xboole_1])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2)
    | ~ r2_xboole_0(X1,X3) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_25,negated_conjecture,
    ( r2_xboole_0(esk1_0,esk2_0)
    & r2_xboole_0(esk2_0,esk3_0)
    & ~ r2_xboole_0(esk1_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_xboole_0(X1,X3)
    | ~ r2_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_17])).

cnf(c_0_27,negated_conjecture,
    ( r2_xboole_0(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_28,plain,(
    ! [X4,X5] :
      ( ~ r2_xboole_0(X4,X5)
      | ~ r2_xboole_0(X5,X4) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_xboole_0])])])).

cnf(c_0_29,plain,
    ( X1 = X2
    | r2_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(esk1_0,X1)
    | ~ r2_xboole_0(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_31,plain,
    ( ~ r2_xboole_0(X1,X2)
    | ~ r2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_32,negated_conjecture,
    ( esk1_0 = X1
    | r2_xboole_0(esk1_0,X1)
    | ~ r2_xboole_0(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_33,negated_conjecture,
    ( r2_xboole_0(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( ~ r2_xboole_0(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,negated_conjecture,
    ( ~ r2_xboole_0(esk2_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_27])).

cnf(c_0_36,negated_conjecture,
    ( esk1_0 = esk3_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])).

cnf(c_0_37,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36]),c_0_33])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:04:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.40  # AutoSched0-Mode selected heuristic G_____X1276__C12_02_nc_F1_AE_CS_SP_RG_S04AN
% 0.19/0.40  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.40  #
% 0.19/0.40  # Preprocessing time       : 0.027 s
% 0.19/0.40  # Presaturation interreduction done
% 0.19/0.40  
% 0.19/0.40  # Proof found!
% 0.19/0.40  # SZS status Theorem
% 0.19/0.40  # SZS output start CNFRefutation
% 0.19/0.40  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.19/0.40  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.19/0.40  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 0.19/0.40  fof(d8_xboole_0, axiom, ![X1, X2]:(r2_xboole_0(X1,X2)<=>(r1_tarski(X1,X2)&X1!=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 0.19/0.40  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.19/0.40  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 0.19/0.40  fof(t56_xboole_1, conjecture, ![X1, X2, X3]:((r2_xboole_0(X1,X2)&r2_xboole_0(X2,X3))=>r2_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_xboole_1)).
% 0.19/0.40  fof(antisymmetry_r2_xboole_0, axiom, ![X1, X2]:(r2_xboole_0(X1,X2)=>~(r2_xboole_0(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', antisymmetry_r2_xboole_0)).
% 0.19/0.40  fof(c_0_8, plain, ![X16, X17]:k2_xboole_0(X16,k4_xboole_0(X17,X16))=k2_xboole_0(X16,X17), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.19/0.40  fof(c_0_9, plain, ![X10, X11]:((k4_xboole_0(X10,X11)!=k1_xboole_0|r1_tarski(X10,X11))&(~r1_tarski(X10,X11)|k4_xboole_0(X10,X11)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.19/0.40  fof(c_0_10, plain, ![X15]:k2_xboole_0(X15,k1_xboole_0)=X15, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.19/0.40  cnf(c_0_11, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.40  cnf(c_0_12, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.40  cnf(c_0_13, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.40  fof(c_0_14, plain, ![X8, X9]:(((r1_tarski(X8,X9)|~r2_xboole_0(X8,X9))&(X8!=X9|~r2_xboole_0(X8,X9)))&(~r1_tarski(X8,X9)|X8=X9|r2_xboole_0(X8,X9))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).
% 0.19/0.40  fof(c_0_15, plain, ![X6, X7]:k2_xboole_0(X6,X7)=k2_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.19/0.40  cnf(c_0_16, plain, (k2_xboole_0(X1,X2)=X1|~r1_tarski(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12]), c_0_13])).
% 0.19/0.40  cnf(c_0_17, plain, (r1_tarski(X1,X2)|~r2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.40  fof(c_0_18, plain, ![X12, X13, X14]:(~r1_tarski(k2_xboole_0(X12,X13),X14)|r1_tarski(X12,X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 0.19/0.40  cnf(c_0_19, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.40  cnf(c_0_20, plain, (k2_xboole_0(X1,X2)=X1|~r2_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.19/0.40  cnf(c_0_21, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.40  cnf(c_0_22, plain, (k2_xboole_0(X1,X2)=X2|~r2_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.19/0.40  fof(c_0_23, negated_conjecture, ~(![X1, X2, X3]:((r2_xboole_0(X1,X2)&r2_xboole_0(X2,X3))=>r2_xboole_0(X1,X3))), inference(assume_negation,[status(cth)],[t56_xboole_1])).
% 0.19/0.40  cnf(c_0_24, plain, (r1_tarski(X1,X2)|~r1_tarski(X3,X2)|~r2_xboole_0(X1,X3)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.19/0.40  fof(c_0_25, negated_conjecture, ((r2_xboole_0(esk1_0,esk2_0)&r2_xboole_0(esk2_0,esk3_0))&~r2_xboole_0(esk1_0,esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).
% 0.19/0.40  cnf(c_0_26, plain, (r1_tarski(X1,X2)|~r2_xboole_0(X1,X3)|~r2_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_24, c_0_17])).
% 0.19/0.40  cnf(c_0_27, negated_conjecture, (r2_xboole_0(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.40  fof(c_0_28, plain, ![X4, X5]:(~r2_xboole_0(X4,X5)|~r2_xboole_0(X5,X4)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_xboole_0])])])).
% 0.19/0.40  cnf(c_0_29, plain, (X1=X2|r2_xboole_0(X1,X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.40  cnf(c_0_30, negated_conjecture, (r1_tarski(esk1_0,X1)|~r2_xboole_0(esk2_0,X1)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.19/0.40  cnf(c_0_31, plain, (~r2_xboole_0(X1,X2)|~r2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.40  cnf(c_0_32, negated_conjecture, (esk1_0=X1|r2_xboole_0(esk1_0,X1)|~r2_xboole_0(esk2_0,X1)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.19/0.40  cnf(c_0_33, negated_conjecture, (r2_xboole_0(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.40  cnf(c_0_34, negated_conjecture, (~r2_xboole_0(esk1_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.40  cnf(c_0_35, negated_conjecture, (~r2_xboole_0(esk2_0,esk1_0)), inference(spm,[status(thm)],[c_0_31, c_0_27])).
% 0.19/0.40  cnf(c_0_36, negated_conjecture, (esk1_0=esk3_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34])).
% 0.19/0.40  cnf(c_0_37, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_36]), c_0_33])]), ['proof']).
% 0.19/0.40  # SZS output end CNFRefutation
% 0.19/0.40  # Proof object total steps             : 38
% 0.19/0.40  # Proof object clause steps            : 21
% 0.19/0.40  # Proof object formula steps           : 17
% 0.19/0.40  # Proof object conjectures             : 11
% 0.19/0.40  # Proof object clause conjectures      : 8
% 0.19/0.40  # Proof object formula conjectures     : 3
% 0.19/0.40  # Proof object initial clauses used    : 11
% 0.19/0.40  # Proof object initial formulas used   : 8
% 0.19/0.40  # Proof object generating inferences   : 9
% 0.19/0.40  # Proof object simplifying inferences  : 5
% 0.19/0.40  # Training examples: 0 positive, 0 negative
% 0.19/0.40  # Parsed axioms                        : 8
% 0.19/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.40  # Initial clauses                      : 13
% 0.19/0.40  # Removed in clause preprocessing      : 0
% 0.19/0.40  # Initial clauses in saturation        : 13
% 0.19/0.40  # Processed clauses                    : 683
% 0.19/0.40  # ...of these trivial                  : 7
% 0.19/0.40  # ...subsumed                          : 512
% 0.19/0.40  # ...remaining for further processing  : 164
% 0.19/0.40  # Other redundant clauses eliminated   : 1
% 0.19/0.40  # Clauses deleted for lack of memory   : 0
% 0.19/0.40  # Backward-subsumed                    : 1
% 0.19/0.40  # Backward-rewritten                   : 40
% 0.19/0.40  # Generated clauses                    : 1144
% 0.19/0.40  # ...of the previous two non-trivial   : 1050
% 0.19/0.40  # Contextual simplify-reflections      : 4
% 0.19/0.40  # Paramodulations                      : 1141
% 0.19/0.40  # Factorizations                       : 0
% 0.19/0.40  # Equation resolutions                 : 2
% 0.19/0.40  # Propositional unsat checks           : 0
% 0.19/0.40  #    Propositional check models        : 0
% 0.19/0.40  #    Propositional check unsatisfiable : 0
% 0.19/0.40  #    Propositional clauses             : 0
% 0.19/0.40  #    Propositional clauses after purity: 0
% 0.19/0.40  #    Propositional unsat core size     : 0
% 0.19/0.40  #    Propositional preprocessing time  : 0.000
% 0.19/0.40  #    Propositional encoding time       : 0.000
% 0.19/0.40  #    Propositional solver time         : 0.000
% 0.19/0.40  #    Success case prop preproc time    : 0.000
% 0.19/0.40  #    Success case prop encoding time   : 0.000
% 0.19/0.40  #    Success case prop solver time     : 0.000
% 0.19/0.40  # Current number of processed clauses  : 108
% 0.19/0.40  #    Positive orientable unit clauses  : 10
% 0.19/0.40  #    Positive unorientable unit clauses: 1
% 0.19/0.40  #    Negative unit clauses             : 4
% 0.19/0.40  #    Non-unit-clauses                  : 93
% 0.19/0.40  # Current number of unprocessed clauses: 359
% 0.19/0.40  # ...number of literals in the above   : 1212
% 0.19/0.40  # Current number of archived formulas  : 0
% 0.19/0.40  # Current number of archived clauses   : 55
% 0.19/0.40  # Clause-clause subsumption calls (NU) : 6845
% 0.19/0.40  # Rec. Clause-clause subsumption calls : 5847
% 0.19/0.40  # Non-unit clause-clause subsumptions  : 443
% 0.19/0.40  # Unit Clause-clause subsumption calls : 10
% 0.19/0.40  # Rewrite failures with RHS unbound    : 0
% 0.19/0.40  # BW rewrite match attempts            : 10
% 0.19/0.40  # BW rewrite match successes           : 10
% 0.19/0.40  # Condensation attempts                : 0
% 0.19/0.40  # Condensation successes               : 0
% 0.19/0.40  # Termbank termtop insertions          : 9277
% 0.19/0.40  
% 0.19/0.40  # -------------------------------------------------
% 0.19/0.40  # User time                : 0.051 s
% 0.19/0.40  # System time              : 0.002 s
% 0.19/0.40  # Total time               : 0.053 s
% 0.19/0.40  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------

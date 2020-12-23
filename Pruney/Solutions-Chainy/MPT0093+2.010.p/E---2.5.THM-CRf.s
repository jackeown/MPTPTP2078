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
% DateTime   : Thu Dec  3 10:33:50 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   47 (  73 expanded)
%              Number of clauses        :   26 (  32 expanded)
%              Number of leaves         :   10 (  19 expanded)
%              Depth                    :   11
%              Number of atoms          :   77 ( 129 expanded)
%              Number of equality atoms :   21 (  41 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t86_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) )
     => r1_tarski(X1,k4_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(t81_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_xboole_0(X1,k4_xboole_0(X2,X3))
     => r1_xboole_0(X2,k4_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_xboole_1)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(t63_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X2,X3) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(c_0_10,plain,(
    ! [X8,X9] : r1_tarski(k4_xboole_0(X8,X9),X8) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_11,plain,(
    ! [X10] : k4_xboole_0(X10,k1_xboole_0) = X10 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_12,plain,(
    ! [X6,X7] :
      ( ( k4_xboole_0(X6,X7) != k1_xboole_0
        | r1_tarski(X6,X7) )
      & ( ~ r1_tarski(X6,X7)
        | k4_xboole_0(X6,X7) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_13,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( r1_tarski(X1,X2)
          & r1_xboole_0(X1,X3) )
       => r1_tarski(X1,k4_xboole_0(X2,X3)) ) ),
    inference(assume_negation,[status(cth)],[t86_xboole_1])).

fof(c_0_16,plain,(
    ! [X11,X12,X13] : k4_xboole_0(k4_xboole_0(X11,X12),X13) = k4_xboole_0(X11,k2_xboole_0(X12,X13)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_17,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

fof(c_0_19,plain,(
    ! [X21,X22] :
      ( ( ~ r1_xboole_0(X21,X22)
        | k4_xboole_0(X21,X22) = X21 )
      & ( k4_xboole_0(X21,X22) != X21
        | r1_xboole_0(X21,X22) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

fof(c_0_20,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0)
    & r1_xboole_0(esk1_0,esk3_0)
    & ~ r1_tarski(esk1_0,k4_xboole_0(esk2_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

fof(c_0_21,plain,(
    ! [X18,X19,X20] :
      ( ~ r1_xboole_0(X18,k4_xboole_0(X19,X20))
      | r1_xboole_0(X19,k4_xboole_0(X18,X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t81_xboole_1])])).

cnf(c_0_22,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

fof(c_0_24,plain,(
    ! [X17] : r1_xboole_0(X17,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( r1_xboole_0(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_27,plain,(
    ! [X14,X15,X16] :
      ( ~ r1_tarski(X14,X15)
      | ~ r1_xboole_0(X15,X16)
      | r1_xboole_0(X14,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).

cnf(c_0_28,plain,
    ( r1_xboole_0(X2,k4_xboole_0(X1,X3))
    | ~ r1_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_30,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( k4_xboole_0(esk1_0,esk3_0) = esk1_0 ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_34,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X1,X3)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])])).

cnf(c_0_35,negated_conjecture,
    ( k4_xboole_0(esk1_0,k2_xboole_0(esk3_0,X1)) = k4_xboole_0(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_31])).

fof(c_0_36,plain,(
    ! [X4,X5] :
      ( ~ r1_xboole_0(X4,X5)
      | r1_xboole_0(X5,X4) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_37,negated_conjecture,
    ( r1_xboole_0(esk1_0,X1)
    | ~ r1_xboole_0(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( r1_xboole_0(X1,k4_xboole_0(esk1_0,k4_xboole_0(X1,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_39,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_40,negated_conjecture,
    ( r1_xboole_0(esk1_0,k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_41,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0)),esk1_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_42,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_13]),c_0_22])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_44,negated_conjecture,
    ( k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_41]),c_0_22]),c_0_42])).

cnf(c_0_45,negated_conjecture,
    ( ~ r1_tarski(esk1_0,k4_xboole_0(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_46,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:52:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.21/0.52  # AutoSched0-Mode selected heuristic G_____Y1346__C12_02_nc_F1_AE_CS_SP_S2S
% 0.21/0.52  # and selection function SelectNewComplexAHP.
% 0.21/0.52  #
% 0.21/0.52  # Preprocessing time       : 0.028 s
% 0.21/0.52  # Presaturation interreduction done
% 0.21/0.52  
% 0.21/0.52  # Proof found!
% 0.21/0.52  # SZS status Theorem
% 0.21/0.52  # SZS output start CNFRefutation
% 0.21/0.52  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.21/0.52  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.21/0.52  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.21/0.52  fof(t86_xboole_1, conjecture, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X1,X3))=>r1_tarski(X1,k4_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_xboole_1)).
% 0.21/0.52  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.21/0.52  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.21/0.52  fof(t81_xboole_1, axiom, ![X1, X2, X3]:(r1_xboole_0(X1,k4_xboole_0(X2,X3))=>r1_xboole_0(X2,k4_xboole_0(X1,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_xboole_1)).
% 0.21/0.52  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.21/0.52  fof(t63_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X2,X3))=>r1_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 0.21/0.52  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.21/0.52  fof(c_0_10, plain, ![X8, X9]:r1_tarski(k4_xboole_0(X8,X9),X8), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.21/0.52  fof(c_0_11, plain, ![X10]:k4_xboole_0(X10,k1_xboole_0)=X10, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.21/0.52  fof(c_0_12, plain, ![X6, X7]:((k4_xboole_0(X6,X7)!=k1_xboole_0|r1_tarski(X6,X7))&(~r1_tarski(X6,X7)|k4_xboole_0(X6,X7)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.21/0.52  cnf(c_0_13, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.52  cnf(c_0_14, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.52  fof(c_0_15, negated_conjecture, ~(![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X1,X3))=>r1_tarski(X1,k4_xboole_0(X2,X3)))), inference(assume_negation,[status(cth)],[t86_xboole_1])).
% 0.21/0.52  fof(c_0_16, plain, ![X11, X12, X13]:k4_xboole_0(k4_xboole_0(X11,X12),X13)=k4_xboole_0(X11,k2_xboole_0(X12,X13)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.21/0.52  cnf(c_0_17, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.52  cnf(c_0_18, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.21/0.52  fof(c_0_19, plain, ![X21, X22]:((~r1_xboole_0(X21,X22)|k4_xboole_0(X21,X22)=X21)&(k4_xboole_0(X21,X22)!=X21|r1_xboole_0(X21,X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.21/0.52  fof(c_0_20, negated_conjecture, ((r1_tarski(esk1_0,esk2_0)&r1_xboole_0(esk1_0,esk3_0))&~r1_tarski(esk1_0,k4_xboole_0(esk2_0,esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.21/0.52  fof(c_0_21, plain, ![X18, X19, X20]:(~r1_xboole_0(X18,k4_xboole_0(X19,X20))|r1_xboole_0(X19,k4_xboole_0(X18,X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t81_xboole_1])])).
% 0.21/0.52  cnf(c_0_22, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.52  cnf(c_0_23, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.21/0.52  fof(c_0_24, plain, ![X17]:r1_xboole_0(X17,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.21/0.52  cnf(c_0_25, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.52  cnf(c_0_26, negated_conjecture, (r1_xboole_0(esk1_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.52  fof(c_0_27, plain, ![X14, X15, X16]:(~r1_tarski(X14,X15)|~r1_xboole_0(X15,X16)|r1_xboole_0(X14,X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).
% 0.21/0.52  cnf(c_0_28, plain, (r1_xboole_0(X2,k4_xboole_0(X1,X3))|~r1_xboole_0(X1,k4_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.52  cnf(c_0_29, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.21/0.52  cnf(c_0_30, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.21/0.52  cnf(c_0_31, negated_conjecture, (k4_xboole_0(esk1_0,esk3_0)=esk1_0), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.21/0.52  cnf(c_0_32, plain, (r1_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.52  cnf(c_0_33, negated_conjecture, (r1_tarski(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.52  cnf(c_0_34, plain, (r1_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X1,X3))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30])])).
% 0.21/0.52  cnf(c_0_35, negated_conjecture, (k4_xboole_0(esk1_0,k2_xboole_0(esk3_0,X1))=k4_xboole_0(esk1_0,X1)), inference(spm,[status(thm)],[c_0_22, c_0_31])).
% 0.21/0.52  fof(c_0_36, plain, ![X4, X5]:(~r1_xboole_0(X4,X5)|r1_xboole_0(X5,X4)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.21/0.52  cnf(c_0_37, negated_conjecture, (r1_xboole_0(esk1_0,X1)|~r1_xboole_0(esk2_0,X1)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.21/0.52  cnf(c_0_38, negated_conjecture, (r1_xboole_0(X1,k4_xboole_0(esk1_0,k4_xboole_0(X1,esk3_0)))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.21/0.52  cnf(c_0_39, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.21/0.52  cnf(c_0_40, negated_conjecture, (r1_xboole_0(esk1_0,k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0)))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.21/0.52  cnf(c_0_41, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0)),esk1_0)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.21/0.52  cnf(c_0_42, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X1))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_13]), c_0_22])).
% 0.21/0.52  cnf(c_0_43, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.52  cnf(c_0_44, negated_conjecture, (k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_41]), c_0_22]), c_0_42])).
% 0.21/0.52  cnf(c_0_45, negated_conjecture, (~r1_tarski(esk1_0,k4_xboole_0(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.52  cnf(c_0_46, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45]), ['proof']).
% 0.21/0.52  # SZS output end CNFRefutation
% 0.21/0.52  # Proof object total steps             : 47
% 0.21/0.52  # Proof object clause steps            : 26
% 0.21/0.52  # Proof object formula steps           : 21
% 0.21/0.52  # Proof object conjectures             : 14
% 0.21/0.52  # Proof object clause conjectures      : 11
% 0.21/0.52  # Proof object formula conjectures     : 3
% 0.21/0.52  # Proof object initial clauses used    : 13
% 0.21/0.52  # Proof object initial formulas used   : 10
% 0.21/0.52  # Proof object generating inferences   : 13
% 0.21/0.52  # Proof object simplifying inferences  : 6
% 0.21/0.52  # Training examples: 0 positive, 0 negative
% 0.21/0.52  # Parsed axioms                        : 10
% 0.21/0.52  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.52  # Initial clauses                      : 14
% 0.21/0.52  # Removed in clause preprocessing      : 0
% 0.21/0.52  # Initial clauses in saturation        : 14
% 0.21/0.52  # Processed clauses                    : 1199
% 0.21/0.52  # ...of these trivial                  : 174
% 0.21/0.52  # ...subsumed                          : 71
% 0.21/0.52  # ...remaining for further processing  : 954
% 0.21/0.52  # Other redundant clauses eliminated   : 0
% 0.21/0.52  # Clauses deleted for lack of memory   : 0
% 0.21/0.52  # Backward-subsumed                    : 2
% 0.21/0.52  # Backward-rewritten                   : 66
% 0.21/0.52  # Generated clauses                    : 28106
% 0.21/0.52  # ...of the previous two non-trivial   : 12098
% 0.21/0.52  # Contextual simplify-reflections      : 0
% 0.21/0.52  # Paramodulations                      : 28101
% 0.21/0.52  # Factorizations                       : 0
% 0.21/0.52  # Equation resolutions                 : 5
% 0.21/0.52  # Propositional unsat checks           : 0
% 0.21/0.52  #    Propositional check models        : 0
% 0.21/0.52  #    Propositional check unsatisfiable : 0
% 0.21/0.52  #    Propositional clauses             : 0
% 0.21/0.52  #    Propositional clauses after purity: 0
% 0.21/0.52  #    Propositional unsat core size     : 0
% 0.21/0.52  #    Propositional preprocessing time  : 0.000
% 0.21/0.52  #    Propositional encoding time       : 0.000
% 0.21/0.52  #    Propositional solver time         : 0.000
% 0.21/0.52  #    Success case prop preproc time    : 0.000
% 0.21/0.52  #    Success case prop encoding time   : 0.000
% 0.21/0.52  #    Success case prop solver time     : 0.000
% 0.21/0.52  # Current number of processed clauses  : 872
% 0.21/0.52  #    Positive orientable unit clauses  : 790
% 0.21/0.52  #    Positive unorientable unit clauses: 0
% 0.21/0.52  #    Negative unit clauses             : 1
% 0.21/0.52  #    Non-unit-clauses                  : 81
% 0.21/0.52  # Current number of unprocessed clauses: 10920
% 0.21/0.52  # ...number of literals in the above   : 12162
% 0.21/0.52  # Current number of archived formulas  : 0
% 0.21/0.52  # Current number of archived clauses   : 82
% 0.21/0.52  # Clause-clause subsumption calls (NU) : 580
% 0.21/0.52  # Rec. Clause-clause subsumption calls : 568
% 0.21/0.52  # Non-unit clause-clause subsumptions  : 73
% 0.21/0.52  # Unit Clause-clause subsumption calls : 10
% 0.21/0.52  # Rewrite failures with RHS unbound    : 0
% 0.21/0.52  # BW rewrite match attempts            : 1987
% 0.21/0.52  # BW rewrite match successes           : 61
% 0.21/0.52  # Condensation attempts                : 0
% 0.21/0.52  # Condensation successes               : 0
% 0.21/0.52  # Termbank termtop insertions          : 263350
% 0.21/0.53  
% 0.21/0.53  # -------------------------------------------------
% 0.21/0.53  # User time                : 0.173 s
% 0.21/0.53  # System time              : 0.011 s
% 0.21/0.53  # Total time               : 0.184 s
% 0.21/0.53  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------

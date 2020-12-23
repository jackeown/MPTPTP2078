%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:33:40 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 267 expanded)
%              Number of clauses        :   35 ( 123 expanded)
%              Number of leaves         :   10 (  71 expanded)
%              Depth                    :   12
%              Number of atoms          :   68 ( 324 expanded)
%              Number of equality atoms :   42 ( 224 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t81_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_xboole_0(X1,k4_xboole_0(X2,X3))
     => r1_xboole_0(X2,k4_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(t49_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(t50_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_xboole_1)).

fof(c_0_10,plain,(
    ! [X8] : k3_xboole_0(X8,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_11,plain,(
    ! [X12,X13] : k4_xboole_0(X12,k4_xboole_0(X12,X13)) = k3_xboole_0(X12,X13) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_xboole_0(X1,k4_xboole_0(X2,X3))
       => r1_xboole_0(X2,k4_xboole_0(X1,X3)) ) ),
    inference(assume_negation,[status(cth)],[t81_xboole_1])).

cnf(c_0_13,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,plain,(
    ! [X9] : k4_xboole_0(X9,k1_xboole_0) = X9 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_16,plain,(
    ! [X4,X5] :
      ( ( ~ r1_xboole_0(X4,X5)
        | k3_xboole_0(X4,X5) = k1_xboole_0 )
      & ( k3_xboole_0(X4,X5) != k1_xboole_0
        | r1_xboole_0(X4,X5) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_17,plain,(
    ! [X6,X7] :
      ( ~ r1_xboole_0(X6,X7)
      | r1_xboole_0(X7,X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

fof(c_0_18,negated_conjecture,
    ( r1_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0))
    & ~ r1_xboole_0(esk2_0,k4_xboole_0(esk1_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

fof(c_0_19,plain,(
    ! [X20,X21] : r1_xboole_0(k4_xboole_0(X20,X21),X21) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

cnf(c_0_20,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_21,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_22,plain,(
    ! [X10,X11] : k4_xboole_0(X10,k3_xboole_0(X10,X11)) = k4_xboole_0(X10,X11) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

cnf(c_0_23,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( r1_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_26,plain,(
    ! [X14,X15,X16] : k3_xboole_0(X14,k4_xboole_0(X15,X16)) = k4_xboole_0(k3_xboole_0(X14,X15),X16) ),
    inference(variable_rename,[status(thm)],[t49_xboole_1])).

cnf(c_0_27,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_29,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_23,c_0_14])).

cnf(c_0_31,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk2_0,esk3_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_32,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

fof(c_0_34,plain,(
    ! [X17,X18,X19] : k3_xboole_0(X17,k4_xboole_0(X18,X19)) = k4_xboole_0(k3_xboole_0(X17,X18),k3_xboole_0(X17,X19)) ),
    inference(variable_rename,[status(thm)],[t50_xboole_1])).

cnf(c_0_35,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_29,c_0_14])).

cnf(c_0_36,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),esk1_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_37,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_14]),c_0_14])).

cnf(c_0_38,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_30,c_0_33])).

cnf(c_0_39,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_40,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_27])).

cnf(c_0_41,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),esk1_0) = k4_xboole_0(esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_21])).

cnf(c_0_42,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_21]),c_0_38])).

cnf(c_0_43,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_14]),c_0_14]),c_0_14])).

cnf(c_0_44,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_30,c_0_40])).

cnf(c_0_45,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(esk1_0,X1))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_41]),c_0_28]),c_0_42])).

cnf(c_0_46,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X3))))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_43,c_0_37])).

cnf(c_0_47,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_44]),c_0_21])).

cnf(c_0_48,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(esk1_0,X1)) = k4_xboole_0(esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_45]),c_0_21])).

cnf(c_0_49,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X3)))) = k4_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_46]),c_0_35])).

cnf(c_0_50,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_47,c_0_47])).

cnf(c_0_51,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk1_0,X1),k4_xboole_0(esk2_0,esk3_0)) = k4_xboole_0(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_52,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2)) = k4_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_28]),c_0_21])).

cnf(c_0_53,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk1_0,esk3_0),esk2_0) = k4_xboole_0(esk1_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_54,negated_conjecture,
    ( ~ r1_xboole_0(esk2_0,k4_xboole_0(esk1_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_55,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_53]),c_0_54]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:08:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.36  # AutoSched0-Mode selected heuristic G_____Y1346__C12_02_nc_F1_AE_CS_SP_S2S
% 0.12/0.36  # and selection function SelectNewComplexAHP.
% 0.12/0.36  #
% 0.12/0.36  # Preprocessing time       : 0.013 s
% 0.12/0.36  # Presaturation interreduction done
% 0.12/0.36  
% 0.12/0.36  # Proof found!
% 0.12/0.36  # SZS status Theorem
% 0.12/0.36  # SZS output start CNFRefutation
% 0.12/0.36  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 0.12/0.36  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.12/0.36  fof(t81_xboole_1, conjecture, ![X1, X2, X3]:(r1_xboole_0(X1,k4_xboole_0(X2,X3))=>r1_xboole_0(X2,k4_xboole_0(X1,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_xboole_1)).
% 0.12/0.36  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.12/0.36  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.12/0.36  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.12/0.36  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.12/0.36  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 0.12/0.36  fof(t49_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 0.12/0.36  fof(t50_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_xboole_1)).
% 0.12/0.36  fof(c_0_10, plain, ![X8]:k3_xboole_0(X8,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.12/0.36  fof(c_0_11, plain, ![X12, X13]:k4_xboole_0(X12,k4_xboole_0(X12,X13))=k3_xboole_0(X12,X13), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.12/0.36  fof(c_0_12, negated_conjecture, ~(![X1, X2, X3]:(r1_xboole_0(X1,k4_xboole_0(X2,X3))=>r1_xboole_0(X2,k4_xboole_0(X1,X3)))), inference(assume_negation,[status(cth)],[t81_xboole_1])).
% 0.12/0.36  cnf(c_0_13, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.36  cnf(c_0_14, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.36  fof(c_0_15, plain, ![X9]:k4_xboole_0(X9,k1_xboole_0)=X9, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.12/0.36  fof(c_0_16, plain, ![X4, X5]:((~r1_xboole_0(X4,X5)|k3_xboole_0(X4,X5)=k1_xboole_0)&(k3_xboole_0(X4,X5)!=k1_xboole_0|r1_xboole_0(X4,X5))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.12/0.36  fof(c_0_17, plain, ![X6, X7]:(~r1_xboole_0(X6,X7)|r1_xboole_0(X7,X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.12/0.36  fof(c_0_18, negated_conjecture, (r1_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0))&~r1_xboole_0(esk2_0,k4_xboole_0(esk1_0,esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.12/0.36  fof(c_0_19, plain, ![X20, X21]:r1_xboole_0(k4_xboole_0(X20,X21),X21), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.12/0.36  cnf(c_0_20, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_13, c_0_14])).
% 0.12/0.36  cnf(c_0_21, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.36  fof(c_0_22, plain, ![X10, X11]:k4_xboole_0(X10,k3_xboole_0(X10,X11))=k4_xboole_0(X10,X11), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 0.12/0.36  cnf(c_0_23, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.36  cnf(c_0_24, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.36  cnf(c_0_25, negated_conjecture, (r1_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.36  fof(c_0_26, plain, ![X14, X15, X16]:k3_xboole_0(X14,k4_xboole_0(X15,X16))=k4_xboole_0(k3_xboole_0(X14,X15),X16), inference(variable_rename,[status(thm)],[t49_xboole_1])).
% 0.12/0.36  cnf(c_0_27, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.36  cnf(c_0_28, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 0.12/0.36  cnf(c_0_29, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.36  cnf(c_0_30, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_23, c_0_14])).
% 0.12/0.36  cnf(c_0_31, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk2_0,esk3_0),esk1_0)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.12/0.36  cnf(c_0_32, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.12/0.36  cnf(c_0_33, plain, (r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.12/0.36  fof(c_0_34, plain, ![X17, X18, X19]:k3_xboole_0(X17,k4_xboole_0(X18,X19))=k4_xboole_0(k3_xboole_0(X17,X18),k3_xboole_0(X17,X19)), inference(variable_rename,[status(thm)],[t50_xboole_1])).
% 0.12/0.36  cnf(c_0_35, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_29, c_0_14])).
% 0.12/0.36  cnf(c_0_36, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),esk1_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.12/0.36  cnf(c_0_37, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))=k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_14]), c_0_14])).
% 0.12/0.36  cnf(c_0_38, plain, (k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_30, c_0_33])).
% 0.12/0.36  cnf(c_0_39, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.12/0.36  cnf(c_0_40, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_24, c_0_27])).
% 0.12/0.36  cnf(c_0_41, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),esk1_0)=k4_xboole_0(esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_21])).
% 0.12/0.36  cnf(c_0_42, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_21]), c_0_38])).
% 0.12/0.36  cnf(c_0_43, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))=k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_14]), c_0_14]), c_0_14])).
% 0.12/0.36  cnf(c_0_44, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_30, c_0_40])).
% 0.12/0.36  cnf(c_0_45, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(esk1_0,X1)))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_41]), c_0_28]), c_0_42])).
% 0.12/0.36  cnf(c_0_46, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X3)))))=k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_43, c_0_37])).
% 0.12/0.36  cnf(c_0_47, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X1))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_44]), c_0_21])).
% 0.12/0.36  cnf(c_0_48, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(esk1_0,X1))=k4_xboole_0(esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_45]), c_0_21])).
% 0.12/0.36  cnf(c_0_49, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X3))))=k4_xboole_0(X1,k4_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_46]), c_0_35])).
% 0.12/0.36  cnf(c_0_50, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_47, c_0_47])).
% 0.12/0.36  cnf(c_0_51, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk1_0,X1),k4_xboole_0(esk2_0,esk3_0))=k4_xboole_0(esk1_0,X1)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.12/0.36  cnf(c_0_52, plain, (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2))=k4_xboole_0(k4_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_28]), c_0_21])).
% 0.12/0.36  cnf(c_0_53, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk1_0,esk3_0),esk2_0)=k4_xboole_0(esk1_0,esk3_0)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.12/0.36  cnf(c_0_54, negated_conjecture, (~r1_xboole_0(esk2_0,k4_xboole_0(esk1_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.36  cnf(c_0_55, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_53]), c_0_54]), ['proof']).
% 0.12/0.36  # SZS output end CNFRefutation
% 0.12/0.36  # Proof object total steps             : 56
% 0.12/0.36  # Proof object clause steps            : 35
% 0.12/0.36  # Proof object formula steps           : 21
% 0.12/0.36  # Proof object conjectures             : 13
% 0.12/0.36  # Proof object clause conjectures      : 10
% 0.12/0.36  # Proof object formula conjectures     : 3
% 0.12/0.36  # Proof object initial clauses used    : 11
% 0.12/0.36  # Proof object initial formulas used   : 10
% 0.12/0.36  # Proof object generating inferences   : 17
% 0.12/0.36  # Proof object simplifying inferences  : 21
% 0.12/0.36  # Training examples: 0 positive, 0 negative
% 0.12/0.36  # Parsed axioms                        : 10
% 0.12/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.36  # Initial clauses                      : 12
% 0.12/0.36  # Removed in clause preprocessing      : 1
% 0.12/0.36  # Initial clauses in saturation        : 11
% 0.12/0.36  # Processed clauses                    : 131
% 0.12/0.36  # ...of these trivial                  : 34
% 0.12/0.36  # ...subsumed                          : 19
% 0.12/0.36  # ...remaining for further processing  : 78
% 0.12/0.36  # Other redundant clauses eliminated   : 0
% 0.12/0.36  # Clauses deleted for lack of memory   : 0
% 0.12/0.36  # Backward-subsumed                    : 0
% 0.12/0.36  # Backward-rewritten                   : 7
% 0.12/0.36  # Generated clauses                    : 1762
% 0.12/0.36  # ...of the previous two non-trivial   : 624
% 0.12/0.36  # Contextual simplify-reflections      : 0
% 0.12/0.36  # Paramodulations                      : 1761
% 0.12/0.36  # Factorizations                       : 0
% 0.12/0.36  # Equation resolutions                 : 1
% 0.12/0.36  # Propositional unsat checks           : 0
% 0.12/0.36  #    Propositional check models        : 0
% 0.12/0.36  #    Propositional check unsatisfiable : 0
% 0.12/0.36  #    Propositional clauses             : 0
% 0.12/0.36  #    Propositional clauses after purity: 0
% 0.12/0.36  #    Propositional unsat core size     : 0
% 0.12/0.36  #    Propositional preprocessing time  : 0.000
% 0.12/0.36  #    Propositional encoding time       : 0.000
% 0.12/0.36  #    Propositional solver time         : 0.000
% 0.12/0.36  #    Success case prop preproc time    : 0.000
% 0.12/0.36  #    Success case prop encoding time   : 0.000
% 0.12/0.36  #    Success case prop solver time     : 0.000
% 0.12/0.36  # Current number of processed clauses  : 60
% 0.12/0.36  #    Positive orientable unit clauses  : 53
% 0.12/0.36  #    Positive unorientable unit clauses: 0
% 0.12/0.36  #    Negative unit clauses             : 1
% 0.12/0.36  #    Non-unit-clauses                  : 6
% 0.12/0.36  # Current number of unprocessed clauses: 497
% 0.12/0.36  # ...number of literals in the above   : 535
% 0.12/0.36  # Current number of archived formulas  : 0
% 0.12/0.36  # Current number of archived clauses   : 19
% 0.12/0.36  # Clause-clause subsumption calls (NU) : 26
% 0.12/0.36  # Rec. Clause-clause subsumption calls : 26
% 0.12/0.36  # Non-unit clause-clause subsumptions  : 19
% 0.12/0.36  # Unit Clause-clause subsumption calls : 2
% 0.12/0.36  # Rewrite failures with RHS unbound    : 0
% 0.12/0.36  # BW rewrite match attempts            : 114
% 0.12/0.36  # BW rewrite match successes           : 8
% 0.12/0.36  # Condensation attempts                : 0
% 0.12/0.36  # Condensation successes               : 0
% 0.12/0.36  # Termbank termtop insertions          : 17482
% 0.12/0.36  
% 0.12/0.36  # -------------------------------------------------
% 0.12/0.36  # User time                : 0.017 s
% 0.12/0.36  # System time              : 0.006 s
% 0.12/0.36  # Total time               : 0.023 s
% 0.12/0.36  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------

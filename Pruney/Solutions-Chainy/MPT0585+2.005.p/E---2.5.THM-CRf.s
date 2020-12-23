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
% DateTime   : Thu Dec  3 10:51:59 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 149 expanded)
%              Number of clauses        :   28 (  66 expanded)
%              Number of leaves         :    9 (  38 expanded)
%              Depth                    :    9
%              Number of atoms          :   71 ( 217 expanded)
%              Number of equality atoms :   40 ( 138 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t90_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k1_relat_1(k7_relat_1(X2,X1)) = k3_xboole_0(k1_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(t189_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k7_relat_1(X1,k1_relat_1(X2)) = k7_relat_1(X1,k1_relat_1(k7_relat_1(X2,k1_relat_1(X1)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t189_relat_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t108_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k7_relat_1(X3,k3_xboole_0(X1,X2)) = k3_xboole_0(k7_relat_1(X3,X1),k7_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_relat_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t88_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k7_relat_1(X2,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

fof(t98_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,k1_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

fof(c_0_9,plain,(
    ! [X10,X11] : k1_setfam_1(k2_tarski(X10,X11)) = k3_xboole_0(X10,X11) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_10,plain,(
    ! [X8,X9] : k1_enumset1(X8,X8,X9) = k2_tarski(X8,X9) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_11,plain,(
    ! [X17,X18] :
      ( ~ v1_relat_1(X18)
      | k1_relat_1(k7_relat_1(X18,X17)) = k3_xboole_0(k1_relat_1(X18),X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).

cnf(c_0_12,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => k7_relat_1(X1,k1_relat_1(X2)) = k7_relat_1(X1,k1_relat_1(k7_relat_1(X2,k1_relat_1(X1)))) ) ) ),
    inference(assume_negation,[status(cth)],[t189_relat_1])).

cnf(c_0_15,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k3_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_12,c_0_13])).

fof(c_0_17,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_relat_1(esk2_0)
    & k7_relat_1(esk1_0,k1_relat_1(esk2_0)) != k7_relat_1(esk1_0,k1_relat_1(k7_relat_1(esk2_0,k1_relat_1(esk1_0)))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_18,plain,(
    ! [X6,X7] : k2_tarski(X6,X7) = k2_tarski(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_19,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_22,plain,(
    ! [X12,X13,X14] :
      ( ~ v1_relat_1(X14)
      | k7_relat_1(X14,k3_xboole_0(X12,X13)) = k3_xboole_0(k7_relat_1(X14,X12),k7_relat_1(X14,X13)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t108_relat_1])])).

fof(c_0_23,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(X4,X5)
      | k3_xboole_0(X4,X5) = X4 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_24,plain,(
    ! [X15,X16] :
      ( ~ v1_relat_1(X16)
      | r1_tarski(k7_relat_1(X16,X15),X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_relat_1])])).

cnf(c_0_25,negated_conjecture,
    ( k1_setfam_1(k1_enumset1(k1_relat_1(esk2_0),k1_relat_1(esk2_0),X1)) = k1_relat_1(k7_relat_1(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,plain,
    ( k1_enumset1(X1,X1,X2) = k1_enumset1(X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_13]),c_0_13])).

cnf(c_0_27,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,plain,
    ( k7_relat_1(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(k7_relat_1(X1,X2),k7_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_29,plain,(
    ! [X19] :
      ( ~ v1_relat_1(X19)
      | k7_relat_1(X19,k1_relat_1(X19)) = X19 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_relat_1])])).

cnf(c_0_30,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( r1_tarski(k7_relat_1(X1,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( k1_setfam_1(k1_enumset1(X1,X1,k1_relat_1(esk2_0))) = k1_relat_1(k7_relat_1(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( k1_setfam_1(k1_enumset1(k1_relat_1(esk1_0),k1_relat_1(esk1_0),X1)) = k1_relat_1(k7_relat_1(esk1_0,X1)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_27])).

cnf(c_0_34,plain,
    ( k7_relat_1(X1,k1_setfam_1(k1_enumset1(X2,X2,X3))) = k1_setfam_1(k1_enumset1(k7_relat_1(X1,X2),k7_relat_1(X1,X2),k7_relat_1(X1,X3)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_16]),c_0_16])).

cnf(c_0_35,plain,
    ( k7_relat_1(X1,k1_relat_1(X1)) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_30,c_0_16])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(k7_relat_1(esk1_0,X1),esk1_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_27])).

cnf(c_0_38,negated_conjecture,
    ( k7_relat_1(esk1_0,k1_relat_1(esk2_0)) != k7_relat_1(esk1_0,k1_relat_1(k7_relat_1(esk2_0,k1_relat_1(esk1_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_39,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk2_0,k1_relat_1(esk1_0))) = k1_relat_1(k7_relat_1(esk1_0,k1_relat_1(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( k1_setfam_1(k1_enumset1(k7_relat_1(esk1_0,X1),k7_relat_1(esk1_0,X1),k7_relat_1(esk1_0,X2))) = k7_relat_1(esk1_0,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_27])).

cnf(c_0_41,negated_conjecture,
    ( k7_relat_1(esk1_0,k1_relat_1(esk1_0)) = esk1_0 ),
    inference(spm,[status(thm)],[c_0_35,c_0_27])).

cnf(c_0_42,negated_conjecture,
    ( k1_setfam_1(k1_enumset1(esk1_0,esk1_0,k7_relat_1(esk1_0,X1))) = k7_relat_1(esk1_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_26])).

cnf(c_0_43,negated_conjecture,
    ( k1_setfam_1(k1_enumset1(X1,X1,k1_relat_1(esk1_0))) = k1_relat_1(k7_relat_1(esk1_0,X1)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_26])).

cnf(c_0_44,negated_conjecture,
    ( k7_relat_1(esk1_0,k1_relat_1(k7_relat_1(esk1_0,k1_relat_1(esk2_0)))) != k7_relat_1(esk1_0,k1_relat_1(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_45,negated_conjecture,
    ( k7_relat_1(esk1_0,k1_relat_1(k7_relat_1(esk1_0,X1))) = k7_relat_1(esk1_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_26]),c_0_42]),c_0_43])).

cnf(c_0_46,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_45])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:54:40 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S089A
% 0.12/0.36  # and selection function SelectCQPrecW.
% 0.12/0.36  #
% 0.12/0.36  # Preprocessing time       : 0.026 s
% 0.12/0.36  # Presaturation interreduction done
% 0.12/0.36  
% 0.12/0.36  # Proof found!
% 0.12/0.36  # SZS status Theorem
% 0.12/0.36  # SZS output start CNFRefutation
% 0.12/0.36  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.12/0.36  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.12/0.36  fof(t90_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k1_relat_1(k7_relat_1(X2,X1))=k3_xboole_0(k1_relat_1(X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 0.12/0.36  fof(t189_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k7_relat_1(X1,k1_relat_1(X2))=k7_relat_1(X1,k1_relat_1(k7_relat_1(X2,k1_relat_1(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t189_relat_1)).
% 0.12/0.36  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.12/0.36  fof(t108_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k7_relat_1(X3,k3_xboole_0(X1,X2))=k3_xboole_0(k7_relat_1(X3,X1),k7_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_relat_1)).
% 0.12/0.36  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.12/0.36  fof(t88_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k7_relat_1(X2,X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 0.12/0.36  fof(t98_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k7_relat_1(X1,k1_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 0.12/0.36  fof(c_0_9, plain, ![X10, X11]:k1_setfam_1(k2_tarski(X10,X11))=k3_xboole_0(X10,X11), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.12/0.36  fof(c_0_10, plain, ![X8, X9]:k1_enumset1(X8,X8,X9)=k2_tarski(X8,X9), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.12/0.36  fof(c_0_11, plain, ![X17, X18]:(~v1_relat_1(X18)|k1_relat_1(k7_relat_1(X18,X17))=k3_xboole_0(k1_relat_1(X18),X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).
% 0.12/0.36  cnf(c_0_12, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.36  cnf(c_0_13, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.36  fof(c_0_14, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k7_relat_1(X1,k1_relat_1(X2))=k7_relat_1(X1,k1_relat_1(k7_relat_1(X2,k1_relat_1(X1))))))), inference(assume_negation,[status(cth)],[t189_relat_1])).
% 0.12/0.36  cnf(c_0_15, plain, (k1_relat_1(k7_relat_1(X1,X2))=k3_xboole_0(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.36  cnf(c_0_16, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_12, c_0_13])).
% 0.12/0.36  fof(c_0_17, negated_conjecture, (v1_relat_1(esk1_0)&(v1_relat_1(esk2_0)&k7_relat_1(esk1_0,k1_relat_1(esk2_0))!=k7_relat_1(esk1_0,k1_relat_1(k7_relat_1(esk2_0,k1_relat_1(esk1_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.12/0.36  fof(c_0_18, plain, ![X6, X7]:k2_tarski(X6,X7)=k2_tarski(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.12/0.36  cnf(c_0_19, plain, (k1_relat_1(k7_relat_1(X1,X2))=k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 0.12/0.36  cnf(c_0_20, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.36  cnf(c_0_21, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.36  fof(c_0_22, plain, ![X12, X13, X14]:(~v1_relat_1(X14)|k7_relat_1(X14,k3_xboole_0(X12,X13))=k3_xboole_0(k7_relat_1(X14,X12),k7_relat_1(X14,X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t108_relat_1])])).
% 0.12/0.36  fof(c_0_23, plain, ![X4, X5]:(~r1_tarski(X4,X5)|k3_xboole_0(X4,X5)=X4), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.12/0.36  fof(c_0_24, plain, ![X15, X16]:(~v1_relat_1(X16)|r1_tarski(k7_relat_1(X16,X15),X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_relat_1])])).
% 0.12/0.36  cnf(c_0_25, negated_conjecture, (k1_setfam_1(k1_enumset1(k1_relat_1(esk2_0),k1_relat_1(esk2_0),X1))=k1_relat_1(k7_relat_1(esk2_0,X1))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.12/0.36  cnf(c_0_26, plain, (k1_enumset1(X1,X1,X2)=k1_enumset1(X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_13]), c_0_13])).
% 0.12/0.36  cnf(c_0_27, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.36  cnf(c_0_28, plain, (k7_relat_1(X1,k3_xboole_0(X2,X3))=k3_xboole_0(k7_relat_1(X1,X2),k7_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.36  fof(c_0_29, plain, ![X19]:(~v1_relat_1(X19)|k7_relat_1(X19,k1_relat_1(X19))=X19), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_relat_1])])).
% 0.12/0.36  cnf(c_0_30, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.12/0.36  cnf(c_0_31, plain, (r1_tarski(k7_relat_1(X1,X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.12/0.36  cnf(c_0_32, negated_conjecture, (k1_setfam_1(k1_enumset1(X1,X1,k1_relat_1(esk2_0)))=k1_relat_1(k7_relat_1(esk2_0,X1))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.12/0.36  cnf(c_0_33, negated_conjecture, (k1_setfam_1(k1_enumset1(k1_relat_1(esk1_0),k1_relat_1(esk1_0),X1))=k1_relat_1(k7_relat_1(esk1_0,X1))), inference(spm,[status(thm)],[c_0_19, c_0_27])).
% 0.12/0.36  cnf(c_0_34, plain, (k7_relat_1(X1,k1_setfam_1(k1_enumset1(X2,X2,X3)))=k1_setfam_1(k1_enumset1(k7_relat_1(X1,X2),k7_relat_1(X1,X2),k7_relat_1(X1,X3)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_16]), c_0_16])).
% 0.12/0.36  cnf(c_0_35, plain, (k7_relat_1(X1,k1_relat_1(X1))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.12/0.36  cnf(c_0_36, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_30, c_0_16])).
% 0.12/0.36  cnf(c_0_37, negated_conjecture, (r1_tarski(k7_relat_1(esk1_0,X1),esk1_0)), inference(spm,[status(thm)],[c_0_31, c_0_27])).
% 0.12/0.36  cnf(c_0_38, negated_conjecture, (k7_relat_1(esk1_0,k1_relat_1(esk2_0))!=k7_relat_1(esk1_0,k1_relat_1(k7_relat_1(esk2_0,k1_relat_1(esk1_0))))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.36  cnf(c_0_39, negated_conjecture, (k1_relat_1(k7_relat_1(esk2_0,k1_relat_1(esk1_0)))=k1_relat_1(k7_relat_1(esk1_0,k1_relat_1(esk2_0)))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.12/0.36  cnf(c_0_40, negated_conjecture, (k1_setfam_1(k1_enumset1(k7_relat_1(esk1_0,X1),k7_relat_1(esk1_0,X1),k7_relat_1(esk1_0,X2)))=k7_relat_1(esk1_0,k1_setfam_1(k1_enumset1(X1,X1,X2)))), inference(spm,[status(thm)],[c_0_34, c_0_27])).
% 0.12/0.36  cnf(c_0_41, negated_conjecture, (k7_relat_1(esk1_0,k1_relat_1(esk1_0))=esk1_0), inference(spm,[status(thm)],[c_0_35, c_0_27])).
% 0.12/0.36  cnf(c_0_42, negated_conjecture, (k1_setfam_1(k1_enumset1(esk1_0,esk1_0,k7_relat_1(esk1_0,X1)))=k7_relat_1(esk1_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_26])).
% 0.12/0.36  cnf(c_0_43, negated_conjecture, (k1_setfam_1(k1_enumset1(X1,X1,k1_relat_1(esk1_0)))=k1_relat_1(k7_relat_1(esk1_0,X1))), inference(spm,[status(thm)],[c_0_33, c_0_26])).
% 0.12/0.36  cnf(c_0_44, negated_conjecture, (k7_relat_1(esk1_0,k1_relat_1(k7_relat_1(esk1_0,k1_relat_1(esk2_0))))!=k7_relat_1(esk1_0,k1_relat_1(esk2_0))), inference(rw,[status(thm)],[c_0_38, c_0_39])).
% 0.12/0.36  cnf(c_0_45, negated_conjecture, (k7_relat_1(esk1_0,k1_relat_1(k7_relat_1(esk1_0,X1)))=k7_relat_1(esk1_0,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_26]), c_0_42]), c_0_43])).
% 0.12/0.36  cnf(c_0_46, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_45])]), ['proof']).
% 0.12/0.36  # SZS output end CNFRefutation
% 0.12/0.36  # Proof object total steps             : 47
% 0.12/0.36  # Proof object clause steps            : 28
% 0.12/0.36  # Proof object formula steps           : 19
% 0.12/0.36  # Proof object conjectures             : 18
% 0.12/0.36  # Proof object clause conjectures      : 15
% 0.12/0.36  # Proof object formula conjectures     : 3
% 0.12/0.36  # Proof object initial clauses used    : 11
% 0.12/0.36  # Proof object initial formulas used   : 9
% 0.12/0.36  # Proof object generating inferences   : 10
% 0.12/0.36  # Proof object simplifying inferences  : 14
% 0.12/0.36  # Training examples: 0 positive, 0 negative
% 0.12/0.36  # Parsed axioms                        : 9
% 0.12/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.36  # Initial clauses                      : 11
% 0.12/0.36  # Removed in clause preprocessing      : 2
% 0.12/0.36  # Initial clauses in saturation        : 9
% 0.12/0.36  # Processed clauses                    : 43
% 0.12/0.36  # ...of these trivial                  : 5
% 0.12/0.36  # ...subsumed                          : 0
% 0.12/0.36  # ...remaining for further processing  : 38
% 0.12/0.36  # Other redundant clauses eliminated   : 0
% 0.12/0.36  # Clauses deleted for lack of memory   : 0
% 0.12/0.36  # Backward-subsumed                    : 0
% 0.12/0.36  # Backward-rewritten                   : 2
% 0.12/0.36  # Generated clauses                    : 53
% 0.12/0.36  # ...of the previous two non-trivial   : 34
% 0.12/0.36  # Contextual simplify-reflections      : 0
% 0.12/0.36  # Paramodulations                      : 53
% 0.12/0.36  # Factorizations                       : 0
% 0.12/0.36  # Equation resolutions                 : 0
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
% 0.12/0.36  # Current number of processed clauses  : 27
% 0.12/0.36  #    Positive orientable unit clauses  : 21
% 0.12/0.36  #    Positive unorientable unit clauses: 1
% 0.12/0.36  #    Negative unit clauses             : 0
% 0.12/0.36  #    Non-unit-clauses                  : 5
% 0.12/0.36  # Current number of unprocessed clauses: 9
% 0.12/0.36  # ...number of literals in the above   : 9
% 0.12/0.36  # Current number of archived formulas  : 0
% 0.12/0.36  # Current number of archived clauses   : 13
% 0.12/0.36  # Clause-clause subsumption calls (NU) : 6
% 0.12/0.36  # Rec. Clause-clause subsumption calls : 6
% 0.12/0.36  # Non-unit clause-clause subsumptions  : 0
% 0.12/0.36  # Unit Clause-clause subsumption calls : 0
% 0.12/0.36  # Rewrite failures with RHS unbound    : 0
% 0.12/0.36  # BW rewrite match attempts            : 30
% 0.12/0.36  # BW rewrite match successes           : 2
% 0.12/0.36  # Condensation attempts                : 0
% 0.12/0.36  # Condensation successes               : 0
% 0.12/0.36  # Termbank termtop insertions          : 1426
% 0.12/0.36  
% 0.12/0.36  # -------------------------------------------------
% 0.12/0.36  # User time                : 0.030 s
% 0.12/0.36  # System time              : 0.001 s
% 0.12/0.36  # Total time               : 0.031 s
% 0.12/0.36  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------

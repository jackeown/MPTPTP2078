%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:52:31 EST 2020

% Result     : Theorem 0.17s
% Output     : CNFRefutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 214 expanded)
%              Number of clauses        :   27 (  95 expanded)
%              Number of leaves         :   11 (  57 expanded)
%              Depth                    :   10
%              Number of atoms          :   81 ( 261 expanded)
%              Number of equality atoms :   49 ( 210 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t213_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k6_subset_1(k1_relat_1(X2),k1_relat_1(k7_relat_1(X2,X1))) = k1_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t213_relat_1)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(t90_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k1_relat_1(k7_relat_1(X2,X1)) = k3_xboole_0(k1_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(t211_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(k1_relat_1(X3),X1)
       => k6_subset_1(X3,k7_relat_1(X3,X2)) = k7_relat_1(X3,k6_subset_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t211_relat_1)).

fof(t191_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k1_relat_1(k7_relat_1(X2,k6_subset_1(k1_relat_1(X2),X1))) = k6_subset_1(k1_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t191_relat_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_11,plain,(
    ! [X16,X17] : k1_setfam_1(k2_tarski(X16,X17)) = k3_xboole_0(X16,X17) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_12,plain,(
    ! [X12,X13] : k1_enumset1(X12,X12,X13) = k2_tarski(X12,X13) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_13,plain,(
    ! [X8,X9] : k4_xboole_0(X8,X9) = k5_xboole_0(X8,k3_xboole_0(X8,X9)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_14,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => k6_subset_1(k1_relat_1(X2),k1_relat_1(k7_relat_1(X2,X1))) = k1_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1))) ) ),
    inference(assume_negation,[status(cth)],[t213_relat_1])).

fof(c_0_17,plain,(
    ! [X10,X11] : k4_xboole_0(X10,k3_xboole_0(X10,X11)) = k4_xboole_0(X10,X11) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

cnf(c_0_18,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

fof(c_0_20,plain,(
    ! [X23,X24] :
      ( ~ v1_relat_1(X24)
      | k1_relat_1(k7_relat_1(X24,X23)) = k3_xboole_0(k1_relat_1(X24),X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).

fof(c_0_21,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & k6_subset_1(k1_relat_1(esk2_0),k1_relat_1(k7_relat_1(esk2_0,esk1_0))) != k1_relat_1(k6_subset_1(esk2_0,k7_relat_1(esk2_0,esk1_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

fof(c_0_22,plain,(
    ! [X14,X15] : k6_subset_1(X14,X15) = k4_xboole_0(X14,X15) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k3_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( k6_subset_1(k1_relat_1(esk2_0),k1_relat_1(k7_relat_1(esk2_0,esk1_0))) != k1_relat_1(k6_subset_1(esk2_0,k7_relat_1(esk2_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,k1_setfam_1(k1_enumset1(X1,X1,X2))))) = k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_19]),c_0_24]),c_0_24])).

cnf(c_0_29,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_25,c_0_19])).

fof(c_0_30,plain,(
    ! [X20,X21,X22] :
      ( ~ v1_relat_1(X22)
      | ~ r1_tarski(k1_relat_1(X22),X20)
      | k6_subset_1(X22,k7_relat_1(X22,X21)) = k7_relat_1(X22,k6_subset_1(X20,X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t211_relat_1])])).

cnf(c_0_31,negated_conjecture,
    ( k5_xboole_0(k1_relat_1(esk2_0),k1_setfam_1(k1_enumset1(k1_relat_1(esk2_0),k1_relat_1(esk2_0),k1_relat_1(k7_relat_1(esk2_0,esk1_0))))) != k1_relat_1(k5_xboole_0(esk2_0,k1_setfam_1(k1_enumset1(esk2_0,esk2_0,k7_relat_1(esk2_0,esk1_0))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27]),c_0_27]),c_0_24]),c_0_24])).

cnf(c_0_32,plain,
    ( k5_xboole_0(k1_relat_1(X1),k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X2))))) = k5_xboole_0(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_34,plain,
    ( k6_subset_1(X1,k7_relat_1(X1,X3)) = k7_relat_1(X1,k6_subset_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_35,plain,(
    ! [X18,X19] :
      ( ~ v1_relat_1(X19)
      | k1_relat_1(k7_relat_1(X19,k6_subset_1(k1_relat_1(X19),X18))) = k6_subset_1(k1_relat_1(X19),X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t191_relat_1])])).

fof(c_0_36,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_37,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | X6 != X7 )
      & ( r1_tarski(X7,X6)
        | X6 != X7 )
      & ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,X6)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_38,negated_conjecture,
    ( k1_relat_1(k5_xboole_0(esk2_0,k1_setfam_1(k1_enumset1(esk2_0,esk2_0,k7_relat_1(esk2_0,esk1_0))))) != k5_xboole_0(k1_relat_1(esk2_0),k1_relat_1(k7_relat_1(esk2_0,esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])])).

cnf(c_0_39,plain,
    ( k7_relat_1(X1,k5_xboole_0(X2,k1_setfam_1(k1_enumset1(X2,X2,X3)))) = k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,k7_relat_1(X1,X3))))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_27]),c_0_27]),c_0_24]),c_0_24])).

cnf(c_0_40,plain,
    ( k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X2))) = k6_subset_1(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_41,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk2_0,k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,esk1_0))))) != k5_xboole_0(k1_relat_1(esk2_0),k1_relat_1(k7_relat_1(esk2_0,esk1_0)))
    | ~ r1_tarski(k1_relat_1(esk2_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_33])])).

cnf(c_0_44,plain,
    ( k1_relat_1(k7_relat_1(X1,k5_xboole_0(k1_relat_1(X1),k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X2))))) = k5_xboole_0(k1_relat_1(X1),k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X2)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_27]),c_0_27]),c_0_24]),c_0_24])).

cnf(c_0_45,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k1_setfam_1(k1_enumset1(X2,X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_19]),c_0_19])).

cnf(c_0_46,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_42])).

cnf(c_0_47,negated_conjecture,
    ( k5_xboole_0(k1_relat_1(esk2_0),k1_setfam_1(k1_enumset1(esk1_0,esk1_0,k1_relat_1(esk2_0)))) != k5_xboole_0(k1_relat_1(esk2_0),k1_relat_1(k7_relat_1(esk2_0,esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45]),c_0_46]),c_0_33])])).

cnf(c_0_48,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,k1_relat_1(X2))) = k1_relat_1(k7_relat_1(X2,X1))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_29,c_0_45])).

cnf(c_0_49,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_33])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.31  % Computer   : n001.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % WCLimit    : 600
% 0.12/0.31  % DateTime   : Tue Dec  1 17:49:30 EST 2020
% 0.17/0.31  % CPUTime    : 
% 0.17/0.31  # Version: 2.5pre002
% 0.17/0.32  # No SInE strategy applied
% 0.17/0.32  # Trying AutoSched0 for 299 seconds
% 0.17/0.35  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.17/0.35  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.17/0.35  #
% 0.17/0.35  # Preprocessing time       : 0.027 s
% 0.17/0.35  # Presaturation interreduction done
% 0.17/0.35  
% 0.17/0.35  # Proof found!
% 0.17/0.35  # SZS status Theorem
% 0.17/0.35  # SZS output start CNFRefutation
% 0.17/0.35  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.17/0.35  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.17/0.35  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.17/0.35  fof(t213_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>k6_subset_1(k1_relat_1(X2),k1_relat_1(k7_relat_1(X2,X1)))=k1_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t213_relat_1)).
% 0.17/0.35  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 0.17/0.35  fof(t90_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k1_relat_1(k7_relat_1(X2,X1))=k3_xboole_0(k1_relat_1(X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 0.17/0.35  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 0.17/0.35  fof(t211_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(k1_relat_1(X3),X1)=>k6_subset_1(X3,k7_relat_1(X3,X2))=k7_relat_1(X3,k6_subset_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t211_relat_1)).
% 0.17/0.35  fof(t191_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k1_relat_1(k7_relat_1(X2,k6_subset_1(k1_relat_1(X2),X1)))=k6_subset_1(k1_relat_1(X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t191_relat_1)).
% 0.17/0.35  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.17/0.35  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.17/0.35  fof(c_0_11, plain, ![X16, X17]:k1_setfam_1(k2_tarski(X16,X17))=k3_xboole_0(X16,X17), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.17/0.35  fof(c_0_12, plain, ![X12, X13]:k1_enumset1(X12,X12,X13)=k2_tarski(X12,X13), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.17/0.35  fof(c_0_13, plain, ![X8, X9]:k4_xboole_0(X8,X9)=k5_xboole_0(X8,k3_xboole_0(X8,X9)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.17/0.35  cnf(c_0_14, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.17/0.35  cnf(c_0_15, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.17/0.35  fof(c_0_16, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>k6_subset_1(k1_relat_1(X2),k1_relat_1(k7_relat_1(X2,X1)))=k1_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1))))), inference(assume_negation,[status(cth)],[t213_relat_1])).
% 0.17/0.35  fof(c_0_17, plain, ![X10, X11]:k4_xboole_0(X10,k3_xboole_0(X10,X11))=k4_xboole_0(X10,X11), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 0.17/0.35  cnf(c_0_18, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.17/0.35  cnf(c_0_19, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.17/0.35  fof(c_0_20, plain, ![X23, X24]:(~v1_relat_1(X24)|k1_relat_1(k7_relat_1(X24,X23))=k3_xboole_0(k1_relat_1(X24),X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).
% 0.17/0.35  fof(c_0_21, negated_conjecture, (v1_relat_1(esk2_0)&k6_subset_1(k1_relat_1(esk2_0),k1_relat_1(k7_relat_1(esk2_0,esk1_0)))!=k1_relat_1(k6_subset_1(esk2_0,k7_relat_1(esk2_0,esk1_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 0.17/0.35  fof(c_0_22, plain, ![X14, X15]:k6_subset_1(X14,X15)=k4_xboole_0(X14,X15), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 0.17/0.35  cnf(c_0_23, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.17/0.35  cnf(c_0_24, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 0.17/0.35  cnf(c_0_25, plain, (k1_relat_1(k7_relat_1(X1,X2))=k3_xboole_0(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.17/0.35  cnf(c_0_26, negated_conjecture, (k6_subset_1(k1_relat_1(esk2_0),k1_relat_1(k7_relat_1(esk2_0,esk1_0)))!=k1_relat_1(k6_subset_1(esk2_0,k7_relat_1(esk2_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.17/0.35  cnf(c_0_27, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.17/0.35  cnf(c_0_28, plain, (k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))))=k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_19]), c_0_24]), c_0_24])).
% 0.17/0.35  cnf(c_0_29, plain, (k1_relat_1(k7_relat_1(X1,X2))=k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_25, c_0_19])).
% 0.17/0.35  fof(c_0_30, plain, ![X20, X21, X22]:(~v1_relat_1(X22)|(~r1_tarski(k1_relat_1(X22),X20)|k6_subset_1(X22,k7_relat_1(X22,X21))=k7_relat_1(X22,k6_subset_1(X20,X21)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t211_relat_1])])).
% 0.17/0.35  cnf(c_0_31, negated_conjecture, (k5_xboole_0(k1_relat_1(esk2_0),k1_setfam_1(k1_enumset1(k1_relat_1(esk2_0),k1_relat_1(esk2_0),k1_relat_1(k7_relat_1(esk2_0,esk1_0)))))!=k1_relat_1(k5_xboole_0(esk2_0,k1_setfam_1(k1_enumset1(esk2_0,esk2_0,k7_relat_1(esk2_0,esk1_0)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_27]), c_0_27]), c_0_24]), c_0_24])).
% 0.17/0.35  cnf(c_0_32, plain, (k5_xboole_0(k1_relat_1(X1),k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X2)))))=k5_xboole_0(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X2)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.17/0.35  cnf(c_0_33, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.17/0.35  cnf(c_0_34, plain, (k6_subset_1(X1,k7_relat_1(X1,X3))=k7_relat_1(X1,k6_subset_1(X2,X3))|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.17/0.35  fof(c_0_35, plain, ![X18, X19]:(~v1_relat_1(X19)|k1_relat_1(k7_relat_1(X19,k6_subset_1(k1_relat_1(X19),X18)))=k6_subset_1(k1_relat_1(X19),X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t191_relat_1])])).
% 0.17/0.35  fof(c_0_36, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.17/0.35  fof(c_0_37, plain, ![X6, X7]:(((r1_tarski(X6,X7)|X6!=X7)&(r1_tarski(X7,X6)|X6!=X7))&(~r1_tarski(X6,X7)|~r1_tarski(X7,X6)|X6=X7)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.17/0.35  cnf(c_0_38, negated_conjecture, (k1_relat_1(k5_xboole_0(esk2_0,k1_setfam_1(k1_enumset1(esk2_0,esk2_0,k7_relat_1(esk2_0,esk1_0)))))!=k5_xboole_0(k1_relat_1(esk2_0),k1_relat_1(k7_relat_1(esk2_0,esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])])).
% 0.17/0.35  cnf(c_0_39, plain, (k7_relat_1(X1,k5_xboole_0(X2,k1_setfam_1(k1_enumset1(X2,X2,X3))))=k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,k7_relat_1(X1,X3))))|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_27]), c_0_27]), c_0_24]), c_0_24])).
% 0.17/0.35  cnf(c_0_40, plain, (k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X2)))=k6_subset_1(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.17/0.35  cnf(c_0_41, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.17/0.35  cnf(c_0_42, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.17/0.35  cnf(c_0_43, negated_conjecture, (k1_relat_1(k7_relat_1(esk2_0,k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,esk1_0)))))!=k5_xboole_0(k1_relat_1(esk2_0),k1_relat_1(k7_relat_1(esk2_0,esk1_0)))|~r1_tarski(k1_relat_1(esk2_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_33])])).
% 0.17/0.35  cnf(c_0_44, plain, (k1_relat_1(k7_relat_1(X1,k5_xboole_0(k1_relat_1(X1),k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X2)))))=k5_xboole_0(k1_relat_1(X1),k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X2)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_27]), c_0_27]), c_0_24]), c_0_24])).
% 0.17/0.35  cnf(c_0_45, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k1_setfam_1(k1_enumset1(X2,X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_19]), c_0_19])).
% 0.17/0.35  cnf(c_0_46, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_42])).
% 0.17/0.35  cnf(c_0_47, negated_conjecture, (k5_xboole_0(k1_relat_1(esk2_0),k1_setfam_1(k1_enumset1(esk1_0,esk1_0,k1_relat_1(esk2_0))))!=k5_xboole_0(k1_relat_1(esk2_0),k1_relat_1(k7_relat_1(esk2_0,esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45]), c_0_46]), c_0_33])])).
% 0.17/0.35  cnf(c_0_48, plain, (k1_setfam_1(k1_enumset1(X1,X1,k1_relat_1(X2)))=k1_relat_1(k7_relat_1(X2,X1))|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_29, c_0_45])).
% 0.17/0.35  cnf(c_0_49, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_33])]), ['proof']).
% 0.17/0.35  # SZS output end CNFRefutation
% 0.17/0.35  # Proof object total steps             : 50
% 0.17/0.35  # Proof object clause steps            : 27
% 0.17/0.35  # Proof object formula steps           : 23
% 0.17/0.35  # Proof object conjectures             : 10
% 0.17/0.35  # Proof object clause conjectures      : 7
% 0.17/0.35  # Proof object formula conjectures     : 3
% 0.17/0.35  # Proof object initial clauses used    : 12
% 0.17/0.35  # Proof object initial formulas used   : 11
% 0.17/0.35  # Proof object generating inferences   : 6
% 0.17/0.35  # Proof object simplifying inferences  : 31
% 0.17/0.35  # Training examples: 0 positive, 0 negative
% 0.17/0.35  # Parsed axioms                        : 11
% 0.17/0.35  # Removed by relevancy pruning/SinE    : 0
% 0.17/0.35  # Initial clauses                      : 14
% 0.17/0.35  # Removed in clause preprocessing      : 4
% 0.17/0.35  # Initial clauses in saturation        : 10
% 0.17/0.35  # Processed clauses                    : 33
% 0.17/0.35  # ...of these trivial                  : 0
% 0.17/0.35  # ...subsumed                          : 3
% 0.17/0.35  # ...remaining for further processing  : 30
% 0.17/0.35  # Other redundant clauses eliminated   : 2
% 0.17/0.35  # Clauses deleted for lack of memory   : 0
% 0.17/0.35  # Backward-subsumed                    : 0
% 0.17/0.35  # Backward-rewritten                   : 0
% 0.17/0.35  # Generated clauses                    : 60
% 0.17/0.35  # ...of the previous two non-trivial   : 58
% 0.17/0.35  # Contextual simplify-reflections      : 0
% 0.17/0.35  # Paramodulations                      : 58
% 0.17/0.35  # Factorizations                       : 0
% 0.17/0.35  # Equation resolutions                 : 2
% 0.17/0.35  # Propositional unsat checks           : 0
% 0.17/0.35  #    Propositional check models        : 0
% 0.17/0.35  #    Propositional check unsatisfiable : 0
% 0.17/0.35  #    Propositional clauses             : 0
% 0.17/0.35  #    Propositional clauses after purity: 0
% 0.17/0.35  #    Propositional unsat core size     : 0
% 0.17/0.35  #    Propositional preprocessing time  : 0.000
% 0.17/0.35  #    Propositional encoding time       : 0.000
% 0.17/0.35  #    Propositional solver time         : 0.000
% 0.17/0.35  #    Success case prop preproc time    : 0.000
% 0.17/0.35  #    Success case prop encoding time   : 0.000
% 0.17/0.35  #    Success case prop solver time     : 0.000
% 0.17/0.35  # Current number of processed clauses  : 19
% 0.17/0.35  #    Positive orientable unit clauses  : 3
% 0.17/0.35  #    Positive unorientable unit clauses: 1
% 0.17/0.35  #    Negative unit clauses             : 6
% 0.17/0.35  #    Non-unit-clauses                  : 9
% 0.17/0.35  # Current number of unprocessed clauses: 44
% 0.17/0.35  # ...number of literals in the above   : 119
% 0.17/0.35  # Current number of archived formulas  : 0
% 0.17/0.35  # Current number of archived clauses   : 13
% 0.17/0.35  # Clause-clause subsumption calls (NU) : 12
% 0.17/0.35  # Rec. Clause-clause subsumption calls : 12
% 0.17/0.35  # Non-unit clause-clause subsumptions  : 2
% 0.17/0.35  # Unit Clause-clause subsumption calls : 7
% 0.17/0.35  # Rewrite failures with RHS unbound    : 0
% 0.17/0.35  # BW rewrite match attempts            : 18
% 0.17/0.35  # BW rewrite match successes           : 14
% 0.17/0.35  # Condensation attempts                : 0
% 0.17/0.35  # Condensation successes               : 0
% 0.17/0.35  # Termbank termtop insertions          : 2160
% 0.17/0.35  
% 0.17/0.35  # -------------------------------------------------
% 0.17/0.35  # User time                : 0.031 s
% 0.17/0.35  # System time              : 0.002 s
% 0.17/0.35  # Total time               : 0.033 s
% 0.17/0.35  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:49:38 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 132 expanded)
%              Number of clauses        :   31 (  58 expanded)
%              Number of leaves         :   14 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :  104 ( 250 expanded)
%              Number of equality atoms :   49 ( 127 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(t90_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k1_relat_1(k7_relat_1(X2,X1)) = k3_xboole_0(k1_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(t95_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k7_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(t67_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_xboole_0(k2_relat_1(X1),k1_relat_1(X2))
           => k5_relat_1(X1,X2) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t94_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k5_relat_1(k6_relat_1(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(c_0_14,plain,(
    ! [X14,X15] : k1_setfam_1(k2_tarski(X14,X15)) = k3_xboole_0(X14,X15) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_15,plain,(
    ! [X12,X13] : k1_enumset1(X12,X12,X13) = k2_tarski(X12,X13) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_16,plain,(
    ! [X6,X7] : k4_xboole_0(X6,k3_xboole_0(X6,X7)) = k4_xboole_0(X6,X7) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

cnf(c_0_17,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,plain,(
    ! [X10,X11] :
      ( ( ~ r1_xboole_0(X10,X11)
        | k4_xboole_0(X10,X11) = X10 )
      & ( k4_xboole_0(X10,X11) != X10
        | r1_xboole_0(X10,X11) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_20,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

fof(c_0_22,plain,(
    ! [X20,X21] :
      ( ~ v1_relat_1(X21)
      | k1_relat_1(k7_relat_1(X21,X20)) = k3_xboole_0(k1_relat_1(X21),X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k3_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_26,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( k7_relat_1(X2,X1) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(X2),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t95_relat_1])).

fof(c_0_27,plain,(
    ! [X5] : k4_xboole_0(X5,k1_xboole_0) = X5 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_28,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_25,c_0_21])).

fof(c_0_30,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & ( k7_relat_1(esk2_0,esk1_0) != k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(esk2_0),esk1_0) )
    & ( k7_relat_1(esk2_0,esk1_0) = k1_xboole_0
      | r1_xboole_0(k1_relat_1(esk2_0),esk1_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])).

cnf(c_0_31,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_33,plain,(
    ! [X8,X9] : r1_xboole_0(k4_xboole_0(X8,X9),X9) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

cnf(c_0_34,plain,
    ( k4_xboole_0(k1_relat_1(X1),X2) = k1_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( k7_relat_1(esk2_0,esk1_0) = k1_xboole_0
    | r1_xboole_0(k1_relat_1(esk2_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_38,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

fof(c_0_39,plain,(
    ! [X17,X18] :
      ( ~ v1_relat_1(X17)
      | ~ v1_relat_1(X18)
      | ~ r1_xboole_0(k2_relat_1(X17),k1_relat_1(X18))
      | k5_relat_1(X17,X18) = k1_xboole_0 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_relat_1])])])).

fof(c_0_40,plain,(
    ! [X19] :
      ( k1_relat_1(k6_relat_1(X19)) = X19
      & k2_relat_1(k6_relat_1(X19)) = X19 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_41,plain,(
    ! [X16] : v1_relat_1(k6_relat_1(X16)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

fof(c_0_42,plain,(
    ! [X3,X4] :
      ( ~ r1_xboole_0(X3,X4)
      | r1_xboole_0(X4,X3) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_43,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_44,negated_conjecture,
    ( k4_xboole_0(k1_relat_1(esk2_0),esk1_0) = k1_relat_1(esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36]),c_0_37]),c_0_38])]),c_0_23])).

fof(c_0_45,plain,(
    ! [X22,X23] :
      ( ~ v1_relat_1(X23)
      | k7_relat_1(X23,X22) = k5_relat_1(k6_relat_1(X22),X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).

cnf(c_0_46,plain,
    ( k5_relat_1(X1,X2) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_xboole_0(k2_relat_1(X1),k1_relat_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_47,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_48,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_49,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_50,negated_conjecture,
    ( k7_relat_1(esk2_0,esk1_0) != k1_xboole_0
    | ~ r1_xboole_0(k1_relat_1(esk2_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_51,negated_conjecture,
    ( r1_xboole_0(k1_relat_1(esk2_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_52,plain,
    ( k7_relat_1(X1,X2) = k5_relat_1(k6_relat_1(X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_53,plain,
    ( k5_relat_1(k6_relat_1(X1),X2) = k1_xboole_0
    | ~ v1_relat_1(X2)
    | ~ r1_xboole_0(X1,k1_relat_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])])).

cnf(c_0_54,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_43])).

cnf(c_0_55,negated_conjecture,
    ( k7_relat_1(esk2_0,esk1_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_51])])).

cnf(c_0_56,plain,
    ( k7_relat_1(X1,X2) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(X2,k1_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_57,negated_conjecture,
    ( r1_xboole_0(esk1_0,k1_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_44])).

cnf(c_0_58,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_36]),c_0_57])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n005.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:37:32 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.14/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.027 s
% 0.14/0.38  # Presaturation interreduction done
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.14/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.14/0.38  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 0.14/0.38  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.14/0.38  fof(t90_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k1_relat_1(k7_relat_1(X2,X1))=k3_xboole_0(k1_relat_1(X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 0.14/0.38  fof(t95_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(k7_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 0.14/0.38  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.14/0.38  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.14/0.38  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 0.14/0.38  fof(t67_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_xboole_0(k2_relat_1(X1),k1_relat_1(X2))=>k5_relat_1(X1,X2)=k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_relat_1)).
% 0.14/0.38  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 0.14/0.38  fof(dt_k6_relat_1, axiom, ![X1]:v1_relat_1(k6_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 0.14/0.38  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.14/0.38  fof(t94_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k5_relat_1(k6_relat_1(X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 0.14/0.38  fof(c_0_14, plain, ![X14, X15]:k1_setfam_1(k2_tarski(X14,X15))=k3_xboole_0(X14,X15), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.14/0.38  fof(c_0_15, plain, ![X12, X13]:k1_enumset1(X12,X12,X13)=k2_tarski(X12,X13), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.14/0.38  fof(c_0_16, plain, ![X6, X7]:k4_xboole_0(X6,k3_xboole_0(X6,X7))=k4_xboole_0(X6,X7), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 0.14/0.38  cnf(c_0_17, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.38  cnf(c_0_18, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.38  fof(c_0_19, plain, ![X10, X11]:((~r1_xboole_0(X10,X11)|k4_xboole_0(X10,X11)=X10)&(k4_xboole_0(X10,X11)!=X10|r1_xboole_0(X10,X11))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.14/0.38  cnf(c_0_20, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.38  cnf(c_0_21, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.14/0.38  fof(c_0_22, plain, ![X20, X21]:(~v1_relat_1(X21)|k1_relat_1(k7_relat_1(X21,X20))=k3_xboole_0(k1_relat_1(X21),X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).
% 0.14/0.38  cnf(c_0_23, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.14/0.38  cnf(c_0_24, plain, (k4_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 0.14/0.38  cnf(c_0_25, plain, (k1_relat_1(k7_relat_1(X1,X2))=k3_xboole_0(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.38  fof(c_0_26, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(k7_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k1_relat_1(X2),X1)))), inference(assume_negation,[status(cth)],[t95_relat_1])).
% 0.14/0.38  fof(c_0_27, plain, ![X5]:k4_xboole_0(X5,k1_xboole_0)=X5, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.14/0.38  cnf(c_0_28, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.14/0.38  cnf(c_0_29, plain, (k1_relat_1(k7_relat_1(X1,X2))=k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_25, c_0_21])).
% 0.14/0.38  fof(c_0_30, negated_conjecture, (v1_relat_1(esk2_0)&((k7_relat_1(esk2_0,esk1_0)!=k1_xboole_0|~r1_xboole_0(k1_relat_1(esk2_0),esk1_0))&(k7_relat_1(esk2_0,esk1_0)=k1_xboole_0|r1_xboole_0(k1_relat_1(esk2_0),esk1_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])).
% 0.14/0.38  cnf(c_0_31, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.14/0.38  cnf(c_0_32, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.14/0.38  fof(c_0_33, plain, ![X8, X9]:r1_xboole_0(k4_xboole_0(X8,X9),X9), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.14/0.38  cnf(c_0_34, plain, (k4_xboole_0(k1_relat_1(X1),X2)=k1_relat_1(X1)|~v1_relat_1(X1)|~r1_xboole_0(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X2)))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.14/0.38  cnf(c_0_35, negated_conjecture, (k7_relat_1(esk2_0,esk1_0)=k1_xboole_0|r1_xboole_0(k1_relat_1(esk2_0),esk1_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.14/0.38  cnf(c_0_36, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.14/0.38  cnf(c_0_37, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.14/0.38  cnf(c_0_38, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.14/0.38  fof(c_0_39, plain, ![X17, X18]:(~v1_relat_1(X17)|(~v1_relat_1(X18)|(~r1_xboole_0(k2_relat_1(X17),k1_relat_1(X18))|k5_relat_1(X17,X18)=k1_xboole_0))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_relat_1])])])).
% 0.14/0.38  fof(c_0_40, plain, ![X19]:(k1_relat_1(k6_relat_1(X19))=X19&k2_relat_1(k6_relat_1(X19))=X19), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.14/0.38  fof(c_0_41, plain, ![X16]:v1_relat_1(k6_relat_1(X16)), inference(variable_rename,[status(thm)],[dt_k6_relat_1])).
% 0.14/0.38  fof(c_0_42, plain, ![X3, X4]:(~r1_xboole_0(X3,X4)|r1_xboole_0(X4,X3)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.14/0.38  cnf(c_0_43, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.14/0.38  cnf(c_0_44, negated_conjecture, (k4_xboole_0(k1_relat_1(esk2_0),esk1_0)=k1_relat_1(esk2_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36]), c_0_37]), c_0_38])]), c_0_23])).
% 0.14/0.38  fof(c_0_45, plain, ![X22, X23]:(~v1_relat_1(X23)|k7_relat_1(X23,X22)=k5_relat_1(k6_relat_1(X22),X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).
% 0.14/0.38  cnf(c_0_46, plain, (k5_relat_1(X1,X2)=k1_xboole_0|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_xboole_0(k2_relat_1(X1),k1_relat_1(X2))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.14/0.38  cnf(c_0_47, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.14/0.38  cnf(c_0_48, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.14/0.38  cnf(c_0_49, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.14/0.38  cnf(c_0_50, negated_conjecture, (k7_relat_1(esk2_0,esk1_0)!=k1_xboole_0|~r1_xboole_0(k1_relat_1(esk2_0),esk1_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.14/0.38  cnf(c_0_51, negated_conjecture, (r1_xboole_0(k1_relat_1(esk2_0),esk1_0)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.14/0.38  cnf(c_0_52, plain, (k7_relat_1(X1,X2)=k5_relat_1(k6_relat_1(X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.14/0.38  cnf(c_0_53, plain, (k5_relat_1(k6_relat_1(X1),X2)=k1_xboole_0|~v1_relat_1(X2)|~r1_xboole_0(X1,k1_relat_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48])])).
% 0.14/0.38  cnf(c_0_54, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_49, c_0_43])).
% 0.14/0.38  cnf(c_0_55, negated_conjecture, (k7_relat_1(esk2_0,esk1_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_51])])).
% 0.14/0.38  cnf(c_0_56, plain, (k7_relat_1(X1,X2)=k1_xboole_0|~v1_relat_1(X1)|~r1_xboole_0(X2,k1_relat_1(X1))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.14/0.38  cnf(c_0_57, negated_conjecture, (r1_xboole_0(esk1_0,k1_relat_1(esk2_0))), inference(spm,[status(thm)],[c_0_54, c_0_44])).
% 0.14/0.38  cnf(c_0_58, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_36]), c_0_57])]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 59
% 0.14/0.38  # Proof object clause steps            : 31
% 0.14/0.38  # Proof object formula steps           : 28
% 0.14/0.38  # Proof object conjectures             : 11
% 0.14/0.38  # Proof object clause conjectures      : 8
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 17
% 0.14/0.38  # Proof object initial formulas used   : 14
% 0.14/0.38  # Proof object generating inferences   : 10
% 0.14/0.38  # Proof object simplifying inferences  : 15
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 14
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 19
% 0.14/0.38  # Removed in clause preprocessing      : 2
% 0.14/0.38  # Initial clauses in saturation        : 17
% 0.14/0.38  # Processed clauses                    : 59
% 0.14/0.38  # ...of these trivial                  : 2
% 0.14/0.38  # ...subsumed                          : 4
% 0.14/0.38  # ...remaining for further processing  : 53
% 0.14/0.38  # Other redundant clauses eliminated   : 0
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 0
% 0.14/0.38  # Backward-rewritten                   : 2
% 0.14/0.38  # Generated clauses                    : 51
% 0.14/0.38  # ...of the previous two non-trivial   : 33
% 0.14/0.38  # Contextual simplify-reflections      : 1
% 0.14/0.38  # Paramodulations                      : 51
% 0.14/0.38  # Factorizations                       : 0
% 0.14/0.38  # Equation resolutions                 : 0
% 0.14/0.38  # Propositional unsat checks           : 0
% 0.14/0.38  #    Propositional check models        : 0
% 0.14/0.38  #    Propositional check unsatisfiable : 0
% 0.14/0.38  #    Propositional clauses             : 0
% 0.14/0.38  #    Propositional clauses after purity: 0
% 0.14/0.38  #    Propositional unsat core size     : 0
% 0.14/0.38  #    Propositional preprocessing time  : 0.000
% 0.14/0.38  #    Propositional encoding time       : 0.000
% 0.14/0.38  #    Propositional solver time         : 0.000
% 0.14/0.38  #    Success case prop preproc time    : 0.000
% 0.14/0.38  #    Success case prop encoding time   : 0.000
% 0.14/0.38  #    Success case prop solver time     : 0.000
% 0.14/0.38  # Current number of processed clauses  : 34
% 0.14/0.38  #    Positive orientable unit clauses  : 16
% 0.14/0.38  #    Positive unorientable unit clauses: 0
% 0.14/0.38  #    Negative unit clauses             : 1
% 0.14/0.38  #    Non-unit-clauses                  : 17
% 0.14/0.38  # Current number of unprocessed clauses: 8
% 0.14/0.38  # ...number of literals in the above   : 12
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 21
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 36
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 34
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 5
% 0.14/0.38  # Unit Clause-clause subsumption calls : 3
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 1
% 0.14/0.38  # BW rewrite match successes           : 1
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 1611
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.031 s
% 0.14/0.38  # System time              : 0.001 s
% 0.14/0.38  # Total time               : 0.032 s
% 0.14/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------

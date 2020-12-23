%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:49:46 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 187 expanded)
%              Number of clauses        :   29 (  73 expanded)
%              Number of leaves         :   14 (  55 expanded)
%              Depth                    :    8
%              Number of atoms          :   87 ( 246 expanded)
%              Number of equality atoms :   54 ( 183 expanded)
%              Maximal formula depth    :    8 (   3 average)
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

fof(t100_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k7_relat_1(k7_relat_1(X3,X1),X2) = k7_relat_1(X3,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t90_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k1_relat_1(k7_relat_1(X2,X1)) = k3_xboole_0(k1_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(t97_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X1)
       => k7_relat_1(X2,X1) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(t103_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => k7_relat_1(k7_relat_1(X3,X2),X1) = k7_relat_1(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_relat_1)).

fof(c_0_14,plain,(
    ! [X37,X38] : k1_setfam_1(k2_tarski(X37,X38)) = k3_xboole_0(X37,X38) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_15,plain,(
    ! [X10,X11] : k1_enumset1(X10,X10,X11) = k2_tarski(X10,X11) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_16,plain,(
    ! [X40,X41,X42] :
      ( ~ v1_relat_1(X42)
      | k7_relat_1(k7_relat_1(X42,X40),X41) = k7_relat_1(X42,k3_xboole_0(X40,X41)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t100_relat_1])])).

cnf(c_0_17,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,plain,(
    ! [X12,X13,X14] : k2_enumset1(X12,X12,X13,X14) = k1_enumset1(X12,X13,X14) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_20,plain,(
    ! [X15,X16,X17,X18] : k3_enumset1(X15,X15,X16,X17,X18) = k2_enumset1(X15,X16,X17,X18) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_21,plain,(
    ! [X19,X20,X21,X22,X23] : k4_enumset1(X19,X19,X20,X21,X22,X23) = k3_enumset1(X19,X20,X21,X22,X23) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_22,plain,(
    ! [X24,X25,X26,X27,X28,X29] : k5_enumset1(X24,X24,X25,X26,X27,X28,X29) = k4_enumset1(X24,X25,X26,X27,X28,X29) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_23,plain,(
    ! [X30,X31,X32,X33,X34,X35,X36] : k6_enumset1(X30,X30,X31,X32,X33,X34,X35,X36) = k5_enumset1(X30,X31,X32,X33,X34,X35,X36) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_24,plain,(
    ! [X8,X9] : k2_tarski(X8,X9) = k2_tarski(X9,X8) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

fof(c_0_25,plain,(
    ! [X44,X45] :
      ( ~ v1_relat_1(X45)
      | k1_relat_1(k7_relat_1(X45,X44)) = k3_xboole_0(k1_relat_1(X45),X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).

cnf(c_0_26,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k7_relat_1(X1,k3_xboole_0(X2,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_28,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k3_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_35,plain,(
    ! [X46,X47] :
      ( ~ v1_relat_1(X47)
      | ~ r1_tarski(k1_relat_1(X47),X46)
      | k7_relat_1(X47,X46) = X47 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).

fof(c_0_36,plain,(
    ! [X43] :
      ( k1_relat_1(k6_relat_1(X43)) = X43
      & k2_relat_1(k6_relat_1(X43)) = X43 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_37,plain,(
    ! [X39] : v1_relat_1(k6_relat_1(X39)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

fof(c_0_38,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( r1_tarski(X1,X2)
         => k7_relat_1(k7_relat_1(X3,X2),X1) = k7_relat_1(X3,X1) ) ) ),
    inference(assume_negation,[status(cth)],[t103_relat_1])).

cnf(c_0_39,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k7_relat_1(X1,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_31]),c_0_32])).

cnf(c_0_40,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_18]),c_0_18]),c_0_28]),c_0_28]),c_0_29]),c_0_29]),c_0_30]),c_0_30]),c_0_31]),c_0_31]),c_0_32]),c_0_32])).

cnf(c_0_41,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_31]),c_0_32])).

cnf(c_0_42,plain,
    ( k7_relat_1(X1,X2) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_44,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_45,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & r1_tarski(esk1_0,esk2_0)
    & k7_relat_1(k7_relat_1(esk3_0,esk2_0),esk1_0) != k7_relat_1(esk3_0,esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_38])])])).

cnf(c_0_46,plain,
    ( k7_relat_1(X1,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))) = k7_relat_1(k7_relat_1(X1,X3),X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_47,plain,
    ( k7_relat_1(k7_relat_1(X1,k1_relat_1(X2)),X3) = k7_relat_1(X1,k1_relat_1(k7_relat_1(X2,X3)))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_41])).

cnf(c_0_48,plain,
    ( k7_relat_1(k6_relat_1(X1),X2) = k6_relat_1(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_50,negated_conjecture,
    ( k7_relat_1(k7_relat_1(esk3_0,esk2_0),esk1_0) != k7_relat_1(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_51,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k7_relat_1(k7_relat_1(X1,X3),X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_53,plain,
    ( k7_relat_1(X1,k1_relat_1(k7_relat_1(k6_relat_1(X2),X3))) = k7_relat_1(k7_relat_1(X1,X2),X3)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_43]),c_0_44])])).

cnf(c_0_54,negated_conjecture,
    ( k7_relat_1(k6_relat_1(esk1_0),esk2_0) = k6_relat_1(esk1_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_55,negated_conjecture,
    ( k7_relat_1(k7_relat_1(esk3_0,esk1_0),esk2_0) != k7_relat_1(esk3_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])])).

cnf(c_0_56,negated_conjecture,
    ( k7_relat_1(k7_relat_1(X1,esk1_0),esk2_0) = k7_relat_1(X1,esk1_0)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_43])).

cnf(c_0_57,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_52])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:16:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.026 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.13/0.37  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.37  fof(t100_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k7_relat_1(k7_relat_1(X3,X1),X2)=k7_relat_1(X3,k3_xboole_0(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 0.13/0.37  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.13/0.37  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.13/0.37  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.13/0.37  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.13/0.37  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.13/0.37  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.13/0.37  fof(t90_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k1_relat_1(k7_relat_1(X2,X1))=k3_xboole_0(k1_relat_1(X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 0.13/0.37  fof(t97_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X2),X1)=>k7_relat_1(X2,X1)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 0.13/0.37  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 0.13/0.37  fof(dt_k6_relat_1, axiom, ![X1]:v1_relat_1(k6_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 0.13/0.37  fof(t103_relat_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>k7_relat_1(k7_relat_1(X3,X2),X1)=k7_relat_1(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_relat_1)).
% 0.13/0.37  fof(c_0_14, plain, ![X37, X38]:k1_setfam_1(k2_tarski(X37,X38))=k3_xboole_0(X37,X38), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.13/0.37  fof(c_0_15, plain, ![X10, X11]:k1_enumset1(X10,X10,X11)=k2_tarski(X10,X11), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.37  fof(c_0_16, plain, ![X40, X41, X42]:(~v1_relat_1(X42)|k7_relat_1(k7_relat_1(X42,X40),X41)=k7_relat_1(X42,k3_xboole_0(X40,X41))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t100_relat_1])])).
% 0.13/0.37  cnf(c_0_17, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.37  cnf(c_0_18, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.37  fof(c_0_19, plain, ![X12, X13, X14]:k2_enumset1(X12,X12,X13,X14)=k1_enumset1(X12,X13,X14), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.13/0.37  fof(c_0_20, plain, ![X15, X16, X17, X18]:k3_enumset1(X15,X15,X16,X17,X18)=k2_enumset1(X15,X16,X17,X18), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.13/0.37  fof(c_0_21, plain, ![X19, X20, X21, X22, X23]:k4_enumset1(X19,X19,X20,X21,X22,X23)=k3_enumset1(X19,X20,X21,X22,X23), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.13/0.37  fof(c_0_22, plain, ![X24, X25, X26, X27, X28, X29]:k5_enumset1(X24,X24,X25,X26,X27,X28,X29)=k4_enumset1(X24,X25,X26,X27,X28,X29), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.13/0.37  fof(c_0_23, plain, ![X30, X31, X32, X33, X34, X35, X36]:k6_enumset1(X30,X30,X31,X32,X33,X34,X35,X36)=k5_enumset1(X30,X31,X32,X33,X34,X35,X36), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.13/0.37  fof(c_0_24, plain, ![X8, X9]:k2_tarski(X8,X9)=k2_tarski(X9,X8), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.13/0.37  fof(c_0_25, plain, ![X44, X45]:(~v1_relat_1(X45)|k1_relat_1(k7_relat_1(X45,X44))=k3_xboole_0(k1_relat_1(X45),X44)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).
% 0.13/0.37  cnf(c_0_26, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k7_relat_1(X1,k3_xboole_0(X2,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.37  cnf(c_0_27, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.13/0.37  cnf(c_0_28, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.37  cnf(c_0_29, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.37  cnf(c_0_30, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.37  cnf(c_0_31, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.37  cnf(c_0_32, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.37  cnf(c_0_33, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.37  cnf(c_0_34, plain, (k1_relat_1(k7_relat_1(X1,X2))=k3_xboole_0(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.37  fof(c_0_35, plain, ![X46, X47]:(~v1_relat_1(X47)|(~r1_tarski(k1_relat_1(X47),X46)|k7_relat_1(X47,X46)=X47)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).
% 0.13/0.37  fof(c_0_36, plain, ![X43]:(k1_relat_1(k6_relat_1(X43))=X43&k2_relat_1(k6_relat_1(X43))=X43), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.13/0.37  fof(c_0_37, plain, ![X39]:v1_relat_1(k6_relat_1(X39)), inference(variable_rename,[status(thm)],[dt_k6_relat_1])).
% 0.13/0.37  fof(c_0_38, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>k7_relat_1(k7_relat_1(X3,X2),X1)=k7_relat_1(X3,X1)))), inference(assume_negation,[status(cth)],[t103_relat_1])).
% 0.13/0.37  cnf(c_0_39, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k7_relat_1(X1,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29]), c_0_30]), c_0_31]), c_0_32])).
% 0.13/0.37  cnf(c_0_40, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_18]), c_0_18]), c_0_28]), c_0_28]), c_0_29]), c_0_29]), c_0_30]), c_0_30]), c_0_31]), c_0_31]), c_0_32]), c_0_32])).
% 0.13/0.37  cnf(c_0_41, plain, (k1_relat_1(k7_relat_1(X1,X2))=k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_27]), c_0_28]), c_0_29]), c_0_30]), c_0_31]), c_0_32])).
% 0.13/0.37  cnf(c_0_42, plain, (k7_relat_1(X1,X2)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.37  cnf(c_0_43, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.13/0.37  cnf(c_0_44, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.13/0.37  fof(c_0_45, negated_conjecture, (v1_relat_1(esk3_0)&(r1_tarski(esk1_0,esk2_0)&k7_relat_1(k7_relat_1(esk3_0,esk2_0),esk1_0)!=k7_relat_1(esk3_0,esk1_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_38])])])).
% 0.13/0.37  cnf(c_0_46, plain, (k7_relat_1(X1,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))=k7_relat_1(k7_relat_1(X1,X3),X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.13/0.37  cnf(c_0_47, plain, (k7_relat_1(k7_relat_1(X1,k1_relat_1(X2)),X3)=k7_relat_1(X1,k1_relat_1(k7_relat_1(X2,X3)))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_39, c_0_41])).
% 0.13/0.37  cnf(c_0_48, plain, (k7_relat_1(k6_relat_1(X1),X2)=k6_relat_1(X1)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44])])).
% 0.13/0.37  cnf(c_0_49, negated_conjecture, (r1_tarski(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.13/0.37  cnf(c_0_50, negated_conjecture, (k7_relat_1(k7_relat_1(esk3_0,esk2_0),esk1_0)!=k7_relat_1(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.13/0.37  cnf(c_0_51, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k7_relat_1(k7_relat_1(X1,X3),X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_39, c_0_46])).
% 0.13/0.37  cnf(c_0_52, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.13/0.37  cnf(c_0_53, plain, (k7_relat_1(X1,k1_relat_1(k7_relat_1(k6_relat_1(X2),X3)))=k7_relat_1(k7_relat_1(X1,X2),X3)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_43]), c_0_44])])).
% 0.13/0.37  cnf(c_0_54, negated_conjecture, (k7_relat_1(k6_relat_1(esk1_0),esk2_0)=k6_relat_1(esk1_0)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.13/0.37  cnf(c_0_55, negated_conjecture, (k7_relat_1(k7_relat_1(esk3_0,esk1_0),esk2_0)!=k7_relat_1(esk3_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52])])).
% 0.13/0.37  cnf(c_0_56, negated_conjecture, (k7_relat_1(k7_relat_1(X1,esk1_0),esk2_0)=k7_relat_1(X1,esk1_0)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_43])).
% 0.13/0.37  cnf(c_0_57, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_52])]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 58
% 0.13/0.37  # Proof object clause steps            : 29
% 0.13/0.37  # Proof object formula steps           : 29
% 0.13/0.37  # Proof object conjectures             : 10
% 0.13/0.37  # Proof object clause conjectures      : 7
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 16
% 0.13/0.37  # Proof object initial formulas used   : 14
% 0.13/0.37  # Proof object generating inferences   : 9
% 0.13/0.37  # Proof object simplifying inferences  : 34
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 14
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 17
% 0.13/0.37  # Removed in clause preprocessing      : 7
% 0.13/0.37  # Initial clauses in saturation        : 10
% 0.13/0.37  # Processed clauses                    : 30
% 0.13/0.37  # ...of these trivial                  : 0
% 0.13/0.37  # ...subsumed                          : 1
% 0.13/0.37  # ...remaining for further processing  : 29
% 0.13/0.37  # Other redundant clauses eliminated   : 0
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 0
% 0.13/0.37  # Backward-rewritten                   : 0
% 0.13/0.37  # Generated clauses                    : 72
% 0.13/0.37  # ...of the previous two non-trivial   : 71
% 0.13/0.37  # Contextual simplify-reflections      : 0
% 0.13/0.37  # Paramodulations                      : 72
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 0
% 0.13/0.37  # Propositional unsat checks           : 0
% 0.13/0.37  #    Propositional check models        : 0
% 0.13/0.37  #    Propositional check unsatisfiable : 0
% 0.13/0.37  #    Propositional clauses             : 0
% 0.13/0.37  #    Propositional clauses after purity: 0
% 0.13/0.37  #    Propositional unsat core size     : 0
% 0.13/0.37  #    Propositional preprocessing time  : 0.000
% 0.13/0.37  #    Propositional encoding time       : 0.000
% 0.13/0.37  #    Propositional solver time         : 0.000
% 0.13/0.37  #    Success case prop preproc time    : 0.000
% 0.13/0.37  #    Success case prop encoding time   : 0.000
% 0.13/0.37  #    Success case prop solver time     : 0.000
% 0.13/0.37  # Current number of processed clauses  : 19
% 0.13/0.37  #    Positive orientable unit clauses  : 6
% 0.13/0.37  #    Positive unorientable unit clauses: 1
% 0.13/0.37  #    Negative unit clauses             : 2
% 0.13/0.37  #    Non-unit-clauses                  : 10
% 0.13/0.37  # Current number of unprocessed clauses: 61
% 0.13/0.37  # ...number of literals in the above   : 180
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 17
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 24
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 20
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 1
% 0.13/0.37  # Unit Clause-clause subsumption calls : 2
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 2
% 0.13/0.37  # BW rewrite match successes           : 2
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 1984
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.028 s
% 0.13/0.38  # System time              : 0.004 s
% 0.13/0.38  # Total time               : 0.032 s
% 0.13/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------

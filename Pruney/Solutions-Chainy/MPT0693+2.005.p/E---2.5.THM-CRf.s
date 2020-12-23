%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:54:55 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 313 expanded)
%              Number of clauses        :   33 ( 135 expanded)
%              Number of leaves         :   13 (  87 expanded)
%              Depth                    :   10
%              Number of atoms          :  100 ( 433 expanded)
%              Number of equality atoms :   52 ( 308 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t43_funct_1,axiom,(
    ! [X1,X2] : k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) = k6_relat_1(k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t148_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => k9_relat_1(X2,k10_relat_1(X2,X1)) = k3_xboole_0(X1,k9_relat_1(X2,k1_relat_1(X2))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(t146_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(t144_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k9_relat_1(X2,X1),k2_relat_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(t168_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(X2,X1) = k10_relat_1(X2,k3_xboole_0(k2_relat_1(X2),X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

fof(t160_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k2_relat_1(k5_relat_1(X1,X2)) = k9_relat_1(X2,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

fof(t147_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r1_tarski(X1,k2_relat_1(X2))
       => k9_relat_1(X2,k10_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(c_0_13,plain,(
    ! [X11,X12] : k1_setfam_1(k2_tarski(X11,X12)) = k3_xboole_0(X11,X12) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_14,plain,(
    ! [X6,X7] : k1_enumset1(X6,X6,X7) = k2_tarski(X6,X7) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_15,plain,(
    ! [X24,X25] : k5_relat_1(k6_relat_1(X25),k6_relat_1(X24)) = k6_relat_1(k3_xboole_0(X24,X25)) ),
    inference(variable_rename,[status(thm)],[t43_funct_1])).

cnf(c_0_16,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,plain,(
    ! [X8,X9,X10] : k2_enumset1(X8,X8,X9,X10) = k1_enumset1(X8,X9,X10) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => k9_relat_1(X2,k10_relat_1(X2,X1)) = k3_xboole_0(X1,k9_relat_1(X2,k1_relat_1(X2))) ) ),
    inference(assume_negation,[status(cth)],[t148_funct_1])).

fof(c_0_20,plain,(
    ! [X20] :
      ( k1_relat_1(k6_relat_1(X20)) = X20
      & k2_relat_1(k6_relat_1(X20)) = X20 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

cnf(c_0_21,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(k3_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_24,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v1_funct_1(esk2_0)
    & k9_relat_1(esk2_0,k10_relat_1(esk2_0,esk1_0)) != k3_xboole_0(esk1_0,k9_relat_1(esk2_0,k1_relat_1(esk2_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

cnf(c_0_25,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(k1_setfam_1(k2_enumset1(X2,X2,X2,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_22]),c_0_23])).

cnf(c_0_27,negated_conjecture,
    ( k9_relat_1(esk2_0,k10_relat_1(esk2_0,esk1_0)) != k3_xboole_0(esk1_0,k9_relat_1(esk2_0,k1_relat_1(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_28,plain,(
    ! [X15] :
      ( ~ v1_relat_1(X15)
      | k9_relat_1(X15,k1_relat_1(X15)) = k2_relat_1(X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).

fof(c_0_29,plain,(
    ! [X13,X14] :
      ( ~ v1_relat_1(X14)
      | r1_tarski(k9_relat_1(X14,X13),k2_relat_1(X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t144_relat_1])])).

fof(c_0_30,plain,(
    ! [X21] :
      ( v1_relat_1(k6_relat_1(X21))
      & v1_funct_1(k6_relat_1(X21)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

fof(c_0_31,plain,(
    ! [X18,X19] :
      ( ~ v1_relat_1(X19)
      | k10_relat_1(X19,X18) = k10_relat_1(X19,k3_xboole_0(k2_relat_1(X19),X18)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t168_relat_1])])).

cnf(c_0_32,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) = k2_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_33,plain,(
    ! [X16,X17] :
      ( ~ v1_relat_1(X16)
      | ~ v1_relat_1(X17)
      | k2_relat_1(k5_relat_1(X16,X17)) = k9_relat_1(X17,k2_relat_1(X16)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t160_relat_1])])])).

cnf(c_0_34,negated_conjecture,
    ( k9_relat_1(esk2_0,k10_relat_1(esk2_0,esk1_0)) != k1_setfam_1(k2_enumset1(esk1_0,esk1_0,esk1_0,k9_relat_1(esk2_0,k1_relat_1(esk2_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_22]),c_0_23])).

cnf(c_0_35,plain,
    ( k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_37,plain,(
    ! [X22,X23] :
      ( ~ v1_relat_1(X23)
      | ~ v1_funct_1(X23)
      | ~ r1_tarski(X22,k2_relat_1(X23))
      | k9_relat_1(X23,k10_relat_1(X23,X22)) = X22 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t147_funct_1])])).

cnf(c_0_38,plain,
    ( r1_tarski(k9_relat_1(X1,X2),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,plain,
    ( k10_relat_1(X1,X2) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,plain,
    ( k6_relat_1(k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) ),
    inference(rw,[status(thm)],[c_0_26,c_0_32])).

cnf(c_0_42,plain,
    ( k2_relat_1(k5_relat_1(X1,X2)) = k9_relat_1(X2,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_43,plain,(
    ! [X4,X5] : k2_tarski(X4,X5) = k2_tarski(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_44,negated_conjecture,
    ( k1_setfam_1(k2_enumset1(esk1_0,esk1_0,esk1_0,k2_relat_1(esk2_0))) != k9_relat_1(esk2_0,k10_relat_1(esk2_0,esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])])).

cnf(c_0_45,plain,
    ( k9_relat_1(X1,k10_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(X2,k2_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_46,plain,
    ( r1_tarski(k9_relat_1(k6_relat_1(X1),X2),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_25]),c_0_39])])).

cnf(c_0_47,plain,
    ( k10_relat_1(X1,X2) = k10_relat_1(X1,k1_setfam_1(k2_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),X2)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_22]),c_0_23])).

cnf(c_0_48,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(k9_relat_1(k6_relat_1(X2),X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_25]),c_0_39]),c_0_39])])).

cnf(c_0_49,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_50,negated_conjecture,
    ( k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(esk2_0)),k6_relat_1(esk1_0))) != k9_relat_1(esk2_0,k10_relat_1(esk2_0,esk1_0)) ),
    inference(rw,[status(thm)],[c_0_44,c_0_32])).

cnf(c_0_51,plain,
    ( k9_relat_1(X1,k10_relat_1(X1,k9_relat_1(k6_relat_1(k2_relat_1(X1)),X2))) = k9_relat_1(k6_relat_1(k2_relat_1(X1)),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_52,plain,
    ( k10_relat_1(X1,k9_relat_1(k6_relat_1(k2_relat_1(X1)),X2)) = k10_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_32]),c_0_48]),c_0_25])).

cnf(c_0_53,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) = k9_relat_1(k6_relat_1(X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_48]),c_0_25])).

cnf(c_0_54,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k2_enumset1(X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_17]),c_0_17]),c_0_23]),c_0_23])).

cnf(c_0_55,negated_conjecture,
    ( k9_relat_1(esk2_0,k10_relat_1(esk2_0,esk1_0)) != k9_relat_1(k6_relat_1(esk1_0),k2_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_42]),c_0_25]),c_0_39]),c_0_39])])).

cnf(c_0_56,plain,
    ( k9_relat_1(X1,k10_relat_1(X1,X2)) = k9_relat_1(k6_relat_1(k2_relat_1(X1)),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_57,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_58,plain,
    ( k9_relat_1(k6_relat_1(X1),X2) = k9_relat_1(k6_relat_1(X2),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_32]),c_0_48]),c_0_25])).

cnf(c_0_59,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57]),c_0_36])]),c_0_58]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:26:49 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.12/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.027 s
% 0.12/0.37  # Presaturation interreduction done
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.12/0.37  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.12/0.37  fof(t43_funct_1, axiom, ![X1, X2]:k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))=k6_relat_1(k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 0.12/0.37  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.12/0.37  fof(t148_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>k9_relat_1(X2,k10_relat_1(X2,X1))=k3_xboole_0(X1,k9_relat_1(X2,k1_relat_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_funct_1)).
% 0.12/0.37  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 0.12/0.37  fof(t146_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 0.12/0.37  fof(t144_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k9_relat_1(X2,X1),k2_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 0.12/0.37  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 0.12/0.37  fof(t168_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k10_relat_1(X2,X1)=k10_relat_1(X2,k3_xboole_0(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t168_relat_1)).
% 0.12/0.37  fof(t160_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k2_relat_1(k5_relat_1(X1,X2))=k9_relat_1(X2,k2_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_relat_1)).
% 0.12/0.37  fof(t147_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(X1,k2_relat_1(X2))=>k9_relat_1(X2,k10_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 0.12/0.37  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.12/0.37  fof(c_0_13, plain, ![X11, X12]:k1_setfam_1(k2_tarski(X11,X12))=k3_xboole_0(X11,X12), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.12/0.37  fof(c_0_14, plain, ![X6, X7]:k1_enumset1(X6,X6,X7)=k2_tarski(X6,X7), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.12/0.37  fof(c_0_15, plain, ![X24, X25]:k5_relat_1(k6_relat_1(X25),k6_relat_1(X24))=k6_relat_1(k3_xboole_0(X24,X25)), inference(variable_rename,[status(thm)],[t43_funct_1])).
% 0.12/0.37  cnf(c_0_16, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.37  cnf(c_0_17, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.37  fof(c_0_18, plain, ![X8, X9, X10]:k2_enumset1(X8,X8,X9,X10)=k1_enumset1(X8,X9,X10), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.12/0.37  fof(c_0_19, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>k9_relat_1(X2,k10_relat_1(X2,X1))=k3_xboole_0(X1,k9_relat_1(X2,k1_relat_1(X2))))), inference(assume_negation,[status(cth)],[t148_funct_1])).
% 0.12/0.37  fof(c_0_20, plain, ![X20]:(k1_relat_1(k6_relat_1(X20))=X20&k2_relat_1(k6_relat_1(X20))=X20), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.12/0.37  cnf(c_0_21, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(k3_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.37  cnf(c_0_22, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 0.12/0.37  cnf(c_0_23, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.37  fof(c_0_24, negated_conjecture, ((v1_relat_1(esk2_0)&v1_funct_1(esk2_0))&k9_relat_1(esk2_0,k10_relat_1(esk2_0,esk1_0))!=k3_xboole_0(esk1_0,k9_relat_1(esk2_0,k1_relat_1(esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 0.12/0.37  cnf(c_0_25, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.37  cnf(c_0_26, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(k1_setfam_1(k2_enumset1(X2,X2,X2,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_22]), c_0_23])).
% 0.12/0.37  cnf(c_0_27, negated_conjecture, (k9_relat_1(esk2_0,k10_relat_1(esk2_0,esk1_0))!=k3_xboole_0(esk1_0,k9_relat_1(esk2_0,k1_relat_1(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.12/0.37  fof(c_0_28, plain, ![X15]:(~v1_relat_1(X15)|k9_relat_1(X15,k1_relat_1(X15))=k2_relat_1(X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).
% 0.12/0.37  fof(c_0_29, plain, ![X13, X14]:(~v1_relat_1(X14)|r1_tarski(k9_relat_1(X14,X13),k2_relat_1(X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t144_relat_1])])).
% 0.12/0.37  fof(c_0_30, plain, ![X21]:(v1_relat_1(k6_relat_1(X21))&v1_funct_1(k6_relat_1(X21))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 0.12/0.37  fof(c_0_31, plain, ![X18, X19]:(~v1_relat_1(X19)|k10_relat_1(X19,X18)=k10_relat_1(X19,k3_xboole_0(k2_relat_1(X19),X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t168_relat_1])])).
% 0.12/0.37  cnf(c_0_32, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,X2))=k2_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.12/0.37  fof(c_0_33, plain, ![X16, X17]:(~v1_relat_1(X16)|(~v1_relat_1(X17)|k2_relat_1(k5_relat_1(X16,X17))=k9_relat_1(X17,k2_relat_1(X16)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t160_relat_1])])])).
% 0.12/0.37  cnf(c_0_34, negated_conjecture, (k9_relat_1(esk2_0,k10_relat_1(esk2_0,esk1_0))!=k1_setfam_1(k2_enumset1(esk1_0,esk1_0,esk1_0,k9_relat_1(esk2_0,k1_relat_1(esk2_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_22]), c_0_23])).
% 0.12/0.37  cnf(c_0_35, plain, (k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.12/0.37  cnf(c_0_36, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.12/0.37  fof(c_0_37, plain, ![X22, X23]:(~v1_relat_1(X23)|~v1_funct_1(X23)|(~r1_tarski(X22,k2_relat_1(X23))|k9_relat_1(X23,k10_relat_1(X23,X22))=X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t147_funct_1])])).
% 0.12/0.37  cnf(c_0_38, plain, (r1_tarski(k9_relat_1(X1,X2),k2_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.12/0.37  cnf(c_0_39, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.12/0.37  cnf(c_0_40, plain, (k10_relat_1(X1,X2)=k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.12/0.37  cnf(c_0_41, plain, (k6_relat_1(k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))))=k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))), inference(rw,[status(thm)],[c_0_26, c_0_32])).
% 0.12/0.37  cnf(c_0_42, plain, (k2_relat_1(k5_relat_1(X1,X2))=k9_relat_1(X2,k2_relat_1(X1))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.12/0.37  fof(c_0_43, plain, ![X4, X5]:k2_tarski(X4,X5)=k2_tarski(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.12/0.37  cnf(c_0_44, negated_conjecture, (k1_setfam_1(k2_enumset1(esk1_0,esk1_0,esk1_0,k2_relat_1(esk2_0)))!=k9_relat_1(esk2_0,k10_relat_1(esk2_0,esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])])).
% 0.12/0.37  cnf(c_0_45, plain, (k9_relat_1(X1,k10_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~v1_funct_1(X1)|~r1_tarski(X2,k2_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.12/0.37  cnf(c_0_46, plain, (r1_tarski(k9_relat_1(k6_relat_1(X1),X2),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_25]), c_0_39])])).
% 0.12/0.37  cnf(c_0_47, plain, (k10_relat_1(X1,X2)=k10_relat_1(X1,k1_setfam_1(k2_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),X2)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_22]), c_0_23])).
% 0.12/0.37  cnf(c_0_48, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(k9_relat_1(k6_relat_1(X2),X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_25]), c_0_39]), c_0_39])])).
% 0.12/0.37  cnf(c_0_49, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.12/0.37  cnf(c_0_50, negated_conjecture, (k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(esk2_0)),k6_relat_1(esk1_0)))!=k9_relat_1(esk2_0,k10_relat_1(esk2_0,esk1_0))), inference(rw,[status(thm)],[c_0_44, c_0_32])).
% 0.12/0.37  cnf(c_0_51, plain, (k9_relat_1(X1,k10_relat_1(X1,k9_relat_1(k6_relat_1(k2_relat_1(X1)),X2)))=k9_relat_1(k6_relat_1(k2_relat_1(X1)),X2)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.12/0.37  cnf(c_0_52, plain, (k10_relat_1(X1,k9_relat_1(k6_relat_1(k2_relat_1(X1)),X2))=k10_relat_1(X1,X2)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_32]), c_0_48]), c_0_25])).
% 0.12/0.37  cnf(c_0_53, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,X2))=k9_relat_1(k6_relat_1(X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_48]), c_0_25])).
% 0.12/0.37  cnf(c_0_54, plain, (k2_enumset1(X1,X1,X1,X2)=k2_enumset1(X2,X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_17]), c_0_17]), c_0_23]), c_0_23])).
% 0.12/0.37  cnf(c_0_55, negated_conjecture, (k9_relat_1(esk2_0,k10_relat_1(esk2_0,esk1_0))!=k9_relat_1(k6_relat_1(esk1_0),k2_relat_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_42]), c_0_25]), c_0_39]), c_0_39])])).
% 0.12/0.37  cnf(c_0_56, plain, (k9_relat_1(X1,k10_relat_1(X1,X2))=k9_relat_1(k6_relat_1(k2_relat_1(X1)),X2)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.12/0.37  cnf(c_0_57, negated_conjecture, (v1_funct_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.12/0.37  cnf(c_0_58, plain, (k9_relat_1(k6_relat_1(X1),X2)=k9_relat_1(k6_relat_1(X2),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_32]), c_0_48]), c_0_25])).
% 0.12/0.37  cnf(c_0_59, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57]), c_0_36])]), c_0_58]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 60
% 0.12/0.37  # Proof object clause steps            : 33
% 0.12/0.37  # Proof object formula steps           : 27
% 0.12/0.37  # Proof object conjectures             : 11
% 0.12/0.37  # Proof object clause conjectures      : 8
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 15
% 0.12/0.37  # Proof object initial formulas used   : 13
% 0.12/0.37  # Proof object generating inferences   : 9
% 0.12/0.37  # Proof object simplifying inferences  : 37
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 13
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 17
% 0.12/0.37  # Removed in clause preprocessing      : 3
% 0.12/0.37  # Initial clauses in saturation        : 14
% 0.12/0.37  # Processed clauses                    : 113
% 0.12/0.37  # ...of these trivial                  : 13
% 0.12/0.37  # ...subsumed                          : 31
% 0.12/0.37  # ...remaining for further processing  : 69
% 0.12/0.37  # Other redundant clauses eliminated   : 0
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 0
% 0.12/0.37  # Backward-rewritten                   : 12
% 0.12/0.37  # Generated clauses                    : 310
% 0.12/0.37  # ...of the previous two non-trivial   : 217
% 0.12/0.37  # Contextual simplify-reflections      : 0
% 0.12/0.37  # Paramodulations                      : 310
% 0.12/0.37  # Factorizations                       : 0
% 0.12/0.37  # Equation resolutions                 : 0
% 0.12/0.37  # Propositional unsat checks           : 0
% 0.12/0.37  #    Propositional check models        : 0
% 0.12/0.37  #    Propositional check unsatisfiable : 0
% 0.12/0.37  #    Propositional clauses             : 0
% 0.12/0.37  #    Propositional clauses after purity: 0
% 0.12/0.37  #    Propositional unsat core size     : 0
% 0.12/0.37  #    Propositional preprocessing time  : 0.000
% 0.12/0.37  #    Propositional encoding time       : 0.000
% 0.12/0.37  #    Propositional solver time         : 0.000
% 0.12/0.37  #    Success case prop preproc time    : 0.000
% 0.12/0.37  #    Success case prop encoding time   : 0.000
% 0.12/0.37  #    Success case prop solver time     : 0.000
% 0.12/0.37  # Current number of processed clauses  : 43
% 0.12/0.37  #    Positive orientable unit clauses  : 19
% 0.12/0.37  #    Positive unorientable unit clauses: 2
% 0.12/0.37  #    Negative unit clauses             : 2
% 0.12/0.37  #    Non-unit-clauses                  : 20
% 0.12/0.37  # Current number of unprocessed clauses: 114
% 0.12/0.37  # ...number of literals in the above   : 254
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 29
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 124
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 87
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 24
% 0.12/0.37  # Unit Clause-clause subsumption calls : 2
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 35
% 0.12/0.37  # BW rewrite match successes           : 31
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 5448
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.033 s
% 0.12/0.37  # System time              : 0.004 s
% 0.12/0.37  # Total time               : 0.036 s
% 0.12/0.37  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------

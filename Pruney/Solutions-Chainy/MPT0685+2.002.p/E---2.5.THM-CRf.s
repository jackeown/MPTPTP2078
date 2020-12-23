%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:54:31 EST 2020

% Result     : Theorem 0.10s
% Output     : CNFRefutation 0.10s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 255 expanded)
%              Number of clauses        :   25 ( 110 expanded)
%              Number of leaves         :   11 (  71 expanded)
%              Depth                    :   11
%              Number of atoms          :   70 ( 329 expanded)
%              Number of equality atoms :   45 ( 255 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    5 (   2 average)

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

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(t139_funct_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k10_relat_1(k7_relat_1(X3,X1),X2) = k3_xboole_0(X1,k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

fof(t182_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(t94_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k5_relat_1(k6_relat_1(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t181_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => k10_relat_1(k5_relat_1(X2,X3),X1) = k10_relat_1(X2,k10_relat_1(X3,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t181_relat_1)).

fof(c_0_11,plain,(
    ! [X11,X12] : k1_setfam_1(k2_tarski(X11,X12)) = k3_xboole_0(X11,X12) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_12,plain,(
    ! [X6,X7] : k1_enumset1(X6,X6,X7) = k2_tarski(X6,X7) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_13,plain,(
    ! [X22,X23] : k5_relat_1(k6_relat_1(X23),k6_relat_1(X22)) = k6_relat_1(k3_xboole_0(X22,X23)) ),
    inference(variable_rename,[status(thm)],[t43_funct_1])).

cnf(c_0_14,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X8,X9,X10] : k2_enumset1(X8,X8,X9,X10) = k1_enumset1(X8,X9,X10) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_17,plain,(
    ! [X18] :
      ( k1_relat_1(k6_relat_1(X18)) = X18
      & k2_relat_1(k6_relat_1(X18)) = X18 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

cnf(c_0_18,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(k3_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => k10_relat_1(k7_relat_1(X3,X1),X2) = k3_xboole_0(X1,k10_relat_1(X3,X2)) ) ),
    inference(assume_negation,[status(cth)],[t139_funct_1])).

cnf(c_0_22,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(k1_setfam_1(k2_enumset1(X2,X2,X2,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_19]),c_0_20])).

fof(c_0_24,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & k10_relat_1(k7_relat_1(esk3_0,esk1_0),esk2_0) != k3_xboole_0(esk1_0,k10_relat_1(esk3_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).

cnf(c_0_25,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) = k1_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

fof(c_0_26,plain,(
    ! [X16,X17] :
      ( ~ v1_relat_1(X16)
      | ~ v1_relat_1(X17)
      | k1_relat_1(k5_relat_1(X16,X17)) = k10_relat_1(X16,k1_relat_1(X17)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).

fof(c_0_27,plain,(
    ! [X21] :
      ( v1_relat_1(k6_relat_1(X21))
      & v1_funct_1(k6_relat_1(X21)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

cnf(c_0_28,negated_conjecture,
    ( k10_relat_1(k7_relat_1(esk3_0,esk1_0),esk2_0) != k3_xboole_0(esk1_0,k10_relat_1(esk3_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,plain,
    ( k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) ),
    inference(rw,[status(thm)],[c_0_23,c_0_25])).

cnf(c_0_30,plain,
    ( k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( k10_relat_1(k7_relat_1(esk3_0,esk1_0),esk2_0) != k1_setfam_1(k2_enumset1(esk1_0,esk1_0,esk1_0,k10_relat_1(esk3_0,esk2_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_19]),c_0_20])).

cnf(c_0_33,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(k10_relat_1(k6_relat_1(X1),X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_22]),c_0_31]),c_0_31])])).

fof(c_0_34,plain,(
    ! [X19,X20] :
      ( ~ v1_relat_1(X20)
      | k7_relat_1(X20,X19) = k5_relat_1(k6_relat_1(X19),X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).

fof(c_0_35,plain,(
    ! [X4,X5] : k2_tarski(X4,X5) = k2_tarski(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_36,negated_conjecture,
    ( k10_relat_1(k7_relat_1(esk3_0,esk1_0),esk2_0) != k10_relat_1(k6_relat_1(k10_relat_1(esk3_0,esk2_0)),esk1_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_25]),c_0_33]),c_0_22])).

cnf(c_0_37,plain,
    ( k7_relat_1(X1,X2) = k5_relat_1(k6_relat_1(X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_38,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_39,plain,(
    ! [X13,X14,X15] :
      ( ~ v1_relat_1(X14)
      | ~ v1_relat_1(X15)
      | k10_relat_1(k5_relat_1(X14,X15),X13) = k10_relat_1(X14,k10_relat_1(X15,X13)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t181_relat_1])])])).

cnf(c_0_40,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( k10_relat_1(k5_relat_1(k6_relat_1(esk1_0),esk3_0),esk2_0) != k10_relat_1(k6_relat_1(k10_relat_1(esk3_0,esk2_0)),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38])])).

cnf(c_0_42,plain,
    ( k10_relat_1(k5_relat_1(X1,X2),X3) = k10_relat_1(X1,k10_relat_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_43,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) = k10_relat_1(k6_relat_1(X2),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_33]),c_0_22])).

cnf(c_0_44,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k2_enumset1(X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_15]),c_0_15]),c_0_20]),c_0_20])).

cnf(c_0_45,negated_conjecture,
    ( k10_relat_1(k6_relat_1(k10_relat_1(esk3_0,esk2_0)),esk1_0) != k10_relat_1(k6_relat_1(esk1_0),k10_relat_1(esk3_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_38]),c_0_31])])).

cnf(c_0_46,plain,
    ( k10_relat_1(k6_relat_1(X1),X2) = k10_relat_1(k6_relat_1(X2),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_25]),c_0_33]),c_0_22])).

cnf(c_0_47,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_46])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.10/0.31  % Computer   : n017.cluster.edu
% 0.10/0.31  % Model      : x86_64 x86_64
% 0.10/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.31  % Memory     : 8042.1875MB
% 0.10/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.31  % CPULimit   : 60
% 0.10/0.31  % WCLimit    : 600
% 0.10/0.31  % DateTime   : Tue Dec  1 10:42:16 EST 2020
% 0.10/0.31  % CPUTime    : 
% 0.10/0.31  # Version: 2.5pre002
% 0.10/0.32  # No SInE strategy applied
% 0.10/0.32  # Trying AutoSched0 for 299 seconds
% 0.10/0.33  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.10/0.33  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.10/0.33  #
% 0.10/0.33  # Preprocessing time       : 0.016 s
% 0.10/0.33  # Presaturation interreduction done
% 0.10/0.33  
% 0.10/0.33  # Proof found!
% 0.10/0.33  # SZS status Theorem
% 0.10/0.33  # SZS output start CNFRefutation
% 0.10/0.33  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.10/0.33  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.10/0.33  fof(t43_funct_1, axiom, ![X1, X2]:k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))=k6_relat_1(k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 0.10/0.33  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.10/0.33  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 0.10/0.33  fof(t139_funct_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>k10_relat_1(k7_relat_1(X3,X1),X2)=k3_xboole_0(X1,k10_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 0.10/0.33  fof(t182_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 0.10/0.33  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 0.10/0.33  fof(t94_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k5_relat_1(k6_relat_1(X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 0.10/0.33  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.10/0.33  fof(t181_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>k10_relat_1(k5_relat_1(X2,X3),X1)=k10_relat_1(X2,k10_relat_1(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t181_relat_1)).
% 0.10/0.33  fof(c_0_11, plain, ![X11, X12]:k1_setfam_1(k2_tarski(X11,X12))=k3_xboole_0(X11,X12), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.10/0.33  fof(c_0_12, plain, ![X6, X7]:k1_enumset1(X6,X6,X7)=k2_tarski(X6,X7), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.10/0.33  fof(c_0_13, plain, ![X22, X23]:k5_relat_1(k6_relat_1(X23),k6_relat_1(X22))=k6_relat_1(k3_xboole_0(X22,X23)), inference(variable_rename,[status(thm)],[t43_funct_1])).
% 0.10/0.33  cnf(c_0_14, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.10/0.33  cnf(c_0_15, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.10/0.33  fof(c_0_16, plain, ![X8, X9, X10]:k2_enumset1(X8,X8,X9,X10)=k1_enumset1(X8,X9,X10), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.10/0.33  fof(c_0_17, plain, ![X18]:(k1_relat_1(k6_relat_1(X18))=X18&k2_relat_1(k6_relat_1(X18))=X18), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.10/0.33  cnf(c_0_18, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(k3_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.10/0.33  cnf(c_0_19, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.10/0.33  cnf(c_0_20, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.10/0.33  fof(c_0_21, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>k10_relat_1(k7_relat_1(X3,X1),X2)=k3_xboole_0(X1,k10_relat_1(X3,X2)))), inference(assume_negation,[status(cth)],[t139_funct_1])).
% 0.10/0.33  cnf(c_0_22, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.10/0.33  cnf(c_0_23, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(k1_setfam_1(k2_enumset1(X2,X2,X2,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_19]), c_0_20])).
% 0.10/0.33  fof(c_0_24, negated_conjecture, (v1_relat_1(esk3_0)&k10_relat_1(k7_relat_1(esk3_0,esk1_0),esk2_0)!=k3_xboole_0(esk1_0,k10_relat_1(esk3_0,esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).
% 0.10/0.33  cnf(c_0_25, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,X2))=k1_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.10/0.33  fof(c_0_26, plain, ![X16, X17]:(~v1_relat_1(X16)|(~v1_relat_1(X17)|k1_relat_1(k5_relat_1(X16,X17))=k10_relat_1(X16,k1_relat_1(X17)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).
% 0.10/0.33  fof(c_0_27, plain, ![X21]:(v1_relat_1(k6_relat_1(X21))&v1_funct_1(k6_relat_1(X21))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 0.10/0.33  cnf(c_0_28, negated_conjecture, (k10_relat_1(k7_relat_1(esk3_0,esk1_0),esk2_0)!=k3_xboole_0(esk1_0,k10_relat_1(esk3_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.10/0.33  cnf(c_0_29, plain, (k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))))=k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))), inference(rw,[status(thm)],[c_0_23, c_0_25])).
% 0.10/0.33  cnf(c_0_30, plain, (k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.10/0.33  cnf(c_0_31, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.10/0.33  cnf(c_0_32, negated_conjecture, (k10_relat_1(k7_relat_1(esk3_0,esk1_0),esk2_0)!=k1_setfam_1(k2_enumset1(esk1_0,esk1_0,esk1_0,k10_relat_1(esk3_0,esk2_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_19]), c_0_20])).
% 0.10/0.33  cnf(c_0_33, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(k10_relat_1(k6_relat_1(X1),X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_22]), c_0_31]), c_0_31])])).
% 0.10/0.33  fof(c_0_34, plain, ![X19, X20]:(~v1_relat_1(X20)|k7_relat_1(X20,X19)=k5_relat_1(k6_relat_1(X19),X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).
% 0.10/0.33  fof(c_0_35, plain, ![X4, X5]:k2_tarski(X4,X5)=k2_tarski(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.10/0.33  cnf(c_0_36, negated_conjecture, (k10_relat_1(k7_relat_1(esk3_0,esk1_0),esk2_0)!=k10_relat_1(k6_relat_1(k10_relat_1(esk3_0,esk2_0)),esk1_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_25]), c_0_33]), c_0_22])).
% 0.10/0.33  cnf(c_0_37, plain, (k7_relat_1(X1,X2)=k5_relat_1(k6_relat_1(X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.10/0.33  cnf(c_0_38, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.10/0.33  fof(c_0_39, plain, ![X13, X14, X15]:(~v1_relat_1(X14)|(~v1_relat_1(X15)|k10_relat_1(k5_relat_1(X14,X15),X13)=k10_relat_1(X14,k10_relat_1(X15,X13)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t181_relat_1])])])).
% 0.10/0.33  cnf(c_0_40, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.10/0.33  cnf(c_0_41, negated_conjecture, (k10_relat_1(k5_relat_1(k6_relat_1(esk1_0),esk3_0),esk2_0)!=k10_relat_1(k6_relat_1(k10_relat_1(esk3_0,esk2_0)),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38])])).
% 0.10/0.33  cnf(c_0_42, plain, (k10_relat_1(k5_relat_1(X1,X2),X3)=k10_relat_1(X1,k10_relat_1(X2,X3))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.10/0.33  cnf(c_0_43, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,X2))=k10_relat_1(k6_relat_1(X2),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_33]), c_0_22])).
% 0.10/0.33  cnf(c_0_44, plain, (k2_enumset1(X1,X1,X1,X2)=k2_enumset1(X2,X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_15]), c_0_15]), c_0_20]), c_0_20])).
% 0.10/0.33  cnf(c_0_45, negated_conjecture, (k10_relat_1(k6_relat_1(k10_relat_1(esk3_0,esk2_0)),esk1_0)!=k10_relat_1(k6_relat_1(esk1_0),k10_relat_1(esk3_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_38]), c_0_31])])).
% 0.10/0.33  cnf(c_0_46, plain, (k10_relat_1(k6_relat_1(X1),X2)=k10_relat_1(k6_relat_1(X2),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_25]), c_0_33]), c_0_22])).
% 0.10/0.33  cnf(c_0_47, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_46])]), ['proof']).
% 0.10/0.33  # SZS output end CNFRefutation
% 0.10/0.33  # Proof object total steps             : 48
% 0.10/0.33  # Proof object clause steps            : 25
% 0.10/0.33  # Proof object formula steps           : 23
% 0.10/0.33  # Proof object conjectures             : 10
% 0.10/0.33  # Proof object clause conjectures      : 7
% 0.10/0.33  # Proof object formula conjectures     : 3
% 0.10/0.33  # Proof object initial clauses used    : 12
% 0.10/0.33  # Proof object initial formulas used   : 11
% 0.10/0.33  # Proof object generating inferences   : 5
% 0.10/0.33  # Proof object simplifying inferences  : 29
% 0.10/0.33  # Training examples: 0 positive, 0 negative
% 0.10/0.33  # Parsed axioms                        : 11
% 0.10/0.33  # Removed by relevancy pruning/SinE    : 0
% 0.10/0.33  # Initial clauses                      : 14
% 0.10/0.33  # Removed in clause preprocessing      : 3
% 0.10/0.33  # Initial clauses in saturation        : 11
% 0.10/0.33  # Processed clauses                    : 34
% 0.10/0.33  # ...of these trivial                  : 0
% 0.10/0.33  # ...subsumed                          : 0
% 0.10/0.33  # ...remaining for further processing  : 34
% 0.10/0.33  # Other redundant clauses eliminated   : 0
% 0.10/0.33  # Clauses deleted for lack of memory   : 0
% 0.10/0.33  # Backward-subsumed                    : 0
% 0.10/0.33  # Backward-rewritten                   : 11
% 0.10/0.33  # Generated clauses                    : 40
% 0.10/0.33  # ...of the previous two non-trivial   : 38
% 0.10/0.33  # Contextual simplify-reflections      : 0
% 0.10/0.33  # Paramodulations                      : 40
% 0.10/0.33  # Factorizations                       : 0
% 0.10/0.33  # Equation resolutions                 : 0
% 0.10/0.33  # Propositional unsat checks           : 0
% 0.10/0.33  #    Propositional check models        : 0
% 0.10/0.33  #    Propositional check unsatisfiable : 0
% 0.10/0.33  #    Propositional clauses             : 0
% 0.10/0.33  #    Propositional clauses after purity: 0
% 0.10/0.33  #    Propositional unsat core size     : 0
% 0.10/0.33  #    Propositional preprocessing time  : 0.000
% 0.10/0.33  #    Propositional encoding time       : 0.000
% 0.10/0.33  #    Propositional solver time         : 0.000
% 0.10/0.33  #    Success case prop preproc time    : 0.000
% 0.10/0.33  #    Success case prop encoding time   : 0.000
% 0.10/0.33  #    Success case prop solver time     : 0.000
% 0.10/0.33  # Current number of processed clauses  : 12
% 0.10/0.33  #    Positive orientable unit clauses  : 7
% 0.10/0.33  #    Positive unorientable unit clauses: 2
% 0.10/0.33  #    Negative unit clauses             : 0
% 0.10/0.33  #    Non-unit-clauses                  : 3
% 0.10/0.33  # Current number of unprocessed clauses: 26
% 0.10/0.33  # ...number of literals in the above   : 26
% 0.10/0.33  # Current number of archived formulas  : 0
% 0.10/0.33  # Current number of archived clauses   : 25
% 0.10/0.33  # Clause-clause subsumption calls (NU) : 0
% 0.10/0.33  # Rec. Clause-clause subsumption calls : 0
% 0.10/0.33  # Non-unit clause-clause subsumptions  : 0
% 0.10/0.33  # Unit Clause-clause subsumption calls : 1
% 0.10/0.33  # Rewrite failures with RHS unbound    : 0
% 0.10/0.33  # BW rewrite match attempts            : 17
% 0.10/0.33  # BW rewrite match successes           : 17
% 0.10/0.33  # Condensation attempts                : 0
% 0.10/0.33  # Condensation successes               : 0
% 0.10/0.33  # Termbank termtop insertions          : 1330
% 0.10/0.33  
% 0.10/0.33  # -------------------------------------------------
% 0.10/0.33  # User time                : 0.018 s
% 0.10/0.33  # System time              : 0.002 s
% 0.10/0.33  # Total time               : 0.020 s
% 0.10/0.33  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------

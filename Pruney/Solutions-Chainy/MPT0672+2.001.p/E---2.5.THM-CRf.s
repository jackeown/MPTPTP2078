%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:54:22 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 195 expanded)
%              Number of clauses        :   29 (  88 expanded)
%              Number of leaves         :    8 (  50 expanded)
%              Depth                    :   13
%              Number of atoms          :   89 ( 390 expanded)
%              Number of equality atoms :   44 ( 186 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t43_funct_1,axiom,(
    ! [X1,X2] : k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) = k6_relat_1(k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t123_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X1,X2) = k5_relat_1(X2,k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(t97_funct_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r1_tarski(X1,X2)
       => ( k8_relat_1(X2,k8_relat_1(X1,X3)) = k8_relat_1(X1,X3)
          & k8_relat_1(X1,k8_relat_1(X2,X3)) = k8_relat_1(X1,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_funct_1)).

fof(t139_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => k8_relat_1(X1,k5_relat_1(X2,X3)) = k5_relat_1(X2,k8_relat_1(X1,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_relat_1)).

fof(c_0_8,plain,(
    ! [X16,X17] : k5_relat_1(k6_relat_1(X17),k6_relat_1(X16)) = k6_relat_1(k3_xboole_0(X16,X17)) ),
    inference(variable_rename,[status(thm)],[t43_funct_1])).

fof(c_0_9,plain,(
    ! [X8,X9] : k1_setfam_1(k2_tarski(X8,X9)) = k3_xboole_0(X8,X9) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_10,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(X4,X5)
      | k3_xboole_0(X4,X5) = X4 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_11,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(k3_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_13,plain,(
    ! [X6,X7] : k2_tarski(X6,X7) = k2_tarski(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_14,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_15,plain,(
    ! [X10,X11] :
      ( ~ v1_relat_1(X11)
      | k8_relat_1(X10,X11) = k5_relat_1(X11,k6_relat_1(X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_relat_1])])).

cnf(c_0_16,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(k1_setfam_1(k2_tarski(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_17,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_18,plain,(
    ! [X15] :
      ( v1_relat_1(k6_relat_1(X15))
      & v1_funct_1(k6_relat_1(X15)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

cnf(c_0_19,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_14,c_0_12])).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => ( r1_tarski(X1,X2)
         => ( k8_relat_1(X2,k8_relat_1(X1,X3)) = k8_relat_1(X1,X3)
            & k8_relat_1(X1,k8_relat_1(X2,X3)) = k8_relat_1(X1,X3) ) ) ) ),
    inference(assume_negation,[status(cth)],[t97_funct_1])).

cnf(c_0_21,plain,
    ( k8_relat_1(X2,X1) = k5_relat_1(X1,k6_relat_1(X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_16])).

cnf(c_0_23,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_19])).

fof(c_0_25,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_funct_1(esk3_0)
    & r1_tarski(esk1_0,esk2_0)
    & ( k8_relat_1(esk2_0,k8_relat_1(esk1_0,esk3_0)) != k8_relat_1(esk1_0,esk3_0)
      | k8_relat_1(esk1_0,k8_relat_1(esk2_0,esk3_0)) != k8_relat_1(esk1_0,esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).

cnf(c_0_26,plain,
    ( k8_relat_1(k1_setfam_1(k2_tarski(X1,X2)),X3) = k5_relat_1(X3,k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)))
    | ~ v1_relat_1(X3) ),
    inference(spm,[status(thm)],[c_0_21,c_0_16])).

cnf(c_0_27,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k8_relat_1(X1,k6_relat_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])])).

fof(c_0_28,plain,(
    ! [X12,X13,X14] :
      ( ~ v1_relat_1(X13)
      | ~ v1_relat_1(X14)
      | k8_relat_1(X12,k5_relat_1(X13,X14)) = k5_relat_1(X13,k8_relat_1(X12,X14)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_relat_1])])])).

cnf(c_0_29,plain,
    ( k8_relat_1(X1,k6_relat_1(X2)) = k6_relat_1(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_24]),c_0_23])])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( k8_relat_1(k1_setfam_1(k2_tarski(X1,X2)),X3) = k5_relat_1(X3,k8_relat_1(X2,k6_relat_1(X1)))
    | ~ v1_relat_1(X3) ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,plain,
    ( k8_relat_1(X3,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X3,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( k8_relat_1(esk1_0,k6_relat_1(esk2_0)) = k6_relat_1(esk1_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_34,plain,
    ( k5_relat_1(X1,k8_relat_1(X2,k6_relat_1(X3))) = k8_relat_1(X3,X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_19])).

cnf(c_0_35,negated_conjecture,
    ( k8_relat_1(esk1_0,k5_relat_1(X1,k6_relat_1(esk2_0))) = k5_relat_1(X1,k6_relat_1(esk1_0))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_23])])).

cnf(c_0_36,plain,
    ( k8_relat_1(X1,k5_relat_1(X2,k6_relat_1(X3))) = k8_relat_1(X3,X2)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X3,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_34]),c_0_23])])).

cnf(c_0_37,negated_conjecture,
    ( k5_relat_1(X1,k6_relat_1(esk1_0)) = k8_relat_1(esk1_0,k8_relat_1(esk2_0,X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_21])).

cnf(c_0_38,negated_conjecture,
    ( k8_relat_1(X1,k8_relat_1(esk1_0,k8_relat_1(esk2_0,X2))) = k8_relat_1(esk1_0,X2)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_39,negated_conjecture,
    ( k8_relat_1(esk2_0,k8_relat_1(esk1_0,k8_relat_1(esk2_0,X1))) = k8_relat_1(esk1_0,X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_30])).

cnf(c_0_40,negated_conjecture,
    ( k8_relat_1(esk1_0,k8_relat_1(esk2_0,X1)) = k8_relat_1(esk1_0,X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( k8_relat_1(esk2_0,k8_relat_1(esk1_0,esk3_0)) != k8_relat_1(esk1_0,esk3_0)
    | k8_relat_1(esk1_0,k8_relat_1(esk2_0,esk3_0)) != k8_relat_1(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_42,negated_conjecture,
    ( k8_relat_1(esk2_0,k8_relat_1(esk1_0,X1)) = k8_relat_1(esk1_0,X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_43,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_44,negated_conjecture,
    ( k8_relat_1(esk1_0,k8_relat_1(esk2_0,esk3_0)) != k8_relat_1(esk1_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])])).

cnf(c_0_45,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_40]),c_0_43])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:31:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.41  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.41  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.41  #
% 0.20/0.41  # Preprocessing time       : 0.049 s
% 0.20/0.41  # Presaturation interreduction done
% 0.20/0.41  
% 0.20/0.41  # Proof found!
% 0.20/0.41  # SZS status Theorem
% 0.20/0.41  # SZS output start CNFRefutation
% 0.20/0.41  fof(t43_funct_1, axiom, ![X1, X2]:k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))=k6_relat_1(k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 0.20/0.41  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.20/0.41  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.20/0.41  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.20/0.41  fof(t123_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k8_relat_1(X1,X2)=k5_relat_1(X2,k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 0.20/0.41  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 0.20/0.41  fof(t97_funct_1, conjecture, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r1_tarski(X1,X2)=>(k8_relat_1(X2,k8_relat_1(X1,X3))=k8_relat_1(X1,X3)&k8_relat_1(X1,k8_relat_1(X2,X3))=k8_relat_1(X1,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_funct_1)).
% 0.20/0.41  fof(t139_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>k8_relat_1(X1,k5_relat_1(X2,X3))=k5_relat_1(X2,k8_relat_1(X1,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_relat_1)).
% 0.20/0.41  fof(c_0_8, plain, ![X16, X17]:k5_relat_1(k6_relat_1(X17),k6_relat_1(X16))=k6_relat_1(k3_xboole_0(X16,X17)), inference(variable_rename,[status(thm)],[t43_funct_1])).
% 0.20/0.41  fof(c_0_9, plain, ![X8, X9]:k1_setfam_1(k2_tarski(X8,X9))=k3_xboole_0(X8,X9), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.20/0.41  fof(c_0_10, plain, ![X4, X5]:(~r1_tarski(X4,X5)|k3_xboole_0(X4,X5)=X4), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.20/0.41  cnf(c_0_11, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(k3_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.41  cnf(c_0_12, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.41  fof(c_0_13, plain, ![X6, X7]:k2_tarski(X6,X7)=k2_tarski(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.20/0.41  cnf(c_0_14, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.41  fof(c_0_15, plain, ![X10, X11]:(~v1_relat_1(X11)|k8_relat_1(X10,X11)=k5_relat_1(X11,k6_relat_1(X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_relat_1])])).
% 0.20/0.41  cnf(c_0_16, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(k1_setfam_1(k2_tarski(X2,X1)))), inference(rw,[status(thm)],[c_0_11, c_0_12])).
% 0.20/0.41  cnf(c_0_17, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.41  fof(c_0_18, plain, ![X15]:(v1_relat_1(k6_relat_1(X15))&v1_funct_1(k6_relat_1(X15))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 0.20/0.41  cnf(c_0_19, plain, (k1_setfam_1(k2_tarski(X1,X2))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_14, c_0_12])).
% 0.20/0.41  fof(c_0_20, negated_conjecture, ~(![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r1_tarski(X1,X2)=>(k8_relat_1(X2,k8_relat_1(X1,X3))=k8_relat_1(X1,X3)&k8_relat_1(X1,k8_relat_1(X2,X3))=k8_relat_1(X1,X3))))), inference(assume_negation,[status(cth)],[t97_funct_1])).
% 0.20/0.41  cnf(c_0_21, plain, (k8_relat_1(X2,X1)=k5_relat_1(X1,k6_relat_1(X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  cnf(c_0_22, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_16])).
% 0.20/0.41  cnf(c_0_23, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.41  cnf(c_0_24, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_16, c_0_19])).
% 0.20/0.41  fof(c_0_25, negated_conjecture, ((v1_relat_1(esk3_0)&v1_funct_1(esk3_0))&(r1_tarski(esk1_0,esk2_0)&(k8_relat_1(esk2_0,k8_relat_1(esk1_0,esk3_0))!=k8_relat_1(esk1_0,esk3_0)|k8_relat_1(esk1_0,k8_relat_1(esk2_0,esk3_0))!=k8_relat_1(esk1_0,esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).
% 0.20/0.41  cnf(c_0_26, plain, (k8_relat_1(k1_setfam_1(k2_tarski(X1,X2)),X3)=k5_relat_1(X3,k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)))|~v1_relat_1(X3)), inference(spm,[status(thm)],[c_0_21, c_0_16])).
% 0.20/0.41  cnf(c_0_27, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k8_relat_1(X1,k6_relat_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])])).
% 0.20/0.41  fof(c_0_28, plain, ![X12, X13, X14]:(~v1_relat_1(X13)|(~v1_relat_1(X14)|k8_relat_1(X12,k5_relat_1(X13,X14))=k5_relat_1(X13,k8_relat_1(X12,X14)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_relat_1])])])).
% 0.20/0.41  cnf(c_0_29, plain, (k8_relat_1(X1,k6_relat_1(X2))=k6_relat_1(X1)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_24]), c_0_23])])).
% 0.20/0.41  cnf(c_0_30, negated_conjecture, (r1_tarski(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.41  cnf(c_0_31, plain, (k8_relat_1(k1_setfam_1(k2_tarski(X1,X2)),X3)=k5_relat_1(X3,k8_relat_1(X2,k6_relat_1(X1)))|~v1_relat_1(X3)), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 0.20/0.41  cnf(c_0_32, plain, (k8_relat_1(X3,k5_relat_1(X1,X2))=k5_relat_1(X1,k8_relat_1(X3,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.41  cnf(c_0_33, negated_conjecture, (k8_relat_1(esk1_0,k6_relat_1(esk2_0))=k6_relat_1(esk1_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.20/0.41  cnf(c_0_34, plain, (k5_relat_1(X1,k8_relat_1(X2,k6_relat_1(X3)))=k8_relat_1(X3,X1)|~v1_relat_1(X1)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_31, c_0_19])).
% 0.20/0.41  cnf(c_0_35, negated_conjecture, (k8_relat_1(esk1_0,k5_relat_1(X1,k6_relat_1(esk2_0)))=k5_relat_1(X1,k6_relat_1(esk1_0))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_23])])).
% 0.20/0.41  cnf(c_0_36, plain, (k8_relat_1(X1,k5_relat_1(X2,k6_relat_1(X3)))=k8_relat_1(X3,X2)|~v1_relat_1(X2)|~r1_tarski(X3,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_34]), c_0_23])])).
% 0.20/0.41  cnf(c_0_37, negated_conjecture, (k5_relat_1(X1,k6_relat_1(esk1_0))=k8_relat_1(esk1_0,k8_relat_1(esk2_0,X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_35, c_0_21])).
% 0.20/0.41  cnf(c_0_38, negated_conjecture, (k8_relat_1(X1,k8_relat_1(esk1_0,k8_relat_1(esk2_0,X2)))=k8_relat_1(esk1_0,X2)|~v1_relat_1(X2)|~r1_tarski(esk1_0,X1)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.20/0.41  cnf(c_0_39, negated_conjecture, (k8_relat_1(esk2_0,k8_relat_1(esk1_0,k8_relat_1(esk2_0,X1)))=k8_relat_1(esk1_0,X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_38, c_0_30])).
% 0.20/0.41  cnf(c_0_40, negated_conjecture, (k8_relat_1(esk1_0,k8_relat_1(esk2_0,X1))=k8_relat_1(esk1_0,X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_21, c_0_37])).
% 0.20/0.41  cnf(c_0_41, negated_conjecture, (k8_relat_1(esk2_0,k8_relat_1(esk1_0,esk3_0))!=k8_relat_1(esk1_0,esk3_0)|k8_relat_1(esk1_0,k8_relat_1(esk2_0,esk3_0))!=k8_relat_1(esk1_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.41  cnf(c_0_42, negated_conjecture, (k8_relat_1(esk2_0,k8_relat_1(esk1_0,X1))=k8_relat_1(esk1_0,X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.20/0.41  cnf(c_0_43, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.41  cnf(c_0_44, negated_conjecture, (k8_relat_1(esk1_0,k8_relat_1(esk2_0,esk3_0))!=k8_relat_1(esk1_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43])])).
% 0.20/0.41  cnf(c_0_45, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_40]), c_0_43])]), ['proof']).
% 0.20/0.41  # SZS output end CNFRefutation
% 0.20/0.41  # Proof object total steps             : 46
% 0.20/0.41  # Proof object clause steps            : 29
% 0.20/0.41  # Proof object formula steps           : 17
% 0.20/0.41  # Proof object conjectures             : 15
% 0.20/0.41  # Proof object clause conjectures      : 12
% 0.20/0.41  # Proof object formula conjectures     : 3
% 0.20/0.41  # Proof object initial clauses used    : 10
% 0.20/0.41  # Proof object initial formulas used   : 8
% 0.20/0.41  # Proof object generating inferences   : 16
% 0.20/0.41  # Proof object simplifying inferences  : 16
% 0.20/0.41  # Training examples: 0 positive, 0 negative
% 0.20/0.41  # Parsed axioms                        : 8
% 0.20/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.41  # Initial clauses                      : 12
% 0.20/0.41  # Removed in clause preprocessing      : 1
% 0.20/0.41  # Initial clauses in saturation        : 11
% 0.20/0.41  # Processed clauses                    : 299
% 0.20/0.41  # ...of these trivial                  : 5
% 0.20/0.41  # ...subsumed                          : 131
% 0.20/0.41  # ...remaining for further processing  : 163
% 0.20/0.41  # Other redundant clauses eliminated   : 0
% 0.20/0.41  # Clauses deleted for lack of memory   : 0
% 0.20/0.41  # Backward-subsumed                    : 7
% 0.20/0.41  # Backward-rewritten                   : 34
% 0.20/0.41  # Generated clauses                    : 1106
% 0.20/0.41  # ...of the previous two non-trivial   : 852
% 0.20/0.41  # Contextual simplify-reflections      : 0
% 0.20/0.41  # Paramodulations                      : 1106
% 0.20/0.41  # Factorizations                       : 0
% 0.20/0.41  # Equation resolutions                 : 0
% 0.20/0.41  # Propositional unsat checks           : 0
% 0.20/0.41  #    Propositional check models        : 0
% 0.20/0.41  #    Propositional check unsatisfiable : 0
% 0.20/0.41  #    Propositional clauses             : 0
% 0.20/0.41  #    Propositional clauses after purity: 0
% 0.20/0.41  #    Propositional unsat core size     : 0
% 0.20/0.41  #    Propositional preprocessing time  : 0.000
% 0.20/0.41  #    Propositional encoding time       : 0.000
% 0.20/0.41  #    Propositional solver time         : 0.000
% 0.20/0.41  #    Success case prop preproc time    : 0.000
% 0.20/0.41  #    Success case prop encoding time   : 0.000
% 0.20/0.41  #    Success case prop solver time     : 0.000
% 0.20/0.41  # Current number of processed clauses  : 111
% 0.20/0.41  #    Positive orientable unit clauses  : 26
% 0.20/0.41  #    Positive unorientable unit clauses: 2
% 0.20/0.41  #    Negative unit clauses             : 1
% 0.20/0.41  #    Non-unit-clauses                  : 82
% 0.20/0.41  # Current number of unprocessed clauses: 514
% 0.20/0.41  # ...number of literals in the above   : 1556
% 0.20/0.41  # Current number of archived formulas  : 0
% 0.20/0.41  # Current number of archived clauses   : 53
% 0.20/0.41  # Clause-clause subsumption calls (NU) : 1912
% 0.20/0.41  # Rec. Clause-clause subsumption calls : 1639
% 0.20/0.41  # Non-unit clause-clause subsumptions  : 120
% 0.20/0.41  # Unit Clause-clause subsumption calls : 12
% 0.20/0.41  # Rewrite failures with RHS unbound    : 0
% 0.20/0.41  # BW rewrite match attempts            : 58
% 0.20/0.41  # BW rewrite match successes           : 39
% 0.20/0.41  # Condensation attempts                : 0
% 0.20/0.41  # Condensation successes               : 0
% 0.20/0.41  # Termbank termtop insertions          : 20355
% 0.20/0.41  
% 0.20/0.41  # -------------------------------------------------
% 0.20/0.41  # User time                : 0.067 s
% 0.20/0.41  # System time              : 0.007 s
% 0.20/0.41  # Total time               : 0.074 s
% 0.20/0.41  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------

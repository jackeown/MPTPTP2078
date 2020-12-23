%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:07:29 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 183 expanded)
%              Number of clauses        :   30 (  80 expanded)
%              Number of leaves         :   12 (  50 expanded)
%              Depth                    :    9
%              Number of atoms          :   90 ( 236 expanded)
%              Number of equality atoms :   37 ( 162 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t19_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t175_funct_2,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( r1_tarski(k10_relat_1(X1,X3),X2)
         => k10_relat_1(X1,X3) = k10_relat_1(k7_relat_1(X1,X2),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).

fof(t139_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k10_relat_1(k7_relat_1(X3,X1),X2) = k3_xboole_0(X1,k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t38_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k4_xboole_0(X2,X1))
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(c_0_12,plain,(
    ! [X24,X25] : k1_setfam_1(k2_tarski(X24,X25)) = k3_xboole_0(X24,X25) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_13,plain,(
    ! [X19,X20] : k1_enumset1(X19,X19,X20) = k2_tarski(X19,X20) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_14,plain,(
    ! [X4,X5,X6] :
      ( ~ r1_tarski(X4,X5)
      | ~ r1_tarski(X4,X6)
      | r1_tarski(X4,k3_xboole_0(X5,X6)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).

cnf(c_0_15,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_17,plain,(
    ! [X21,X22,X23] : k2_enumset1(X21,X21,X22,X23) = k1_enumset1(X21,X22,X23) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_18,plain,(
    ! [X15,X16] : k4_xboole_0(X15,k4_xboole_0(X15,X16)) = k3_xboole_0(X15,X16) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ! [X2,X3] :
            ( r1_tarski(k10_relat_1(X1,X3),X2)
           => k10_relat_1(X1,X3) = k10_relat_1(k7_relat_1(X1,X2),X3) ) ) ),
    inference(assume_negation,[status(cth)],[t175_funct_2])).

fof(c_0_20,plain,(
    ! [X26,X27,X28] :
      ( ~ v1_relat_1(X28)
      | k10_relat_1(k7_relat_1(X28,X26),X27) = k3_xboole_0(X26,k10_relat_1(X28,X27)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_23,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_25,plain,(
    ! [X7,X8,X9] :
      ( ~ r1_tarski(X7,X8)
      | ~ r1_tarski(X8,X9)
      | r1_tarski(X7,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_26,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_funct_1(esk1_0)
    & r1_tarski(k10_relat_1(esk1_0,esk3_0),esk2_0)
    & k10_relat_1(esk1_0,esk3_0) != k10_relat_1(k7_relat_1(esk1_0,esk2_0),esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

fof(c_0_27,plain,(
    ! [X17,X18] : k2_tarski(X17,X18) = k2_tarski(X18,X17) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_28,plain,
    ( k10_relat_1(k7_relat_1(X1,X2),X3) = k3_xboole_0(X2,k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_22]),c_0_23])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_22]),c_0_23])).

fof(c_0_31,plain,(
    ! [X10,X11] : r1_tarski(k4_xboole_0(X10,X11),X10) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk1_0,esk3_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,plain,
    ( k10_relat_1(k7_relat_1(X1,X2),X3) = k1_setfam_1(k2_enumset1(X2,X2,X2,k10_relat_1(X1,X3)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_22]),c_0_23])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_37,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(X1,esk2_0)
    | ~ r1_tarski(X1,k10_relat_1(esk1_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_39,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k2_enumset1(X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_16]),c_0_16]),c_0_23]),c_0_23])).

cnf(c_0_40,plain,
    ( k10_relat_1(k7_relat_1(X1,X2),X3) = k4_xboole_0(X2,k4_xboole_0(X2,k10_relat_1(X1,X3)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_35,c_0_30])).

cnf(c_0_41,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_42,plain,(
    ! [X12,X13] :
      ( ~ r1_tarski(X12,k4_xboole_0(X13,X12))
      | X12 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_xboole_1])])).

cnf(c_0_43,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),k4_xboole_0(X3,k4_xboole_0(X3,X1)))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(k4_xboole_0(k10_relat_1(esk1_0,esk3_0),X1),esk2_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_37])).

cnf(c_0_45,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_39]),c_0_30])).

cnf(c_0_46,negated_conjecture,
    ( k10_relat_1(esk1_0,esk3_0) != k10_relat_1(k7_relat_1(esk1_0,esk2_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_47,negated_conjecture,
    ( k10_relat_1(k7_relat_1(esk1_0,X1),X2) = k4_xboole_0(X1,k4_xboole_0(X1,k10_relat_1(esk1_0,X2))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_48,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(k4_xboole_0(k10_relat_1(esk1_0,esk3_0),X1),k4_xboole_0(k10_relat_1(esk1_0,esk3_0),k4_xboole_0(k10_relat_1(esk1_0,esk3_0),esk2_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])).

fof(c_0_50,plain,(
    ! [X14] : k4_xboole_0(X14,k1_xboole_0) = X14 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_51,negated_conjecture,
    ( k4_xboole_0(k10_relat_1(esk1_0,esk3_0),k4_xboole_0(k10_relat_1(esk1_0,esk3_0),esk2_0)) != k10_relat_1(esk1_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_47]),c_0_45])).

cnf(c_0_52,negated_conjecture,
    ( k4_xboole_0(k10_relat_1(esk1_0,esk3_0),esk2_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_53,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_54,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_52]),c_0_53])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:04:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___107_B00_00_F1_PI_AE_Q4_CS_SP_PS_S064A
% 0.19/0.38  # and selection function SelectComplexG.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.026 s
% 0.19/0.38  # Presaturation interreduction done
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.19/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.38  fof(t19_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(X1,k3_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 0.19/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.38  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.19/0.38  fof(t175_funct_2, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:(r1_tarski(k10_relat_1(X1,X3),X2)=>k10_relat_1(X1,X3)=k10_relat_1(k7_relat_1(X1,X2),X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_funct_2)).
% 0.19/0.38  fof(t139_funct_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k10_relat_1(k7_relat_1(X3,X1),X2)=k3_xboole_0(X1,k10_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 0.19/0.38  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.19/0.38  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.19/0.38  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.19/0.38  fof(t38_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,k4_xboole_0(X2,X1))=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_xboole_1)).
% 0.19/0.38  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 0.19/0.38  fof(c_0_12, plain, ![X24, X25]:k1_setfam_1(k2_tarski(X24,X25))=k3_xboole_0(X24,X25), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.19/0.38  fof(c_0_13, plain, ![X19, X20]:k1_enumset1(X19,X19,X20)=k2_tarski(X19,X20), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.38  fof(c_0_14, plain, ![X4, X5, X6]:(~r1_tarski(X4,X5)|~r1_tarski(X4,X6)|r1_tarski(X4,k3_xboole_0(X5,X6))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).
% 0.19/0.38  cnf(c_0_15, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_16, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  fof(c_0_17, plain, ![X21, X22, X23]:k2_enumset1(X21,X21,X22,X23)=k1_enumset1(X21,X22,X23), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.38  fof(c_0_18, plain, ![X15, X16]:k4_xboole_0(X15,k4_xboole_0(X15,X16))=k3_xboole_0(X15,X16), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.19/0.38  fof(c_0_19, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:(r1_tarski(k10_relat_1(X1,X3),X2)=>k10_relat_1(X1,X3)=k10_relat_1(k7_relat_1(X1,X2),X3)))), inference(assume_negation,[status(cth)],[t175_funct_2])).
% 0.19/0.38  fof(c_0_20, plain, ![X26, X27, X28]:(~v1_relat_1(X28)|k10_relat_1(k7_relat_1(X28,X26),X27)=k3_xboole_0(X26,k10_relat_1(X28,X27))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).
% 0.19/0.38  cnf(c_0_21, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.38  cnf(c_0_22, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 0.19/0.38  cnf(c_0_23, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.38  cnf(c_0_24, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.38  fof(c_0_25, plain, ![X7, X8, X9]:(~r1_tarski(X7,X8)|~r1_tarski(X8,X9)|r1_tarski(X7,X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.19/0.38  fof(c_0_26, negated_conjecture, ((v1_relat_1(esk1_0)&v1_funct_1(esk1_0))&(r1_tarski(k10_relat_1(esk1_0,esk3_0),esk2_0)&k10_relat_1(esk1_0,esk3_0)!=k10_relat_1(k7_relat_1(esk1_0,esk2_0),esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 0.19/0.38  fof(c_0_27, plain, ![X17, X18]:k2_tarski(X17,X18)=k2_tarski(X18,X17), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.19/0.38  cnf(c_0_28, plain, (k10_relat_1(k7_relat_1(X1,X2),X3)=k3_xboole_0(X2,k10_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.38  cnf(c_0_29, plain, (r1_tarski(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))|~r1_tarski(X1,X3)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_22]), c_0_23])).
% 0.19/0.38  cnf(c_0_30, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_setfam_1(k2_enumset1(X1,X1,X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_22]), c_0_23])).
% 0.19/0.38  fof(c_0_31, plain, ![X10, X11]:r1_tarski(k4_xboole_0(X10,X11),X10), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.19/0.38  cnf(c_0_32, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.38  cnf(c_0_33, negated_conjecture, (r1_tarski(k10_relat_1(esk1_0,esk3_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.38  cnf(c_0_34, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.38  cnf(c_0_35, plain, (k10_relat_1(k7_relat_1(X1,X2),X3)=k1_setfam_1(k2_enumset1(X2,X2,X2,k10_relat_1(X1,X3)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_22]), c_0_23])).
% 0.19/0.38  cnf(c_0_36, plain, (r1_tarski(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))|~r1_tarski(X1,X3)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_29, c_0_30])).
% 0.19/0.38  cnf(c_0_37, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.38  cnf(c_0_38, negated_conjecture, (r1_tarski(X1,esk2_0)|~r1_tarski(X1,k10_relat_1(esk1_0,esk3_0))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.19/0.38  cnf(c_0_39, plain, (k2_enumset1(X1,X1,X1,X2)=k2_enumset1(X2,X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_16]), c_0_16]), c_0_23]), c_0_23])).
% 0.19/0.38  cnf(c_0_40, plain, (k10_relat_1(k7_relat_1(X1,X2),X3)=k4_xboole_0(X2,k4_xboole_0(X2,k10_relat_1(X1,X3)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_35, c_0_30])).
% 0.19/0.38  cnf(c_0_41, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.38  fof(c_0_42, plain, ![X12, X13]:(~r1_tarski(X12,k4_xboole_0(X13,X12))|X12=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_xboole_1])])).
% 0.19/0.38  cnf(c_0_43, plain, (r1_tarski(k4_xboole_0(X1,X2),k4_xboole_0(X3,k4_xboole_0(X3,X1)))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.19/0.38  cnf(c_0_44, negated_conjecture, (r1_tarski(k4_xboole_0(k10_relat_1(esk1_0,esk3_0),X1),esk2_0)), inference(spm,[status(thm)],[c_0_38, c_0_37])).
% 0.19/0.38  cnf(c_0_45, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_39]), c_0_30])).
% 0.19/0.38  cnf(c_0_46, negated_conjecture, (k10_relat_1(esk1_0,esk3_0)!=k10_relat_1(k7_relat_1(esk1_0,esk2_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.38  cnf(c_0_47, negated_conjecture, (k10_relat_1(k7_relat_1(esk1_0,X1),X2)=k4_xboole_0(X1,k4_xboole_0(X1,k10_relat_1(esk1_0,X2)))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.19/0.38  cnf(c_0_48, plain, (X1=k1_xboole_0|~r1_tarski(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.38  cnf(c_0_49, negated_conjecture, (r1_tarski(k4_xboole_0(k10_relat_1(esk1_0,esk3_0),X1),k4_xboole_0(k10_relat_1(esk1_0,esk3_0),k4_xboole_0(k10_relat_1(esk1_0,esk3_0),esk2_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45])).
% 0.19/0.38  fof(c_0_50, plain, ![X14]:k4_xboole_0(X14,k1_xboole_0)=X14, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.19/0.38  cnf(c_0_51, negated_conjecture, (k4_xboole_0(k10_relat_1(esk1_0,esk3_0),k4_xboole_0(k10_relat_1(esk1_0,esk3_0),esk2_0))!=k10_relat_1(esk1_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_47]), c_0_45])).
% 0.19/0.38  cnf(c_0_52, negated_conjecture, (k4_xboole_0(k10_relat_1(esk1_0,esk3_0),esk2_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.19/0.38  cnf(c_0_53, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.19/0.38  cnf(c_0_54, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_52]), c_0_53])]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 55
% 0.19/0.38  # Proof object clause steps            : 30
% 0.19/0.38  # Proof object formula steps           : 25
% 0.19/0.38  # Proof object conjectures             : 13
% 0.19/0.38  # Proof object clause conjectures      : 10
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 14
% 0.19/0.38  # Proof object initial formulas used   : 12
% 0.19/0.38  # Proof object generating inferences   : 7
% 0.19/0.38  # Proof object simplifying inferences  : 20
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 12
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 15
% 0.19/0.38  # Removed in clause preprocessing      : 3
% 0.19/0.38  # Initial clauses in saturation        : 12
% 0.19/0.38  # Processed clauses                    : 143
% 0.19/0.38  # ...of these trivial                  : 34
% 0.19/0.38  # ...subsumed                          : 32
% 0.19/0.38  # ...remaining for further processing  : 77
% 0.19/0.38  # Other redundant clauses eliminated   : 0
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 1
% 0.19/0.38  # Backward-rewritten                   : 15
% 0.19/0.38  # Generated clauses                    : 629
% 0.19/0.38  # ...of the previous two non-trivial   : 396
% 0.19/0.38  # Contextual simplify-reflections      : 0
% 0.19/0.38  # Paramodulations                      : 629
% 0.19/0.38  # Factorizations                       : 0
% 0.19/0.38  # Equation resolutions                 : 0
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 49
% 0.19/0.38  #    Positive orientable unit clauses  : 28
% 0.19/0.38  #    Positive unorientable unit clauses: 2
% 0.19/0.38  #    Negative unit clauses             : 0
% 0.19/0.38  #    Non-unit-clauses                  : 19
% 0.19/0.38  # Current number of unprocessed clauses: 253
% 0.19/0.38  # ...number of literals in the above   : 313
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 31
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 263
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 228
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 32
% 0.19/0.38  # Unit Clause-clause subsumption calls : 22
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 88
% 0.19/0.38  # BW rewrite match successes           : 20
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 8167
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.033 s
% 0.19/0.38  # System time              : 0.006 s
% 0.19/0.38  # Total time               : 0.039 s
% 0.19/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------

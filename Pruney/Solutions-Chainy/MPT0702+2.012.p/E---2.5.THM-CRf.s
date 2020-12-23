%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:55:09 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 117 expanded)
%              Number of clauses        :   27 (  44 expanded)
%              Number of leaves         :    9 (  30 expanded)
%              Depth                    :    9
%              Number of atoms          :  103 ( 373 expanded)
%              Number of equality atoms :   25 (  48 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t157_funct_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( ( r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X3,X2))
          & r1_tarski(X1,k1_relat_1(X3))
          & v2_funct_1(X3) )
       => r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_funct_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t146_funct_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(t121_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( v2_funct_1(X3)
       => k9_relat_1(X3,k3_xboole_0(X1,X2)) = k3_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t152_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( v2_funct_1(X2)
       => r1_tarski(k10_relat_1(X2,k9_relat_1(X2,X1)),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => ( ( r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X3,X2))
            & r1_tarski(X1,k1_relat_1(X3))
            & v2_funct_1(X3) )
         => r1_tarski(X1,X2) ) ) ),
    inference(assume_negation,[status(cth)],[t157_funct_1])).

fof(c_0_10,plain,(
    ! [X15,X16] :
      ( ~ r1_tarski(X15,X16)
      | k3_xboole_0(X15,X16) = X15 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_11,plain,(
    ! [X17,X18] : k1_setfam_1(k2_tarski(X17,X18)) = k3_xboole_0(X17,X18) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_12,plain,(
    ! [X22,X23] :
      ( ~ v1_relat_1(X23)
      | ~ r1_tarski(X22,k1_relat_1(X23))
      | r1_tarski(X22,k10_relat_1(X23,k9_relat_1(X23,X22))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_funct_1])])).

fof(c_0_13,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_funct_1(esk3_0)
    & r1_tarski(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk2_0))
    & r1_tarski(esk1_0,k1_relat_1(esk3_0))
    & v2_funct_1(esk3_0)
    & ~ r1_tarski(esk1_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_14,plain,(
    ! [X19,X20,X21] :
      ( ~ v1_relat_1(X21)
      | ~ v1_funct_1(X21)
      | ~ v2_funct_1(X21)
      | k9_relat_1(X21,k3_xboole_0(X19,X20)) = k3_xboole_0(k9_relat_1(X21,X19),k9_relat_1(X21,X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t121_funct_1])])).

cnf(c_0_15,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_17,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | X6 != X7 )
      & ( r1_tarski(X7,X6)
        | X6 != X7 )
      & ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,X6)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_18,plain,
    ( r1_tarski(X2,k10_relat_1(X1,k9_relat_1(X1,X2)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( r1_tarski(esk1_0,k1_relat_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( k9_relat_1(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(esk1_0,k10_relat_1(esk3_0,k9_relat_1(esk3_0,esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])])).

fof(c_0_26,plain,(
    ! [X24,X25] :
      ( ~ v1_relat_1(X25)
      | ~ v1_funct_1(X25)
      | ~ v2_funct_1(X25)
      | r1_tarski(k10_relat_1(X25,k9_relat_1(X25,X24)),X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t152_funct_1])])).

fof(c_0_27,plain,(
    ! [X13,X14] : r1_tarski(k3_xboole_0(X13,X14),X13) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_28,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_29,plain,
    ( k9_relat_1(X1,k1_setfam_1(k2_tarski(X2,X3))) = k1_setfam_1(k2_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,X3)))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_16]),c_0_16])).

cnf(c_0_30,negated_conjecture,
    ( k1_setfam_1(k2_tarski(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk2_0))) = k9_relat_1(esk3_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( v2_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_32,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_33,negated_conjecture,
    ( k10_relat_1(esk3_0,k9_relat_1(esk3_0,esk1_0)) = esk1_0
    | ~ r1_tarski(k10_relat_1(esk3_0,k9_relat_1(esk3_0,esk1_0)),esk1_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_34,plain,
    ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,negated_conjecture,
    ( k9_relat_1(esk3_0,k1_setfam_1(k2_tarski(esk1_0,esk2_0))) = k9_relat_1(esk3_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_32]),c_0_20])])).

cnf(c_0_38,negated_conjecture,
    ( k10_relat_1(esk3_0,k9_relat_1(esk3_0,esk1_0)) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_31]),c_0_32]),c_0_20])])).

cnf(c_0_39,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_35,c_0_16])).

cnf(c_0_40,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k1_setfam_1(k2_tarski(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_16]),c_0_16])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(esk1_0,k1_setfam_1(k2_tarski(esk1_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_37]),c_0_38]),c_0_31]),c_0_32]),c_0_20])])).

cnf(c_0_42,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_43,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk1_0,esk2_0)) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_41]),c_0_39])])).

cnf(c_0_44,negated_conjecture,
    ( ~ r1_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_45,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:37:20 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S4c
% 0.12/0.38  # and selection function SelectCQPrecWNTNp.
% 0.12/0.38  #
% 0.12/0.38  # Preprocessing time       : 0.027 s
% 0.12/0.38  # Presaturation interreduction done
% 0.12/0.38  
% 0.12/0.38  # Proof found!
% 0.12/0.38  # SZS status Theorem
% 0.12/0.38  # SZS output start CNFRefutation
% 0.12/0.38  fof(t157_funct_1, conjecture, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(((r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X3,X2))&r1_tarski(X1,k1_relat_1(X3)))&v2_funct_1(X3))=>r1_tarski(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t157_funct_1)).
% 0.12/0.38  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.12/0.38  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.12/0.38  fof(t146_funct_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 0.12/0.38  fof(t121_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(v2_funct_1(X3)=>k9_relat_1(X3,k3_xboole_0(X1,X2))=k3_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t121_funct_1)).
% 0.12/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.12/0.38  fof(t152_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(v2_funct_1(X2)=>r1_tarski(k10_relat_1(X2,k9_relat_1(X2,X1)),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_funct_1)).
% 0.12/0.38  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.12/0.38  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.12/0.38  fof(c_0_9, negated_conjecture, ~(![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(((r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X3,X2))&r1_tarski(X1,k1_relat_1(X3)))&v2_funct_1(X3))=>r1_tarski(X1,X2)))), inference(assume_negation,[status(cth)],[t157_funct_1])).
% 0.12/0.38  fof(c_0_10, plain, ![X15, X16]:(~r1_tarski(X15,X16)|k3_xboole_0(X15,X16)=X15), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.12/0.38  fof(c_0_11, plain, ![X17, X18]:k1_setfam_1(k2_tarski(X17,X18))=k3_xboole_0(X17,X18), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.12/0.38  fof(c_0_12, plain, ![X22, X23]:(~v1_relat_1(X23)|(~r1_tarski(X22,k1_relat_1(X23))|r1_tarski(X22,k10_relat_1(X23,k9_relat_1(X23,X22))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_funct_1])])).
% 0.12/0.38  fof(c_0_13, negated_conjecture, ((v1_relat_1(esk3_0)&v1_funct_1(esk3_0))&(((r1_tarski(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk2_0))&r1_tarski(esk1_0,k1_relat_1(esk3_0)))&v2_funct_1(esk3_0))&~r1_tarski(esk1_0,esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.12/0.38  fof(c_0_14, plain, ![X19, X20, X21]:(~v1_relat_1(X21)|~v1_funct_1(X21)|(~v2_funct_1(X21)|k9_relat_1(X21,k3_xboole_0(X19,X20))=k3_xboole_0(k9_relat_1(X21,X19),k9_relat_1(X21,X20)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t121_funct_1])])).
% 0.12/0.38  cnf(c_0_15, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.38  cnf(c_0_16, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.38  fof(c_0_17, plain, ![X6, X7]:(((r1_tarski(X6,X7)|X6!=X7)&(r1_tarski(X7,X6)|X6!=X7))&(~r1_tarski(X6,X7)|~r1_tarski(X7,X6)|X6=X7)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.12/0.38  cnf(c_0_18, plain, (r1_tarski(X2,k10_relat_1(X1,k9_relat_1(X1,X2)))|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.38  cnf(c_0_19, negated_conjecture, (r1_tarski(esk1_0,k1_relat_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.38  cnf(c_0_20, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.38  cnf(c_0_21, plain, (k9_relat_1(X1,k3_xboole_0(X2,X3))=k3_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.38  cnf(c_0_22, plain, (k1_setfam_1(k2_tarski(X1,X2))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 0.12/0.38  cnf(c_0_23, negated_conjecture, (r1_tarski(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.38  cnf(c_0_24, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.38  cnf(c_0_25, negated_conjecture, (r1_tarski(esk1_0,k10_relat_1(esk3_0,k9_relat_1(esk3_0,esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20])])).
% 0.12/0.38  fof(c_0_26, plain, ![X24, X25]:(~v1_relat_1(X25)|~v1_funct_1(X25)|(~v2_funct_1(X25)|r1_tarski(k10_relat_1(X25,k9_relat_1(X25,X24)),X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t152_funct_1])])).
% 0.12/0.38  fof(c_0_27, plain, ![X13, X14]:r1_tarski(k3_xboole_0(X13,X14),X13), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.12/0.38  fof(c_0_28, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.12/0.38  cnf(c_0_29, plain, (k9_relat_1(X1,k1_setfam_1(k2_tarski(X2,X3)))=k1_setfam_1(k2_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,X3)))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_16]), c_0_16])).
% 0.12/0.38  cnf(c_0_30, negated_conjecture, (k1_setfam_1(k2_tarski(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk2_0)))=k9_relat_1(esk3_0,esk1_0)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.12/0.38  cnf(c_0_31, negated_conjecture, (v2_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.38  cnf(c_0_32, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.38  cnf(c_0_33, negated_conjecture, (k10_relat_1(esk3_0,k9_relat_1(esk3_0,esk1_0))=esk1_0|~r1_tarski(k10_relat_1(esk3_0,k9_relat_1(esk3_0,esk1_0)),esk1_0)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.12/0.38  cnf(c_0_34, plain, (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X2)),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.12/0.38  cnf(c_0_35, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.12/0.38  cnf(c_0_36, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.12/0.38  cnf(c_0_37, negated_conjecture, (k9_relat_1(esk3_0,k1_setfam_1(k2_tarski(esk1_0,esk2_0)))=k9_relat_1(esk3_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31]), c_0_32]), c_0_20])])).
% 0.12/0.38  cnf(c_0_38, negated_conjecture, (k10_relat_1(esk3_0,k9_relat_1(esk3_0,esk1_0))=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_31]), c_0_32]), c_0_20])])).
% 0.12/0.38  cnf(c_0_39, plain, (r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_35, c_0_16])).
% 0.12/0.38  cnf(c_0_40, plain, (k1_setfam_1(k2_tarski(X1,X2))=k1_setfam_1(k2_tarski(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_16]), c_0_16])).
% 0.12/0.38  cnf(c_0_41, negated_conjecture, (r1_tarski(esk1_0,k1_setfam_1(k2_tarski(esk1_0,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_37]), c_0_38]), c_0_31]), c_0_32]), c_0_20])])).
% 0.12/0.38  cnf(c_0_42, plain, (r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.12/0.38  cnf(c_0_43, negated_conjecture, (k1_setfam_1(k2_tarski(esk1_0,esk2_0))=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_41]), c_0_39])])).
% 0.12/0.38  cnf(c_0_44, negated_conjecture, (~r1_tarski(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.38  cnf(c_0_45, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44]), ['proof']).
% 0.12/0.38  # SZS output end CNFRefutation
% 0.12/0.38  # Proof object total steps             : 46
% 0.12/0.38  # Proof object clause steps            : 27
% 0.12/0.38  # Proof object formula steps           : 19
% 0.12/0.38  # Proof object conjectures             : 17
% 0.12/0.38  # Proof object clause conjectures      : 14
% 0.12/0.38  # Proof object formula conjectures     : 3
% 0.12/0.38  # Proof object initial clauses used    : 14
% 0.12/0.38  # Proof object initial formulas used   : 9
% 0.12/0.38  # Proof object generating inferences   : 9
% 0.12/0.38  # Proof object simplifying inferences  : 24
% 0.12/0.38  # Training examples: 0 positive, 0 negative
% 0.12/0.38  # Parsed axioms                        : 11
% 0.12/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.38  # Initial clauses                      : 18
% 0.12/0.38  # Removed in clause preprocessing      : 1
% 0.12/0.38  # Initial clauses in saturation        : 17
% 0.12/0.38  # Processed clauses                    : 64
% 0.12/0.38  # ...of these trivial                  : 1
% 0.12/0.38  # ...subsumed                          : 4
% 0.12/0.38  # ...remaining for further processing  : 59
% 0.12/0.38  # Other redundant clauses eliminated   : 2
% 0.12/0.38  # Clauses deleted for lack of memory   : 0
% 0.12/0.38  # Backward-subsumed                    : 0
% 0.12/0.38  # Backward-rewritten                   : 4
% 0.12/0.38  # Generated clauses                    : 110
% 0.12/0.38  # ...of the previous two non-trivial   : 80
% 0.12/0.38  # Contextual simplify-reflections      : 0
% 0.12/0.38  # Paramodulations                      : 108
% 0.12/0.38  # Factorizations                       : 0
% 0.12/0.38  # Equation resolutions                 : 2
% 0.12/0.38  # Propositional unsat checks           : 0
% 0.12/0.38  #    Propositional check models        : 0
% 0.12/0.38  #    Propositional check unsatisfiable : 0
% 0.12/0.38  #    Propositional clauses             : 0
% 0.12/0.38  #    Propositional clauses after purity: 0
% 0.12/0.38  #    Propositional unsat core size     : 0
% 0.12/0.38  #    Propositional preprocessing time  : 0.000
% 0.12/0.38  #    Propositional encoding time       : 0.000
% 0.12/0.38  #    Propositional solver time         : 0.000
% 0.12/0.38  #    Success case prop preproc time    : 0.000
% 0.12/0.38  #    Success case prop encoding time   : 0.000
% 0.12/0.38  #    Success case prop solver time     : 0.000
% 0.12/0.38  # Current number of processed clauses  : 37
% 0.12/0.38  #    Positive orientable unit clauses  : 20
% 0.12/0.38  #    Positive unorientable unit clauses: 1
% 0.12/0.38  #    Negative unit clauses             : 1
% 0.12/0.38  #    Non-unit-clauses                  : 15
% 0.12/0.38  # Current number of unprocessed clauses: 49
% 0.12/0.38  # ...number of literals in the above   : 99
% 0.12/0.38  # Current number of archived formulas  : 0
% 0.12/0.38  # Current number of archived clauses   : 21
% 0.12/0.38  # Clause-clause subsumption calls (NU) : 48
% 0.12/0.38  # Rec. Clause-clause subsumption calls : 35
% 0.12/0.38  # Non-unit clause-clause subsumptions  : 4
% 0.12/0.38  # Unit Clause-clause subsumption calls : 4
% 0.12/0.38  # Rewrite failures with RHS unbound    : 0
% 0.12/0.38  # BW rewrite match attempts            : 22
% 0.12/0.38  # BW rewrite match successes           : 6
% 0.12/0.38  # Condensation attempts                : 0
% 0.12/0.38  # Condensation successes               : 0
% 0.12/0.38  # Termbank termtop insertions          : 2266
% 0.12/0.38  
% 0.12/0.38  # -------------------------------------------------
% 0.12/0.38  # User time                : 0.031 s
% 0.12/0.38  # System time              : 0.003 s
% 0.12/0.38  # Total time               : 0.034 s
% 0.12/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------

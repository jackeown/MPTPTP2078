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
% DateTime   : Thu Dec  3 10:54:45 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   44 (  93 expanded)
%              Number of clauses        :   25 (  39 expanded)
%              Number of leaves         :    9 (  23 expanded)
%              Depth                    :   10
%              Number of atoms          :   68 ( 174 expanded)
%              Number of equality atoms :   22 (  38 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t146_funct_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(t169_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(t167_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

fof(t139_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k10_relat_1(k7_relat_1(X3,X1),X2) = k3_xboole_0(X1,k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X1,k1_relat_1(X2))
         => r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))) ) ) ),
    inference(assume_negation,[status(cth)],[t146_funct_1])).

fof(c_0_10,plain,(
    ! [X20,X21] :
      ( ~ v1_relat_1(X20)
      | v1_relat_1(k7_relat_1(X20,X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

fof(c_0_11,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & r1_tarski(esk1_0,k1_relat_1(esk2_0))
    & ~ r1_tarski(esk1_0,k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_12,plain,(
    ! [X22,X23] :
      ( ~ v1_relat_1(X23)
      | k2_relat_1(k7_relat_1(X23,X22)) = k9_relat_1(X23,X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

fof(c_0_13,plain,(
    ! [X26] :
      ( ~ v1_relat_1(X26)
      | k10_relat_1(X26,k2_relat_1(X26)) = k1_relat_1(X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).

cnf(c_0_14,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,plain,(
    ! [X24,X25] :
      ( ~ v1_relat_1(X25)
      | r1_tarski(k10_relat_1(X25,X24),k1_relat_1(X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).

cnf(c_0_18,plain,
    ( k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( v1_relat_1(k7_relat_1(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk2_0,X1)) = k9_relat_1(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_15])).

fof(c_0_21,plain,(
    ! [X30,X31,X32] :
      ( ~ v1_relat_1(X32)
      | k10_relat_1(k7_relat_1(X32,X30),X31) = k3_xboole_0(X30,k10_relat_1(X32,X31)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).

cnf(c_0_22,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk2_0,X1)) = k10_relat_1(k7_relat_1(esk2_0,X1),k9_relat_1(esk2_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])).

cnf(c_0_24,plain,
    ( k10_relat_1(k7_relat_1(X1,X2),X3) = k3_xboole_0(X2,k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_25,plain,(
    ! [X18,X19] :
      ( ~ r1_tarski(X18,X19)
      | k3_xboole_0(X18,X19) = X18 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_26,negated_conjecture,
    ( r1_tarski(esk1_0,k1_relat_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_27,negated_conjecture,
    ( k1_relat_1(esk2_0) = k10_relat_1(esk2_0,k2_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_15])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(k10_relat_1(k7_relat_1(esk2_0,X1),X2),k10_relat_1(k7_relat_1(esk2_0,X1),k9_relat_1(esk2_0,X1))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_19]),c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( k10_relat_1(k7_relat_1(esk2_0,X1),X2) = k3_xboole_0(X1,k10_relat_1(esk2_0,X2)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_15])).

cnf(c_0_30,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(esk1_0,k10_relat_1(esk2_0,k2_relat_1(esk2_0))) ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

fof(c_0_32,plain,(
    ! [X16,X17] : r1_tarski(k3_xboole_0(X16,X17),X16) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_33,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(k3_xboole_0(X1,k10_relat_1(esk2_0,X2)),k3_xboole_0(X1,k10_relat_1(esk2_0,k9_relat_1(esk2_0,X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_29]),c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( k3_xboole_0(esk1_0,k10_relat_1(esk2_0,k2_relat_1(esk2_0))) = esk1_0 ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_36,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_37,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(esk1_0,k3_xboole_0(esk1_0,k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_39,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_36]),c_0_37])).

cnf(c_0_40,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( k3_xboole_0(esk1_0,k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0))) = esk1_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_38]),c_0_39])).

cnf(c_0_42,negated_conjecture,
    ( ~ r1_tarski(esk1_0,k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_43,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.32  % Computer   : n025.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % WCLimit    : 600
% 0.13/0.32  % DateTime   : Tue Dec  1 10:53:20 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.33  # No SInE strategy applied
% 0.13/0.33  # Trying AutoSched0 for 299 seconds
% 0.13/0.36  # AutoSched0-Mode selected heuristic G_E___208_B01_00_F1_SE_CS_SP_PS_S064A
% 0.13/0.36  # and selection function SelectComplexG.
% 0.13/0.36  #
% 0.13/0.36  # Preprocessing time       : 0.027 s
% 0.13/0.36  # Presaturation interreduction done
% 0.13/0.36  
% 0.13/0.36  # Proof found!
% 0.13/0.36  # SZS status Theorem
% 0.13/0.36  # SZS output start CNFRefutation
% 0.13/0.36  fof(t146_funct_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 0.13/0.36  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.13/0.36  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 0.13/0.36  fof(t169_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 0.13/0.36  fof(t167_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 0.13/0.36  fof(t139_funct_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k10_relat_1(k7_relat_1(X3,X1),X2)=k3_xboole_0(X1,k10_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 0.13/0.36  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.13/0.36  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.13/0.36  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.13/0.36  fof(c_0_9, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1)))))), inference(assume_negation,[status(cth)],[t146_funct_1])).
% 0.13/0.36  fof(c_0_10, plain, ![X20, X21]:(~v1_relat_1(X20)|v1_relat_1(k7_relat_1(X20,X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.13/0.36  fof(c_0_11, negated_conjecture, (v1_relat_1(esk2_0)&(r1_tarski(esk1_0,k1_relat_1(esk2_0))&~r1_tarski(esk1_0,k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.13/0.36  fof(c_0_12, plain, ![X22, X23]:(~v1_relat_1(X23)|k2_relat_1(k7_relat_1(X23,X22))=k9_relat_1(X23,X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.13/0.36  fof(c_0_13, plain, ![X26]:(~v1_relat_1(X26)|k10_relat_1(X26,k2_relat_1(X26))=k1_relat_1(X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).
% 0.13/0.36  cnf(c_0_14, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.36  cnf(c_0_15, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.36  cnf(c_0_16, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.36  fof(c_0_17, plain, ![X24, X25]:(~v1_relat_1(X25)|r1_tarski(k10_relat_1(X25,X24),k1_relat_1(X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).
% 0.13/0.36  cnf(c_0_18, plain, (k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.36  cnf(c_0_19, negated_conjecture, (v1_relat_1(k7_relat_1(esk2_0,X1))), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.13/0.36  cnf(c_0_20, negated_conjecture, (k2_relat_1(k7_relat_1(esk2_0,X1))=k9_relat_1(esk2_0,X1)), inference(spm,[status(thm)],[c_0_16, c_0_15])).
% 0.13/0.36  fof(c_0_21, plain, ![X30, X31, X32]:(~v1_relat_1(X32)|k10_relat_1(k7_relat_1(X32,X30),X31)=k3_xboole_0(X30,k10_relat_1(X32,X31))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).
% 0.13/0.36  cnf(c_0_22, plain, (r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.36  cnf(c_0_23, negated_conjecture, (k1_relat_1(k7_relat_1(esk2_0,X1))=k10_relat_1(k7_relat_1(esk2_0,X1),k9_relat_1(esk2_0,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20])).
% 0.13/0.36  cnf(c_0_24, plain, (k10_relat_1(k7_relat_1(X1,X2),X3)=k3_xboole_0(X2,k10_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.36  fof(c_0_25, plain, ![X18, X19]:(~r1_tarski(X18,X19)|k3_xboole_0(X18,X19)=X18), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.13/0.36  cnf(c_0_26, negated_conjecture, (r1_tarski(esk1_0,k1_relat_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.36  cnf(c_0_27, negated_conjecture, (k1_relat_1(esk2_0)=k10_relat_1(esk2_0,k2_relat_1(esk2_0))), inference(spm,[status(thm)],[c_0_18, c_0_15])).
% 0.13/0.36  cnf(c_0_28, negated_conjecture, (r1_tarski(k10_relat_1(k7_relat_1(esk2_0,X1),X2),k10_relat_1(k7_relat_1(esk2_0,X1),k9_relat_1(esk2_0,X1)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_19]), c_0_23])).
% 0.13/0.36  cnf(c_0_29, negated_conjecture, (k10_relat_1(k7_relat_1(esk2_0,X1),X2)=k3_xboole_0(X1,k10_relat_1(esk2_0,X2))), inference(spm,[status(thm)],[c_0_24, c_0_15])).
% 0.13/0.36  cnf(c_0_30, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.36  cnf(c_0_31, negated_conjecture, (r1_tarski(esk1_0,k10_relat_1(esk2_0,k2_relat_1(esk2_0)))), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 0.13/0.36  fof(c_0_32, plain, ![X16, X17]:r1_tarski(k3_xboole_0(X16,X17),X16), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.13/0.36  fof(c_0_33, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.13/0.36  cnf(c_0_34, negated_conjecture, (r1_tarski(k3_xboole_0(X1,k10_relat_1(esk2_0,X2)),k3_xboole_0(X1,k10_relat_1(esk2_0,k9_relat_1(esk2_0,X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_29]), c_0_29])).
% 0.13/0.36  cnf(c_0_35, negated_conjecture, (k3_xboole_0(esk1_0,k10_relat_1(esk2_0,k2_relat_1(esk2_0)))=esk1_0), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.13/0.36  cnf(c_0_36, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.36  cnf(c_0_37, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.13/0.36  cnf(c_0_38, negated_conjecture, (r1_tarski(esk1_0,k3_xboole_0(esk1_0,k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0))))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.13/0.36  cnf(c_0_39, plain, (k3_xboole_0(X1,k3_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_36]), c_0_37])).
% 0.13/0.36  cnf(c_0_40, plain, (r1_tarski(k3_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.13/0.36  cnf(c_0_41, negated_conjecture, (k3_xboole_0(esk1_0,k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0)))=esk1_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_38]), c_0_39])).
% 0.13/0.36  cnf(c_0_42, negated_conjecture, (~r1_tarski(esk1_0,k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.36  cnf(c_0_43, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42]), ['proof']).
% 0.13/0.36  # SZS output end CNFRefutation
% 0.13/0.36  # Proof object total steps             : 44
% 0.13/0.36  # Proof object clause steps            : 25
% 0.13/0.36  # Proof object formula steps           : 19
% 0.13/0.36  # Proof object conjectures             : 18
% 0.13/0.36  # Proof object clause conjectures      : 15
% 0.13/0.36  # Proof object formula conjectures     : 3
% 0.13/0.36  # Proof object initial clauses used    : 11
% 0.13/0.36  # Proof object initial formulas used   : 9
% 0.13/0.36  # Proof object generating inferences   : 12
% 0.13/0.36  # Proof object simplifying inferences  : 8
% 0.13/0.36  # Training examples: 0 positive, 0 negative
% 0.13/0.36  # Parsed axioms                        : 14
% 0.13/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.36  # Initial clauses                      : 18
% 0.13/0.36  # Removed in clause preprocessing      : 0
% 0.13/0.36  # Initial clauses in saturation        : 18
% 0.13/0.36  # Processed clauses                    : 122
% 0.13/0.36  # ...of these trivial                  : 10
% 0.13/0.36  # ...subsumed                          : 18
% 0.13/0.36  # ...remaining for further processing  : 94
% 0.13/0.36  # Other redundant clauses eliminated   : 2
% 0.13/0.36  # Clauses deleted for lack of memory   : 0
% 0.13/0.36  # Backward-subsumed                    : 0
% 0.13/0.36  # Backward-rewritten                   : 6
% 0.13/0.36  # Generated clauses                    : 365
% 0.13/0.36  # ...of the previous two non-trivial   : 226
% 0.13/0.36  # Contextual simplify-reflections      : 0
% 0.13/0.36  # Paramodulations                      : 363
% 0.13/0.36  # Factorizations                       : 0
% 0.13/0.36  # Equation resolutions                 : 2
% 0.13/0.36  # Propositional unsat checks           : 0
% 0.13/0.36  #    Propositional check models        : 0
% 0.13/0.36  #    Propositional check unsatisfiable : 0
% 0.13/0.36  #    Propositional clauses             : 0
% 0.13/0.36  #    Propositional clauses after purity: 0
% 0.13/0.36  #    Propositional unsat core size     : 0
% 0.13/0.36  #    Propositional preprocessing time  : 0.000
% 0.13/0.36  #    Propositional encoding time       : 0.000
% 0.13/0.36  #    Propositional solver time         : 0.000
% 0.13/0.36  #    Success case prop preproc time    : 0.000
% 0.13/0.36  #    Success case prop encoding time   : 0.000
% 0.13/0.36  #    Success case prop solver time     : 0.000
% 0.13/0.36  # Current number of processed clauses  : 69
% 0.13/0.36  #    Positive orientable unit clauses  : 41
% 0.13/0.36  #    Positive unorientable unit clauses: 1
% 0.13/0.36  #    Negative unit clauses             : 1
% 0.13/0.36  #    Non-unit-clauses                  : 26
% 0.13/0.36  # Current number of unprocessed clauses: 134
% 0.13/0.36  # ...number of literals in the above   : 160
% 0.13/0.36  # Current number of archived formulas  : 0
% 0.13/0.36  # Current number of archived clauses   : 23
% 0.13/0.36  # Clause-clause subsumption calls (NU) : 71
% 0.13/0.36  # Rec. Clause-clause subsumption calls : 68
% 0.13/0.36  # Non-unit clause-clause subsumptions  : 18
% 0.13/0.36  # Unit Clause-clause subsumption calls : 5
% 0.13/0.36  # Rewrite failures with RHS unbound    : 0
% 0.13/0.36  # BW rewrite match attempts            : 22
% 0.13/0.36  # BW rewrite match successes           : 8
% 0.13/0.36  # Condensation attempts                : 0
% 0.13/0.36  # Condensation successes               : 0
% 0.13/0.36  # Termbank termtop insertions          : 4940
% 0.13/0.36  
% 0.13/0.36  # -------------------------------------------------
% 0.13/0.36  # User time                : 0.036 s
% 0.13/0.36  # System time              : 0.001 s
% 0.13/0.36  # Total time               : 0.037 s
% 0.13/0.36  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------

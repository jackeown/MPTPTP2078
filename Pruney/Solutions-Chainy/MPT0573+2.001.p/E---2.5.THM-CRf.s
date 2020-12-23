%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:51:47 EST 2020

% Result     : Theorem 15.96s
% Output     : CNFRefutation 15.96s
% Verified   : 
% Statistics : Number of formulae       :   35 (  49 expanded)
%              Number of clauses        :   18 (  22 expanded)
%              Number of leaves         :    8 (  12 expanded)
%              Depth                    :    8
%              Number of atoms          :   49 (  72 expanded)
%              Number of equality atoms :   28 (  35 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t177_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => r1_tarski(k6_subset_1(k10_relat_1(X3,X1),k10_relat_1(X3,X2)),k10_relat_1(X3,k6_subset_1(X1,X2))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t177_relat_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t175_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k10_relat_1(X3,k2_xboole_0(X1,X2)) = k2_xboole_0(k10_relat_1(X3,X1),k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).

fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => r1_tarski(k6_subset_1(k10_relat_1(X3,X1),k10_relat_1(X3,X2)),k10_relat_1(X3,k6_subset_1(X1,X2))) ) ),
    inference(assume_negation,[status(cth)],[t177_relat_1])).

fof(c_0_9,plain,(
    ! [X7,X8] :
      ( ( k4_xboole_0(X7,X8) != k1_xboole_0
        | r1_tarski(X7,X8) )
      & ( ~ r1_tarski(X7,X8)
        | k4_xboole_0(X7,X8) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_10,plain,(
    ! [X13,X14,X15] : k4_xboole_0(k4_xboole_0(X13,X14),X15) = k4_xboole_0(X13,k2_xboole_0(X14,X15)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

fof(c_0_11,plain,(
    ! [X38,X39,X40] :
      ( ~ v1_relat_1(X40)
      | k10_relat_1(X40,k2_xboole_0(X38,X39)) = k2_xboole_0(k10_relat_1(X40,X38),k10_relat_1(X40,X39)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t175_relat_1])])).

fof(c_0_12,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & ~ r1_tarski(k6_subset_1(k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk2_0)),k10_relat_1(esk3_0,k6_subset_1(esk1_0,esk2_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

cnf(c_0_13,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( k10_relat_1(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,plain,(
    ! [X16,X17] : k4_xboole_0(X16,k2_xboole_0(X16,X17)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

fof(c_0_18,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_19,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | k4_xboole_0(X1,k2_xboole_0(X2,X3)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( k2_xboole_0(k10_relat_1(esk3_0,X1),k10_relat_1(esk3_0,X2)) = k10_relat_1(esk3_0,k2_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_21,plain,(
    ! [X10,X11] : k2_xboole_0(X10,k4_xboole_0(X11,X10)) = k2_xboole_0(X10,X11) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_24,plain,(
    ! [X29,X30] : k6_subset_1(X29,X30) = k4_xboole_0(X29,X30) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(k4_xboole_0(X1,k10_relat_1(esk3_0,X2)),k10_relat_1(esk3_0,X3))
    | k4_xboole_0(X1,k10_relat_1(esk3_0,k2_xboole_0(X2,X3))) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( ~ r1_tarski(k6_subset_1(k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk2_0)),k10_relat_1(esk3_0,k6_subset_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_29,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(k4_xboole_0(X1,k10_relat_1(esk3_0,X2)),k10_relat_1(esk3_0,k4_xboole_0(X3,X2)))
    | k4_xboole_0(X1,k10_relat_1(esk3_0,k2_xboole_0(X2,X3))) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( k4_xboole_0(k10_relat_1(esk3_0,X1),k10_relat_1(esk3_0,k2_xboole_0(X2,X1))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_27,c_0_20])).

cnf(c_0_32,negated_conjecture,
    ( ~ r1_tarski(k4_xboole_0(k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk2_0)),k10_relat_1(esk3_0,k4_xboole_0(esk1_0,esk2_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_29]),c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(k4_xboole_0(k10_relat_1(esk3_0,X1),k10_relat_1(esk3_0,X2)),k10_relat_1(esk3_0,k4_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_34,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_33])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:56:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 15.96/16.15  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S05DN
% 15.96/16.15  # and selection function SelectDivLits.
% 15.96/16.15  #
% 15.96/16.15  # Preprocessing time       : 0.045 s
% 15.96/16.15  # Presaturation interreduction done
% 15.96/16.15  
% 15.96/16.15  # Proof found!
% 15.96/16.15  # SZS status Theorem
% 15.96/16.15  # SZS output start CNFRefutation
% 15.96/16.15  fof(t177_relat_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>r1_tarski(k6_subset_1(k10_relat_1(X3,X1),k10_relat_1(X3,X2)),k10_relat_1(X3,k6_subset_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t177_relat_1)).
% 15.96/16.15  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 15.96/16.15  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 15.96/16.15  fof(t175_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k10_relat_1(X3,k2_xboole_0(X1,X2))=k2_xboole_0(k10_relat_1(X3,X1),k10_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_relat_1)).
% 15.96/16.15  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 15.96/16.15  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 15.96/16.15  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 15.96/16.15  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 15.96/16.15  fof(c_0_8, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>r1_tarski(k6_subset_1(k10_relat_1(X3,X1),k10_relat_1(X3,X2)),k10_relat_1(X3,k6_subset_1(X1,X2))))), inference(assume_negation,[status(cth)],[t177_relat_1])).
% 15.96/16.15  fof(c_0_9, plain, ![X7, X8]:((k4_xboole_0(X7,X8)!=k1_xboole_0|r1_tarski(X7,X8))&(~r1_tarski(X7,X8)|k4_xboole_0(X7,X8)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 15.96/16.15  fof(c_0_10, plain, ![X13, X14, X15]:k4_xboole_0(k4_xboole_0(X13,X14),X15)=k4_xboole_0(X13,k2_xboole_0(X14,X15)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 15.96/16.15  fof(c_0_11, plain, ![X38, X39, X40]:(~v1_relat_1(X40)|k10_relat_1(X40,k2_xboole_0(X38,X39))=k2_xboole_0(k10_relat_1(X40,X38),k10_relat_1(X40,X39))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t175_relat_1])])).
% 15.96/16.15  fof(c_0_12, negated_conjecture, (v1_relat_1(esk3_0)&~r1_tarski(k6_subset_1(k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk2_0)),k10_relat_1(esk3_0,k6_subset_1(esk1_0,esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 15.96/16.15  cnf(c_0_13, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 15.96/16.15  cnf(c_0_14, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 15.96/16.15  cnf(c_0_15, plain, (k10_relat_1(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 15.96/16.15  cnf(c_0_16, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 15.96/16.15  fof(c_0_17, plain, ![X16, X17]:k4_xboole_0(X16,k2_xboole_0(X16,X17))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 15.96/16.15  fof(c_0_18, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 15.96/16.15  cnf(c_0_19, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|k4_xboole_0(X1,k2_xboole_0(X2,X3))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 15.96/16.15  cnf(c_0_20, negated_conjecture, (k2_xboole_0(k10_relat_1(esk3_0,X1),k10_relat_1(esk3_0,X2))=k10_relat_1(esk3_0,k2_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 15.96/16.15  fof(c_0_21, plain, ![X10, X11]:k2_xboole_0(X10,k4_xboole_0(X11,X10))=k2_xboole_0(X10,X11), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 15.96/16.15  cnf(c_0_22, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 15.96/16.15  cnf(c_0_23, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 15.96/16.15  fof(c_0_24, plain, ![X29, X30]:k6_subset_1(X29,X30)=k4_xboole_0(X29,X30), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 15.96/16.15  cnf(c_0_25, negated_conjecture, (r1_tarski(k4_xboole_0(X1,k10_relat_1(esk3_0,X2)),k10_relat_1(esk3_0,X3))|k4_xboole_0(X1,k10_relat_1(esk3_0,k2_xboole_0(X2,X3)))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 15.96/16.15  cnf(c_0_26, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 15.96/16.15  cnf(c_0_27, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 15.96/16.15  cnf(c_0_28, negated_conjecture, (~r1_tarski(k6_subset_1(k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk2_0)),k10_relat_1(esk3_0,k6_subset_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 15.96/16.15  cnf(c_0_29, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 15.96/16.15  cnf(c_0_30, negated_conjecture, (r1_tarski(k4_xboole_0(X1,k10_relat_1(esk3_0,X2)),k10_relat_1(esk3_0,k4_xboole_0(X3,X2)))|k4_xboole_0(X1,k10_relat_1(esk3_0,k2_xboole_0(X2,X3)))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 15.96/16.15  cnf(c_0_31, negated_conjecture, (k4_xboole_0(k10_relat_1(esk3_0,X1),k10_relat_1(esk3_0,k2_xboole_0(X2,X1)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_27, c_0_20])).
% 15.96/16.15  cnf(c_0_32, negated_conjecture, (~r1_tarski(k4_xboole_0(k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk2_0)),k10_relat_1(esk3_0,k4_xboole_0(esk1_0,esk2_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_29]), c_0_29])).
% 15.96/16.15  cnf(c_0_33, negated_conjecture, (r1_tarski(k4_xboole_0(k10_relat_1(esk3_0,X1),k10_relat_1(esk3_0,X2)),k10_relat_1(esk3_0,k4_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 15.96/16.15  cnf(c_0_34, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_33])]), ['proof']).
% 15.96/16.15  # SZS output end CNFRefutation
% 15.96/16.15  # Proof object total steps             : 35
% 15.96/16.15  # Proof object clause steps            : 18
% 15.96/16.15  # Proof object formula steps           : 17
% 15.96/16.15  # Proof object conjectures             : 12
% 15.96/16.15  # Proof object clause conjectures      : 9
% 15.96/16.15  # Proof object formula conjectures     : 3
% 15.96/16.15  # Proof object initial clauses used    : 9
% 15.96/16.15  # Proof object initial formulas used   : 8
% 15.96/16.15  # Proof object generating inferences   : 7
% 15.96/16.15  # Proof object simplifying inferences  : 4
% 15.96/16.15  # Training examples: 0 positive, 0 negative
% 15.96/16.15  # Parsed axioms                        : 21
% 15.96/16.15  # Removed by relevancy pruning/SinE    : 0
% 15.96/16.15  # Initial clauses                      : 25
% 15.96/16.15  # Removed in clause preprocessing      : 2
% 15.96/16.15  # Initial clauses in saturation        : 23
% 15.96/16.15  # Processed clauses                    : 39926
% 15.96/16.15  # ...of these trivial                  : 1358
% 15.96/16.15  # ...subsumed                          : 35361
% 15.96/16.15  # ...remaining for further processing  : 3207
% 15.96/16.15  # Other redundant clauses eliminated   : 4670
% 15.96/16.15  # Clauses deleted for lack of memory   : 0
% 15.96/16.15  # Backward-subsumed                    : 42
% 15.96/16.15  # Backward-rewritten                   : 465
% 15.96/16.15  # Generated clauses                    : 1154496
% 15.96/16.15  # ...of the previous two non-trivial   : 911854
% 15.96/16.15  # Contextual simplify-reflections      : 0
% 15.96/16.15  # Paramodulations                      : 1149781
% 15.96/16.15  # Factorizations                       : 0
% 15.96/16.15  # Equation resolutions                 : 4715
% 15.96/16.15  # Propositional unsat checks           : 0
% 15.96/16.15  #    Propositional check models        : 0
% 15.96/16.15  #    Propositional check unsatisfiable : 0
% 15.96/16.15  #    Propositional clauses             : 0
% 15.96/16.15  #    Propositional clauses after purity: 0
% 15.96/16.15  #    Propositional unsat core size     : 0
% 15.96/16.15  #    Propositional preprocessing time  : 0.000
% 15.96/16.15  #    Propositional encoding time       : 0.000
% 15.96/16.15  #    Propositional solver time         : 0.000
% 15.96/16.15  #    Success case prop preproc time    : 0.000
% 15.96/16.15  #    Success case prop encoding time   : 0.000
% 15.96/16.15  #    Success case prop solver time     : 0.000
% 15.96/16.15  # Current number of processed clauses  : 2676
% 15.96/16.15  #    Positive orientable unit clauses  : 873
% 15.96/16.15  #    Positive unorientable unit clauses: 8
% 15.96/16.15  #    Negative unit clauses             : 0
% 15.96/16.15  #    Non-unit-clauses                  : 1795
% 15.96/16.15  # Current number of unprocessed clauses: 866144
% 15.96/16.15  # ...number of literals in the above   : 1478456
% 15.96/16.15  # Current number of archived formulas  : 0
% 15.96/16.15  # Current number of archived clauses   : 532
% 15.96/16.15  # Clause-clause subsumption calls (NU) : 1081178
% 15.96/16.15  # Rec. Clause-clause subsumption calls : 1056014
% 15.96/16.15  # Non-unit clause-clause subsumptions  : 35127
% 15.96/16.15  # Unit Clause-clause subsumption calls : 6520
% 15.96/16.15  # Rewrite failures with RHS unbound    : 0
% 15.96/16.15  # BW rewrite match attempts            : 27612
% 15.96/16.15  # BW rewrite match successes           : 969
% 15.96/16.15  # Condensation attempts                : 0
% 15.96/16.15  # Condensation successes               : 0
% 15.96/16.15  # Termbank termtop insertions          : 26361675
% 16.02/16.20  
% 16.02/16.20  # -------------------------------------------------
% 16.02/16.20  # User time                : 15.287 s
% 16.02/16.20  # System time              : 0.577 s
% 16.02/16.20  # Total time               : 15.864 s
% 16.02/16.20  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------

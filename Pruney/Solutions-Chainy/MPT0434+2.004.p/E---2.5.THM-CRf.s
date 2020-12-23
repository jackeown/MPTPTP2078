%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:48:09 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   41 (  74 expanded)
%              Number of clauses        :   22 (  31 expanded)
%              Number of leaves         :    9 (  19 expanded)
%              Depth                    :    8
%              Number of atoms          :   67 ( 131 expanded)
%              Number of equality atoms :   22 (  41 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t15_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k6_subset_1(k1_relat_1(X1),k1_relat_1(X2)),k1_relat_1(k6_subset_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_relat_1)).

fof(t13_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k1_relat_1(k2_xboole_0(X1,X2)) = k2_xboole_0(k1_relat_1(X1),k1_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relat_1)).

fof(fc2_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_relat_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(t43_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_xboole_0(X2,X3))
     => r1_tarski(k4_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => r1_tarski(k6_subset_1(k1_relat_1(X1),k1_relat_1(X2)),k1_relat_1(k6_subset_1(X1,X2))) ) ) ),
    inference(assume_negation,[status(cth)],[t15_relat_1])).

fof(c_0_10,plain,(
    ! [X19,X20] :
      ( ~ v1_relat_1(X19)
      | ~ v1_relat_1(X20)
      | k1_relat_1(k2_xboole_0(X19,X20)) = k2_xboole_0(k1_relat_1(X19),k1_relat_1(X20)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_relat_1])])])).

fof(c_0_11,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_relat_1(esk2_0)
    & ~ r1_tarski(k6_subset_1(k1_relat_1(esk1_0),k1_relat_1(esk2_0)),k1_relat_1(k6_subset_1(esk1_0,esk2_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_12,plain,(
    ! [X17,X18] :
      ( ~ v1_relat_1(X17)
      | v1_relat_1(k4_xboole_0(X17,X18)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_relat_1])])).

cnf(c_0_13,plain,
    ( k1_relat_1(k2_xboole_0(X1,X2)) = k2_xboole_0(k1_relat_1(X1),k1_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( v1_relat_1(k4_xboole_0(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_17,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_18,plain,(
    ! [X6,X7] :
      ( ( k4_xboole_0(X6,X7) != k1_xboole_0
        | r1_tarski(X6,X7) )
      & ( ~ r1_tarski(X6,X7)
        | k4_xboole_0(X6,X7) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_19,plain,(
    ! [X13,X14] : k4_xboole_0(X13,k2_xboole_0(X13,X14)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

fof(c_0_20,plain,(
    ! [X10,X11,X12] :
      ( ~ r1_tarski(X10,k2_xboole_0(X11,X12))
      | r1_tarski(k4_xboole_0(X10,X11),X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).

cnf(c_0_21,negated_conjecture,
    ( k2_xboole_0(k1_relat_1(X1),k1_relat_1(esk2_0)) = k1_relat_1(k2_xboole_0(X1,esk2_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( v1_relat_1(k4_xboole_0(esk1_0,X1)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_23,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( k2_xboole_0(k1_relat_1(esk2_0),k1_relat_1(k4_xboole_0(esk1_0,X1))) = k1_relat_1(k2_xboole_0(esk2_0,k4_xboole_0(esk1_0,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23]),c_0_23])).

fof(c_0_28,plain,(
    ! [X8,X9] : k2_xboole_0(X8,k4_xboole_0(X9,X8)) = k2_xboole_0(X8,X9) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

fof(c_0_30,plain,(
    ! [X15,X16] : k6_subset_1(X15,X16) = k4_xboole_0(X15,X16) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(k4_xboole_0(X1,k1_relat_1(esk2_0)),k1_relat_1(k4_xboole_0(esk1_0,X2)))
    | ~ r1_tarski(X1,k1_relat_1(k2_xboole_0(esk2_0,k4_xboole_0(esk1_0,X2)))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_23])).

cnf(c_0_34,negated_conjecture,
    ( k2_xboole_0(k1_relat_1(esk2_0),k1_relat_1(esk1_0)) = k1_relat_1(k2_xboole_0(esk2_0,esk1_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_16]),c_0_23]),c_0_23])).

cnf(c_0_35,negated_conjecture,
    ( ~ r1_tarski(k6_subset_1(k1_relat_1(esk1_0),k1_relat_1(esk2_0)),k1_relat_1(k6_subset_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_36,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(k4_xboole_0(X1,k1_relat_1(esk2_0)),k1_relat_1(k4_xboole_0(esk1_0,esk2_0)))
    | ~ r1_tarski(X1,k1_relat_1(k2_xboole_0(esk2_0,esk1_0))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk1_0),k1_relat_1(k2_xboole_0(esk2_0,esk1_0))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( ~ r1_tarski(k4_xboole_0(k1_relat_1(esk1_0),k1_relat_1(esk2_0)),k1_relat_1(k4_xboole_0(esk1_0,esk2_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36]),c_0_36])).

cnf(c_0_40,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:38:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.18/0.57  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_PS_S0i
% 0.18/0.57  # and selection function SelectDiffNegLit.
% 0.18/0.57  #
% 0.18/0.57  # Preprocessing time       : 0.026 s
% 0.18/0.57  # Presaturation interreduction done
% 0.18/0.57  
% 0.18/0.57  # Proof found!
% 0.18/0.57  # SZS status Theorem
% 0.18/0.57  # SZS output start CNFRefutation
% 0.18/0.57  fof(t15_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k6_subset_1(k1_relat_1(X1),k1_relat_1(X2)),k1_relat_1(k6_subset_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_relat_1)).
% 0.18/0.57  fof(t13_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k1_relat_1(k2_xboole_0(X1,X2))=k2_xboole_0(k1_relat_1(X1),k1_relat_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relat_1)).
% 0.18/0.57  fof(fc2_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k4_xboole_0(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_relat_1)).
% 0.18/0.57  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.18/0.57  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.18/0.57  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 0.18/0.57  fof(t43_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_xboole_0(X2,X3))=>r1_tarski(k4_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 0.18/0.57  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.18/0.57  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 0.18/0.57  fof(c_0_9, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k6_subset_1(k1_relat_1(X1),k1_relat_1(X2)),k1_relat_1(k6_subset_1(X1,X2)))))), inference(assume_negation,[status(cth)],[t15_relat_1])).
% 0.18/0.57  fof(c_0_10, plain, ![X19, X20]:(~v1_relat_1(X19)|(~v1_relat_1(X20)|k1_relat_1(k2_xboole_0(X19,X20))=k2_xboole_0(k1_relat_1(X19),k1_relat_1(X20)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_relat_1])])])).
% 0.18/0.57  fof(c_0_11, negated_conjecture, (v1_relat_1(esk1_0)&(v1_relat_1(esk2_0)&~r1_tarski(k6_subset_1(k1_relat_1(esk1_0),k1_relat_1(esk2_0)),k1_relat_1(k6_subset_1(esk1_0,esk2_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.18/0.57  fof(c_0_12, plain, ![X17, X18]:(~v1_relat_1(X17)|v1_relat_1(k4_xboole_0(X17,X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_relat_1])])).
% 0.18/0.57  cnf(c_0_13, plain, (k1_relat_1(k2_xboole_0(X1,X2))=k2_xboole_0(k1_relat_1(X1),k1_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.57  cnf(c_0_14, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.57  cnf(c_0_15, plain, (v1_relat_1(k4_xboole_0(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.57  cnf(c_0_16, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.57  fof(c_0_17, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.18/0.57  fof(c_0_18, plain, ![X6, X7]:((k4_xboole_0(X6,X7)!=k1_xboole_0|r1_tarski(X6,X7))&(~r1_tarski(X6,X7)|k4_xboole_0(X6,X7)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.18/0.57  fof(c_0_19, plain, ![X13, X14]:k4_xboole_0(X13,k2_xboole_0(X13,X14))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 0.18/0.57  fof(c_0_20, plain, ![X10, X11, X12]:(~r1_tarski(X10,k2_xboole_0(X11,X12))|r1_tarski(k4_xboole_0(X10,X11),X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).
% 0.18/0.57  cnf(c_0_21, negated_conjecture, (k2_xboole_0(k1_relat_1(X1),k1_relat_1(esk2_0))=k1_relat_1(k2_xboole_0(X1,esk2_0))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.18/0.57  cnf(c_0_22, negated_conjecture, (v1_relat_1(k4_xboole_0(esk1_0,X1))), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.18/0.57  cnf(c_0_23, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.18/0.57  cnf(c_0_24, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.18/0.57  cnf(c_0_25, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.18/0.57  cnf(c_0_26, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.57  cnf(c_0_27, negated_conjecture, (k2_xboole_0(k1_relat_1(esk2_0),k1_relat_1(k4_xboole_0(esk1_0,X1)))=k1_relat_1(k2_xboole_0(esk2_0,k4_xboole_0(esk1_0,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23]), c_0_23])).
% 0.18/0.57  fof(c_0_28, plain, ![X8, X9]:k2_xboole_0(X8,k4_xboole_0(X9,X8))=k2_xboole_0(X8,X9), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.18/0.57  cnf(c_0_29, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.18/0.57  fof(c_0_30, plain, ![X15, X16]:k6_subset_1(X15,X16)=k4_xboole_0(X15,X16), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 0.18/0.57  cnf(c_0_31, negated_conjecture, (r1_tarski(k4_xboole_0(X1,k1_relat_1(esk2_0)),k1_relat_1(k4_xboole_0(esk1_0,X2)))|~r1_tarski(X1,k1_relat_1(k2_xboole_0(esk2_0,k4_xboole_0(esk1_0,X2))))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.18/0.57  cnf(c_0_32, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.18/0.57  cnf(c_0_33, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_29, c_0_23])).
% 0.18/0.57  cnf(c_0_34, negated_conjecture, (k2_xboole_0(k1_relat_1(esk2_0),k1_relat_1(esk1_0))=k1_relat_1(k2_xboole_0(esk2_0,esk1_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_16]), c_0_23]), c_0_23])).
% 0.18/0.57  cnf(c_0_35, negated_conjecture, (~r1_tarski(k6_subset_1(k1_relat_1(esk1_0),k1_relat_1(esk2_0)),k1_relat_1(k6_subset_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.57  cnf(c_0_36, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.18/0.57  cnf(c_0_37, negated_conjecture, (r1_tarski(k4_xboole_0(X1,k1_relat_1(esk2_0)),k1_relat_1(k4_xboole_0(esk1_0,esk2_0)))|~r1_tarski(X1,k1_relat_1(k2_xboole_0(esk2_0,esk1_0)))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.18/0.57  cnf(c_0_38, negated_conjecture, (r1_tarski(k1_relat_1(esk1_0),k1_relat_1(k2_xboole_0(esk2_0,esk1_0)))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.18/0.57  cnf(c_0_39, negated_conjecture, (~r1_tarski(k4_xboole_0(k1_relat_1(esk1_0),k1_relat_1(esk2_0)),k1_relat_1(k4_xboole_0(esk1_0,esk2_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_36]), c_0_36])).
% 0.18/0.57  cnf(c_0_40, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39]), ['proof']).
% 0.18/0.57  # SZS output end CNFRefutation
% 0.18/0.57  # Proof object total steps             : 41
% 0.18/0.57  # Proof object clause steps            : 22
% 0.18/0.57  # Proof object formula steps           : 19
% 0.18/0.57  # Proof object conjectures             : 15
% 0.18/0.57  # Proof object clause conjectures      : 12
% 0.18/0.57  # Proof object formula conjectures     : 3
% 0.18/0.57  # Proof object initial clauses used    : 11
% 0.18/0.57  # Proof object initial formulas used   : 9
% 0.18/0.57  # Proof object generating inferences   : 10
% 0.18/0.57  # Proof object simplifying inferences  : 7
% 0.18/0.57  # Training examples: 0 positive, 0 negative
% 0.18/0.57  # Parsed axioms                        : 9
% 0.18/0.57  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.57  # Initial clauses                      : 12
% 0.18/0.57  # Removed in clause preprocessing      : 1
% 0.18/0.57  # Initial clauses in saturation        : 11
% 0.18/0.57  # Processed clauses                    : 1763
% 0.18/0.57  # ...of these trivial                  : 226
% 0.18/0.57  # ...subsumed                          : 542
% 0.18/0.57  # ...remaining for further processing  : 995
% 0.18/0.57  # Other redundant clauses eliminated   : 0
% 0.18/0.57  # Clauses deleted for lack of memory   : 0
% 0.18/0.57  # Backward-subsumed                    : 3
% 0.18/0.57  # Backward-rewritten                   : 63
% 0.18/0.57  # Generated clauses                    : 28363
% 0.18/0.57  # ...of the previous two non-trivial   : 11062
% 0.18/0.57  # Contextual simplify-reflections      : 0
% 0.18/0.57  # Paramodulations                      : 28363
% 0.18/0.57  # Factorizations                       : 0
% 0.18/0.57  # Equation resolutions                 : 0
% 0.18/0.57  # Propositional unsat checks           : 0
% 0.18/0.57  #    Propositional check models        : 0
% 0.18/0.57  #    Propositional check unsatisfiable : 0
% 0.18/0.57  #    Propositional clauses             : 0
% 0.18/0.57  #    Propositional clauses after purity: 0
% 0.18/0.57  #    Propositional unsat core size     : 0
% 0.18/0.57  #    Propositional preprocessing time  : 0.000
% 0.18/0.57  #    Propositional encoding time       : 0.000
% 0.18/0.57  #    Propositional solver time         : 0.000
% 0.18/0.57  #    Success case prop preproc time    : 0.000
% 0.18/0.57  #    Success case prop encoding time   : 0.000
% 0.18/0.57  #    Success case prop solver time     : 0.000
% 0.18/0.57  # Current number of processed clauses  : 918
% 0.18/0.57  #    Positive orientable unit clauses  : 820
% 0.18/0.57  #    Positive unorientable unit clauses: 6
% 0.18/0.57  #    Negative unit clauses             : 1
% 0.18/0.57  #    Non-unit-clauses                  : 91
% 0.18/0.57  # Current number of unprocessed clauses: 9266
% 0.18/0.57  # ...number of literals in the above   : 11411
% 0.18/0.57  # Current number of archived formulas  : 0
% 0.18/0.57  # Current number of archived clauses   : 78
% 0.18/0.57  # Clause-clause subsumption calls (NU) : 6064
% 0.18/0.57  # Rec. Clause-clause subsumption calls : 5924
% 0.18/0.57  # Non-unit clause-clause subsumptions  : 522
% 0.18/0.57  # Unit Clause-clause subsumption calls : 212
% 0.18/0.57  # Rewrite failures with RHS unbound    : 0
% 0.18/0.57  # BW rewrite match attempts            : 8707
% 0.18/0.57  # BW rewrite match successes           : 70
% 0.18/0.57  # Condensation attempts                : 0
% 0.18/0.57  # Condensation successes               : 0
% 0.18/0.57  # Termbank termtop insertions          : 431797
% 0.18/0.57  
% 0.18/0.57  # -------------------------------------------------
% 0.18/0.57  # User time                : 0.222 s
% 0.18/0.57  # System time              : 0.017 s
% 0.18/0.57  # Total time               : 0.239 s
% 0.18/0.57  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------

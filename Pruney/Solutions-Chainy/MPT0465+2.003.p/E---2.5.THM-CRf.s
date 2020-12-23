%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:48:43 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 102 expanded)
%              Number of clauses        :   27 (  43 expanded)
%              Number of leaves         :    9 (  26 expanded)
%              Depth                    :    9
%              Number of atoms          :   80 ( 204 expanded)
%              Number of equality atoms :   22 (  57 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t51_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => k5_relat_1(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_relat_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t53_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => r1_tarski(k6_subset_1(k5_relat_1(X1,X2),k5_relat_1(X1,X3)),k5_relat_1(X1,k6_subset_1(X2,X3))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_relat_1)).

fof(fc2_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_relat_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t43_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_xboole_0(X2,X3))
     => r1_tarski(k4_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(c_0_9,plain,(
    ! [X19,X20,X21] :
      ( ~ v1_relat_1(X19)
      | ~ v1_relat_1(X20)
      | ~ v1_relat_1(X21)
      | k5_relat_1(X19,k2_xboole_0(X20,X21)) = k2_xboole_0(k5_relat_1(X19,X20),k5_relat_1(X19,X21)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t51_relat_1])])])).

fof(c_0_10,plain,(
    ! [X13,X14] : k3_tarski(k2_tarski(X13,X14)) = k2_xboole_0(X13,X14) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ! [X3] :
                ( v1_relat_1(X3)
               => r1_tarski(k6_subset_1(k5_relat_1(X1,X2),k5_relat_1(X1,X3)),k5_relat_1(X1,k6_subset_1(X2,X3))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t53_relat_1])).

cnf(c_0_12,plain,
    ( k5_relat_1(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_relat_1(esk2_0)
    & v1_relat_1(esk3_0)
    & ~ r1_tarski(k6_subset_1(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk3_0)),k5_relat_1(esk1_0,k6_subset_1(esk2_0,esk3_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

fof(c_0_15,plain,(
    ! [X17,X18] :
      ( ~ v1_relat_1(X17)
      | v1_relat_1(k4_xboole_0(X17,X18)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_relat_1])])).

cnf(c_0_16,plain,
    ( k5_relat_1(X1,k3_tarski(k2_tarski(X2,X3))) = k3_tarski(k2_tarski(k5_relat_1(X1,X2),k5_relat_1(X1,X3)))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_12,c_0_13]),c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( v1_relat_1(k4_xboole_0(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_20,plain,(
    ! [X11,X12] : k2_tarski(X11,X12) = k2_tarski(X12,X11) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

fof(c_0_21,plain,(
    ! [X6,X7,X8] :
      ( ~ r1_tarski(X6,k2_xboole_0(X7,X8))
      | r1_tarski(k4_xboole_0(X6,X7),X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).

cnf(c_0_22,negated_conjecture,
    ( k3_tarski(k2_tarski(k5_relat_1(X1,X2),k5_relat_1(X1,esk3_0))) = k5_relat_1(X1,k3_tarski(k2_tarski(X2,esk3_0)))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( v1_relat_1(k4_xboole_0(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_24,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( k3_tarski(k2_tarski(k5_relat_1(X1,esk3_0),k5_relat_1(X1,k4_xboole_0(esk2_0,X2)))) = k5_relat_1(X1,k3_tarski(k2_tarski(esk3_0,k4_xboole_0(esk2_0,X2))))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_24])).

cnf(c_0_27,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_28,plain,(
    ! [X4,X5] : k2_xboole_0(X4,k4_xboole_0(X5,X4)) = k2_xboole_0(X4,X5) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

fof(c_0_29,plain,(
    ! [X9,X10] : r1_tarski(X9,k2_xboole_0(X9,X10)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_30,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k3_tarski(k2_tarski(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_25,c_0_13])).

cnf(c_0_31,negated_conjecture,
    ( k3_tarski(k2_tarski(k5_relat_1(esk1_0,esk3_0),k5_relat_1(esk1_0,k4_xboole_0(esk2_0,X1)))) = k5_relat_1(esk1_0,k3_tarski(k2_tarski(esk3_0,k4_xboole_0(esk2_0,X1)))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( k3_tarski(k2_tarski(k5_relat_1(X1,esk2_0),k5_relat_1(X1,esk3_0))) = k5_relat_1(X1,k3_tarski(k2_tarski(esk2_0,esk3_0)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_19])).

fof(c_0_35,plain,(
    ! [X15,X16] : k6_subset_1(X15,X16) = k4_xboole_0(X15,X16) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(k4_xboole_0(X1,k5_relat_1(esk1_0,esk3_0)),k5_relat_1(esk1_0,k4_xboole_0(esk2_0,X2)))
    | ~ r1_tarski(X1,k5_relat_1(esk1_0,k3_tarski(k2_tarski(esk3_0,k4_xboole_0(esk2_0,X2))))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_37,plain,
    ( k3_tarski(k2_tarski(X1,k4_xboole_0(X2,X1))) = k3_tarski(k2_tarski(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_13]),c_0_13])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_33,c_0_13])).

cnf(c_0_39,negated_conjecture,
    ( k3_tarski(k2_tarski(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk3_0))) = k5_relat_1(esk1_0,k3_tarski(k2_tarski(esk2_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_27])).

cnf(c_0_40,negated_conjecture,
    ( ~ r1_tarski(k6_subset_1(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk3_0)),k5_relat_1(esk1_0,k6_subset_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_41,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(k4_xboole_0(X1,k5_relat_1(esk1_0,esk3_0)),k5_relat_1(esk1_0,k4_xboole_0(esk2_0,esk3_0)))
    | ~ r1_tarski(X1,k5_relat_1(esk1_0,k3_tarski(k2_tarski(esk2_0,esk3_0)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_24])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,k3_tarski(k2_tarski(esk2_0,esk3_0)))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( ~ r1_tarski(k4_xboole_0(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk3_0)),k5_relat_1(esk1_0,k4_xboole_0(esk2_0,esk3_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_41]),c_0_41])).

cnf(c_0_45,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:49:27 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.18/0.54  # AutoSched0-Mode selected heuristic G_E___208_C09_12_F1_SE_CS_SP_PS_S064A
% 0.18/0.54  # and selection function SelectComplexG.
% 0.18/0.54  #
% 0.18/0.54  # Preprocessing time       : 0.026 s
% 0.18/0.54  # Presaturation interreduction done
% 0.18/0.54  
% 0.18/0.54  # Proof found!
% 0.18/0.54  # SZS status Theorem
% 0.18/0.54  # SZS output start CNFRefutation
% 0.18/0.54  fof(t51_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>k5_relat_1(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_relat_1)).
% 0.18/0.54  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.18/0.54  fof(t53_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>r1_tarski(k6_subset_1(k5_relat_1(X1,X2),k5_relat_1(X1,X3)),k5_relat_1(X1,k6_subset_1(X2,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_relat_1)).
% 0.18/0.54  fof(fc2_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k4_xboole_0(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_relat_1)).
% 0.18/0.54  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.18/0.54  fof(t43_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_xboole_0(X2,X3))=>r1_tarski(k4_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 0.18/0.54  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.18/0.54  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.18/0.54  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 0.18/0.54  fof(c_0_9, plain, ![X19, X20, X21]:(~v1_relat_1(X19)|(~v1_relat_1(X20)|(~v1_relat_1(X21)|k5_relat_1(X19,k2_xboole_0(X20,X21))=k2_xboole_0(k5_relat_1(X19,X20),k5_relat_1(X19,X21))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t51_relat_1])])])).
% 0.18/0.54  fof(c_0_10, plain, ![X13, X14]:k3_tarski(k2_tarski(X13,X14))=k2_xboole_0(X13,X14), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.18/0.54  fof(c_0_11, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>r1_tarski(k6_subset_1(k5_relat_1(X1,X2),k5_relat_1(X1,X3)),k5_relat_1(X1,k6_subset_1(X2,X3))))))), inference(assume_negation,[status(cth)],[t53_relat_1])).
% 0.18/0.54  cnf(c_0_12, plain, (k5_relat_1(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.18/0.54  cnf(c_0_13, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.54  fof(c_0_14, negated_conjecture, (v1_relat_1(esk1_0)&(v1_relat_1(esk2_0)&(v1_relat_1(esk3_0)&~r1_tarski(k6_subset_1(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk3_0)),k5_relat_1(esk1_0,k6_subset_1(esk2_0,esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 0.18/0.54  fof(c_0_15, plain, ![X17, X18]:(~v1_relat_1(X17)|v1_relat_1(k4_xboole_0(X17,X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_relat_1])])).
% 0.18/0.54  cnf(c_0_16, plain, (k5_relat_1(X1,k3_tarski(k2_tarski(X2,X3)))=k3_tarski(k2_tarski(k5_relat_1(X1,X2),k5_relat_1(X1,X3)))|~v1_relat_1(X3)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_12, c_0_13]), c_0_13])).
% 0.18/0.54  cnf(c_0_17, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.54  cnf(c_0_18, plain, (v1_relat_1(k4_xboole_0(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.54  cnf(c_0_19, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.54  fof(c_0_20, plain, ![X11, X12]:k2_tarski(X11,X12)=k2_tarski(X12,X11), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.18/0.54  fof(c_0_21, plain, ![X6, X7, X8]:(~r1_tarski(X6,k2_xboole_0(X7,X8))|r1_tarski(k4_xboole_0(X6,X7),X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).
% 0.18/0.54  cnf(c_0_22, negated_conjecture, (k3_tarski(k2_tarski(k5_relat_1(X1,X2),k5_relat_1(X1,esk3_0)))=k5_relat_1(X1,k3_tarski(k2_tarski(X2,esk3_0)))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.18/0.54  cnf(c_0_23, negated_conjecture, (v1_relat_1(k4_xboole_0(esk2_0,X1))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.18/0.54  cnf(c_0_24, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.54  cnf(c_0_25, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.18/0.54  cnf(c_0_26, negated_conjecture, (k3_tarski(k2_tarski(k5_relat_1(X1,esk3_0),k5_relat_1(X1,k4_xboole_0(esk2_0,X2))))=k5_relat_1(X1,k3_tarski(k2_tarski(esk3_0,k4_xboole_0(esk2_0,X2))))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24]), c_0_24])).
% 0.18/0.54  cnf(c_0_27, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.54  fof(c_0_28, plain, ![X4, X5]:k2_xboole_0(X4,k4_xboole_0(X5,X4))=k2_xboole_0(X4,X5), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.18/0.54  fof(c_0_29, plain, ![X9, X10]:r1_tarski(X9,k2_xboole_0(X9,X10)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.18/0.54  cnf(c_0_30, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))), inference(rw,[status(thm)],[c_0_25, c_0_13])).
% 0.18/0.54  cnf(c_0_31, negated_conjecture, (k3_tarski(k2_tarski(k5_relat_1(esk1_0,esk3_0),k5_relat_1(esk1_0,k4_xboole_0(esk2_0,X1))))=k5_relat_1(esk1_0,k3_tarski(k2_tarski(esk3_0,k4_xboole_0(esk2_0,X1))))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.18/0.54  cnf(c_0_32, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.18/0.54  cnf(c_0_33, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.18/0.54  cnf(c_0_34, negated_conjecture, (k3_tarski(k2_tarski(k5_relat_1(X1,esk2_0),k5_relat_1(X1,esk3_0)))=k5_relat_1(X1,k3_tarski(k2_tarski(esk2_0,esk3_0)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_22, c_0_19])).
% 0.18/0.54  fof(c_0_35, plain, ![X15, X16]:k6_subset_1(X15,X16)=k4_xboole_0(X15,X16), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 0.18/0.54  cnf(c_0_36, negated_conjecture, (r1_tarski(k4_xboole_0(X1,k5_relat_1(esk1_0,esk3_0)),k5_relat_1(esk1_0,k4_xboole_0(esk2_0,X2)))|~r1_tarski(X1,k5_relat_1(esk1_0,k3_tarski(k2_tarski(esk3_0,k4_xboole_0(esk2_0,X2)))))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.18/0.54  cnf(c_0_37, plain, (k3_tarski(k2_tarski(X1,k4_xboole_0(X2,X1)))=k3_tarski(k2_tarski(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_13]), c_0_13])).
% 0.18/0.54  cnf(c_0_38, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_33, c_0_13])).
% 0.18/0.54  cnf(c_0_39, negated_conjecture, (k3_tarski(k2_tarski(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk3_0)))=k5_relat_1(esk1_0,k3_tarski(k2_tarski(esk2_0,esk3_0)))), inference(spm,[status(thm)],[c_0_34, c_0_27])).
% 0.18/0.54  cnf(c_0_40, negated_conjecture, (~r1_tarski(k6_subset_1(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk3_0)),k5_relat_1(esk1_0,k6_subset_1(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.54  cnf(c_0_41, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.18/0.54  cnf(c_0_42, negated_conjecture, (r1_tarski(k4_xboole_0(X1,k5_relat_1(esk1_0,esk3_0)),k5_relat_1(esk1_0,k4_xboole_0(esk2_0,esk3_0)))|~r1_tarski(X1,k5_relat_1(esk1_0,k3_tarski(k2_tarski(esk2_0,esk3_0))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_24])).
% 0.18/0.54  cnf(c_0_43, negated_conjecture, (r1_tarski(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,k3_tarski(k2_tarski(esk2_0,esk3_0))))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.18/0.54  cnf(c_0_44, negated_conjecture, (~r1_tarski(k4_xboole_0(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk3_0)),k5_relat_1(esk1_0,k4_xboole_0(esk2_0,esk3_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_41]), c_0_41])).
% 0.18/0.54  cnf(c_0_45, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44]), ['proof']).
% 0.18/0.54  # SZS output end CNFRefutation
% 0.18/0.54  # Proof object total steps             : 46
% 0.18/0.54  # Proof object clause steps            : 27
% 0.18/0.54  # Proof object formula steps           : 19
% 0.18/0.54  # Proof object conjectures             : 18
% 0.18/0.54  # Proof object clause conjectures      : 15
% 0.18/0.54  # Proof object formula conjectures     : 3
% 0.18/0.54  # Proof object initial clauses used    : 12
% 0.18/0.54  # Proof object initial formulas used   : 9
% 0.18/0.54  # Proof object generating inferences   : 10
% 0.18/0.54  # Proof object simplifying inferences  : 12
% 0.18/0.54  # Training examples: 0 positive, 0 negative
% 0.18/0.54  # Parsed axioms                        : 9
% 0.18/0.54  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.54  # Initial clauses                      : 12
% 0.18/0.54  # Removed in clause preprocessing      : 2
% 0.18/0.54  # Initial clauses in saturation        : 10
% 0.18/0.54  # Processed clauses                    : 966
% 0.18/0.54  # ...of these trivial                  : 164
% 0.18/0.54  # ...subsumed                          : 177
% 0.18/0.54  # ...remaining for further processing  : 625
% 0.18/0.54  # Other redundant clauses eliminated   : 0
% 0.18/0.54  # Clauses deleted for lack of memory   : 0
% 0.18/0.54  # Backward-subsumed                    : 0
% 0.18/0.54  # Backward-rewritten                   : 0
% 0.18/0.54  # Generated clauses                    : 16679
% 0.18/0.54  # ...of the previous two non-trivial   : 14687
% 0.18/0.54  # Contextual simplify-reflections      : 0
% 0.18/0.54  # Paramodulations                      : 16679
% 0.18/0.54  # Factorizations                       : 0
% 0.18/0.54  # Equation resolutions                 : 0
% 0.18/0.54  # Propositional unsat checks           : 0
% 0.18/0.54  #    Propositional check models        : 0
% 0.18/0.54  #    Propositional check unsatisfiable : 0
% 0.18/0.54  #    Propositional clauses             : 0
% 0.18/0.54  #    Propositional clauses after purity: 0
% 0.18/0.54  #    Propositional unsat core size     : 0
% 0.18/0.54  #    Propositional preprocessing time  : 0.000
% 0.18/0.54  #    Propositional encoding time       : 0.000
% 0.18/0.54  #    Propositional solver time         : 0.000
% 0.18/0.54  #    Success case prop preproc time    : 0.000
% 0.18/0.54  #    Success case prop encoding time   : 0.000
% 0.18/0.54  #    Success case prop solver time     : 0.000
% 0.18/0.54  # Current number of processed clauses  : 615
% 0.18/0.54  #    Positive orientable unit clauses  : 399
% 0.18/0.54  #    Positive unorientable unit clauses: 1
% 0.18/0.54  #    Negative unit clauses             : 1
% 0.18/0.54  #    Non-unit-clauses                  : 214
% 0.18/0.54  # Current number of unprocessed clauses: 13741
% 0.18/0.54  # ...number of literals in the above   : 15412
% 0.18/0.54  # Current number of archived formulas  : 0
% 0.18/0.54  # Current number of archived clauses   : 12
% 0.18/0.54  # Clause-clause subsumption calls (NU) : 7107
% 0.18/0.54  # Rec. Clause-clause subsumption calls : 7098
% 0.18/0.54  # Non-unit clause-clause subsumptions  : 177
% 0.18/0.54  # Unit Clause-clause subsumption calls : 1659
% 0.18/0.54  # Rewrite failures with RHS unbound    : 0
% 0.18/0.54  # BW rewrite match attempts            : 5616
% 0.18/0.54  # BW rewrite match successes           : 2
% 0.18/0.54  # Condensation attempts                : 0
% 0.18/0.54  # Condensation successes               : 0
% 0.18/0.54  # Termbank termtop insertions          : 437696
% 0.18/0.54  
% 0.18/0.54  # -------------------------------------------------
% 0.18/0.54  # User time                : 0.194 s
% 0.18/0.54  # System time              : 0.015 s
% 0.18/0.54  # Total time               : 0.209 s
% 0.18/0.54  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------

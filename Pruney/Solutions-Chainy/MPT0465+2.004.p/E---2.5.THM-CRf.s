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
% DateTime   : Thu Dec  3 10:48:43 EST 2020

% Result     : Theorem 0.34s
% Output     : CNFRefutation 0.34s
% Verified   : 
% Statistics : Number of formulae       :   39 (  66 expanded)
%              Number of clauses        :   22 (  27 expanded)
%              Number of leaves         :    8 (  16 expanded)
%              Depth                    :   10
%              Number of atoms          :   70 ( 160 expanded)
%              Number of equality atoms :   19 (  25 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(t51_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => k5_relat_1(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_relat_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t43_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_xboole_0(X2,X3))
     => r1_tarski(k4_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ! [X3] :
                ( v1_relat_1(X3)
               => r1_tarski(k6_subset_1(k5_relat_1(X1,X2),k5_relat_1(X1,X3)),k5_relat_1(X1,k6_subset_1(X2,X3))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t53_relat_1])).

fof(c_0_9,plain,(
    ! [X15,X16] :
      ( ~ v1_relat_1(X15)
      | v1_relat_1(k4_xboole_0(X15,X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_relat_1])])).

fof(c_0_10,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_relat_1(esk2_0)
    & v1_relat_1(esk3_0)
    & ~ r1_tarski(k6_subset_1(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk3_0)),k5_relat_1(esk1_0,k6_subset_1(esk2_0,esk3_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_11,plain,(
    ! [X17,X18,X19] :
      ( ~ v1_relat_1(X17)
      | ~ v1_relat_1(X18)
      | ~ v1_relat_1(X19)
      | k5_relat_1(X17,k2_xboole_0(X18,X19)) = k2_xboole_0(k5_relat_1(X17,X18),k5_relat_1(X17,X19)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t51_relat_1])])])).

cnf(c_0_12,plain,
    ( v1_relat_1(k4_xboole_0(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( k5_relat_1(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( v1_relat_1(k4_xboole_0(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_16,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( k5_relat_1(X1,k2_xboole_0(X2,k4_xboole_0(esk2_0,X3))) = k2_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,k4_xboole_0(esk2_0,X3)))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_18,negated_conjecture,
    ( k5_relat_1(X1,k2_xboole_0(X2,esk3_0)) = k2_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,esk3_0))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( k5_relat_1(X1,k2_xboole_0(esk3_0,k4_xboole_0(esk2_0,X2))) = k2_xboole_0(k5_relat_1(X1,esk3_0),k5_relat_1(X1,k4_xboole_0(esk2_0,X2)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_21,plain,(
    ! [X6,X7] : k2_xboole_0(X6,k4_xboole_0(X7,X6)) = k2_xboole_0(X6,X7) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

fof(c_0_22,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_23,negated_conjecture,
    ( k5_relat_1(X1,k2_xboole_0(esk2_0,esk3_0)) = k2_xboole_0(k5_relat_1(X1,esk2_0),k5_relat_1(X1,esk3_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_13])).

fof(c_0_24,plain,(
    ! [X8,X9,X10] :
      ( ~ r1_tarski(X8,k2_xboole_0(X9,X10))
      | r1_tarski(k4_xboole_0(X8,X9),X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).

cnf(c_0_25,negated_conjecture,
    ( k5_relat_1(esk1_0,k2_xboole_0(esk3_0,k4_xboole_0(esk2_0,X1))) = k2_xboole_0(k5_relat_1(esk1_0,esk3_0),k5_relat_1(esk1_0,k4_xboole_0(esk2_0,X1))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( k5_relat_1(esk1_0,k2_xboole_0(esk2_0,esk3_0)) = k2_xboole_0(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_20])).

fof(c_0_29,plain,(
    ! [X13,X14] : k6_subset_1(X13,X14) = k4_xboole_0(X13,X14) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

cnf(c_0_30,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( k2_xboole_0(k5_relat_1(esk1_0,esk3_0),k5_relat_1(esk1_0,k4_xboole_0(esk2_0,esk3_0))) = k2_xboole_0(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28])).

fof(c_0_32,plain,(
    ! [X11,X12] : r1_tarski(X11,k2_xboole_0(X11,X12)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_33,negated_conjecture,
    ( ~ r1_tarski(k6_subset_1(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk3_0)),k5_relat_1(esk1_0,k6_subset_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_34,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(k4_xboole_0(X1,k5_relat_1(esk1_0,esk3_0)),k5_relat_1(esk1_0,k4_xboole_0(esk2_0,esk3_0)))
    | ~ r1_tarski(X1,k2_xboole_0(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( ~ r1_tarski(k4_xboole_0(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk3_0)),k5_relat_1(esk1_0,k4_xboole_0(esk2_0,esk3_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_34]),c_0_34])).

cnf(c_0_38,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:04:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.34/0.52  # AutoSched0-Mode selected heuristic G_E___200_B02_F1_AE_CS_SP_PI_S0S
% 0.34/0.52  # and selection function SelectComplexG.
% 0.34/0.52  #
% 0.34/0.52  # Preprocessing time       : 0.039 s
% 0.34/0.52  
% 0.34/0.52  # Proof found!
% 0.34/0.52  # SZS status Theorem
% 0.34/0.52  # SZS output start CNFRefutation
% 0.34/0.52  fof(t53_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>r1_tarski(k6_subset_1(k5_relat_1(X1,X2),k5_relat_1(X1,X3)),k5_relat_1(X1,k6_subset_1(X2,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_relat_1)).
% 0.34/0.52  fof(fc2_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k4_xboole_0(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_relat_1)).
% 0.34/0.52  fof(t51_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>k5_relat_1(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_relat_1)).
% 0.34/0.52  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.34/0.52  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.34/0.52  fof(t43_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_xboole_0(X2,X3))=>r1_tarski(k4_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 0.34/0.52  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 0.34/0.52  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.34/0.52  fof(c_0_8, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>r1_tarski(k6_subset_1(k5_relat_1(X1,X2),k5_relat_1(X1,X3)),k5_relat_1(X1,k6_subset_1(X2,X3))))))), inference(assume_negation,[status(cth)],[t53_relat_1])).
% 0.34/0.52  fof(c_0_9, plain, ![X15, X16]:(~v1_relat_1(X15)|v1_relat_1(k4_xboole_0(X15,X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_relat_1])])).
% 0.34/0.52  fof(c_0_10, negated_conjecture, (v1_relat_1(esk1_0)&(v1_relat_1(esk2_0)&(v1_relat_1(esk3_0)&~r1_tarski(k6_subset_1(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk3_0)),k5_relat_1(esk1_0,k6_subset_1(esk2_0,esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.34/0.52  fof(c_0_11, plain, ![X17, X18, X19]:(~v1_relat_1(X17)|(~v1_relat_1(X18)|(~v1_relat_1(X19)|k5_relat_1(X17,k2_xboole_0(X18,X19))=k2_xboole_0(k5_relat_1(X17,X18),k5_relat_1(X17,X19))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t51_relat_1])])])).
% 0.34/0.52  cnf(c_0_12, plain, (v1_relat_1(k4_xboole_0(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.34/0.52  cnf(c_0_13, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.34/0.52  cnf(c_0_14, plain, (k5_relat_1(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.34/0.52  cnf(c_0_15, negated_conjecture, (v1_relat_1(k4_xboole_0(esk2_0,X1))), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.34/0.52  cnf(c_0_16, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.34/0.52  cnf(c_0_17, negated_conjecture, (k5_relat_1(X1,k2_xboole_0(X2,k4_xboole_0(esk2_0,X3)))=k2_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,k4_xboole_0(esk2_0,X3)))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.34/0.52  cnf(c_0_18, negated_conjecture, (k5_relat_1(X1,k2_xboole_0(X2,esk3_0))=k2_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,esk3_0))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_14, c_0_16])).
% 0.34/0.52  cnf(c_0_19, negated_conjecture, (k5_relat_1(X1,k2_xboole_0(esk3_0,k4_xboole_0(esk2_0,X2)))=k2_xboole_0(k5_relat_1(X1,esk3_0),k5_relat_1(X1,k4_xboole_0(esk2_0,X2)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_17, c_0_16])).
% 0.34/0.52  cnf(c_0_20, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.34/0.52  fof(c_0_21, plain, ![X6, X7]:k2_xboole_0(X6,k4_xboole_0(X7,X6))=k2_xboole_0(X6,X7), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.34/0.52  fof(c_0_22, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.34/0.52  cnf(c_0_23, negated_conjecture, (k5_relat_1(X1,k2_xboole_0(esk2_0,esk3_0))=k2_xboole_0(k5_relat_1(X1,esk2_0),k5_relat_1(X1,esk3_0))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_18, c_0_13])).
% 0.34/0.52  fof(c_0_24, plain, ![X8, X9, X10]:(~r1_tarski(X8,k2_xboole_0(X9,X10))|r1_tarski(k4_xboole_0(X8,X9),X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).
% 0.34/0.52  cnf(c_0_25, negated_conjecture, (k5_relat_1(esk1_0,k2_xboole_0(esk3_0,k4_xboole_0(esk2_0,X1)))=k2_xboole_0(k5_relat_1(esk1_0,esk3_0),k5_relat_1(esk1_0,k4_xboole_0(esk2_0,X1)))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.34/0.52  cnf(c_0_26, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.34/0.52  cnf(c_0_27, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.34/0.52  cnf(c_0_28, negated_conjecture, (k5_relat_1(esk1_0,k2_xboole_0(esk2_0,esk3_0))=k2_xboole_0(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk3_0))), inference(spm,[status(thm)],[c_0_23, c_0_20])).
% 0.34/0.52  fof(c_0_29, plain, ![X13, X14]:k6_subset_1(X13,X14)=k4_xboole_0(X13,X14), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 0.34/0.52  cnf(c_0_30, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.34/0.52  cnf(c_0_31, negated_conjecture, (k2_xboole_0(k5_relat_1(esk1_0,esk3_0),k5_relat_1(esk1_0,k4_xboole_0(esk2_0,esk3_0)))=k2_xboole_0(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27]), c_0_28])).
% 0.34/0.52  fof(c_0_32, plain, ![X11, X12]:r1_tarski(X11,k2_xboole_0(X11,X12)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.34/0.52  cnf(c_0_33, negated_conjecture, (~r1_tarski(k6_subset_1(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk3_0)),k5_relat_1(esk1_0,k6_subset_1(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.34/0.52  cnf(c_0_34, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.34/0.52  cnf(c_0_35, negated_conjecture, (r1_tarski(k4_xboole_0(X1,k5_relat_1(esk1_0,esk3_0)),k5_relat_1(esk1_0,k4_xboole_0(esk2_0,esk3_0)))|~r1_tarski(X1,k2_xboole_0(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk3_0)))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.34/0.52  cnf(c_0_36, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.34/0.52  cnf(c_0_37, negated_conjecture, (~r1_tarski(k4_xboole_0(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk3_0)),k5_relat_1(esk1_0,k4_xboole_0(esk2_0,esk3_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_34]), c_0_34])).
% 0.34/0.52  cnf(c_0_38, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37]), ['proof']).
% 0.34/0.52  # SZS output end CNFRefutation
% 0.34/0.52  # Proof object total steps             : 39
% 0.34/0.52  # Proof object clause steps            : 22
% 0.34/0.52  # Proof object formula steps           : 17
% 0.34/0.52  # Proof object conjectures             : 18
% 0.34/0.52  # Proof object clause conjectures      : 15
% 0.34/0.52  # Proof object formula conjectures     : 3
% 0.34/0.52  # Proof object initial clauses used    : 11
% 0.34/0.52  # Proof object initial formulas used   : 8
% 0.34/0.52  # Proof object generating inferences   : 10
% 0.34/0.52  # Proof object simplifying inferences  : 5
% 0.34/0.52  # Training examples: 0 positive, 0 negative
% 0.34/0.52  # Parsed axioms                        : 8
% 0.34/0.52  # Removed by relevancy pruning/SinE    : 0
% 0.34/0.52  # Initial clauses                      : 11
% 0.34/0.52  # Removed in clause preprocessing      : 1
% 0.34/0.52  # Initial clauses in saturation        : 10
% 0.34/0.52  # Processed clauses                    : 893
% 0.34/0.52  # ...of these trivial                  : 104
% 0.34/0.52  # ...subsumed                          : 105
% 0.34/0.52  # ...remaining for further processing  : 684
% 0.34/0.52  # Other redundant clauses eliminated   : 0
% 0.34/0.52  # Clauses deleted for lack of memory   : 0
% 0.34/0.52  # Backward-subsumed                    : 0
% 0.34/0.52  # Backward-rewritten                   : 0
% 0.34/0.52  # Generated clauses                    : 9602
% 0.34/0.52  # ...of the previous two non-trivial   : 8821
% 0.34/0.52  # Contextual simplify-reflections      : 0
% 0.34/0.52  # Paramodulations                      : 9602
% 0.34/0.52  # Factorizations                       : 0
% 0.34/0.52  # Equation resolutions                 : 0
% 0.34/0.52  # Propositional unsat checks           : 0
% 0.34/0.52  #    Propositional check models        : 0
% 0.34/0.52  #    Propositional check unsatisfiable : 0
% 0.34/0.52  #    Propositional clauses             : 0
% 0.34/0.52  #    Propositional clauses after purity: 0
% 0.34/0.52  #    Propositional unsat core size     : 0
% 0.34/0.52  #    Propositional preprocessing time  : 0.000
% 0.34/0.52  #    Propositional encoding time       : 0.000
% 0.34/0.52  #    Propositional solver time         : 0.000
% 0.34/0.52  #    Success case prop preproc time    : 0.000
% 0.34/0.52  #    Success case prop encoding time   : 0.000
% 0.34/0.52  #    Success case prop solver time     : 0.000
% 0.34/0.52  # Current number of processed clauses  : 684
% 0.34/0.52  #    Positive orientable unit clauses  : 506
% 0.34/0.52  #    Positive unorientable unit clauses: 1
% 0.34/0.52  #    Negative unit clauses             : 1
% 0.34/0.52  #    Non-unit-clauses                  : 176
% 0.34/0.52  # Current number of unprocessed clauses: 7884
% 0.34/0.52  # ...number of literals in the above   : 8851
% 0.34/0.52  # Current number of archived formulas  : 0
% 0.34/0.52  # Current number of archived clauses   : 1
% 0.34/0.52  # Clause-clause subsumption calls (NU) : 2971
% 0.34/0.52  # Rec. Clause-clause subsumption calls : 2971
% 0.34/0.52  # Non-unit clause-clause subsumptions  : 105
% 0.34/0.52  # Unit Clause-clause subsumption calls : 223
% 0.34/0.52  # Rewrite failures with RHS unbound    : 0
% 0.34/0.52  # BW rewrite match attempts            : 2792
% 0.34/0.52  # BW rewrite match successes           : 4
% 0.34/0.52  # Condensation attempts                : 0
% 0.34/0.52  # Condensation successes               : 0
% 0.34/0.52  # Termbank termtop insertions          : 237737
% 0.34/0.52  
% 0.34/0.52  # -------------------------------------------------
% 0.34/0.52  # User time                : 0.157 s
% 0.34/0.52  # System time              : 0.011 s
% 0.34/0.52  # Total time               : 0.169 s
% 0.34/0.52  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------

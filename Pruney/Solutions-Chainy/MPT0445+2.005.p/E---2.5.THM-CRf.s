%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:48:19 EST 2020

% Result     : Theorem 1.32s
% Output     : CNFRefutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :   37 (  70 expanded)
%              Number of clauses        :   20 (  29 expanded)
%              Number of leaves         :    8 (  18 expanded)
%              Depth                    :    8
%              Number of atoms          :   58 ( 122 expanded)
%              Number of equality atoms :   15 (  34 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t28_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k6_subset_1(k2_relat_1(X1),k2_relat_1(X2)),k2_relat_1(k6_subset_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_relat_1)).

fof(t26_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k2_relat_1(k2_xboole_0(X1,X2)) = k2_xboole_0(k2_relat_1(X1),k2_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_relat_1)).

fof(fc2_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_relat_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t43_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_xboole_0(X2,X3))
     => r1_tarski(k4_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => r1_tarski(k6_subset_1(k2_relat_1(X1),k2_relat_1(X2)),k2_relat_1(k6_subset_1(X1,X2))) ) ) ),
    inference(assume_negation,[status(cth)],[t28_relat_1])).

fof(c_0_9,plain,(
    ! [X21,X22] :
      ( ~ v1_relat_1(X21)
      | ~ v1_relat_1(X22)
      | k2_relat_1(k2_xboole_0(X21,X22)) = k2_xboole_0(k2_relat_1(X21),k2_relat_1(X22)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_relat_1])])])).

fof(c_0_10,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_relat_1(esk2_0)
    & ~ r1_tarski(k6_subset_1(k2_relat_1(esk1_0),k2_relat_1(esk2_0)),k2_relat_1(k6_subset_1(esk1_0,esk2_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_11,plain,(
    ! [X15,X16] :
      ( ~ v1_relat_1(X15)
      | v1_relat_1(k4_xboole_0(X15,X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_relat_1])])).

cnf(c_0_12,plain,
    ( k2_relat_1(k2_xboole_0(X1,X2)) = k2_xboole_0(k2_relat_1(X1),k2_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( v1_relat_1(k4_xboole_0(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_16,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_17,plain,(
    ! [X8,X9,X10] :
      ( ~ r1_tarski(X8,k2_xboole_0(X9,X10))
      | r1_tarski(k4_xboole_0(X8,X9),X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).

cnf(c_0_18,negated_conjecture,
    ( k2_xboole_0(k2_relat_1(X1),k2_relat_1(esk2_0)) = k2_relat_1(k2_xboole_0(X1,esk2_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( v1_relat_1(k4_xboole_0(esk1_0,X1)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_21,plain,(
    ! [X11,X12] : r1_tarski(X11,k2_xboole_0(X11,X12)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_22,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( k2_xboole_0(k2_relat_1(esk2_0),k2_relat_1(k4_xboole_0(esk1_0,X1))) = k2_relat_1(k2_xboole_0(esk2_0,k4_xboole_0(esk1_0,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_20])).

fof(c_0_24,plain,(
    ! [X6,X7] : k2_xboole_0(X6,k4_xboole_0(X7,X6)) = k2_xboole_0(X6,X7) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_26,plain,(
    ! [X13,X14] : k6_subset_1(X13,X14) = k4_xboole_0(X13,X14) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(k4_xboole_0(X1,k2_relat_1(esk2_0)),k2_relat_1(k4_xboole_0(esk1_0,X2)))
    | ~ r1_tarski(X1,k2_relat_1(k2_xboole_0(esk2_0,k4_xboole_0(esk1_0,X2)))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_20])).

cnf(c_0_30,negated_conjecture,
    ( k2_xboole_0(k2_relat_1(esk2_0),k2_relat_1(esk1_0)) = k2_relat_1(k2_xboole_0(esk2_0,esk1_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_15]),c_0_20]),c_0_20])).

cnf(c_0_31,negated_conjecture,
    ( ~ r1_tarski(k6_subset_1(k2_relat_1(esk1_0),k2_relat_1(esk2_0)),k2_relat_1(k6_subset_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_32,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(k4_xboole_0(X1,k2_relat_1(esk2_0)),k2_relat_1(k4_xboole_0(esk1_0,esk2_0)))
    | ~ r1_tarski(X1,k2_relat_1(k2_xboole_0(esk2_0,esk1_0))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk1_0),k2_relat_1(k2_xboole_0(esk2_0,esk1_0))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( ~ r1_tarski(k4_xboole_0(k2_relat_1(esk1_0),k2_relat_1(esk2_0)),k2_relat_1(k4_xboole_0(esk1_0,esk2_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_32]),c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:03:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 1.32/1.48  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_PS_S0i
% 1.32/1.48  # and selection function SelectDiffNegLit.
% 1.32/1.48  #
% 1.32/1.48  # Preprocessing time       : 0.027 s
% 1.32/1.48  # Presaturation interreduction done
% 1.32/1.48  
% 1.32/1.48  # Proof found!
% 1.32/1.48  # SZS status Theorem
% 1.32/1.48  # SZS output start CNFRefutation
% 1.32/1.48  fof(t28_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k6_subset_1(k2_relat_1(X1),k2_relat_1(X2)),k2_relat_1(k6_subset_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_relat_1)).
% 1.32/1.48  fof(t26_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k2_relat_1(k2_xboole_0(X1,X2))=k2_xboole_0(k2_relat_1(X1),k2_relat_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_relat_1)).
% 1.32/1.48  fof(fc2_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k4_xboole_0(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_relat_1)).
% 1.32/1.48  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.32/1.48  fof(t43_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_xboole_0(X2,X3))=>r1_tarski(k4_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 1.32/1.48  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.32/1.48  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 1.32/1.48  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 1.32/1.48  fof(c_0_8, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k6_subset_1(k2_relat_1(X1),k2_relat_1(X2)),k2_relat_1(k6_subset_1(X1,X2)))))), inference(assume_negation,[status(cth)],[t28_relat_1])).
% 1.32/1.48  fof(c_0_9, plain, ![X21, X22]:(~v1_relat_1(X21)|(~v1_relat_1(X22)|k2_relat_1(k2_xboole_0(X21,X22))=k2_xboole_0(k2_relat_1(X21),k2_relat_1(X22)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_relat_1])])])).
% 1.32/1.48  fof(c_0_10, negated_conjecture, (v1_relat_1(esk1_0)&(v1_relat_1(esk2_0)&~r1_tarski(k6_subset_1(k2_relat_1(esk1_0),k2_relat_1(esk2_0)),k2_relat_1(k6_subset_1(esk1_0,esk2_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 1.32/1.48  fof(c_0_11, plain, ![X15, X16]:(~v1_relat_1(X15)|v1_relat_1(k4_xboole_0(X15,X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_relat_1])])).
% 1.32/1.48  cnf(c_0_12, plain, (k2_relat_1(k2_xboole_0(X1,X2))=k2_xboole_0(k2_relat_1(X1),k2_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 1.32/1.48  cnf(c_0_13, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 1.32/1.48  cnf(c_0_14, plain, (v1_relat_1(k4_xboole_0(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 1.32/1.48  cnf(c_0_15, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 1.32/1.48  fof(c_0_16, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 1.32/1.48  fof(c_0_17, plain, ![X8, X9, X10]:(~r1_tarski(X8,k2_xboole_0(X9,X10))|r1_tarski(k4_xboole_0(X8,X9),X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).
% 1.32/1.48  cnf(c_0_18, negated_conjecture, (k2_xboole_0(k2_relat_1(X1),k2_relat_1(esk2_0))=k2_relat_1(k2_xboole_0(X1,esk2_0))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 1.32/1.48  cnf(c_0_19, negated_conjecture, (v1_relat_1(k4_xboole_0(esk1_0,X1))), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 1.32/1.48  cnf(c_0_20, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.32/1.48  fof(c_0_21, plain, ![X11, X12]:r1_tarski(X11,k2_xboole_0(X11,X12)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 1.32/1.48  cnf(c_0_22, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.32/1.48  cnf(c_0_23, negated_conjecture, (k2_xboole_0(k2_relat_1(esk2_0),k2_relat_1(k4_xboole_0(esk1_0,X1)))=k2_relat_1(k2_xboole_0(esk2_0,k4_xboole_0(esk1_0,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20]), c_0_20])).
% 1.32/1.48  fof(c_0_24, plain, ![X6, X7]:k2_xboole_0(X6,k4_xboole_0(X7,X6))=k2_xboole_0(X6,X7), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 1.32/1.48  cnf(c_0_25, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.32/1.48  fof(c_0_26, plain, ![X13, X14]:k6_subset_1(X13,X14)=k4_xboole_0(X13,X14), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 1.32/1.48  cnf(c_0_27, negated_conjecture, (r1_tarski(k4_xboole_0(X1,k2_relat_1(esk2_0)),k2_relat_1(k4_xboole_0(esk1_0,X2)))|~r1_tarski(X1,k2_relat_1(k2_xboole_0(esk2_0,k4_xboole_0(esk1_0,X2))))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 1.32/1.48  cnf(c_0_28, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.32/1.48  cnf(c_0_29, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_25, c_0_20])).
% 1.32/1.48  cnf(c_0_30, negated_conjecture, (k2_xboole_0(k2_relat_1(esk2_0),k2_relat_1(esk1_0))=k2_relat_1(k2_xboole_0(esk2_0,esk1_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_15]), c_0_20]), c_0_20])).
% 1.32/1.48  cnf(c_0_31, negated_conjecture, (~r1_tarski(k6_subset_1(k2_relat_1(esk1_0),k2_relat_1(esk2_0)),k2_relat_1(k6_subset_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 1.32/1.48  cnf(c_0_32, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 1.32/1.48  cnf(c_0_33, negated_conjecture, (r1_tarski(k4_xboole_0(X1,k2_relat_1(esk2_0)),k2_relat_1(k4_xboole_0(esk1_0,esk2_0)))|~r1_tarski(X1,k2_relat_1(k2_xboole_0(esk2_0,esk1_0)))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 1.32/1.48  cnf(c_0_34, negated_conjecture, (r1_tarski(k2_relat_1(esk1_0),k2_relat_1(k2_xboole_0(esk2_0,esk1_0)))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 1.32/1.48  cnf(c_0_35, negated_conjecture, (~r1_tarski(k4_xboole_0(k2_relat_1(esk1_0),k2_relat_1(esk2_0)),k2_relat_1(k4_xboole_0(esk1_0,esk2_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_32]), c_0_32])).
% 1.32/1.48  cnf(c_0_36, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35]), ['proof']).
% 1.32/1.48  # SZS output end CNFRefutation
% 1.32/1.48  # Proof object total steps             : 37
% 1.32/1.48  # Proof object clause steps            : 20
% 1.32/1.48  # Proof object formula steps           : 17
% 1.32/1.48  # Proof object conjectures             : 15
% 1.32/1.48  # Proof object clause conjectures      : 12
% 1.32/1.48  # Proof object formula conjectures     : 3
% 1.32/1.48  # Proof object initial clauses used    : 10
% 1.32/1.48  # Proof object initial formulas used   : 8
% 1.32/1.48  # Proof object generating inferences   : 9
% 1.32/1.48  # Proof object simplifying inferences  : 7
% 1.32/1.48  # Training examples: 0 positive, 0 negative
% 1.32/1.48  # Parsed axioms                        : 10
% 1.32/1.48  # Removed by relevancy pruning/SinE    : 0
% 1.32/1.48  # Initial clauses                      : 13
% 1.32/1.48  # Removed in clause preprocessing      : 1
% 1.32/1.48  # Initial clauses in saturation        : 12
% 1.32/1.48  # Processed clauses                    : 2450
% 1.32/1.48  # ...of these trivial                  : 298
% 1.32/1.48  # ...subsumed                          : 144
% 1.32/1.48  # ...remaining for further processing  : 2008
% 1.32/1.48  # Other redundant clauses eliminated   : 0
% 1.32/1.48  # Clauses deleted for lack of memory   : 0
% 1.32/1.48  # Backward-subsumed                    : 2
% 1.32/1.48  # Backward-rewritten                   : 14
% 1.32/1.48  # Generated clauses                    : 215809
% 1.32/1.48  # ...of the previous two non-trivial   : 213991
% 1.32/1.48  # Contextual simplify-reflections      : 2
% 1.32/1.48  # Paramodulations                      : 215809
% 1.32/1.48  # Factorizations                       : 0
% 1.32/1.48  # Equation resolutions                 : 0
% 1.32/1.48  # Propositional unsat checks           : 0
% 1.32/1.48  #    Propositional check models        : 0
% 1.32/1.48  #    Propositional check unsatisfiable : 0
% 1.32/1.48  #    Propositional clauses             : 0
% 1.32/1.48  #    Propositional clauses after purity: 0
% 1.32/1.48  #    Propositional unsat core size     : 0
% 1.32/1.48  #    Propositional preprocessing time  : 0.000
% 1.32/1.48  #    Propositional encoding time       : 0.000
% 1.32/1.48  #    Propositional solver time         : 0.000
% 1.32/1.48  #    Success case prop preproc time    : 0.000
% 1.32/1.48  #    Success case prop encoding time   : 0.000
% 1.32/1.48  #    Success case prop solver time     : 0.000
% 1.32/1.48  # Current number of processed clauses  : 1980
% 1.32/1.48  #    Positive orientable unit clauses  : 1150
% 1.32/1.48  #    Positive unorientable unit clauses: 1
% 1.32/1.48  #    Negative unit clauses             : 1
% 1.32/1.48  #    Non-unit-clauses                  : 828
% 1.32/1.48  # Current number of unprocessed clauses: 211549
% 1.32/1.48  # ...number of literals in the above   : 216437
% 1.32/1.48  # Current number of archived formulas  : 0
% 1.32/1.48  # Current number of archived clauses   : 29
% 1.32/1.48  # Clause-clause subsumption calls (NU) : 43260
% 1.32/1.48  # Rec. Clause-clause subsumption calls : 43260
% 1.32/1.48  # Non-unit clause-clause subsumptions  : 148
% 1.32/1.48  # Unit Clause-clause subsumption calls : 8445
% 1.32/1.48  # Rewrite failures with RHS unbound    : 0
% 1.32/1.48  # BW rewrite match attempts            : 23388
% 1.32/1.48  # BW rewrite match successes           : 18
% 1.32/1.48  # Condensation attempts                : 0
% 1.32/1.48  # Condensation successes               : 0
% 1.32/1.48  # Termbank termtop insertions          : 4480315
% 1.32/1.49  
% 1.32/1.49  # -------------------------------------------------
% 1.32/1.49  # User time                : 1.058 s
% 1.32/1.49  # System time              : 0.089 s
% 1.32/1.49  # Total time               : 1.146 s
% 1.32/1.49  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------

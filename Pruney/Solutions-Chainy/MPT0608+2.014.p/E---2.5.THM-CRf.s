%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:52:29 EST 2020

% Result     : Theorem 14.38s
% Output     : CNFRefutation 14.38s
% Verified   : 
% Statistics : Number of formulae       :   35 (  78 expanded)
%              Number of clauses        :   18 (  32 expanded)
%              Number of leaves         :    8 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :   51 (  97 expanded)
%              Number of equality atoms :   33 (  76 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(t109_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k7_relat_1(X3,k6_subset_1(X1,X2)) = k6_subset_1(k7_relat_1(X3,X1),k7_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_relat_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(t212_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k1_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1))) = k6_subset_1(k1_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t212_relat_1)).

fof(t90_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k1_relat_1(k7_relat_1(X2,X1)) = k3_xboole_0(k1_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(t98_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,k1_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

fof(c_0_8,plain,(
    ! [X8,X9] : k4_xboole_0(X8,k4_xboole_0(X8,X9)) = k3_xboole_0(X8,X9) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_9,plain,(
    ! [X4,X5] : k4_xboole_0(X4,X5) = k5_xboole_0(X4,k3_xboole_0(X4,X5)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_10,plain,(
    ! [X6,X7] : k4_xboole_0(X6,k3_xboole_0(X6,X7)) = k4_xboole_0(X6,X7) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

cnf(c_0_11,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,plain,(
    ! [X12,X13,X14] :
      ( ~ v1_relat_1(X14)
      | k7_relat_1(X14,k6_subset_1(X12,X13)) = k6_subset_1(k7_relat_1(X14,X12),k7_relat_1(X14,X13)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t109_relat_1])])).

fof(c_0_15,plain,(
    ! [X10,X11] : k6_subset_1(X10,X11) = k4_xboole_0(X10,X11) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => k1_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1))) = k6_subset_1(k1_relat_1(X2),X1) ) ),
    inference(assume_negation,[status(cth)],[t212_relat_1])).

fof(c_0_17,plain,(
    ! [X15,X16] :
      ( ~ v1_relat_1(X16)
      | k1_relat_1(k7_relat_1(X16,X15)) = k3_xboole_0(k1_relat_1(X16),X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).

cnf(c_0_18,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_11,c_0_12]),c_0_12])).

cnf(c_0_19,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_12]),c_0_12])).

cnf(c_0_20,plain,
    ( k7_relat_1(X1,k6_subset_1(X2,X3)) = k6_subset_1(k7_relat_1(X1,X2),k7_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_22,plain,(
    ! [X17] :
      ( ~ v1_relat_1(X17)
      | k7_relat_1(X17,k1_relat_1(X17)) = X17 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_relat_1])])).

fof(c_0_23,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & k1_relat_1(k6_subset_1(esk2_0,k7_relat_1(esk2_0,esk1_0))) != k6_subset_1(k1_relat_1(esk2_0),esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

cnf(c_0_24,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k3_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_18]),c_0_19])).

cnf(c_0_26,plain,
    ( k7_relat_1(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) = k5_xboole_0(k7_relat_1(X1,X2),k3_xboole_0(k7_relat_1(X1,X2),k7_relat_1(X1,X3)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21]),c_0_21]),c_0_12]),c_0_12])).

cnf(c_0_27,plain,
    ( k7_relat_1(X1,k1_relat_1(X1)) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( k1_relat_1(k6_subset_1(esk2_0,k7_relat_1(esk2_0,esk1_0))) != k6_subset_1(k1_relat_1(esk2_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( k1_relat_1(k7_relat_1(X1,k5_xboole_0(k1_relat_1(X1),k3_xboole_0(k1_relat_1(X1),X2)))) = k5_xboole_0(k1_relat_1(X1),k3_xboole_0(k1_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,plain,
    ( k7_relat_1(X1,k5_xboole_0(k1_relat_1(X1),k3_xboole_0(k1_relat_1(X1),X2))) = k5_xboole_0(X1,k3_xboole_0(X1,k7_relat_1(X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( k1_relat_1(k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,k7_relat_1(esk2_0,esk1_0)))) != k5_xboole_0(k1_relat_1(esk2_0),k3_xboole_0(k1_relat_1(esk2_0),esk1_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_21]),c_0_21]),c_0_12]),c_0_12])).

cnf(c_0_32,plain,
    ( k1_relat_1(k5_xboole_0(X1,k3_xboole_0(X1,k7_relat_1(X1,X2)))) = k5_xboole_0(k1_relat_1(X1),k3_xboole_0(k1_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_33,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:46:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 14.38/14.54  # AutoSched0-Mode selected heuristic G_E___208_C12_11_nc_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 14.38/14.54  # and selection function SelectComplexExceptUniqMaxHorn.
% 14.38/14.54  #
% 14.38/14.54  # Preprocessing time       : 0.027 s
% 14.38/14.54  # Presaturation interreduction done
% 14.38/14.54  
% 14.38/14.54  # Proof found!
% 14.38/14.54  # SZS status Theorem
% 14.38/14.54  # SZS output start CNFRefutation
% 14.38/14.54  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 14.38/14.54  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 14.38/14.54  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 14.38/14.54  fof(t109_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k7_relat_1(X3,k6_subset_1(X1,X2))=k6_subset_1(k7_relat_1(X3,X1),k7_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_relat_1)).
% 14.38/14.54  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 14.38/14.54  fof(t212_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>k1_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)))=k6_subset_1(k1_relat_1(X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t212_relat_1)).
% 14.38/14.54  fof(t90_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k1_relat_1(k7_relat_1(X2,X1))=k3_xboole_0(k1_relat_1(X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 14.38/14.54  fof(t98_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k7_relat_1(X1,k1_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 14.38/14.54  fof(c_0_8, plain, ![X8, X9]:k4_xboole_0(X8,k4_xboole_0(X8,X9))=k3_xboole_0(X8,X9), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 14.38/14.54  fof(c_0_9, plain, ![X4, X5]:k4_xboole_0(X4,X5)=k5_xboole_0(X4,k3_xboole_0(X4,X5)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 14.38/14.54  fof(c_0_10, plain, ![X6, X7]:k4_xboole_0(X6,k3_xboole_0(X6,X7))=k4_xboole_0(X6,X7), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 14.38/14.54  cnf(c_0_11, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 14.38/14.54  cnf(c_0_12, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 14.38/14.54  cnf(c_0_13, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 14.38/14.54  fof(c_0_14, plain, ![X12, X13, X14]:(~v1_relat_1(X14)|k7_relat_1(X14,k6_subset_1(X12,X13))=k6_subset_1(k7_relat_1(X14,X12),k7_relat_1(X14,X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t109_relat_1])])).
% 14.38/14.54  fof(c_0_15, plain, ![X10, X11]:k6_subset_1(X10,X11)=k4_xboole_0(X10,X11), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 14.38/14.54  fof(c_0_16, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>k1_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)))=k6_subset_1(k1_relat_1(X2),X1))), inference(assume_negation,[status(cth)],[t212_relat_1])).
% 14.38/14.54  fof(c_0_17, plain, ![X15, X16]:(~v1_relat_1(X16)|k1_relat_1(k7_relat_1(X16,X15))=k3_xboole_0(k1_relat_1(X16),X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).
% 14.38/14.54  cnf(c_0_18, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_11, c_0_12]), c_0_12])).
% 14.38/14.54  cnf(c_0_19, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2)))=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13, c_0_12]), c_0_12])).
% 14.38/14.54  cnf(c_0_20, plain, (k7_relat_1(X1,k6_subset_1(X2,X3))=k6_subset_1(k7_relat_1(X1,X2),k7_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 14.38/14.54  cnf(c_0_21, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 14.38/14.54  fof(c_0_22, plain, ![X17]:(~v1_relat_1(X17)|k7_relat_1(X17,k1_relat_1(X17))=X17), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_relat_1])])).
% 14.38/14.54  fof(c_0_23, negated_conjecture, (v1_relat_1(esk2_0)&k1_relat_1(k6_subset_1(esk2_0,k7_relat_1(esk2_0,esk1_0)))!=k6_subset_1(k1_relat_1(esk2_0),esk1_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 14.38/14.54  cnf(c_0_24, plain, (k1_relat_1(k7_relat_1(X1,X2))=k3_xboole_0(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 14.38/14.54  cnf(c_0_25, plain, (k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_18]), c_0_19])).
% 14.38/14.54  cnf(c_0_26, plain, (k7_relat_1(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))=k5_xboole_0(k7_relat_1(X1,X2),k3_xboole_0(k7_relat_1(X1,X2),k7_relat_1(X1,X3)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_21]), c_0_21]), c_0_12]), c_0_12])).
% 14.38/14.54  cnf(c_0_27, plain, (k7_relat_1(X1,k1_relat_1(X1))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 14.38/14.54  cnf(c_0_28, negated_conjecture, (k1_relat_1(k6_subset_1(esk2_0,k7_relat_1(esk2_0,esk1_0)))!=k6_subset_1(k1_relat_1(esk2_0),esk1_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 14.38/14.54  cnf(c_0_29, plain, (k1_relat_1(k7_relat_1(X1,k5_xboole_0(k1_relat_1(X1),k3_xboole_0(k1_relat_1(X1),X2))))=k5_xboole_0(k1_relat_1(X1),k3_xboole_0(k1_relat_1(X1),X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 14.38/14.54  cnf(c_0_30, plain, (k7_relat_1(X1,k5_xboole_0(k1_relat_1(X1),k3_xboole_0(k1_relat_1(X1),X2)))=k5_xboole_0(X1,k3_xboole_0(X1,k7_relat_1(X1,X2)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 14.38/14.54  cnf(c_0_31, negated_conjecture, (k1_relat_1(k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,k7_relat_1(esk2_0,esk1_0))))!=k5_xboole_0(k1_relat_1(esk2_0),k3_xboole_0(k1_relat_1(esk2_0),esk1_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_21]), c_0_21]), c_0_12]), c_0_12])).
% 14.38/14.54  cnf(c_0_32, plain, (k1_relat_1(k5_xboole_0(X1,k3_xboole_0(X1,k7_relat_1(X1,X2))))=k5_xboole_0(k1_relat_1(X1),k3_xboole_0(k1_relat_1(X1),X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 14.38/14.54  cnf(c_0_33, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 14.38/14.54  cnf(c_0_34, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])]), ['proof']).
% 14.38/14.54  # SZS output end CNFRefutation
% 14.38/14.54  # Proof object total steps             : 35
% 14.38/14.54  # Proof object clause steps            : 18
% 14.38/14.54  # Proof object formula steps           : 17
% 14.38/14.54  # Proof object conjectures             : 7
% 14.38/14.54  # Proof object clause conjectures      : 4
% 14.38/14.54  # Proof object formula conjectures     : 3
% 14.38/14.54  # Proof object initial clauses used    : 9
% 14.38/14.54  # Proof object initial formulas used   : 8
% 14.38/14.54  # Proof object generating inferences   : 5
% 14.38/14.54  # Proof object simplifying inferences  : 15
% 14.38/14.54  # Training examples: 0 positive, 0 negative
% 14.38/14.54  # Parsed axioms                        : 8
% 14.38/14.54  # Removed by relevancy pruning/SinE    : 0
% 14.38/14.54  # Initial clauses                      : 9
% 14.38/14.54  # Removed in clause preprocessing      : 2
% 14.38/14.54  # Initial clauses in saturation        : 7
% 14.38/14.54  # Processed clauses                    : 10269
% 14.38/14.54  # ...of these trivial                  : 1
% 14.38/14.54  # ...subsumed                          : 8916
% 14.38/14.54  # ...remaining for further processing  : 1352
% 14.38/14.54  # Other redundant clauses eliminated   : 0
% 14.38/14.54  # Clauses deleted for lack of memory   : 0
% 14.38/14.54  # Backward-subsumed                    : 58
% 14.38/14.54  # Backward-rewritten                   : 2
% 14.38/14.54  # Generated clauses                    : 1031006
% 14.38/14.54  # ...of the previous two non-trivial   : 1029529
% 14.38/14.54  # Contextual simplify-reflections      : 0
% 14.38/14.54  # Paramodulations                      : 1031006
% 14.38/14.54  # Factorizations                       : 0
% 14.38/14.54  # Equation resolutions                 : 0
% 14.38/14.54  # Propositional unsat checks           : 0
% 14.38/14.54  #    Propositional check models        : 0
% 14.38/14.54  #    Propositional check unsatisfiable : 0
% 14.38/14.54  #    Propositional clauses             : 0
% 14.38/14.54  #    Propositional clauses after purity: 0
% 14.38/14.54  #    Propositional unsat core size     : 0
% 14.38/14.54  #    Propositional preprocessing time  : 0.000
% 14.38/14.54  #    Propositional encoding time       : 0.000
% 14.38/14.54  #    Propositional solver time         : 0.000
% 14.38/14.54  #    Success case prop preproc time    : 0.000
% 14.38/14.54  #    Success case prop encoding time   : 0.000
% 14.38/14.54  #    Success case prop solver time     : 0.000
% 14.38/14.54  # Current number of processed clauses  : 1285
% 14.38/14.54  #    Positive orientable unit clauses  : 4
% 14.38/14.54  #    Positive unorientable unit clauses: 0
% 14.38/14.54  #    Negative unit clauses             : 1
% 14.38/14.54  #    Non-unit-clauses                  : 1280
% 14.38/14.54  # Current number of unprocessed clauses: 1017797
% 14.38/14.54  # ...number of literals in the above   : 5546660
% 14.38/14.54  # Current number of archived formulas  : 0
% 14.38/14.54  # Current number of archived clauses   : 69
% 14.38/14.54  # Clause-clause subsumption calls (NU) : 928761
% 14.38/14.54  # Rec. Clause-clause subsumption calls : 609383
% 14.38/14.54  # Non-unit clause-clause subsumptions  : 8974
% 14.38/14.54  # Unit Clause-clause subsumption calls : 1
% 14.38/14.54  # Rewrite failures with RHS unbound    : 0
% 14.38/14.54  # BW rewrite match attempts            : 2
% 14.38/14.54  # BW rewrite match successes           : 2
% 14.38/14.54  # Condensation attempts                : 0
% 14.38/14.54  # Condensation successes               : 0
% 14.38/14.54  # Termbank termtop insertions          : 58058767
% 14.40/14.59  
% 14.40/14.59  # -------------------------------------------------
% 14.40/14.59  # User time                : 13.829 s
% 14.40/14.59  # System time              : 0.420 s
% 14.40/14.59  # Total time               : 14.249 s
% 14.40/14.59  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------

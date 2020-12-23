%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:52:42 EST 2020

% Result     : Theorem 0.77s
% Output     : CNFRefutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :   38 (  57 expanded)
%              Number of clauses        :   21 (  26 expanded)
%              Number of leaves         :    8 (  14 expanded)
%              Depth                    :    8
%              Number of atoms          :   87 ( 130 expanded)
%              Number of equality atoms :   32 (  49 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(t85_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_xboole_0(X1,k4_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t109_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k7_relat_1(X3,k6_subset_1(X1,X2)) = k6_subset_1(k7_relat_1(X3,X1),k7_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_relat_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(t97_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X1)
       => k7_relat_1(X2,X1) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

fof(t216_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => k7_relat_1(k6_subset_1(X3,k7_relat_1(X3,X2)),X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t216_relat_1)).

fof(t207_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_xboole_0(X1,X2)
       => k7_relat_1(k7_relat_1(X3,X1),X2) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).

fof(c_0_8,plain,(
    ! [X6,X7] :
      ( ( ~ r1_xboole_0(X6,X7)
        | k4_xboole_0(X6,X7) = X6 )
      & ( k4_xboole_0(X6,X7) != X6
        | r1_xboole_0(X6,X7) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

fof(c_0_9,plain,(
    ! [X8,X9,X10] :
      ( ~ r1_tarski(X8,X9)
      | r1_xboole_0(X8,k4_xboole_0(X10,X9)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_xboole_1])])).

cnf(c_0_10,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_12,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_13,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = X1
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_14,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_15,plain,(
    ! [X13,X14,X15] :
      ( ~ v1_relat_1(X15)
      | k7_relat_1(X15,k6_subset_1(X13,X14)) = k6_subset_1(k7_relat_1(X15,X13),k7_relat_1(X15,X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t109_relat_1])])).

fof(c_0_16,plain,(
    ! [X11,X12] : k6_subset_1(X11,X12) = k4_xboole_0(X11,X12) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

fof(c_0_17,plain,(
    ! [X19,X20] :
      ( ~ v1_relat_1(X20)
      | ~ r1_tarski(k1_relat_1(X20),X19)
      | k7_relat_1(X20,X19) = X20 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( r1_tarski(X1,X2)
         => k7_relat_1(k6_subset_1(X3,k7_relat_1(X3,X2)),X1) = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t216_relat_1])).

fof(c_0_19,plain,(
    ! [X16,X17,X18] :
      ( ~ v1_relat_1(X18)
      | ~ r1_xboole_0(X16,X17)
      | k7_relat_1(k7_relat_1(X18,X16),X17) = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t207_relat_1])])).

cnf(c_0_20,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X3,X4))
    | ~ r1_tarski(X2,X4) ),
    inference(spm,[status(thm)],[c_0_11,c_0_13])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( k7_relat_1(X1,k6_subset_1(X2,X3)) = k6_subset_1(k7_relat_1(X1,X2),k7_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( k7_relat_1(X1,X2) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_25,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & r1_tarski(esk1_0,esk2_0)
    & k7_relat_1(k6_subset_1(esk3_0,k7_relat_1(esk3_0,esk2_0)),esk1_0) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

cnf(c_0_26,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_28,plain,
    ( k7_relat_1(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k7_relat_1(X1,X2),k7_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_23]),c_0_23])).

cnf(c_0_29,plain,
    ( k7_relat_1(X1,k1_relat_1(X1)) = X1
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_21])).

cnf(c_0_30,negated_conjecture,
    ( k7_relat_1(k6_subset_1(esk3_0,k7_relat_1(esk3_0,esk2_0)),esk1_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( k7_relat_1(k7_relat_1(X1,k4_xboole_0(X2,X3)),X4) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X4,X3) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,plain,
    ( k7_relat_1(X1,k4_xboole_0(k1_relat_1(X1),X2)) = k4_xboole_0(X1,k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( k7_relat_1(k4_xboole_0(esk3_0,k7_relat_1(esk3_0,esk2_0)),esk1_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_30,c_0_23])).

cnf(c_0_34,plain,
    ( k7_relat_1(k4_xboole_0(X1,k7_relat_1(X1,X2)),X3) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_35,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_36])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:26:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.77/0.98  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_TT_S0Y
% 0.77/0.98  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.77/0.98  #
% 0.77/0.98  # Preprocessing time       : 0.029 s
% 0.77/0.98  # Presaturation interreduction done
% 0.77/0.98  
% 0.77/0.98  # Proof found!
% 0.77/0.98  # SZS status Theorem
% 0.77/0.98  # SZS output start CNFRefutation
% 0.77/0.98  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.77/0.98  fof(t85_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_xboole_0(X1,k4_xboole_0(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 0.77/0.98  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.77/0.98  fof(t109_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k7_relat_1(X3,k6_subset_1(X1,X2))=k6_subset_1(k7_relat_1(X3,X1),k7_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_relat_1)).
% 0.77/0.98  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 0.77/0.98  fof(t97_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X2),X1)=>k7_relat_1(X2,X1)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 0.77/0.98  fof(t216_relat_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>k7_relat_1(k6_subset_1(X3,k7_relat_1(X3,X2)),X1)=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t216_relat_1)).
% 0.77/0.98  fof(t207_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_xboole_0(X1,X2)=>k7_relat_1(k7_relat_1(X3,X1),X2)=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t207_relat_1)).
% 0.77/0.98  fof(c_0_8, plain, ![X6, X7]:((~r1_xboole_0(X6,X7)|k4_xboole_0(X6,X7)=X6)&(k4_xboole_0(X6,X7)!=X6|r1_xboole_0(X6,X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.77/0.98  fof(c_0_9, plain, ![X8, X9, X10]:(~r1_tarski(X8,X9)|r1_xboole_0(X8,k4_xboole_0(X10,X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_xboole_1])])).
% 0.77/0.98  cnf(c_0_10, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.77/0.98  cnf(c_0_11, plain, (r1_xboole_0(X1,k4_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.77/0.98  fof(c_0_12, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.77/0.98  cnf(c_0_13, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X3))=X1|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.77/0.98  cnf(c_0_14, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.77/0.98  fof(c_0_15, plain, ![X13, X14, X15]:(~v1_relat_1(X15)|k7_relat_1(X15,k6_subset_1(X13,X14))=k6_subset_1(k7_relat_1(X15,X13),k7_relat_1(X15,X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t109_relat_1])])).
% 0.77/0.98  fof(c_0_16, plain, ![X11, X12]:k6_subset_1(X11,X12)=k4_xboole_0(X11,X12), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 0.77/0.98  fof(c_0_17, plain, ![X19, X20]:(~v1_relat_1(X20)|(~r1_tarski(k1_relat_1(X20),X19)|k7_relat_1(X20,X19)=X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).
% 0.77/0.98  fof(c_0_18, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>k7_relat_1(k6_subset_1(X3,k7_relat_1(X3,X2)),X1)=k1_xboole_0))), inference(assume_negation,[status(cth)],[t216_relat_1])).
% 0.77/0.98  fof(c_0_19, plain, ![X16, X17, X18]:(~v1_relat_1(X18)|(~r1_xboole_0(X16,X17)|k7_relat_1(k7_relat_1(X18,X16),X17)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t207_relat_1])])).
% 0.77/0.98  cnf(c_0_20, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,k4_xboole_0(X3,X4))|~r1_tarski(X2,X4)), inference(spm,[status(thm)],[c_0_11, c_0_13])).
% 0.77/0.98  cnf(c_0_21, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_14])).
% 0.77/0.98  cnf(c_0_22, plain, (k7_relat_1(X1,k6_subset_1(X2,X3))=k6_subset_1(k7_relat_1(X1,X2),k7_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.77/0.98  cnf(c_0_23, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.77/0.98  cnf(c_0_24, plain, (k7_relat_1(X1,X2)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.77/0.98  fof(c_0_25, negated_conjecture, (v1_relat_1(esk3_0)&(r1_tarski(esk1_0,esk2_0)&k7_relat_1(k6_subset_1(esk3_0,k7_relat_1(esk3_0,esk2_0)),esk1_0)!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 0.77/0.98  cnf(c_0_26, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k1_xboole_0|~v1_relat_1(X1)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.77/0.98  cnf(c_0_27, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X3)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.77/0.98  cnf(c_0_28, plain, (k7_relat_1(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k7_relat_1(X1,X2),k7_relat_1(X1,X3))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_23]), c_0_23])).
% 0.77/0.98  cnf(c_0_29, plain, (k7_relat_1(X1,k1_relat_1(X1))=X1|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_24, c_0_21])).
% 0.77/0.98  cnf(c_0_30, negated_conjecture, (k7_relat_1(k6_subset_1(esk3_0,k7_relat_1(esk3_0,esk2_0)),esk1_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.77/0.98  cnf(c_0_31, plain, (k7_relat_1(k7_relat_1(X1,k4_xboole_0(X2,X3)),X4)=k1_xboole_0|~v1_relat_1(X1)|~r1_tarski(X4,X3)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.77/0.98  cnf(c_0_32, plain, (k7_relat_1(X1,k4_xboole_0(k1_relat_1(X1),X2))=k4_xboole_0(X1,k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.77/0.98  cnf(c_0_33, negated_conjecture, (k7_relat_1(k4_xboole_0(esk3_0,k7_relat_1(esk3_0,esk2_0)),esk1_0)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_30, c_0_23])).
% 0.77/0.98  cnf(c_0_34, plain, (k7_relat_1(k4_xboole_0(X1,k7_relat_1(X1,X2)),X3)=k1_xboole_0|~v1_relat_1(X1)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.77/0.98  cnf(c_0_35, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.77/0.98  cnf(c_0_36, negated_conjecture, (r1_tarski(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.77/0.98  cnf(c_0_37, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35]), c_0_36])]), ['proof']).
% 0.77/0.98  # SZS output end CNFRefutation
% 0.77/0.98  # Proof object total steps             : 38
% 0.77/0.98  # Proof object clause steps            : 21
% 0.77/0.98  # Proof object formula steps           : 17
% 0.77/0.98  # Proof object conjectures             : 8
% 0.77/0.98  # Proof object clause conjectures      : 5
% 0.77/0.98  # Proof object formula conjectures     : 3
% 0.77/0.98  # Proof object initial clauses used    : 10
% 0.77/0.98  # Proof object initial formulas used   : 8
% 0.77/0.98  # Proof object generating inferences   : 8
% 0.77/0.98  # Proof object simplifying inferences  : 7
% 0.77/0.98  # Training examples: 0 positive, 0 negative
% 0.77/0.98  # Parsed axioms                        : 8
% 0.77/0.98  # Removed by relevancy pruning/SinE    : 0
% 0.77/0.98  # Initial clauses                      : 13
% 0.77/0.98  # Removed in clause preprocessing      : 1
% 0.77/0.98  # Initial clauses in saturation        : 12
% 0.77/0.98  # Processed clauses                    : 3922
% 0.77/0.98  # ...of these trivial                  : 0
% 0.77/0.98  # ...subsumed                          : 3179
% 0.77/0.98  # ...remaining for further processing  : 743
% 0.77/0.98  # Other redundant clauses eliminated   : 8
% 0.77/0.98  # Clauses deleted for lack of memory   : 0
% 0.77/0.98  # Backward-subsumed                    : 22
% 0.77/0.98  # Backward-rewritten                   : 0
% 0.77/0.98  # Generated clauses                    : 36631
% 0.77/0.98  # ...of the previous two non-trivial   : 36539
% 0.77/0.98  # Contextual simplify-reflections      : 0
% 0.77/0.98  # Paramodulations                      : 36623
% 0.77/0.98  # Factorizations                       : 0
% 0.77/0.98  # Equation resolutions                 : 8
% 0.77/0.98  # Propositional unsat checks           : 0
% 0.77/0.98  #    Propositional check models        : 0
% 0.77/0.98  #    Propositional check unsatisfiable : 0
% 0.77/0.98  #    Propositional clauses             : 0
% 0.77/0.98  #    Propositional clauses after purity: 0
% 0.77/0.98  #    Propositional unsat core size     : 0
% 0.77/0.98  #    Propositional preprocessing time  : 0.000
% 0.77/0.98  #    Propositional encoding time       : 0.000
% 0.77/0.98  #    Propositional solver time         : 0.000
% 0.77/0.98  #    Success case prop preproc time    : 0.000
% 0.77/0.98  #    Success case prop encoding time   : 0.000
% 0.77/0.98  #    Success case prop solver time     : 0.000
% 0.77/0.98  # Current number of processed clauses  : 708
% 0.77/0.98  #    Positive orientable unit clauses  : 3
% 0.77/0.98  #    Positive unorientable unit clauses: 0
% 0.77/0.98  #    Negative unit clauses             : 1
% 0.77/0.98  #    Non-unit-clauses                  : 704
% 0.77/0.98  # Current number of unprocessed clauses: 32307
% 0.77/0.98  # ...number of literals in the above   : 204146
% 0.77/0.98  # Current number of archived formulas  : 0
% 0.77/0.98  # Current number of archived clauses   : 34
% 0.77/0.98  # Clause-clause subsumption calls (NU) : 86980
% 0.77/0.98  # Rec. Clause-clause subsumption calls : 37048
% 0.77/0.98  # Non-unit clause-clause subsumptions  : 3201
% 0.77/0.98  # Unit Clause-clause subsumption calls : 0
% 0.77/0.98  # Rewrite failures with RHS unbound    : 0
% 0.77/0.98  # BW rewrite match attempts            : 2
% 0.77/0.98  # BW rewrite match successes           : 0
% 0.77/0.98  # Condensation attempts                : 0
% 0.77/0.98  # Condensation successes               : 0
% 0.77/0.98  # Termbank termtop insertions          : 615154
% 0.77/0.99  
% 0.77/0.99  # -------------------------------------------------
% 0.77/0.99  # User time                : 0.610 s
% 0.77/0.99  # System time              : 0.034 s
% 0.77/0.99  # Total time               : 0.644 s
% 0.77/0.99  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:52:44 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   43 (  62 expanded)
%              Number of clauses        :   22 (  26 expanded)
%              Number of leaves         :   10 (  16 expanded)
%              Depth                    :    8
%              Number of atoms          :   73 ( 110 expanded)
%              Number of equality atoms :   35 (  53 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t216_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => k7_relat_1(k6_subset_1(X3,k7_relat_1(X3,X2)),X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t216_relat_1)).

fof(t212_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k1_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1))) = k6_subset_1(k1_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t212_relat_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t95_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k7_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(fc2_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_relat_1)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( r1_tarski(X1,X2)
         => k7_relat_1(k6_subset_1(X3,k7_relat_1(X3,X2)),X1) = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t216_relat_1])).

fof(c_0_11,plain,(
    ! [X18,X19] :
      ( ~ v1_relat_1(X19)
      | k1_relat_1(k6_subset_1(X19,k7_relat_1(X19,X18))) = k6_subset_1(k1_relat_1(X19),X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t212_relat_1])])).

fof(c_0_12,plain,(
    ! [X14,X15] : k6_subset_1(X14,X15) = k4_xboole_0(X14,X15) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

fof(c_0_13,plain,(
    ! [X4,X5] :
      ( ( k4_xboole_0(X4,X5) != k1_xboole_0
        | r1_tarski(X4,X5) )
      & ( ~ r1_tarski(X4,X5)
        | k4_xboole_0(X4,X5) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_14,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & r1_tarski(esk1_0,esk2_0)
    & k7_relat_1(k6_subset_1(esk3_0,k7_relat_1(esk3_0,esk2_0)),esk1_0) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

cnf(c_0_15,plain,
    ( k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X2))) = k6_subset_1(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,plain,(
    ! [X6,X7] : k2_xboole_0(X6,k4_xboole_0(X7,X6)) = k2_xboole_0(X6,X7) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_18,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_20,plain,(
    ! [X20,X21] :
      ( ( k7_relat_1(X21,X20) != k1_xboole_0
        | r1_xboole_0(k1_relat_1(X21),X20)
        | ~ v1_relat_1(X21) )
      & ( ~ r1_xboole_0(k1_relat_1(X21),X20)
        | k7_relat_1(X21,X20) = k1_xboole_0
        | ~ v1_relat_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_relat_1])])])).

cnf(c_0_21,plain,
    ( k1_relat_1(k4_xboole_0(X1,k7_relat_1(X1,X2))) = k4_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_16]),c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_23,plain,(
    ! [X9,X10,X11] : k4_xboole_0(k4_xboole_0(X9,X10),X11) = k4_xboole_0(X9,k2_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_24,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( k4_xboole_0(esk1_0,esk2_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

fof(c_0_26,plain,(
    ! [X8] : k4_xboole_0(X8,k1_xboole_0) = X8 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_27,plain,
    ( k7_relat_1(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( k1_relat_1(k4_xboole_0(esk3_0,k7_relat_1(esk3_0,X1))) = k4_xboole_0(k1_relat_1(esk3_0),X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_29,plain,(
    ! [X16,X17] :
      ( ~ v1_relat_1(X16)
      | v1_relat_1(k4_xboole_0(X16,X17)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_relat_1])])).

fof(c_0_30,plain,(
    ! [X12,X13] : r1_xboole_0(k4_xboole_0(X12,X13),X13) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

cnf(c_0_31,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,negated_conjecture,
    ( k2_xboole_0(esk2_0,esk1_0) = k2_xboole_0(esk2_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_33,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( k7_relat_1(k6_subset_1(esk3_0,k7_relat_1(esk3_0,esk2_0)),esk1_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_35,negated_conjecture,
    ( k7_relat_1(k4_xboole_0(esk3_0,k7_relat_1(esk3_0,X1)),X2) = k1_xboole_0
    | ~ v1_relat_1(k4_xboole_0(esk3_0,k7_relat_1(esk3_0,X1)))
    | ~ r1_xboole_0(k4_xboole_0(k1_relat_1(esk3_0),X1),X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_36,plain,
    ( v1_relat_1(k4_xboole_0(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(X1,esk2_0),esk1_0) = k4_xboole_0(X1,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_31]),c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( k7_relat_1(k4_xboole_0(esk3_0,k7_relat_1(esk3_0,esk2_0)),esk1_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_34,c_0_16])).

cnf(c_0_40,negated_conjecture,
    ( k7_relat_1(k4_xboole_0(esk3_0,k7_relat_1(esk3_0,X1)),X2) = k1_xboole_0
    | ~ r1_xboole_0(k4_xboole_0(k1_relat_1(esk3_0),X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_22])])).

cnf(c_0_41,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(X1,esk2_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_42,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:27:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.43  # AutoSched0-Mode selected heuristic G_E___208_C12_11_nc_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.43  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.43  #
% 0.19/0.43  # Preprocessing time       : 0.026 s
% 0.19/0.43  # Presaturation interreduction done
% 0.19/0.43  
% 0.19/0.43  # Proof found!
% 0.19/0.43  # SZS status Theorem
% 0.19/0.43  # SZS output start CNFRefutation
% 0.19/0.43  fof(t216_relat_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>k7_relat_1(k6_subset_1(X3,k7_relat_1(X3,X2)),X1)=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t216_relat_1)).
% 0.19/0.43  fof(t212_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k1_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)))=k6_subset_1(k1_relat_1(X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t212_relat_1)).
% 0.19/0.43  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 0.19/0.43  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.19/0.43  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.19/0.43  fof(t95_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(k7_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 0.19/0.43  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.19/0.43  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.19/0.43  fof(fc2_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k4_xboole_0(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_relat_1)).
% 0.19/0.43  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.19/0.43  fof(c_0_10, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>k7_relat_1(k6_subset_1(X3,k7_relat_1(X3,X2)),X1)=k1_xboole_0))), inference(assume_negation,[status(cth)],[t216_relat_1])).
% 0.19/0.43  fof(c_0_11, plain, ![X18, X19]:(~v1_relat_1(X19)|k1_relat_1(k6_subset_1(X19,k7_relat_1(X19,X18)))=k6_subset_1(k1_relat_1(X19),X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t212_relat_1])])).
% 0.19/0.43  fof(c_0_12, plain, ![X14, X15]:k6_subset_1(X14,X15)=k4_xboole_0(X14,X15), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 0.19/0.43  fof(c_0_13, plain, ![X4, X5]:((k4_xboole_0(X4,X5)!=k1_xboole_0|r1_tarski(X4,X5))&(~r1_tarski(X4,X5)|k4_xboole_0(X4,X5)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.19/0.43  fof(c_0_14, negated_conjecture, (v1_relat_1(esk3_0)&(r1_tarski(esk1_0,esk2_0)&k7_relat_1(k6_subset_1(esk3_0,k7_relat_1(esk3_0,esk2_0)),esk1_0)!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 0.19/0.43  cnf(c_0_15, plain, (k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X2)))=k6_subset_1(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.43  cnf(c_0_16, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.43  fof(c_0_17, plain, ![X6, X7]:k2_xboole_0(X6,k4_xboole_0(X7,X6))=k2_xboole_0(X6,X7), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.19/0.43  cnf(c_0_18, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.43  cnf(c_0_19, negated_conjecture, (r1_tarski(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.43  fof(c_0_20, plain, ![X20, X21]:((k7_relat_1(X21,X20)!=k1_xboole_0|r1_xboole_0(k1_relat_1(X21),X20)|~v1_relat_1(X21))&(~r1_xboole_0(k1_relat_1(X21),X20)|k7_relat_1(X21,X20)=k1_xboole_0|~v1_relat_1(X21))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_relat_1])])])).
% 0.19/0.43  cnf(c_0_21, plain, (k1_relat_1(k4_xboole_0(X1,k7_relat_1(X1,X2)))=k4_xboole_0(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15, c_0_16]), c_0_16])).
% 0.19/0.43  cnf(c_0_22, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.43  fof(c_0_23, plain, ![X9, X10, X11]:k4_xboole_0(k4_xboole_0(X9,X10),X11)=k4_xboole_0(X9,k2_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.19/0.43  cnf(c_0_24, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.43  cnf(c_0_25, negated_conjecture, (k4_xboole_0(esk1_0,esk2_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.19/0.43  fof(c_0_26, plain, ![X8]:k4_xboole_0(X8,k1_xboole_0)=X8, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.19/0.43  cnf(c_0_27, plain, (k7_relat_1(X1,X2)=k1_xboole_0|~r1_xboole_0(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.43  cnf(c_0_28, negated_conjecture, (k1_relat_1(k4_xboole_0(esk3_0,k7_relat_1(esk3_0,X1)))=k4_xboole_0(k1_relat_1(esk3_0),X1)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.19/0.43  fof(c_0_29, plain, ![X16, X17]:(~v1_relat_1(X16)|v1_relat_1(k4_xboole_0(X16,X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_relat_1])])).
% 0.19/0.43  fof(c_0_30, plain, ![X12, X13]:r1_xboole_0(k4_xboole_0(X12,X13),X13), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.19/0.43  cnf(c_0_31, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.43  cnf(c_0_32, negated_conjecture, (k2_xboole_0(esk2_0,esk1_0)=k2_xboole_0(esk2_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.19/0.43  cnf(c_0_33, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.43  cnf(c_0_34, negated_conjecture, (k7_relat_1(k6_subset_1(esk3_0,k7_relat_1(esk3_0,esk2_0)),esk1_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.43  cnf(c_0_35, negated_conjecture, (k7_relat_1(k4_xboole_0(esk3_0,k7_relat_1(esk3_0,X1)),X2)=k1_xboole_0|~v1_relat_1(k4_xboole_0(esk3_0,k7_relat_1(esk3_0,X1)))|~r1_xboole_0(k4_xboole_0(k1_relat_1(esk3_0),X1),X2)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.19/0.43  cnf(c_0_36, plain, (v1_relat_1(k4_xboole_0(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.43  cnf(c_0_37, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.43  cnf(c_0_38, negated_conjecture, (k4_xboole_0(k4_xboole_0(X1,esk2_0),esk1_0)=k4_xboole_0(X1,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_31]), c_0_33])).
% 0.19/0.43  cnf(c_0_39, negated_conjecture, (k7_relat_1(k4_xboole_0(esk3_0,k7_relat_1(esk3_0,esk2_0)),esk1_0)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_34, c_0_16])).
% 0.19/0.43  cnf(c_0_40, negated_conjecture, (k7_relat_1(k4_xboole_0(esk3_0,k7_relat_1(esk3_0,X1)),X2)=k1_xboole_0|~r1_xboole_0(k4_xboole_0(k1_relat_1(esk3_0),X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_22])])).
% 0.19/0.43  cnf(c_0_41, negated_conjecture, (r1_xboole_0(k4_xboole_0(X1,esk2_0),esk1_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.19/0.43  cnf(c_0_42, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41])]), ['proof']).
% 0.19/0.43  # SZS output end CNFRefutation
% 0.19/0.43  # Proof object total steps             : 43
% 0.19/0.43  # Proof object clause steps            : 22
% 0.19/0.43  # Proof object formula steps           : 21
% 0.19/0.43  # Proof object conjectures             : 15
% 0.19/0.43  # Proof object clause conjectures      : 12
% 0.19/0.43  # Proof object formula conjectures     : 3
% 0.19/0.43  # Proof object initial clauses used    : 12
% 0.19/0.43  # Proof object initial formulas used   : 10
% 0.19/0.43  # Proof object generating inferences   : 8
% 0.19/0.43  # Proof object simplifying inferences  : 9
% 0.19/0.43  # Training examples: 0 positive, 0 negative
% 0.19/0.43  # Parsed axioms                        : 10
% 0.19/0.43  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.43  # Initial clauses                      : 14
% 0.19/0.43  # Removed in clause preprocessing      : 1
% 0.19/0.43  # Initial clauses in saturation        : 13
% 0.19/0.43  # Processed clauses                    : 593
% 0.19/0.43  # ...of these trivial                  : 53
% 0.19/0.43  # ...subsumed                          : 129
% 0.19/0.43  # ...remaining for further processing  : 411
% 0.19/0.43  # Other redundant clauses eliminated   : 0
% 0.19/0.43  # Clauses deleted for lack of memory   : 0
% 0.19/0.43  # Backward-subsumed                    : 1
% 0.19/0.43  # Backward-rewritten                   : 14
% 0.19/0.43  # Generated clauses                    : 4777
% 0.19/0.43  # ...of the previous two non-trivial   : 2896
% 0.19/0.43  # Contextual simplify-reflections      : 0
% 0.19/0.43  # Paramodulations                      : 4777
% 0.19/0.43  # Factorizations                       : 0
% 0.19/0.43  # Equation resolutions                 : 0
% 0.19/0.43  # Propositional unsat checks           : 0
% 0.19/0.43  #    Propositional check models        : 0
% 0.19/0.43  #    Propositional check unsatisfiable : 0
% 0.19/0.43  #    Propositional clauses             : 0
% 0.19/0.43  #    Propositional clauses after purity: 0
% 0.19/0.43  #    Propositional unsat core size     : 0
% 0.19/0.43  #    Propositional preprocessing time  : 0.000
% 0.19/0.43  #    Propositional encoding time       : 0.000
% 0.19/0.43  #    Propositional solver time         : 0.000
% 0.19/0.43  #    Success case prop preproc time    : 0.000
% 0.19/0.43  #    Success case prop encoding time   : 0.000
% 0.19/0.43  #    Success case prop solver time     : 0.000
% 0.19/0.43  # Current number of processed clauses  : 383
% 0.19/0.43  #    Positive orientable unit clauses  : 350
% 0.19/0.43  #    Positive unorientable unit clauses: 1
% 0.19/0.43  #    Negative unit clauses             : 1
% 0.19/0.43  #    Non-unit-clauses                  : 31
% 0.19/0.43  # Current number of unprocessed clauses: 2329
% 0.19/0.43  # ...number of literals in the above   : 2614
% 0.19/0.43  # Current number of archived formulas  : 0
% 0.19/0.43  # Current number of archived clauses   : 29
% 0.19/0.43  # Clause-clause subsumption calls (NU) : 548
% 0.19/0.43  # Rec. Clause-clause subsumption calls : 548
% 0.19/0.43  # Non-unit clause-clause subsumptions  : 130
% 0.19/0.43  # Unit Clause-clause subsumption calls : 18
% 0.19/0.43  # Rewrite failures with RHS unbound    : 0
% 0.19/0.43  # BW rewrite match attempts            : 1399
% 0.19/0.43  # BW rewrite match successes           : 14
% 0.19/0.43  # Condensation attempts                : 0
% 0.19/0.43  # Condensation successes               : 0
% 0.19/0.43  # Termbank termtop insertions          : 62313
% 0.19/0.43  
% 0.19/0.43  # -------------------------------------------------
% 0.19/0.43  # User time                : 0.084 s
% 0.19/0.43  # System time              : 0.008 s
% 0.19/0.43  # Total time               : 0.092 s
% 0.19/0.43  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:52:43 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   41 (  65 expanded)
%              Number of clauses        :   22 (  27 expanded)
%              Number of leaves         :    9 (  16 expanded)
%              Depth                    :    7
%              Number of atoms          :   83 ( 137 expanded)
%              Number of equality atoms :   23 (  44 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t85_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_xboole_0(X1,k4_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

fof(t207_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_xboole_0(X1,X2)
       => k7_relat_1(k7_relat_1(X3,X1),X2) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).

fof(t216_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => k7_relat_1(k6_subset_1(X3,k7_relat_1(X3,X2)),X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t216_relat_1)).

fof(t109_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k7_relat_1(X3,k6_subset_1(X1,X2)) = k6_subset_1(k7_relat_1(X3,X1),k7_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_relat_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t209_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => X2 = k7_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(c_0_9,plain,(
    ! [X4,X5] :
      ( ~ r1_xboole_0(X4,X5)
      | r1_xboole_0(X5,X4) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

fof(c_0_10,plain,(
    ! [X8,X9,X10] :
      ( ~ r1_tarski(X8,X9)
      | r1_xboole_0(X8,k4_xboole_0(X10,X9)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_xboole_1])])).

fof(c_0_11,plain,(
    ! [X18,X19,X20] :
      ( ~ v1_relat_1(X20)
      | ~ r1_xboole_0(X18,X19)
      | k7_relat_1(k7_relat_1(X20,X18),X19) = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t207_relat_1])])).

cnf(c_0_12,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( r1_tarski(X1,X2)
         => k7_relat_1(k6_subset_1(X3,k7_relat_1(X3,X2)),X1) = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t216_relat_1])).

fof(c_0_15,plain,(
    ! [X15,X16,X17] :
      ( ~ v1_relat_1(X17)
      | k7_relat_1(X17,k6_subset_1(X15,X16)) = k6_subset_1(k7_relat_1(X17,X15),k7_relat_1(X17,X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t109_relat_1])])).

fof(c_0_16,plain,(
    ! [X11,X12] : k6_subset_1(X11,X12) = k4_xboole_0(X11,X12) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

fof(c_0_17,plain,(
    ! [X13,X14] :
      ( ( ~ v4_relat_1(X14,X13)
        | r1_tarski(k1_relat_1(X14),X13)
        | ~ v1_relat_1(X14) )
      & ( ~ r1_tarski(k1_relat_1(X14),X13)
        | v4_relat_1(X14,X13)
        | ~ v1_relat_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

fof(c_0_18,plain,(
    ! [X6,X7] : r1_tarski(X6,k2_xboole_0(X6,X7)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_19,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

fof(c_0_21,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & r1_tarski(esk1_0,esk2_0)
    & k7_relat_1(k6_subset_1(esk3_0,k7_relat_1(esk3_0,esk2_0)),esk1_0) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

cnf(c_0_22,plain,
    ( k7_relat_1(X1,k6_subset_1(X2,X3)) = k6_subset_1(k7_relat_1(X1,X2),k7_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( v4_relat_1(X1,X2)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( k7_relat_1(k7_relat_1(X1,k4_xboole_0(X2,X3)),X4) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X4,X3) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( k7_relat_1(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k7_relat_1(X1,X2),k7_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_23]),c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_30,plain,(
    ! [X21,X22] :
      ( ~ v1_relat_1(X22)
      | ~ v4_relat_1(X22,X21)
      | X22 = k7_relat_1(X22,X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).

cnf(c_0_31,plain,
    ( v4_relat_1(X1,k2_xboole_0(k1_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( k7_relat_1(k7_relat_1(X1,k4_xboole_0(X2,esk2_0)),esk1_0) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( k7_relat_1(esk3_0,k4_xboole_0(X1,X2)) = k4_xboole_0(k7_relat_1(esk3_0,X1),k7_relat_1(esk3_0,X2)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_34,plain,
    ( X1 = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( v4_relat_1(esk3_0,k2_xboole_0(k1_relat_1(esk3_0),X1)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( k7_relat_1(k6_subset_1(esk3_0,k7_relat_1(esk3_0,esk2_0)),esk1_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_37,negated_conjecture,
    ( k7_relat_1(k4_xboole_0(k7_relat_1(esk3_0,X1),k7_relat_1(esk3_0,esk2_0)),esk1_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_29]),c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( k7_relat_1(esk3_0,k2_xboole_0(k1_relat_1(esk3_0),X1)) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_29])])).

cnf(c_0_39,negated_conjecture,
    ( k7_relat_1(k4_xboole_0(esk3_0,k7_relat_1(esk3_0,esk2_0)),esk1_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_36,c_0_23])).

cnf(c_0_40,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:11:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___208_B00_00_F1_SE_CS_SP_PS_S070I
% 0.13/0.37  # and selection function SelectVGNonCR.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.027 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.13/0.37  fof(t85_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_xboole_0(X1,k4_xboole_0(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 0.13/0.37  fof(t207_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_xboole_0(X1,X2)=>k7_relat_1(k7_relat_1(X3,X1),X2)=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t207_relat_1)).
% 0.13/0.37  fof(t216_relat_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>k7_relat_1(k6_subset_1(X3,k7_relat_1(X3,X2)),X1)=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t216_relat_1)).
% 0.13/0.37  fof(t109_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k7_relat_1(X3,k6_subset_1(X1,X2))=k6_subset_1(k7_relat_1(X3,X1),k7_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_relat_1)).
% 0.13/0.37  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 0.13/0.37  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 0.13/0.37  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.13/0.37  fof(t209_relat_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>X2=k7_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 0.13/0.37  fof(c_0_9, plain, ![X4, X5]:(~r1_xboole_0(X4,X5)|r1_xboole_0(X5,X4)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.13/0.37  fof(c_0_10, plain, ![X8, X9, X10]:(~r1_tarski(X8,X9)|r1_xboole_0(X8,k4_xboole_0(X10,X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_xboole_1])])).
% 0.13/0.37  fof(c_0_11, plain, ![X18, X19, X20]:(~v1_relat_1(X20)|(~r1_xboole_0(X18,X19)|k7_relat_1(k7_relat_1(X20,X18),X19)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t207_relat_1])])).
% 0.13/0.37  cnf(c_0_12, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.37  cnf(c_0_13, plain, (r1_xboole_0(X1,k4_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.37  fof(c_0_14, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>k7_relat_1(k6_subset_1(X3,k7_relat_1(X3,X2)),X1)=k1_xboole_0))), inference(assume_negation,[status(cth)],[t216_relat_1])).
% 0.13/0.37  fof(c_0_15, plain, ![X15, X16, X17]:(~v1_relat_1(X17)|k7_relat_1(X17,k6_subset_1(X15,X16))=k6_subset_1(k7_relat_1(X17,X15),k7_relat_1(X17,X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t109_relat_1])])).
% 0.13/0.37  fof(c_0_16, plain, ![X11, X12]:k6_subset_1(X11,X12)=k4_xboole_0(X11,X12), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 0.13/0.37  fof(c_0_17, plain, ![X13, X14]:((~v4_relat_1(X14,X13)|r1_tarski(k1_relat_1(X14),X13)|~v1_relat_1(X14))&(~r1_tarski(k1_relat_1(X14),X13)|v4_relat_1(X14,X13)|~v1_relat_1(X14))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.13/0.37  fof(c_0_18, plain, ![X6, X7]:r1_tarski(X6,k2_xboole_0(X6,X7)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.13/0.37  cnf(c_0_19, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k1_xboole_0|~v1_relat_1(X1)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.37  cnf(c_0_20, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X3)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.13/0.37  fof(c_0_21, negated_conjecture, (v1_relat_1(esk3_0)&(r1_tarski(esk1_0,esk2_0)&k7_relat_1(k6_subset_1(esk3_0,k7_relat_1(esk3_0,esk2_0)),esk1_0)!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.13/0.37  cnf(c_0_22, plain, (k7_relat_1(X1,k6_subset_1(X2,X3))=k6_subset_1(k7_relat_1(X1,X2),k7_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.37  cnf(c_0_23, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.37  cnf(c_0_24, plain, (v4_relat_1(X1,X2)|~r1_tarski(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.37  cnf(c_0_25, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.37  cnf(c_0_26, plain, (k7_relat_1(k7_relat_1(X1,k4_xboole_0(X2,X3)),X4)=k1_xboole_0|~v1_relat_1(X1)|~r1_tarski(X4,X3)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.13/0.37  cnf(c_0_27, negated_conjecture, (r1_tarski(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.37  cnf(c_0_28, plain, (k7_relat_1(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k7_relat_1(X1,X2),k7_relat_1(X1,X3))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_23]), c_0_23])).
% 0.13/0.37  cnf(c_0_29, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.37  fof(c_0_30, plain, ![X21, X22]:(~v1_relat_1(X22)|~v4_relat_1(X22,X21)|X22=k7_relat_1(X22,X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).
% 0.13/0.37  cnf(c_0_31, plain, (v4_relat_1(X1,k2_xboole_0(k1_relat_1(X1),X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.13/0.37  cnf(c_0_32, negated_conjecture, (k7_relat_1(k7_relat_1(X1,k4_xboole_0(X2,esk2_0)),esk1_0)=k1_xboole_0|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.13/0.37  cnf(c_0_33, negated_conjecture, (k7_relat_1(esk3_0,k4_xboole_0(X1,X2))=k4_xboole_0(k7_relat_1(esk3_0,X1),k7_relat_1(esk3_0,X2))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.13/0.37  cnf(c_0_34, plain, (X1=k7_relat_1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.37  cnf(c_0_35, negated_conjecture, (v4_relat_1(esk3_0,k2_xboole_0(k1_relat_1(esk3_0),X1))), inference(spm,[status(thm)],[c_0_31, c_0_29])).
% 0.13/0.37  cnf(c_0_36, negated_conjecture, (k7_relat_1(k6_subset_1(esk3_0,k7_relat_1(esk3_0,esk2_0)),esk1_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.37  cnf(c_0_37, negated_conjecture, (k7_relat_1(k4_xboole_0(k7_relat_1(esk3_0,X1),k7_relat_1(esk3_0,esk2_0)),esk1_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_29]), c_0_33])).
% 0.13/0.37  cnf(c_0_38, negated_conjecture, (k7_relat_1(esk3_0,k2_xboole_0(k1_relat_1(esk3_0),X1))=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_29])])).
% 0.13/0.37  cnf(c_0_39, negated_conjecture, (k7_relat_1(k4_xboole_0(esk3_0,k7_relat_1(esk3_0,esk2_0)),esk1_0)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_36, c_0_23])).
% 0.13/0.37  cnf(c_0_40, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 41
% 0.13/0.37  # Proof object clause steps            : 22
% 0.13/0.37  # Proof object formula steps           : 19
% 0.13/0.37  # Proof object conjectures             : 13
% 0.13/0.37  # Proof object clause conjectures      : 10
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 11
% 0.13/0.37  # Proof object initial formulas used   : 9
% 0.13/0.37  # Proof object generating inferences   : 9
% 0.13/0.37  # Proof object simplifying inferences  : 7
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 9
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 12
% 0.13/0.37  # Removed in clause preprocessing      : 1
% 0.13/0.37  # Initial clauses in saturation        : 11
% 0.13/0.37  # Processed clauses                    : 35
% 0.13/0.37  # ...of these trivial                  : 0
% 0.13/0.37  # ...subsumed                          : 1
% 0.13/0.37  # ...remaining for further processing  : 34
% 0.13/0.37  # Other redundant clauses eliminated   : 0
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 0
% 0.13/0.37  # Backward-rewritten                   : 0
% 0.13/0.37  # Generated clauses                    : 18
% 0.13/0.37  # ...of the previous two non-trivial   : 16
% 0.13/0.37  # Contextual simplify-reflections      : 0
% 0.13/0.37  # Paramodulations                      : 18
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 0
% 0.13/0.37  # Propositional unsat checks           : 0
% 0.13/0.37  #    Propositional check models        : 0
% 0.13/0.37  #    Propositional check unsatisfiable : 0
% 0.13/0.37  #    Propositional clauses             : 0
% 0.13/0.37  #    Propositional clauses after purity: 0
% 0.13/0.37  #    Propositional unsat core size     : 0
% 0.13/0.37  #    Propositional preprocessing time  : 0.000
% 0.13/0.37  #    Propositional encoding time       : 0.000
% 0.13/0.37  #    Propositional solver time         : 0.000
% 0.13/0.37  #    Success case prop preproc time    : 0.000
% 0.13/0.37  #    Success case prop encoding time   : 0.000
% 0.13/0.37  #    Success case prop solver time     : 0.000
% 0.13/0.37  # Current number of processed clauses  : 23
% 0.13/0.37  #    Positive orientable unit clauses  : 8
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 1
% 0.13/0.37  #    Non-unit-clauses                  : 14
% 0.13/0.37  # Current number of unprocessed clauses: 2
% 0.13/0.37  # ...number of literals in the above   : 3
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 12
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 17
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 17
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 1
% 0.13/0.37  # Unit Clause-clause subsumption calls : 9
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 0
% 0.13/0.37  # BW rewrite match successes           : 0
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 1140
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.026 s
% 0.13/0.37  # System time              : 0.005 s
% 0.13/0.37  # Total time               : 0.031 s
% 0.13/0.37  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:52:41 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   40 (  52 expanded)
%              Number of clauses        :   21 (  23 expanded)
%              Number of leaves         :    9 (  13 expanded)
%              Depth                    :    8
%              Number of atoms          :   94 ( 118 expanded)
%              Number of equality atoms :   27 (  39 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t85_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_xboole_0(X1,k4_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

fof(t109_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k7_relat_1(X3,k6_subset_1(X1,X2)) = k6_subset_1(k7_relat_1(X3,X1),k7_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_relat_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(t209_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => X2 = k7_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(t216_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => k7_relat_1(k6_subset_1(X3,k7_relat_1(X3,X2)),X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t216_relat_1)).

fof(t207_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_xboole_0(X1,X2)
       => k7_relat_1(k7_relat_1(X3,X1),X2) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).

fof(c_0_9,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | X6 != X7 )
      & ( r1_tarski(X7,X6)
        | X6 != X7 )
      & ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,X6)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_10,plain,(
    ! [X13,X14] :
      ( ( ~ v4_relat_1(X14,X13)
        | r1_tarski(k1_relat_1(X14),X13)
        | ~ v1_relat_1(X14) )
      & ( ~ r1_tarski(k1_relat_1(X14),X13)
        | v4_relat_1(X14,X13)
        | ~ v1_relat_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

cnf(c_0_11,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_12,plain,(
    ! [X4,X5] :
      ( ~ r1_xboole_0(X4,X5)
      | r1_xboole_0(X5,X4) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

fof(c_0_13,plain,(
    ! [X8,X9,X10] :
      ( ~ r1_tarski(X8,X9)
      | r1_xboole_0(X8,k4_xboole_0(X10,X9)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_xboole_1])])).

fof(c_0_14,plain,(
    ! [X15,X16,X17] :
      ( ~ v1_relat_1(X17)
      | k7_relat_1(X17,k6_subset_1(X15,X16)) = k6_subset_1(k7_relat_1(X17,X15),k7_relat_1(X17,X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t109_relat_1])])).

fof(c_0_15,plain,(
    ! [X11,X12] : k6_subset_1(X11,X12) = k4_xboole_0(X11,X12) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

fof(c_0_16,plain,(
    ! [X21,X22] :
      ( ~ v1_relat_1(X22)
      | ~ v4_relat_1(X22,X21)
      | X22 = k7_relat_1(X22,X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).

cnf(c_0_17,plain,
    ( v4_relat_1(X1,X2)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_11])).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( r1_tarski(X1,X2)
         => k7_relat_1(k6_subset_1(X3,k7_relat_1(X3,X2)),X1) = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t216_relat_1])).

fof(c_0_20,plain,(
    ! [X18,X19,X20] :
      ( ~ v1_relat_1(X20)
      | ~ r1_xboole_0(X18,X19)
      | k7_relat_1(k7_relat_1(X20,X18),X19) = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t207_relat_1])])).

cnf(c_0_21,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,plain,
    ( k7_relat_1(X1,k6_subset_1(X2,X3)) = k6_subset_1(k7_relat_1(X1,X2),k7_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( X1 = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( v4_relat_1(X1,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

fof(c_0_27,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & r1_tarski(esk1_0,esk2_0)
    & k7_relat_1(k6_subset_1(esk3_0,k7_relat_1(esk3_0,esk2_0)),esk1_0) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

cnf(c_0_28,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_30,plain,
    ( k7_relat_1(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k7_relat_1(X1,X2),k7_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24]),c_0_24])).

cnf(c_0_31,plain,
    ( k7_relat_1(X1,k1_relat_1(X1)) = X1
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( k7_relat_1(k6_subset_1(esk3_0,k7_relat_1(esk3_0,esk2_0)),esk1_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,plain,
    ( k7_relat_1(k7_relat_1(X1,k4_xboole_0(X2,X3)),X4) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X4,X3) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_34,plain,
    ( k7_relat_1(X1,k4_xboole_0(k1_relat_1(X1),X2)) = k4_xboole_0(X1,k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( k7_relat_1(k4_xboole_0(esk3_0,k7_relat_1(esk3_0,esk2_0)),esk1_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_32,c_0_24])).

cnf(c_0_36,plain,
    ( k7_relat_1(k4_xboole_0(X1,k7_relat_1(X1,X2)),X3) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_37,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_39,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_38])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:27:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.49  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_TT_S0Y
% 0.21/0.49  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.21/0.49  #
% 0.21/0.49  # Preprocessing time       : 0.027 s
% 0.21/0.49  # Presaturation interreduction done
% 0.21/0.49  
% 0.21/0.49  # Proof found!
% 0.21/0.49  # SZS status Theorem
% 0.21/0.49  # SZS output start CNFRefutation
% 0.21/0.49  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.21/0.49  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 0.21/0.49  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.21/0.49  fof(t85_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_xboole_0(X1,k4_xboole_0(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 0.21/0.49  fof(t109_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k7_relat_1(X3,k6_subset_1(X1,X2))=k6_subset_1(k7_relat_1(X3,X1),k7_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t109_relat_1)).
% 0.21/0.49  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 0.21/0.49  fof(t209_relat_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>X2=k7_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 0.21/0.49  fof(t216_relat_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>k7_relat_1(k6_subset_1(X3,k7_relat_1(X3,X2)),X1)=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t216_relat_1)).
% 0.21/0.49  fof(t207_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_xboole_0(X1,X2)=>k7_relat_1(k7_relat_1(X3,X1),X2)=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t207_relat_1)).
% 0.21/0.49  fof(c_0_9, plain, ![X6, X7]:(((r1_tarski(X6,X7)|X6!=X7)&(r1_tarski(X7,X6)|X6!=X7))&(~r1_tarski(X6,X7)|~r1_tarski(X7,X6)|X6=X7)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.21/0.49  fof(c_0_10, plain, ![X13, X14]:((~v4_relat_1(X14,X13)|r1_tarski(k1_relat_1(X14),X13)|~v1_relat_1(X14))&(~r1_tarski(k1_relat_1(X14),X13)|v4_relat_1(X14,X13)|~v1_relat_1(X14))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.21/0.49  cnf(c_0_11, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.49  fof(c_0_12, plain, ![X4, X5]:(~r1_xboole_0(X4,X5)|r1_xboole_0(X5,X4)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.21/0.49  fof(c_0_13, plain, ![X8, X9, X10]:(~r1_tarski(X8,X9)|r1_xboole_0(X8,k4_xboole_0(X10,X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_xboole_1])])).
% 0.21/0.49  fof(c_0_14, plain, ![X15, X16, X17]:(~v1_relat_1(X17)|k7_relat_1(X17,k6_subset_1(X15,X16))=k6_subset_1(k7_relat_1(X17,X15),k7_relat_1(X17,X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t109_relat_1])])).
% 0.21/0.49  fof(c_0_15, plain, ![X11, X12]:k6_subset_1(X11,X12)=k4_xboole_0(X11,X12), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 0.21/0.49  fof(c_0_16, plain, ![X21, X22]:(~v1_relat_1(X22)|~v4_relat_1(X22,X21)|X22=k7_relat_1(X22,X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).
% 0.21/0.49  cnf(c_0_17, plain, (v4_relat_1(X1,X2)|~r1_tarski(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.49  cnf(c_0_18, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_11])).
% 0.21/0.49  fof(c_0_19, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>k7_relat_1(k6_subset_1(X3,k7_relat_1(X3,X2)),X1)=k1_xboole_0))), inference(assume_negation,[status(cth)],[t216_relat_1])).
% 0.21/0.49  fof(c_0_20, plain, ![X18, X19, X20]:(~v1_relat_1(X20)|(~r1_xboole_0(X18,X19)|k7_relat_1(k7_relat_1(X20,X18),X19)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t207_relat_1])])).
% 0.21/0.49  cnf(c_0_21, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.49  cnf(c_0_22, plain, (r1_xboole_0(X1,k4_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.49  cnf(c_0_23, plain, (k7_relat_1(X1,k6_subset_1(X2,X3))=k6_subset_1(k7_relat_1(X1,X2),k7_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.49  cnf(c_0_24, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.49  cnf(c_0_25, plain, (X1=k7_relat_1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.49  cnf(c_0_26, plain, (v4_relat_1(X1,k1_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.21/0.49  fof(c_0_27, negated_conjecture, (v1_relat_1(esk3_0)&(r1_tarski(esk1_0,esk2_0)&k7_relat_1(k6_subset_1(esk3_0,k7_relat_1(esk3_0,esk2_0)),esk1_0)!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 0.21/0.49  cnf(c_0_28, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k1_xboole_0|~v1_relat_1(X1)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.49  cnf(c_0_29, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X3)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.21/0.49  cnf(c_0_30, plain, (k7_relat_1(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k7_relat_1(X1,X2),k7_relat_1(X1,X3))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_24]), c_0_24])).
% 0.21/0.49  cnf(c_0_31, plain, (k7_relat_1(X1,k1_relat_1(X1))=X1|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.21/0.49  cnf(c_0_32, negated_conjecture, (k7_relat_1(k6_subset_1(esk3_0,k7_relat_1(esk3_0,esk2_0)),esk1_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.49  cnf(c_0_33, plain, (k7_relat_1(k7_relat_1(X1,k4_xboole_0(X2,X3)),X4)=k1_xboole_0|~v1_relat_1(X1)|~r1_tarski(X4,X3)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.21/0.49  cnf(c_0_34, plain, (k7_relat_1(X1,k4_xboole_0(k1_relat_1(X1),X2))=k4_xboole_0(X1,k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.21/0.49  cnf(c_0_35, negated_conjecture, (k7_relat_1(k4_xboole_0(esk3_0,k7_relat_1(esk3_0,esk2_0)),esk1_0)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_32, c_0_24])).
% 0.21/0.49  cnf(c_0_36, plain, (k7_relat_1(k4_xboole_0(X1,k7_relat_1(X1,X2)),X3)=k1_xboole_0|~v1_relat_1(X1)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.21/0.49  cnf(c_0_37, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.49  cnf(c_0_38, negated_conjecture, (r1_tarski(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.49  cnf(c_0_39, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37]), c_0_38])]), ['proof']).
% 0.21/0.49  # SZS output end CNFRefutation
% 0.21/0.49  # Proof object total steps             : 40
% 0.21/0.49  # Proof object clause steps            : 21
% 0.21/0.49  # Proof object formula steps           : 19
% 0.21/0.49  # Proof object conjectures             : 8
% 0.21/0.49  # Proof object clause conjectures      : 5
% 0.21/0.49  # Proof object formula conjectures     : 3
% 0.21/0.49  # Proof object initial clauses used    : 11
% 0.21/0.49  # Proof object initial formulas used   : 9
% 0.21/0.49  # Proof object generating inferences   : 7
% 0.21/0.49  # Proof object simplifying inferences  : 7
% 0.21/0.49  # Training examples: 0 positive, 0 negative
% 0.21/0.49  # Parsed axioms                        : 9
% 0.21/0.49  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.49  # Initial clauses                      : 14
% 0.21/0.49  # Removed in clause preprocessing      : 1
% 0.21/0.49  # Initial clauses in saturation        : 13
% 0.21/0.49  # Processed clauses                    : 765
% 0.21/0.49  # ...of these trivial                  : 0
% 0.21/0.49  # ...subsumed                          : 473
% 0.21/0.49  # ...remaining for further processing  : 292
% 0.21/0.49  # Other redundant clauses eliminated   : 2
% 0.21/0.49  # Clauses deleted for lack of memory   : 0
% 0.21/0.49  # Backward-subsumed                    : 27
% 0.21/0.49  # Backward-rewritten                   : 0
% 0.21/0.49  # Generated clauses                    : 5335
% 0.21/0.49  # ...of the previous two non-trivial   : 5290
% 0.21/0.49  # Contextual simplify-reflections      : 0
% 0.21/0.49  # Paramodulations                      : 5333
% 0.21/0.49  # Factorizations                       : 0
% 0.21/0.49  # Equation resolutions                 : 2
% 0.21/0.49  # Propositional unsat checks           : 0
% 0.21/0.49  #    Propositional check models        : 0
% 0.21/0.49  #    Propositional check unsatisfiable : 0
% 0.21/0.49  #    Propositional clauses             : 0
% 0.21/0.49  #    Propositional clauses after purity: 0
% 0.21/0.49  #    Propositional unsat core size     : 0
% 0.21/0.49  #    Propositional preprocessing time  : 0.000
% 0.21/0.49  #    Propositional encoding time       : 0.000
% 0.21/0.49  #    Propositional solver time         : 0.000
% 0.21/0.49  #    Success case prop preproc time    : 0.000
% 0.21/0.49  #    Success case prop encoding time   : 0.000
% 0.21/0.49  #    Success case prop solver time     : 0.000
% 0.21/0.49  # Current number of processed clauses  : 251
% 0.21/0.49  #    Positive orientable unit clauses  : 3
% 0.21/0.49  #    Positive unorientable unit clauses: 0
% 0.21/0.49  #    Negative unit clauses             : 1
% 0.21/0.49  #    Non-unit-clauses                  : 247
% 0.21/0.49  # Current number of unprocessed clauses: 4389
% 0.21/0.49  # ...number of literals in the above   : 23525
% 0.21/0.49  # Current number of archived formulas  : 0
% 0.21/0.49  # Current number of archived clauses   : 40
% 0.21/0.49  # Clause-clause subsumption calls (NU) : 14911
% 0.21/0.49  # Rec. Clause-clause subsumption calls : 4341
% 0.21/0.49  # Non-unit clause-clause subsumptions  : 500
% 0.21/0.49  # Unit Clause-clause subsumption calls : 0
% 0.21/0.49  # Rewrite failures with RHS unbound    : 0
% 0.21/0.49  # BW rewrite match attempts            : 2
% 0.21/0.49  # BW rewrite match successes           : 0
% 0.21/0.49  # Condensation attempts                : 0
% 0.21/0.49  # Condensation successes               : 0
% 0.21/0.49  # Termbank termtop insertions          : 103545
% 0.21/0.49  
% 0.21/0.49  # -------------------------------------------------
% 0.21/0.49  # User time                : 0.129 s
% 0.21/0.49  # System time              : 0.011 s
% 0.21/0.49  # Total time               : 0.140 s
% 0.21/0.49  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------

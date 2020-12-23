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
% DateTime   : Thu Dec  3 10:52:44 EST 2020

% Result     : Theorem 4.61s
% Output     : CNFRefutation 4.61s
% Verified   : 
% Statistics : Number of formulae       :   45 (  73 expanded)
%              Number of clauses        :   24 (  32 expanded)
%              Number of leaves         :   10 (  18 expanded)
%              Depth                    :    8
%              Number of atoms          :   82 ( 137 expanded)
%              Number of equality atoms :   27 (  53 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t216_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => k7_relat_1(k6_subset_1(X3,k7_relat_1(X3,X2)),X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t216_relat_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t106_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k4_xboole_0(X2,X3))
     => ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(t212_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k1_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1))) = k6_subset_1(k1_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t212_relat_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t187_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r1_xboole_0(X2,k1_relat_1(X1))
         => k7_relat_1(X1,X2) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(fc2_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_relat_1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( r1_tarski(X1,X2)
         => k7_relat_1(k6_subset_1(X3,k7_relat_1(X3,X2)),X1) = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t216_relat_1])).

fof(c_0_11,plain,(
    ! [X4,X5] :
      ( ~ r1_xboole_0(X4,X5)
      | r1_xboole_0(X5,X4) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

fof(c_0_12,plain,(
    ! [X6,X7,X8] :
      ( ( r1_tarski(X6,X7)
        | ~ r1_tarski(X6,k4_xboole_0(X7,X8)) )
      & ( r1_xboole_0(X6,X8)
        | ~ r1_tarski(X6,k4_xboole_0(X7,X8)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).

fof(c_0_13,plain,(
    ! [X22,X23] :
      ( ~ v1_relat_1(X23)
      | k1_relat_1(k6_subset_1(X23,k7_relat_1(X23,X22))) = k6_subset_1(k1_relat_1(X23),X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t212_relat_1])])).

fof(c_0_14,plain,(
    ! [X16,X17] : k6_subset_1(X16,X17) = k4_xboole_0(X16,X17) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

fof(c_0_15,plain,(
    ! [X9,X10] :
      ( ~ r1_tarski(X9,X10)
      | k2_xboole_0(X9,X10) = X10 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_16,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & r1_tarski(esk1_0,esk2_0)
    & k7_relat_1(k6_subset_1(esk3_0,k7_relat_1(esk3_0,esk2_0)),esk1_0) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

fof(c_0_17,plain,(
    ! [X20,X21] :
      ( ~ v1_relat_1(X20)
      | ~ r1_xboole_0(X21,k1_relat_1(X20))
      | k7_relat_1(X20,X21) = k1_xboole_0 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t187_relat_1])])])).

cnf(c_0_18,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X2))) = k6_subset_1(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_22,plain,(
    ! [X13,X14,X15] : k4_xboole_0(k4_xboole_0(X13,X14),X15) = k4_xboole_0(X13,k2_xboole_0(X14,X15)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_23,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( k7_relat_1(X1,X2) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X2,k4_xboole_0(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_27,plain,
    ( k1_relat_1(k4_xboole_0(X1,k7_relat_1(X1,X2))) = k4_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21]),c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_29,plain,(
    ! [X11,X12] : r1_tarski(k4_xboole_0(X11,X12),X11) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_30,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,negated_conjecture,
    ( k2_xboole_0(esk1_0,esk2_0) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_32,plain,
    ( k7_relat_1(X1,X2) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),k4_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( k1_relat_1(k4_xboole_0(esk3_0,k7_relat_1(esk3_0,X1))) = k4_xboole_0(k1_relat_1(esk3_0),X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

fof(c_0_34,plain,(
    ! [X18,X19] :
      ( ~ v1_relat_1(X18)
      | v1_relat_1(k4_xboole_0(X18,X19)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_relat_1])])).

cnf(c_0_35,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(X1,esk1_0),esk2_0) = k4_xboole_0(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( k7_relat_1(k4_xboole_0(esk3_0,k7_relat_1(esk3_0,X1)),X2) = k1_xboole_0
    | ~ v1_relat_1(k4_xboole_0(esk3_0,k7_relat_1(esk3_0,X1)))
    | ~ r1_tarski(k4_xboole_0(k1_relat_1(esk3_0),X1),k4_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_38,plain,
    ( v1_relat_1(k4_xboole_0(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(k4_xboole_0(X1,esk2_0),k4_xboole_0(X1,esk1_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_40,negated_conjecture,
    ( k7_relat_1(k6_subset_1(esk3_0,k7_relat_1(esk3_0,esk2_0)),esk1_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_41,negated_conjecture,
    ( k7_relat_1(k4_xboole_0(esk3_0,k7_relat_1(esk3_0,X1)),X2) = k1_xboole_0
    | ~ r1_tarski(k4_xboole_0(k1_relat_1(esk3_0),X1),k4_xboole_0(X3,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_28])])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(k4_xboole_0(X1,esk2_0),k4_xboole_0(k4_xboole_0(X1,esk1_0),esk1_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( k7_relat_1(k4_xboole_0(esk3_0,k7_relat_1(esk3_0,esk2_0)),esk1_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_40,c_0_21])).

cnf(c_0_44,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 10:54:37 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.33  # No SInE strategy applied
% 0.13/0.33  # Trying AutoSched0 for 299 seconds
% 4.61/4.80  # AutoSched0-Mode selected heuristic G_E___208_B00_00_F1_SE_CS_SP_PS_S070I
% 4.61/4.80  # and selection function SelectVGNonCR.
% 4.61/4.80  #
% 4.61/4.80  # Preprocessing time       : 0.028 s
% 4.61/4.80  # Presaturation interreduction done
% 4.61/4.80  
% 4.61/4.80  # Proof found!
% 4.61/4.80  # SZS status Theorem
% 4.61/4.80  # SZS output start CNFRefutation
% 4.61/4.80  fof(t216_relat_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>k7_relat_1(k6_subset_1(X3,k7_relat_1(X3,X2)),X1)=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t216_relat_1)).
% 4.61/4.80  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 4.61/4.80  fof(t106_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 4.61/4.80  fof(t212_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k1_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)))=k6_subset_1(k1_relat_1(X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t212_relat_1)).
% 4.61/4.80  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 4.61/4.80  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.61/4.80  fof(t187_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(r1_xboole_0(X2,k1_relat_1(X1))=>k7_relat_1(X1,X2)=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t187_relat_1)).
% 4.61/4.80  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 4.61/4.80  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.61/4.80  fof(fc2_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k4_xboole_0(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_relat_1)).
% 4.61/4.80  fof(c_0_10, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>k7_relat_1(k6_subset_1(X3,k7_relat_1(X3,X2)),X1)=k1_xboole_0))), inference(assume_negation,[status(cth)],[t216_relat_1])).
% 4.61/4.80  fof(c_0_11, plain, ![X4, X5]:(~r1_xboole_0(X4,X5)|r1_xboole_0(X5,X4)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 4.61/4.80  fof(c_0_12, plain, ![X6, X7, X8]:((r1_tarski(X6,X7)|~r1_tarski(X6,k4_xboole_0(X7,X8)))&(r1_xboole_0(X6,X8)|~r1_tarski(X6,k4_xboole_0(X7,X8)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).
% 4.61/4.80  fof(c_0_13, plain, ![X22, X23]:(~v1_relat_1(X23)|k1_relat_1(k6_subset_1(X23,k7_relat_1(X23,X22)))=k6_subset_1(k1_relat_1(X23),X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t212_relat_1])])).
% 4.61/4.80  fof(c_0_14, plain, ![X16, X17]:k6_subset_1(X16,X17)=k4_xboole_0(X16,X17), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 4.61/4.80  fof(c_0_15, plain, ![X9, X10]:(~r1_tarski(X9,X10)|k2_xboole_0(X9,X10)=X10), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 4.61/4.80  fof(c_0_16, negated_conjecture, (v1_relat_1(esk3_0)&(r1_tarski(esk1_0,esk2_0)&k7_relat_1(k6_subset_1(esk3_0,k7_relat_1(esk3_0,esk2_0)),esk1_0)!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 4.61/4.80  fof(c_0_17, plain, ![X20, X21]:(~v1_relat_1(X20)|(~r1_xboole_0(X21,k1_relat_1(X20))|k7_relat_1(X20,X21)=k1_xboole_0)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t187_relat_1])])])).
% 4.61/4.80  cnf(c_0_18, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 4.61/4.80  cnf(c_0_19, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,k4_xboole_0(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 4.61/4.80  cnf(c_0_20, plain, (k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X2)))=k6_subset_1(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 4.61/4.80  cnf(c_0_21, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 4.61/4.80  fof(c_0_22, plain, ![X13, X14, X15]:k4_xboole_0(k4_xboole_0(X13,X14),X15)=k4_xboole_0(X13,k2_xboole_0(X14,X15)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 4.61/4.80  cnf(c_0_23, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 4.61/4.80  cnf(c_0_24, negated_conjecture, (r1_tarski(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 4.61/4.80  cnf(c_0_25, plain, (k7_relat_1(X1,X2)=k1_xboole_0|~v1_relat_1(X1)|~r1_xboole_0(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 4.61/4.80  cnf(c_0_26, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X2,k4_xboole_0(X3,X1))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 4.61/4.80  cnf(c_0_27, plain, (k1_relat_1(k4_xboole_0(X1,k7_relat_1(X1,X2)))=k4_xboole_0(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_21]), c_0_21])).
% 4.61/4.80  cnf(c_0_28, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 4.61/4.80  fof(c_0_29, plain, ![X11, X12]:r1_tarski(k4_xboole_0(X11,X12),X11), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 4.61/4.80  cnf(c_0_30, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 4.61/4.80  cnf(c_0_31, negated_conjecture, (k2_xboole_0(esk1_0,esk2_0)=esk2_0), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 4.61/4.80  cnf(c_0_32, plain, (k7_relat_1(X1,X2)=k1_xboole_0|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),k4_xboole_0(X3,X2))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 4.61/4.80  cnf(c_0_33, negated_conjecture, (k1_relat_1(k4_xboole_0(esk3_0,k7_relat_1(esk3_0,X1)))=k4_xboole_0(k1_relat_1(esk3_0),X1)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 4.61/4.80  fof(c_0_34, plain, ![X18, X19]:(~v1_relat_1(X18)|v1_relat_1(k4_xboole_0(X18,X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_relat_1])])).
% 4.61/4.80  cnf(c_0_35, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 4.61/4.80  cnf(c_0_36, negated_conjecture, (k4_xboole_0(k4_xboole_0(X1,esk1_0),esk2_0)=k4_xboole_0(X1,esk2_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 4.61/4.80  cnf(c_0_37, negated_conjecture, (k7_relat_1(k4_xboole_0(esk3_0,k7_relat_1(esk3_0,X1)),X2)=k1_xboole_0|~v1_relat_1(k4_xboole_0(esk3_0,k7_relat_1(esk3_0,X1)))|~r1_tarski(k4_xboole_0(k1_relat_1(esk3_0),X1),k4_xboole_0(X3,X2))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 4.61/4.80  cnf(c_0_38, plain, (v1_relat_1(k4_xboole_0(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 4.61/4.80  cnf(c_0_39, negated_conjecture, (r1_tarski(k4_xboole_0(X1,esk2_0),k4_xboole_0(X1,esk1_0))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 4.61/4.80  cnf(c_0_40, negated_conjecture, (k7_relat_1(k6_subset_1(esk3_0,k7_relat_1(esk3_0,esk2_0)),esk1_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 4.61/4.80  cnf(c_0_41, negated_conjecture, (k7_relat_1(k4_xboole_0(esk3_0,k7_relat_1(esk3_0,X1)),X2)=k1_xboole_0|~r1_tarski(k4_xboole_0(k1_relat_1(esk3_0),X1),k4_xboole_0(X3,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_28])])).
% 4.61/4.80  cnf(c_0_42, negated_conjecture, (r1_tarski(k4_xboole_0(X1,esk2_0),k4_xboole_0(k4_xboole_0(X1,esk1_0),esk1_0))), inference(spm,[status(thm)],[c_0_39, c_0_36])).
% 4.61/4.80  cnf(c_0_43, negated_conjecture, (k7_relat_1(k4_xboole_0(esk3_0,k7_relat_1(esk3_0,esk2_0)),esk1_0)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_40, c_0_21])).
% 4.61/4.80  cnf(c_0_44, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43]), ['proof']).
% 4.61/4.80  # SZS output end CNFRefutation
% 4.61/4.80  # Proof object total steps             : 45
% 4.61/4.80  # Proof object clause steps            : 24
% 4.61/4.80  # Proof object formula steps           : 21
% 4.61/4.80  # Proof object conjectures             : 15
% 4.61/4.80  # Proof object clause conjectures      : 12
% 4.61/4.80  # Proof object formula conjectures     : 3
% 4.61/4.80  # Proof object initial clauses used    : 12
% 4.61/4.80  # Proof object initial formulas used   : 10
% 4.61/4.80  # Proof object generating inferences   : 10
% 4.61/4.80  # Proof object simplifying inferences  : 6
% 4.61/4.80  # Training examples: 0 positive, 0 negative
% 4.61/4.80  # Parsed axioms                        : 10
% 4.61/4.80  # Removed by relevancy pruning/SinE    : 0
% 4.61/4.80  # Initial clauses                      : 13
% 4.61/4.80  # Removed in clause preprocessing      : 1
% 4.61/4.80  # Initial clauses in saturation        : 12
% 4.61/4.80  # Processed clauses                    : 15021
% 4.61/4.80  # ...of these trivial                  : 417
% 4.61/4.80  # ...subsumed                          : 13103
% 4.61/4.80  # ...remaining for further processing  : 1501
% 4.61/4.80  # Other redundant clauses eliminated   : 0
% 4.61/4.80  # Clauses deleted for lack of memory   : 0
% 4.61/4.80  # Backward-subsumed                    : 48
% 4.61/4.80  # Backward-rewritten                   : 193
% 4.61/4.80  # Generated clauses                    : 428932
% 4.61/4.80  # ...of the previous two non-trivial   : 387502
% 4.61/4.80  # Contextual simplify-reflections      : 0
% 4.61/4.80  # Paramodulations                      : 428932
% 4.61/4.80  # Factorizations                       : 0
% 4.61/4.80  # Equation resolutions                 : 0
% 4.61/4.80  # Propositional unsat checks           : 0
% 4.61/4.80  #    Propositional check models        : 0
% 4.61/4.80  #    Propositional check unsatisfiable : 0
% 4.61/4.80  #    Propositional clauses             : 0
% 4.61/4.80  #    Propositional clauses after purity: 0
% 4.61/4.80  #    Propositional unsat core size     : 0
% 4.61/4.80  #    Propositional preprocessing time  : 0.000
% 4.61/4.80  #    Propositional encoding time       : 0.000
% 4.61/4.80  #    Propositional solver time         : 0.000
% 4.61/4.80  #    Success case prop preproc time    : 0.000
% 4.61/4.80  #    Success case prop encoding time   : 0.000
% 4.61/4.80  #    Success case prop solver time     : 0.000
% 4.61/4.80  # Current number of processed clauses  : 1248
% 4.61/4.80  #    Positive orientable unit clauses  : 407
% 4.61/4.80  #    Positive unorientable unit clauses: 52
% 4.61/4.80  #    Negative unit clauses             : 1
% 4.61/4.80  #    Non-unit-clauses                  : 788
% 4.61/4.80  # Current number of unprocessed clauses: 370795
% 4.61/4.80  # ...number of literals in the above   : 558312
% 4.61/4.80  # Current number of archived formulas  : 0
% 4.61/4.80  # Current number of archived clauses   : 254
% 4.61/4.80  # Clause-clause subsumption calls (NU) : 523529
% 4.61/4.80  # Rec. Clause-clause subsumption calls : 452933
% 4.61/4.80  # Non-unit clause-clause subsumptions  : 13046
% 4.61/4.80  # Unit Clause-clause subsumption calls : 2044
% 4.61/4.80  # Rewrite failures with RHS unbound    : 361026
% 4.61/4.80  # BW rewrite match attempts            : 12490
% 4.61/4.80  # BW rewrite match successes           : 2523
% 4.61/4.80  # Condensation attempts                : 0
% 4.61/4.80  # Condensation successes               : 0
% 4.61/4.80  # Termbank termtop insertions          : 7541699
% 4.61/4.82  
% 4.61/4.82  # -------------------------------------------------
% 4.61/4.82  # User time                : 4.336 s
% 4.61/4.82  # System time              : 0.151 s
% 4.61/4.82  # Total time               : 4.487 s
% 4.61/4.82  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------

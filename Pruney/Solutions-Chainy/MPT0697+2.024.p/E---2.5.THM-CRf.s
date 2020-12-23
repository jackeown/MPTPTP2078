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
% DateTime   : Thu Dec  3 10:55:05 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 164 expanded)
%              Number of clauses        :   39 (  68 expanded)
%              Number of leaves         :   13 (  42 expanded)
%              Depth                    :   10
%              Number of atoms          :  123 ( 358 expanded)
%              Number of equality atoms :   33 (  82 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t45_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => X2 = k2_xboole_0(X1,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t152_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( v2_funct_1(X2)
       => r1_tarski(k10_relat_1(X2,k9_relat_1(X2,X1)),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).

fof(t11_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X1,X2),X3)
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(t167_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

fof(t145_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

fof(t123_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( v2_funct_1(X3)
       => k9_relat_1(X3,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(X3,X1),k9_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_funct_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(t138_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => k10_relat_1(X3,k6_subset_1(X1,X2)) = k6_subset_1(k10_relat_1(X3,X1),k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(t146_funct_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(c_0_13,plain,(
    ! [X16,X17] :
      ( ~ r1_tarski(X16,X17)
      | X17 = k2_xboole_0(X16,k4_xboole_0(X17,X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_xboole_1])])).

fof(c_0_14,plain,(
    ! [X10,X11] : r1_tarski(k4_xboole_0(X10,X11),X10) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( v2_funct_1(X2)
         => r1_tarski(k10_relat_1(X2,k9_relat_1(X2,X1)),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t152_funct_1])).

fof(c_0_16,plain,(
    ! [X6,X7,X8] :
      ( ~ r1_tarski(k2_xboole_0(X6,X7),X8)
      | r1_tarski(X6,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

cnf(c_0_17,plain,
    ( X2 = k2_xboole_0(X1,k4_xboole_0(X2,X1))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,plain,(
    ! [X20,X21] :
      ( ~ v1_relat_1(X21)
      | r1_tarski(k10_relat_1(X21,X20),k1_relat_1(X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).

fof(c_0_20,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v1_funct_1(esk2_0)
    & v2_funct_1(esk2_0)
    & ~ r1_tarski(k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0)),esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

fof(c_0_21,plain,(
    ! [X28,X29] :
      ( ~ v1_relat_1(X29)
      | ~ v1_funct_1(X29)
      | r1_tarski(k9_relat_1(X29,k10_relat_1(X29,X28)),X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).

fof(c_0_22,plain,(
    ! [X22,X23,X24] :
      ( ~ v1_relat_1(X24)
      | ~ v1_funct_1(X24)
      | ~ v2_funct_1(X24)
      | k9_relat_1(X24,k6_subset_1(X22,X23)) = k6_subset_1(k9_relat_1(X24,X22),k9_relat_1(X24,X23)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_funct_1])])).

fof(c_0_23,plain,(
    ! [X18,X19] : k6_subset_1(X18,X19) = k4_xboole_0(X18,X19) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

fof(c_0_24,plain,(
    ! [X25,X26,X27] :
      ( ~ v1_relat_1(X27)
      | ~ v1_funct_1(X27)
      | k10_relat_1(X27,k6_subset_1(X25,X26)) = k6_subset_1(k10_relat_1(X27,X25),k10_relat_1(X27,X26)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t138_funct_1])])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) = X1 ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_27,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_29,plain,(
    ! [X4,X5] :
      ( ( k4_xboole_0(X4,X5) != k1_xboole_0
        | r1_tarski(X4,X5) )
      & ( ~ r1_tarski(X4,X5)
        | k4_xboole_0(X4,X5) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_30,plain,
    ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_32,plain,
    ( k9_relat_1(X1,k6_subset_1(X2,X3)) = k6_subset_1(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,plain,
    ( k10_relat_1(X1,k6_subset_1(X2,X3)) = k6_subset_1(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_35,plain,(
    ! [X12] : k4_xboole_0(X12,k1_xboole_0) = X12 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_36,plain,(
    ! [X30,X31] :
      ( ~ v1_relat_1(X31)
      | ~ r1_tarski(X30,k1_relat_1(X31))
      | r1_tarski(X30,k10_relat_1(X31,k9_relat_1(X31,X30))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_funct_1])])).

cnf(c_0_37,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk2_0,X1),k1_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_39,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk2_0,k10_relat_1(esk2_0,X1)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_28])])).

cnf(c_0_41,plain,
    ( k9_relat_1(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_33]),c_0_33])).

cnf(c_0_42,negated_conjecture,
    ( v2_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_43,plain,
    ( k10_relat_1(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_33]),c_0_33])).

cnf(c_0_44,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_45,plain,
    ( r1_tarski(X2,k10_relat_1(X1,k9_relat_1(X1,X2)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(k4_xboole_0(k10_relat_1(esk2_0,X1),X2),k1_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_47,negated_conjecture,
    ( k4_xboole_0(k9_relat_1(esk2_0,k10_relat_1(esk2_0,X1)),X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( k4_xboole_0(k9_relat_1(esk2_0,X1),k9_relat_1(esk2_0,X2)) = k9_relat_1(esk2_0,k4_xboole_0(X1,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_31]),c_0_28])])).

cnf(c_0_49,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_39,c_0_18])).

cnf(c_0_50,negated_conjecture,
    ( k4_xboole_0(k10_relat_1(esk2_0,X1),k10_relat_1(esk2_0,X2)) = k10_relat_1(esk2_0,k4_xboole_0(X1,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_31]),c_0_28])])).

fof(c_0_51,plain,(
    ! [X9] : r1_tarski(k1_xboole_0,X9) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_44])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(k4_xboole_0(k10_relat_1(esk2_0,X1),X2),k10_relat_1(esk2_0,k9_relat_1(esk2_0,k4_xboole_0(k10_relat_1(esk2_0,X1),X2)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_28])])).

cnf(c_0_54,negated_conjecture,
    ( k9_relat_1(esk2_0,k4_xboole_0(k10_relat_1(esk2_0,k9_relat_1(esk2_0,X1)),X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_55,negated_conjecture,
    ( k10_relat_1(esk2_0,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_50]),c_0_49])).

cnf(c_0_56,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_57,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_39,c_0_52])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(k4_xboole_0(k10_relat_1(esk2_0,k9_relat_1(esk2_0,X1)),X1),k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55])).

cnf(c_0_59,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_39,c_0_56])).

cnf(c_0_60,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_52]),c_0_57])).

cnf(c_0_61,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_62,negated_conjecture,
    ( k4_xboole_0(k10_relat_1(esk2_0,k9_relat_1(esk2_0,X1)),X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_58]),c_0_59]),c_0_60])).

cnf(c_0_63,negated_conjecture,
    ( ~ r1_tarski(k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0)),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk2_0,k9_relat_1(esk2_0,X1)),X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_65,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_64])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.32  % Computer   : n014.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 17:21:37 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  # Version: 2.5pre002
% 0.11/0.33  # No SInE strategy applied
% 0.11/0.33  # Trying AutoSched0 for 299 seconds
% 0.18/0.49  # AutoSched0-Mode selected heuristic G_E___208_C09_12_F1_SE_CS_SP_PS_S064A
% 0.18/0.49  # and selection function SelectComplexG.
% 0.18/0.49  #
% 0.18/0.49  # Preprocessing time       : 0.029 s
% 0.18/0.49  # Presaturation interreduction done
% 0.18/0.49  
% 0.18/0.49  # Proof found!
% 0.18/0.49  # SZS status Theorem
% 0.18/0.49  # SZS output start CNFRefutation
% 0.18/0.49  fof(t45_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>X2=k2_xboole_0(X1,k4_xboole_0(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_xboole_1)).
% 0.18/0.49  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.18/0.49  fof(t152_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(v2_funct_1(X2)=>r1_tarski(k10_relat_1(X2,k9_relat_1(X2,X1)),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_funct_1)).
% 0.18/0.49  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 0.18/0.49  fof(t167_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 0.18/0.49  fof(t145_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_funct_1)).
% 0.18/0.49  fof(t123_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(v2_funct_1(X3)=>k9_relat_1(X3,k6_subset_1(X1,X2))=k6_subset_1(k9_relat_1(X3,X1),k9_relat_1(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_funct_1)).
% 0.18/0.49  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 0.18/0.49  fof(t138_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>k10_relat_1(X3,k6_subset_1(X1,X2))=k6_subset_1(k10_relat_1(X3,X1),k10_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_funct_1)).
% 0.18/0.49  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.18/0.49  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 0.18/0.49  fof(t146_funct_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 0.18/0.49  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.18/0.49  fof(c_0_13, plain, ![X16, X17]:(~r1_tarski(X16,X17)|X17=k2_xboole_0(X16,k4_xboole_0(X17,X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_xboole_1])])).
% 0.18/0.49  fof(c_0_14, plain, ![X10, X11]:r1_tarski(k4_xboole_0(X10,X11),X10), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.18/0.49  fof(c_0_15, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(v2_funct_1(X2)=>r1_tarski(k10_relat_1(X2,k9_relat_1(X2,X1)),X1)))), inference(assume_negation,[status(cth)],[t152_funct_1])).
% 0.18/0.49  fof(c_0_16, plain, ![X6, X7, X8]:(~r1_tarski(k2_xboole_0(X6,X7),X8)|r1_tarski(X6,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 0.18/0.49  cnf(c_0_17, plain, (X2=k2_xboole_0(X1,k4_xboole_0(X2,X1))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.49  cnf(c_0_18, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.49  fof(c_0_19, plain, ![X20, X21]:(~v1_relat_1(X21)|r1_tarski(k10_relat_1(X21,X20),k1_relat_1(X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).
% 0.18/0.49  fof(c_0_20, negated_conjecture, ((v1_relat_1(esk2_0)&v1_funct_1(esk2_0))&(v2_funct_1(esk2_0)&~r1_tarski(k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0)),esk1_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.18/0.49  fof(c_0_21, plain, ![X28, X29]:(~v1_relat_1(X29)|~v1_funct_1(X29)|r1_tarski(k9_relat_1(X29,k10_relat_1(X29,X28)),X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).
% 0.18/0.49  fof(c_0_22, plain, ![X22, X23, X24]:(~v1_relat_1(X24)|~v1_funct_1(X24)|(~v2_funct_1(X24)|k9_relat_1(X24,k6_subset_1(X22,X23))=k6_subset_1(k9_relat_1(X24,X22),k9_relat_1(X24,X23)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_funct_1])])).
% 0.18/0.49  fof(c_0_23, plain, ![X18, X19]:k6_subset_1(X18,X19)=k4_xboole_0(X18,X19), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 0.18/0.49  fof(c_0_24, plain, ![X25, X26, X27]:(~v1_relat_1(X27)|~v1_funct_1(X27)|k10_relat_1(X27,k6_subset_1(X25,X26))=k6_subset_1(k10_relat_1(X27,X25),k10_relat_1(X27,X26))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t138_funct_1])])).
% 0.18/0.49  cnf(c_0_25, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.49  cnf(c_0_26, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))=X1), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.18/0.49  cnf(c_0_27, plain, (r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.18/0.49  cnf(c_0_28, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.49  fof(c_0_29, plain, ![X4, X5]:((k4_xboole_0(X4,X5)!=k1_xboole_0|r1_tarski(X4,X5))&(~r1_tarski(X4,X5)|k4_xboole_0(X4,X5)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.18/0.49  cnf(c_0_30, plain, (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.18/0.49  cnf(c_0_31, negated_conjecture, (v1_funct_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.49  cnf(c_0_32, plain, (k9_relat_1(X1,k6_subset_1(X2,X3))=k6_subset_1(k9_relat_1(X1,X2),k9_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.18/0.49  cnf(c_0_33, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.49  cnf(c_0_34, plain, (k10_relat_1(X1,k6_subset_1(X2,X3))=k6_subset_1(k10_relat_1(X1,X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.18/0.49  fof(c_0_35, plain, ![X12]:k4_xboole_0(X12,k1_xboole_0)=X12, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.18/0.49  fof(c_0_36, plain, ![X30, X31]:(~v1_relat_1(X31)|(~r1_tarski(X30,k1_relat_1(X31))|r1_tarski(X30,k10_relat_1(X31,k9_relat_1(X31,X30))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_funct_1])])).
% 0.18/0.49  cnf(c_0_37, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.18/0.49  cnf(c_0_38, negated_conjecture, (r1_tarski(k10_relat_1(esk2_0,X1),k1_relat_1(esk2_0))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.18/0.49  cnf(c_0_39, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.18/0.49  cnf(c_0_40, negated_conjecture, (r1_tarski(k9_relat_1(esk2_0,k10_relat_1(esk2_0,X1)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_28])])).
% 0.18/0.49  cnf(c_0_41, plain, (k9_relat_1(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_33]), c_0_33])).
% 0.18/0.49  cnf(c_0_42, negated_conjecture, (v2_funct_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.49  cnf(c_0_43, plain, (k10_relat_1(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_33]), c_0_33])).
% 0.18/0.49  cnf(c_0_44, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.18/0.49  cnf(c_0_45, plain, (r1_tarski(X2,k10_relat_1(X1,k9_relat_1(X1,X2)))|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.18/0.49  cnf(c_0_46, negated_conjecture, (r1_tarski(k4_xboole_0(k10_relat_1(esk2_0,X1),X2),k1_relat_1(esk2_0))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.18/0.49  cnf(c_0_47, negated_conjecture, (k4_xboole_0(k9_relat_1(esk2_0,k10_relat_1(esk2_0,X1)),X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.18/0.49  cnf(c_0_48, negated_conjecture, (k4_xboole_0(k9_relat_1(esk2_0,X1),k9_relat_1(esk2_0,X2))=k9_relat_1(esk2_0,k4_xboole_0(X1,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_31]), c_0_28])])).
% 0.18/0.49  cnf(c_0_49, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_39, c_0_18])).
% 0.18/0.49  cnf(c_0_50, negated_conjecture, (k4_xboole_0(k10_relat_1(esk2_0,X1),k10_relat_1(esk2_0,X2))=k10_relat_1(esk2_0,k4_xboole_0(X1,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_31]), c_0_28])])).
% 0.18/0.49  fof(c_0_51, plain, ![X9]:r1_tarski(k1_xboole_0,X9), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.18/0.49  cnf(c_0_52, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_18, c_0_44])).
% 0.18/0.49  cnf(c_0_53, negated_conjecture, (r1_tarski(k4_xboole_0(k10_relat_1(esk2_0,X1),X2),k10_relat_1(esk2_0,k9_relat_1(esk2_0,k4_xboole_0(k10_relat_1(esk2_0,X1),X2))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_28])])).
% 0.18/0.49  cnf(c_0_54, negated_conjecture, (k9_relat_1(esk2_0,k4_xboole_0(k10_relat_1(esk2_0,k9_relat_1(esk2_0,X1)),X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.18/0.49  cnf(c_0_55, negated_conjecture, (k10_relat_1(esk2_0,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_50]), c_0_49])).
% 0.18/0.49  cnf(c_0_56, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.18/0.49  cnf(c_0_57, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_39, c_0_52])).
% 0.18/0.49  cnf(c_0_58, negated_conjecture, (r1_tarski(k4_xboole_0(k10_relat_1(esk2_0,k9_relat_1(esk2_0,X1)),X1),k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55])).
% 0.18/0.49  cnf(c_0_59, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_39, c_0_56])).
% 0.18/0.49  cnf(c_0_60, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_52]), c_0_57])).
% 0.18/0.49  cnf(c_0_61, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.18/0.49  cnf(c_0_62, negated_conjecture, (k4_xboole_0(k10_relat_1(esk2_0,k9_relat_1(esk2_0,X1)),X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_58]), c_0_59]), c_0_60])).
% 0.18/0.49  cnf(c_0_63, negated_conjecture, (~r1_tarski(k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0)),esk1_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.49  cnf(c_0_64, negated_conjecture, (r1_tarski(k10_relat_1(esk2_0,k9_relat_1(esk2_0,X1)),X1)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.18/0.49  cnf(c_0_65, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_64])]), ['proof']).
% 0.18/0.49  # SZS output end CNFRefutation
% 0.18/0.49  # Proof object total steps             : 66
% 0.18/0.49  # Proof object clause steps            : 39
% 0.18/0.49  # Proof object formula steps           : 27
% 0.18/0.49  # Proof object conjectures             : 20
% 0.18/0.49  # Proof object clause conjectures      : 17
% 0.18/0.49  # Proof object formula conjectures     : 3
% 0.18/0.49  # Proof object initial clauses used    : 17
% 0.18/0.49  # Proof object initial formulas used   : 13
% 0.18/0.49  # Proof object generating inferences   : 19
% 0.18/0.49  # Proof object simplifying inferences  : 21
% 0.18/0.49  # Training examples: 0 positive, 0 negative
% 0.18/0.49  # Parsed axioms                        : 14
% 0.18/0.49  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.49  # Initial clauses                      : 18
% 0.18/0.49  # Removed in clause preprocessing      : 1
% 0.18/0.49  # Initial clauses in saturation        : 17
% 0.18/0.49  # Processed clauses                    : 761
% 0.18/0.49  # ...of these trivial                  : 91
% 0.18/0.49  # ...subsumed                          : 291
% 0.18/0.49  # ...remaining for further processing  : 379
% 0.18/0.49  # Other redundant clauses eliminated   : 1
% 0.18/0.49  # Clauses deleted for lack of memory   : 0
% 0.18/0.49  # Backward-subsumed                    : 0
% 0.18/0.49  # Backward-rewritten                   : 15
% 0.18/0.49  # Generated clauses                    : 14226
% 0.18/0.49  # ...of the previous two non-trivial   : 7288
% 0.18/0.49  # Contextual simplify-reflections      : 0
% 0.18/0.49  # Paramodulations                      : 14225
% 0.18/0.49  # Factorizations                       : 0
% 0.18/0.49  # Equation resolutions                 : 1
% 0.18/0.49  # Propositional unsat checks           : 0
% 0.18/0.49  #    Propositional check models        : 0
% 0.18/0.49  #    Propositional check unsatisfiable : 0
% 0.18/0.49  #    Propositional clauses             : 0
% 0.18/0.49  #    Propositional clauses after purity: 0
% 0.18/0.49  #    Propositional unsat core size     : 0
% 0.18/0.49  #    Propositional preprocessing time  : 0.000
% 0.18/0.49  #    Propositional encoding time       : 0.000
% 0.18/0.49  #    Propositional solver time         : 0.000
% 0.18/0.49  #    Success case prop preproc time    : 0.000
% 0.18/0.49  #    Success case prop encoding time   : 0.000
% 0.18/0.49  #    Success case prop solver time     : 0.000
% 0.18/0.49  # Current number of processed clauses  : 347
% 0.18/0.49  #    Positive orientable unit clauses  : 229
% 0.18/0.49  #    Positive unorientable unit clauses: 0
% 0.18/0.49  #    Negative unit clauses             : 0
% 0.18/0.49  #    Non-unit-clauses                  : 118
% 0.18/0.49  # Current number of unprocessed clauses: 6551
% 0.18/0.49  # ...number of literals in the above   : 7028
% 0.18/0.49  # Current number of archived formulas  : 0
% 0.18/0.49  # Current number of archived clauses   : 33
% 0.18/0.49  # Clause-clause subsumption calls (NU) : 2914
% 0.18/0.49  # Rec. Clause-clause subsumption calls : 2875
% 0.18/0.49  # Non-unit clause-clause subsumptions  : 291
% 0.18/0.49  # Unit Clause-clause subsumption calls : 79
% 0.18/0.49  # Rewrite failures with RHS unbound    : 0
% 0.18/0.49  # BW rewrite match attempts            : 559
% 0.18/0.49  # BW rewrite match successes           : 11
% 0.18/0.49  # Condensation attempts                : 0
% 0.18/0.49  # Condensation successes               : 0
% 0.18/0.49  # Termbank termtop insertions          : 222101
% 0.18/0.49  
% 0.18/0.49  # -------------------------------------------------
% 0.18/0.49  # User time                : 0.152 s
% 0.18/0.49  # System time              : 0.010 s
% 0.18/0.49  # Total time               : 0.162 s
% 0.18/0.49  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------

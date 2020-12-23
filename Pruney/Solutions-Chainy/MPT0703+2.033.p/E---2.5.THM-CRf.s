%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:55:18 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 241 expanded)
%              Number of clauses        :   43 ( 108 expanded)
%              Number of leaves         :   12 (  61 expanded)
%              Depth                    :   13
%              Number of atoms          :  140 ( 592 expanded)
%              Number of equality atoms :   27 (  93 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t43_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_xboole_0(X2,X3))
     => r1_tarski(k4_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t158_funct_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( ( r1_tarski(k10_relat_1(X3,X1),k10_relat_1(X3,X2))
          & r1_tarski(X1,k2_relat_1(X3)) )
       => r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).

fof(t45_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => X2 = k2_xboole_0(X1,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

fof(t138_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => k10_relat_1(X3,k6_subset_1(X1,X2)) = k6_subset_1(k10_relat_1(X3,X1),k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(t147_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r1_tarski(X1,k2_relat_1(X2))
       => k9_relat_1(X2,k10_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

fof(t44_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X1,X2),X3)
     => r1_tarski(X1,k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(c_0_12,plain,(
    ! [X11,X12,X13] :
      ( ~ r1_tarski(X11,X12)
      | ~ r1_tarski(X12,X13)
      | r1_tarski(X11,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_13,plain,(
    ! [X15,X16] : r1_tarski(k4_xboole_0(X15,X16),X15) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_14,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_15,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_16,plain,(
    ! [X17,X18,X19] :
      ( ~ r1_tarski(X17,k2_xboole_0(X18,X19))
      | r1_tarski(k4_xboole_0(X17,X18),X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).

fof(c_0_17,plain,(
    ! [X25,X26] : r1_tarski(X25,k2_xboole_0(X25,X26)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_18,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_19,plain,(
    ! [X14] : r1_tarski(k1_xboole_0,X14) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_21,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_23,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => ( ( r1_tarski(k10_relat_1(X3,X1),k10_relat_1(X3,X2))
            & r1_tarski(X1,k2_relat_1(X3)) )
         => r1_tarski(X1,X2) ) ) ),
    inference(assume_negation,[status(cth)],[t158_funct_1])).

cnf(c_0_24,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,k4_xboole_0(X3,X4))) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_14,c_0_22])).

fof(c_0_28,negated_conjecture,
    ( v1_relat_1(esk4_0)
    & v1_funct_1(esk4_0)
    & r1_tarski(k10_relat_1(esk4_0,esk2_0),k10_relat_1(esk4_0,esk3_0))
    & r1_tarski(esk2_0,k2_relat_1(esk4_0))
    & ~ r1_tarski(esk2_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).

fof(c_0_29,plain,(
    ! [X23,X24] :
      ( ~ r1_tarski(X23,X24)
      | X24 = k2_xboole_0(X23,k4_xboole_0(X24,X23)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_xboole_1])])).

cnf(c_0_30,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_31,plain,
    ( r1_tarski(k4_xboole_0(X1,X1),X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_22])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_33,plain,(
    ! [X29,X30,X31] :
      ( ~ v1_relat_1(X31)
      | ~ v1_funct_1(X31)
      | k10_relat_1(X31,k6_subset_1(X29,X30)) = k6_subset_1(k10_relat_1(X31,X29),k10_relat_1(X31,X30)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t138_funct_1])])).

fof(c_0_34,plain,(
    ! [X27,X28] : k6_subset_1(X27,X28) = k4_xboole_0(X27,X28) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X4)
    | ~ r1_tarski(X4,X2) ),
    inference(spm,[status(thm)],[c_0_14,c_0_27])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk4_0,esk2_0),k10_relat_1(esk4_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,plain,
    ( X2 = k2_xboole_0(X1,k4_xboole_0(X2,X1))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_40,plain,
    ( k10_relat_1(X1,k6_subset_1(X2,X3)) = k6_subset_1(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk4_0,esk2_0),k2_xboole_0(X1,X2))
    | ~ r1_tarski(k10_relat_1(esk4_0,esk3_0),X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_43,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(esk2_0,k2_relat_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_45,plain,
    ( k10_relat_1(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_41]),c_0_41])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk4_0,esk2_0),X1)
    | ~ r1_tarski(k10_relat_1(esk4_0,esk3_0),X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(X1,k2_relat_1(esk4_0))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_44])).

cnf(c_0_48,plain,
    ( r1_tarski(k10_relat_1(X1,k4_xboole_0(X2,X3)),X4)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k10_relat_1(X1,X2),k2_xboole_0(k10_relat_1(X1,X3),X4)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_45])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk4_0,esk2_0),k2_xboole_0(k10_relat_1(esk4_0,esk3_0),X1)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_22])).

cnf(c_0_50,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_51,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_52,plain,(
    ! [X32,X33] :
      ( ~ v1_relat_1(X33)
      | ~ v1_funct_1(X33)
      | ~ r1_tarski(X32,k2_relat_1(X33))
      | k9_relat_1(X33,k10_relat_1(X33,X32)) = X32 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t147_funct_1])])).

cnf(c_0_53,plain,
    ( k10_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_38]),c_0_38])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(X1,k2_relat_1(esk4_0))
    | ~ r1_tarski(X2,esk2_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_14,c_0_47])).

fof(c_0_55,plain,(
    ! [X20,X21,X22] :
      ( ~ r1_tarski(k4_xboole_0(X20,X21),X22)
      | r1_tarski(X20,k2_xboole_0(X21,X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk4_0,k4_xboole_0(esk2_0,esk3_0)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50]),c_0_51])])).

cnf(c_0_57,plain,
    ( k9_relat_1(X1,k10_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(X2,k2_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_58,negated_conjecture,
    ( k10_relat_1(esk4_0,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_50]),c_0_51])])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(X1,k2_relat_1(esk4_0))
    | ~ r1_tarski(X1,k4_xboole_0(esk2_0,X2)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_15])).

cnf(c_0_60,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_61,negated_conjecture,
    ( k10_relat_1(esk4_0,k4_xboole_0(esk2_0,esk3_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_30,c_0_56])).

cnf(c_0_62,negated_conjecture,
    ( k9_relat_1(esk4_0,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_50]),c_0_51]),c_0_25])])).

cnf(c_0_63,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk2_0,X1),k2_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_39])).

cnf(c_0_64,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_60,c_0_39])).

cnf(c_0_65,negated_conjecture,
    ( k4_xboole_0(esk2_0,esk3_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_61]),c_0_62]),c_0_50]),c_0_51]),c_0_63])])).

cnf(c_0_66,negated_conjecture,
    ( ~ r1_tarski(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_67,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_43]),c_0_66]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:36:01 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.44  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.44  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.44  #
% 0.19/0.44  # Preprocessing time       : 0.027 s
% 0.19/0.44  # Presaturation interreduction done
% 0.19/0.44  
% 0.19/0.44  # Proof found!
% 0.19/0.44  # SZS status Theorem
% 0.19/0.44  # SZS output start CNFRefutation
% 0.19/0.44  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.19/0.44  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.19/0.44  fof(t43_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_xboole_0(X2,X3))=>r1_tarski(k4_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 0.19/0.44  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.19/0.44  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.44  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.19/0.44  fof(t158_funct_1, conjecture, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((r1_tarski(k10_relat_1(X3,X1),k10_relat_1(X3,X2))&r1_tarski(X1,k2_relat_1(X3)))=>r1_tarski(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t158_funct_1)).
% 0.19/0.44  fof(t45_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>X2=k2_xboole_0(X1,k4_xboole_0(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_xboole_1)).
% 0.19/0.44  fof(t138_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>k10_relat_1(X3,k6_subset_1(X1,X2))=k6_subset_1(k10_relat_1(X3,X1),k10_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_funct_1)).
% 0.19/0.44  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 0.19/0.44  fof(t147_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(X1,k2_relat_1(X2))=>k9_relat_1(X2,k10_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 0.19/0.44  fof(t44_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k4_xboole_0(X1,X2),X3)=>r1_tarski(X1,k2_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 0.19/0.44  fof(c_0_12, plain, ![X11, X12, X13]:(~r1_tarski(X11,X12)|~r1_tarski(X12,X13)|r1_tarski(X11,X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.19/0.44  fof(c_0_13, plain, ![X15, X16]:r1_tarski(k4_xboole_0(X15,X16),X15), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.19/0.44  cnf(c_0_14, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.44  cnf(c_0_15, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.44  fof(c_0_16, plain, ![X17, X18, X19]:(~r1_tarski(X17,k2_xboole_0(X18,X19))|r1_tarski(k4_xboole_0(X17,X18),X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).
% 0.19/0.44  fof(c_0_17, plain, ![X25, X26]:r1_tarski(X25,k2_xboole_0(X25,X26)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.19/0.44  fof(c_0_18, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.44  fof(c_0_19, plain, ![X14]:r1_tarski(k1_xboole_0,X14), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.19/0.44  cnf(c_0_20, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.19/0.44  cnf(c_0_21, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.44  cnf(c_0_22, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.44  fof(c_0_23, negated_conjecture, ~(![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((r1_tarski(k10_relat_1(X3,X1),k10_relat_1(X3,X2))&r1_tarski(X1,k2_relat_1(X3)))=>r1_tarski(X1,X2)))), inference(assume_negation,[status(cth)],[t158_funct_1])).
% 0.19/0.44  cnf(c_0_24, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.44  cnf(c_0_25, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.44  cnf(c_0_26, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k2_xboole_0(X2,k4_xboole_0(X3,X4)))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.44  cnf(c_0_27, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_14, c_0_22])).
% 0.19/0.44  fof(c_0_28, negated_conjecture, ((v1_relat_1(esk4_0)&v1_funct_1(esk4_0))&((r1_tarski(k10_relat_1(esk4_0,esk2_0),k10_relat_1(esk4_0,esk3_0))&r1_tarski(esk2_0,k2_relat_1(esk4_0)))&~r1_tarski(esk2_0,esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).
% 0.19/0.44  fof(c_0_29, plain, ![X23, X24]:(~r1_tarski(X23,X24)|X24=k2_xboole_0(X23,k4_xboole_0(X24,X23))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_xboole_1])])).
% 0.19/0.44  cnf(c_0_30, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.19/0.44  cnf(c_0_31, plain, (r1_tarski(k4_xboole_0(X1,X1),X2)), inference(spm,[status(thm)],[c_0_26, c_0_22])).
% 0.19/0.44  cnf(c_0_32, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.44  fof(c_0_33, plain, ![X29, X30, X31]:(~v1_relat_1(X31)|~v1_funct_1(X31)|k10_relat_1(X31,k6_subset_1(X29,X30))=k6_subset_1(k10_relat_1(X31,X29),k10_relat_1(X31,X30))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t138_funct_1])])).
% 0.19/0.44  fof(c_0_34, plain, ![X27, X28]:k6_subset_1(X27,X28)=k4_xboole_0(X27,X28), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 0.19/0.44  cnf(c_0_35, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(X1,X4)|~r1_tarski(X4,X2)), inference(spm,[status(thm)],[c_0_14, c_0_27])).
% 0.19/0.44  cnf(c_0_36, negated_conjecture, (r1_tarski(k10_relat_1(esk4_0,esk2_0),k10_relat_1(esk4_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.44  cnf(c_0_37, plain, (X2=k2_xboole_0(X1,k4_xboole_0(X2,X1))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.44  cnf(c_0_38, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.19/0.44  cnf(c_0_39, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_32])).
% 0.19/0.44  cnf(c_0_40, plain, (k10_relat_1(X1,k6_subset_1(X2,X3))=k6_subset_1(k10_relat_1(X1,X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.44  cnf(c_0_41, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.44  cnf(c_0_42, negated_conjecture, (r1_tarski(k10_relat_1(esk4_0,esk2_0),k2_xboole_0(X1,X2))|~r1_tarski(k10_relat_1(esk4_0,esk3_0),X1)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.19/0.44  cnf(c_0_43, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])])).
% 0.19/0.44  cnf(c_0_44, negated_conjecture, (r1_tarski(esk2_0,k2_relat_1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.44  cnf(c_0_45, plain, (k10_relat_1(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_41]), c_0_41])).
% 0.19/0.44  cnf(c_0_46, negated_conjecture, (r1_tarski(k10_relat_1(esk4_0,esk2_0),X1)|~r1_tarski(k10_relat_1(esk4_0,esk3_0),X1)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.19/0.44  cnf(c_0_47, negated_conjecture, (r1_tarski(X1,k2_relat_1(esk4_0))|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_14, c_0_44])).
% 0.19/0.44  cnf(c_0_48, plain, (r1_tarski(k10_relat_1(X1,k4_xboole_0(X2,X3)),X4)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(k10_relat_1(X1,X2),k2_xboole_0(k10_relat_1(X1,X3),X4))), inference(spm,[status(thm)],[c_0_21, c_0_45])).
% 0.19/0.44  cnf(c_0_49, negated_conjecture, (r1_tarski(k10_relat_1(esk4_0,esk2_0),k2_xboole_0(k10_relat_1(esk4_0,esk3_0),X1))), inference(spm,[status(thm)],[c_0_46, c_0_22])).
% 0.19/0.44  cnf(c_0_50, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.44  cnf(c_0_51, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.44  fof(c_0_52, plain, ![X32, X33]:(~v1_relat_1(X33)|~v1_funct_1(X33)|(~r1_tarski(X32,k2_relat_1(X33))|k9_relat_1(X33,k10_relat_1(X33,X32))=X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t147_funct_1])])).
% 0.19/0.44  cnf(c_0_53, plain, (k10_relat_1(X1,k1_xboole_0)=k1_xboole_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_38]), c_0_38])).
% 0.19/0.44  cnf(c_0_54, negated_conjecture, (r1_tarski(X1,k2_relat_1(esk4_0))|~r1_tarski(X2,esk2_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_14, c_0_47])).
% 0.19/0.44  fof(c_0_55, plain, ![X20, X21, X22]:(~r1_tarski(k4_xboole_0(X20,X21),X22)|r1_tarski(X20,k2_xboole_0(X21,X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).
% 0.19/0.44  cnf(c_0_56, negated_conjecture, (r1_tarski(k10_relat_1(esk4_0,k4_xboole_0(esk2_0,esk3_0)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50]), c_0_51])])).
% 0.19/0.44  cnf(c_0_57, plain, (k9_relat_1(X1,k10_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~v1_funct_1(X1)|~r1_tarski(X2,k2_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.19/0.44  cnf(c_0_58, negated_conjecture, (k10_relat_1(esk4_0,k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_50]), c_0_51])])).
% 0.19/0.44  cnf(c_0_59, negated_conjecture, (r1_tarski(X1,k2_relat_1(esk4_0))|~r1_tarski(X1,k4_xboole_0(esk2_0,X2))), inference(spm,[status(thm)],[c_0_54, c_0_15])).
% 0.19/0.44  cnf(c_0_60, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.19/0.44  cnf(c_0_61, negated_conjecture, (k10_relat_1(esk4_0,k4_xboole_0(esk2_0,esk3_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_30, c_0_56])).
% 0.19/0.44  cnf(c_0_62, negated_conjecture, (k9_relat_1(esk4_0,k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_50]), c_0_51]), c_0_25])])).
% 0.19/0.44  cnf(c_0_63, negated_conjecture, (r1_tarski(k4_xboole_0(esk2_0,X1),k2_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_59, c_0_39])).
% 0.19/0.44  cnf(c_0_64, plain, (r1_tarski(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_60, c_0_39])).
% 0.19/0.44  cnf(c_0_65, negated_conjecture, (k4_xboole_0(esk2_0,esk3_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_61]), c_0_62]), c_0_50]), c_0_51]), c_0_63])])).
% 0.19/0.44  cnf(c_0_66, negated_conjecture, (~r1_tarski(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.44  cnf(c_0_67, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_43]), c_0_66]), ['proof']).
% 0.19/0.44  # SZS output end CNFRefutation
% 0.19/0.44  # Proof object total steps             : 68
% 0.19/0.44  # Proof object clause steps            : 43
% 0.19/0.44  # Proof object formula steps           : 25
% 0.19/0.44  # Proof object conjectures             : 21
% 0.19/0.44  # Proof object clause conjectures      : 18
% 0.19/0.44  # Proof object formula conjectures     : 3
% 0.19/0.44  # Proof object initial clauses used    : 17
% 0.19/0.44  # Proof object initial formulas used   : 12
% 0.19/0.44  # Proof object generating inferences   : 24
% 0.19/0.44  # Proof object simplifying inferences  : 22
% 0.19/0.44  # Training examples: 0 positive, 0 negative
% 0.19/0.44  # Parsed axioms                        : 13
% 0.19/0.44  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.44  # Initial clauses                      : 21
% 0.19/0.44  # Removed in clause preprocessing      : 1
% 0.19/0.44  # Initial clauses in saturation        : 20
% 0.19/0.44  # Processed clauses                    : 898
% 0.19/0.44  # ...of these trivial                  : 6
% 0.19/0.44  # ...subsumed                          : 590
% 0.19/0.44  # ...remaining for further processing  : 302
% 0.19/0.44  # Other redundant clauses eliminated   : 2
% 0.19/0.44  # Clauses deleted for lack of memory   : 0
% 0.19/0.44  # Backward-subsumed                    : 3
% 0.19/0.44  # Backward-rewritten                   : 17
% 0.19/0.44  # Generated clauses                    : 4104
% 0.19/0.44  # ...of the previous two non-trivial   : 3468
% 0.19/0.44  # Contextual simplify-reflections      : 2
% 0.19/0.44  # Paramodulations                      : 4102
% 0.19/0.44  # Factorizations                       : 0
% 0.19/0.44  # Equation resolutions                 : 2
% 0.19/0.44  # Propositional unsat checks           : 0
% 0.19/0.44  #    Propositional check models        : 0
% 0.19/0.44  #    Propositional check unsatisfiable : 0
% 0.19/0.44  #    Propositional clauses             : 0
% 0.19/0.44  #    Propositional clauses after purity: 0
% 0.19/0.44  #    Propositional unsat core size     : 0
% 0.19/0.44  #    Propositional preprocessing time  : 0.000
% 0.19/0.44  #    Propositional encoding time       : 0.000
% 0.19/0.44  #    Propositional solver time         : 0.000
% 0.19/0.44  #    Success case prop preproc time    : 0.000
% 0.19/0.44  #    Success case prop encoding time   : 0.000
% 0.19/0.44  #    Success case prop solver time     : 0.000
% 0.19/0.44  # Current number of processed clauses  : 261
% 0.19/0.44  #    Positive orientable unit clauses  : 39
% 0.19/0.44  #    Positive unorientable unit clauses: 0
% 0.19/0.44  #    Negative unit clauses             : 1
% 0.19/0.44  #    Non-unit-clauses                  : 221
% 0.19/0.44  # Current number of unprocessed clauses: 2575
% 0.19/0.44  # ...number of literals in the above   : 7422
% 0.19/0.44  # Current number of archived formulas  : 0
% 0.19/0.44  # Current number of archived clauses   : 40
% 0.19/0.44  # Clause-clause subsumption calls (NU) : 11827
% 0.19/0.44  # Rec. Clause-clause subsumption calls : 10156
% 0.19/0.44  # Non-unit clause-clause subsumptions  : 595
% 0.19/0.44  # Unit Clause-clause subsumption calls : 35
% 0.19/0.44  # Rewrite failures with RHS unbound    : 0
% 0.19/0.44  # BW rewrite match attempts            : 64
% 0.19/0.44  # BW rewrite match successes           : 11
% 0.19/0.44  # Condensation attempts                : 0
% 0.19/0.44  # Condensation successes               : 0
% 0.19/0.44  # Termbank termtop insertions          : 57869
% 0.19/0.44  
% 0.19/0.44  # -------------------------------------------------
% 0.19/0.44  # User time                : 0.102 s
% 0.19/0.44  # System time              : 0.003 s
% 0.19/0.44  # Total time               : 0.105 s
% 0.19/0.44  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:54:53 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 222 expanded)
%              Number of clauses        :   37 (  93 expanded)
%              Number of leaves         :   10 (  55 expanded)
%              Depth                    :   14
%              Number of atoms          :  128 ( 582 expanded)
%              Number of equality atoms :   42 ( 202 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t138_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => k10_relat_1(X3,k6_subset_1(X1,X2)) = k6_subset_1(k10_relat_1(X3,X1),k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(t147_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r1_tarski(X1,k2_relat_1(X2))
       => k9_relat_1(X2,k10_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t145_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

fof(t146_funct_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(t167_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(t174_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ~ ( X1 != k1_xboole_0
          & r1_tarski(X1,k2_relat_1(X2))
          & k10_relat_1(X2,X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_relat_1)).

fof(t109_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k4_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_xboole_1)).

fof(c_0_10,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_11,plain,(
    ! [X17,X18,X19] :
      ( ~ v1_relat_1(X19)
      | ~ v1_funct_1(X19)
      | k10_relat_1(X19,k6_subset_1(X17,X18)) = k6_subset_1(k10_relat_1(X19,X17),k10_relat_1(X19,X18)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t138_funct_1])])).

fof(c_0_12,plain,(
    ! [X11,X12] : k6_subset_1(X11,X12) = k4_xboole_0(X11,X12) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( r1_tarski(X1,k2_relat_1(X2))
         => k9_relat_1(X2,k10_relat_1(X2,X1)) = X1 ) ) ),
    inference(assume_negation,[status(cth)],[t147_funct_1])).

fof(c_0_14,plain,(
    ! [X6,X7] :
      ( ( k4_xboole_0(X6,X7) != k1_xboole_0
        | r1_tarski(X6,X7) )
      & ( ~ r1_tarski(X6,X7)
        | k4_xboole_0(X6,X7) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_15,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k10_relat_1(X1,k6_subset_1(X2,X3)) = k6_subset_1(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_18,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v1_funct_1(esk2_0)
    & r1_tarski(esk1_0,k2_relat_1(esk2_0))
    & k9_relat_1(esk2_0,k10_relat_1(esk2_0,esk1_0)) != esk1_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

fof(c_0_19,plain,(
    ! [X20,X21] :
      ( ~ v1_relat_1(X21)
      | ~ v1_funct_1(X21)
      | r1_tarski(k9_relat_1(X21,k10_relat_1(X21,X20)),X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).

cnf(c_0_20,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( k10_relat_1(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_17]),c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

fof(c_0_27,plain,(
    ! [X22,X23] :
      ( ~ v1_relat_1(X23)
      | ~ r1_tarski(X22,k1_relat_1(X23))
      | r1_tarski(X22,k10_relat_1(X23,k9_relat_1(X23,X22))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_funct_1])])).

fof(c_0_28,plain,(
    ! [X13,X14] :
      ( ~ v1_relat_1(X14)
      | r1_tarski(k10_relat_1(X14,X13),k1_relat_1(X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_30,negated_conjecture,
    ( k4_xboole_0(k10_relat_1(esk2_0,X1),k10_relat_1(esk2_0,X2)) = k10_relat_1(esk2_0,k4_xboole_0(X1,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk2_0,k10_relat_1(esk2_0,X1)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_23]),c_0_24])])).

cnf(c_0_32,plain,
    ( k10_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_26]),c_0_26])).

cnf(c_0_33,plain,
    ( r1_tarski(X2,k10_relat_1(X1,k9_relat_1(X1,X2)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk2_0,X1),k10_relat_1(esk2_0,X2))
    | k10_relat_1(esk2_0,k4_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( k4_xboole_0(k9_relat_1(esk2_0,k10_relat_1(esk2_0,X1)),X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_20,c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( k10_relat_1(esk2_0,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_23]),c_0_24])])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(X1,k10_relat_1(esk2_0,k9_relat_1(esk2_0,X1)))
    | ~ r1_tarski(X1,k1_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_24])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk2_0,X1),k1_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_24])).

fof(c_0_40,plain,(
    ! [X15,X16] :
      ( ~ v1_relat_1(X16)
      | X15 = k1_xboole_0
      | ~ r1_tarski(X15,k2_relat_1(X16))
      | k10_relat_1(X16,X15) != k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t174_relat_1])])).

cnf(c_0_41,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk2_0,k9_relat_1(esk2_0,k10_relat_1(esk2_0,X1))),k10_relat_1(esk2_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk2_0,X1),k10_relat_1(esk2_0,k9_relat_1(esk2_0,k10_relat_1(esk2_0,X1)))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_44,plain,
    ( X2 = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k2_relat_1(X1))
    | k10_relat_1(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_45,negated_conjecture,
    ( k10_relat_1(esk2_0,k9_relat_1(esk2_0,k10_relat_1(esk2_0,X1))) = k10_relat_1(esk2_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])])).

cnf(c_0_46,negated_conjecture,
    ( X1 = k1_xboole_0
    | k10_relat_1(esk2_0,X1) != k1_xboole_0
    | ~ r1_tarski(X1,k2_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_24])).

cnf(c_0_47,negated_conjecture,
    ( k10_relat_1(esk2_0,k4_xboole_0(X1,k9_relat_1(esk2_0,k10_relat_1(esk2_0,X2)))) = k10_relat_1(esk2_0,k4_xboole_0(X1,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_45]),c_0_30]),c_0_23]),c_0_24])])).

fof(c_0_48,plain,(
    ! [X8,X9,X10] :
      ( ~ r1_tarski(X8,X9)
      | r1_tarski(k4_xboole_0(X8,X10),X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t109_xboole_1])])).

cnf(c_0_49,negated_conjecture,
    ( k4_xboole_0(X1,k9_relat_1(esk2_0,k10_relat_1(esk2_0,X2))) = k1_xboole_0
    | k10_relat_1(esk2_0,k4_xboole_0(X1,X2)) != k1_xboole_0
    | ~ r1_tarski(k4_xboole_0(X1,k9_relat_1(esk2_0,k10_relat_1(esk2_0,X2))),k2_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_50,plain,
    ( r1_tarski(k4_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(esk1_0,k2_relat_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_52,negated_conjecture,
    ( k4_xboole_0(X1,k9_relat_1(esk2_0,k10_relat_1(esk2_0,X1))) = k1_xboole_0
    | ~ r1_tarski(k4_xboole_0(X1,k9_relat_1(esk2_0,k10_relat_1(esk2_0,X1))),k2_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_26]),c_0_37])])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk1_0,X1),k2_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_54,negated_conjecture,
    ( k4_xboole_0(esk1_0,k9_relat_1(esk2_0,k10_relat_1(esk2_0,esk1_0))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(esk1_0,k9_relat_1(esk2_0,k10_relat_1(esk2_0,esk1_0))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_54])).

cnf(c_0_56,negated_conjecture,
    ( k9_relat_1(esk2_0,k10_relat_1(esk2_0,esk1_0)) != esk1_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_57,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_55]),c_0_31])]),c_0_56]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:39:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.50  # AutoSched0-Mode selected heuristic G_E___107_C00_02_nc_F1_PI_AE_Q4_CS_SP_PS_S00EN
% 0.20/0.50  # and selection function PSelectSmallestOrientable.
% 0.20/0.50  #
% 0.20/0.50  # Preprocessing time       : 0.027 s
% 0.20/0.50  # Presaturation interreduction done
% 0.20/0.50  
% 0.20/0.50  # Proof found!
% 0.20/0.50  # SZS status Theorem
% 0.20/0.50  # SZS output start CNFRefutation
% 0.20/0.50  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.50  fof(t138_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>k10_relat_1(X3,k6_subset_1(X1,X2))=k6_subset_1(k10_relat_1(X3,X1),k10_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_funct_1)).
% 0.20/0.50  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 0.20/0.50  fof(t147_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(X1,k2_relat_1(X2))=>k9_relat_1(X2,k10_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 0.20/0.50  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.20/0.50  fof(t145_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 0.20/0.50  fof(t146_funct_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 0.20/0.50  fof(t167_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 0.20/0.50  fof(t174_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>~(((X1!=k1_xboole_0&r1_tarski(X1,k2_relat_1(X2)))&k10_relat_1(X2,X1)=k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t174_relat_1)).
% 0.20/0.50  fof(t109_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(k4_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t109_xboole_1)).
% 0.20/0.50  fof(c_0_10, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.50  fof(c_0_11, plain, ![X17, X18, X19]:(~v1_relat_1(X19)|~v1_funct_1(X19)|k10_relat_1(X19,k6_subset_1(X17,X18))=k6_subset_1(k10_relat_1(X19,X17),k10_relat_1(X19,X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t138_funct_1])])).
% 0.20/0.50  fof(c_0_12, plain, ![X11, X12]:k6_subset_1(X11,X12)=k4_xboole_0(X11,X12), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 0.20/0.50  fof(c_0_13, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(X1,k2_relat_1(X2))=>k9_relat_1(X2,k10_relat_1(X2,X1))=X1))), inference(assume_negation,[status(cth)],[t147_funct_1])).
% 0.20/0.50  fof(c_0_14, plain, ![X6, X7]:((k4_xboole_0(X6,X7)!=k1_xboole_0|r1_tarski(X6,X7))&(~r1_tarski(X6,X7)|k4_xboole_0(X6,X7)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.20/0.50  cnf(c_0_15, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.50  cnf(c_0_16, plain, (k10_relat_1(X1,k6_subset_1(X2,X3))=k6_subset_1(k10_relat_1(X1,X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.50  cnf(c_0_17, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.50  fof(c_0_18, negated_conjecture, ((v1_relat_1(esk2_0)&v1_funct_1(esk2_0))&(r1_tarski(esk1_0,k2_relat_1(esk2_0))&k9_relat_1(esk2_0,k10_relat_1(esk2_0,esk1_0))!=esk1_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.20/0.50  fof(c_0_19, plain, ![X20, X21]:(~v1_relat_1(X21)|~v1_funct_1(X21)|r1_tarski(k9_relat_1(X21,k10_relat_1(X21,X20)),X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).
% 0.20/0.50  cnf(c_0_20, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.50  cnf(c_0_21, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_15])).
% 0.20/0.50  cnf(c_0_22, plain, (k10_relat_1(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16, c_0_17]), c_0_17])).
% 0.20/0.50  cnf(c_0_23, negated_conjecture, (v1_funct_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.50  cnf(c_0_24, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.50  cnf(c_0_25, plain, (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.50  cnf(c_0_26, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.20/0.50  fof(c_0_27, plain, ![X22, X23]:(~v1_relat_1(X23)|(~r1_tarski(X22,k1_relat_1(X23))|r1_tarski(X22,k10_relat_1(X23,k9_relat_1(X23,X22))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_funct_1])])).
% 0.20/0.50  fof(c_0_28, plain, ![X13, X14]:(~v1_relat_1(X14)|r1_tarski(k10_relat_1(X14,X13),k1_relat_1(X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).
% 0.20/0.50  cnf(c_0_29, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.50  cnf(c_0_30, negated_conjecture, (k4_xboole_0(k10_relat_1(esk2_0,X1),k10_relat_1(esk2_0,X2))=k10_relat_1(esk2_0,k4_xboole_0(X1,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])])).
% 0.20/0.50  cnf(c_0_31, negated_conjecture, (r1_tarski(k9_relat_1(esk2_0,k10_relat_1(esk2_0,X1)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_23]), c_0_24])])).
% 0.20/0.50  cnf(c_0_32, plain, (k10_relat_1(X1,k1_xboole_0)=k1_xboole_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_26]), c_0_26])).
% 0.20/0.50  cnf(c_0_33, plain, (r1_tarski(X2,k10_relat_1(X1,k9_relat_1(X1,X2)))|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.50  cnf(c_0_34, plain, (r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.50  cnf(c_0_35, negated_conjecture, (r1_tarski(k10_relat_1(esk2_0,X1),k10_relat_1(esk2_0,X2))|k10_relat_1(esk2_0,k4_xboole_0(X1,X2))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.20/0.50  cnf(c_0_36, negated_conjecture, (k4_xboole_0(k9_relat_1(esk2_0,k10_relat_1(esk2_0,X1)),X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_20, c_0_31])).
% 0.20/0.50  cnf(c_0_37, negated_conjecture, (k10_relat_1(esk2_0,k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_23]), c_0_24])])).
% 0.20/0.50  cnf(c_0_38, negated_conjecture, (r1_tarski(X1,k10_relat_1(esk2_0,k9_relat_1(esk2_0,X1)))|~r1_tarski(X1,k1_relat_1(esk2_0))), inference(spm,[status(thm)],[c_0_33, c_0_24])).
% 0.20/0.50  cnf(c_0_39, negated_conjecture, (r1_tarski(k10_relat_1(esk2_0,X1),k1_relat_1(esk2_0))), inference(spm,[status(thm)],[c_0_34, c_0_24])).
% 0.20/0.50  fof(c_0_40, plain, ![X15, X16]:(~v1_relat_1(X16)|(X15=k1_xboole_0|~r1_tarski(X15,k2_relat_1(X16))|k10_relat_1(X16,X15)!=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t174_relat_1])])).
% 0.20/0.50  cnf(c_0_41, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.50  cnf(c_0_42, negated_conjecture, (r1_tarski(k10_relat_1(esk2_0,k9_relat_1(esk2_0,k10_relat_1(esk2_0,X1))),k10_relat_1(esk2_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37])])).
% 0.20/0.50  cnf(c_0_43, negated_conjecture, (r1_tarski(k10_relat_1(esk2_0,X1),k10_relat_1(esk2_0,k9_relat_1(esk2_0,k10_relat_1(esk2_0,X1))))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.20/0.50  cnf(c_0_44, plain, (X2=k1_xboole_0|~v1_relat_1(X1)|~r1_tarski(X2,k2_relat_1(X1))|k10_relat_1(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.50  cnf(c_0_45, negated_conjecture, (k10_relat_1(esk2_0,k9_relat_1(esk2_0,k10_relat_1(esk2_0,X1)))=k10_relat_1(esk2_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43])])).
% 0.20/0.50  cnf(c_0_46, negated_conjecture, (X1=k1_xboole_0|k10_relat_1(esk2_0,X1)!=k1_xboole_0|~r1_tarski(X1,k2_relat_1(esk2_0))), inference(spm,[status(thm)],[c_0_44, c_0_24])).
% 0.20/0.50  cnf(c_0_47, negated_conjecture, (k10_relat_1(esk2_0,k4_xboole_0(X1,k9_relat_1(esk2_0,k10_relat_1(esk2_0,X2))))=k10_relat_1(esk2_0,k4_xboole_0(X1,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_45]), c_0_30]), c_0_23]), c_0_24])])).
% 0.20/0.50  fof(c_0_48, plain, ![X8, X9, X10]:(~r1_tarski(X8,X9)|r1_tarski(k4_xboole_0(X8,X10),X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t109_xboole_1])])).
% 0.20/0.50  cnf(c_0_49, negated_conjecture, (k4_xboole_0(X1,k9_relat_1(esk2_0,k10_relat_1(esk2_0,X2)))=k1_xboole_0|k10_relat_1(esk2_0,k4_xboole_0(X1,X2))!=k1_xboole_0|~r1_tarski(k4_xboole_0(X1,k9_relat_1(esk2_0,k10_relat_1(esk2_0,X2))),k2_relat_1(esk2_0))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.20/0.50  cnf(c_0_50, plain, (r1_tarski(k4_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.20/0.50  cnf(c_0_51, negated_conjecture, (r1_tarski(esk1_0,k2_relat_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.50  cnf(c_0_52, negated_conjecture, (k4_xboole_0(X1,k9_relat_1(esk2_0,k10_relat_1(esk2_0,X1)))=k1_xboole_0|~r1_tarski(k4_xboole_0(X1,k9_relat_1(esk2_0,k10_relat_1(esk2_0,X1))),k2_relat_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_26]), c_0_37])])).
% 0.20/0.50  cnf(c_0_53, negated_conjecture, (r1_tarski(k4_xboole_0(esk1_0,X1),k2_relat_1(esk2_0))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.20/0.50  cnf(c_0_54, negated_conjecture, (k4_xboole_0(esk1_0,k9_relat_1(esk2_0,k10_relat_1(esk2_0,esk1_0)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.20/0.50  cnf(c_0_55, negated_conjecture, (r1_tarski(esk1_0,k9_relat_1(esk2_0,k10_relat_1(esk2_0,esk1_0)))), inference(spm,[status(thm)],[c_0_29, c_0_54])).
% 0.20/0.50  cnf(c_0_56, negated_conjecture, (k9_relat_1(esk2_0,k10_relat_1(esk2_0,esk1_0))!=esk1_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.50  cnf(c_0_57, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_55]), c_0_31])]), c_0_56]), ['proof']).
% 0.20/0.50  # SZS output end CNFRefutation
% 0.20/0.50  # Proof object total steps             : 58
% 0.20/0.50  # Proof object clause steps            : 37
% 0.20/0.50  # Proof object formula steps           : 21
% 0.20/0.50  # Proof object conjectures             : 25
% 0.20/0.50  # Proof object clause conjectures      : 22
% 0.20/0.50  # Proof object formula conjectures     : 3
% 0.20/0.50  # Proof object initial clauses used    : 15
% 0.20/0.50  # Proof object initial formulas used   : 10
% 0.20/0.50  # Proof object generating inferences   : 20
% 0.20/0.50  # Proof object simplifying inferences  : 23
% 0.20/0.50  # Training examples: 0 positive, 0 negative
% 0.20/0.50  # Parsed axioms                        : 10
% 0.20/0.50  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.50  # Initial clauses                      : 16
% 0.20/0.50  # Removed in clause preprocessing      : 1
% 0.20/0.50  # Initial clauses in saturation        : 15
% 0.20/0.50  # Processed clauses                    : 1254
% 0.20/0.50  # ...of these trivial                  : 187
% 0.20/0.50  # ...subsumed                          : 730
% 0.20/0.50  # ...remaining for further processing  : 337
% 0.20/0.50  # Other redundant clauses eliminated   : 2
% 0.20/0.50  # Clauses deleted for lack of memory   : 0
% 0.20/0.50  # Backward-subsumed                    : 0
% 0.20/0.50  # Backward-rewritten                   : 23
% 0.20/0.50  # Generated clauses                    : 15893
% 0.20/0.50  # ...of the previous two non-trivial   : 6110
% 0.20/0.50  # Contextual simplify-reflections      : 0
% 0.20/0.50  # Paramodulations                      : 15891
% 0.20/0.50  # Factorizations                       : 0
% 0.20/0.50  # Equation resolutions                 : 2
% 0.20/0.50  # Propositional unsat checks           : 0
% 0.20/0.50  #    Propositional check models        : 0
% 0.20/0.50  #    Propositional check unsatisfiable : 0
% 0.20/0.50  #    Propositional clauses             : 0
% 0.20/0.50  #    Propositional clauses after purity: 0
% 0.20/0.50  #    Propositional unsat core size     : 0
% 0.20/0.50  #    Propositional preprocessing time  : 0.000
% 0.20/0.50  #    Propositional encoding time       : 0.000
% 0.20/0.50  #    Propositional solver time         : 0.000
% 0.20/0.50  #    Success case prop preproc time    : 0.000
% 0.20/0.50  #    Success case prop encoding time   : 0.000
% 0.20/0.50  #    Success case prop solver time     : 0.000
% 0.20/0.50  # Current number of processed clauses  : 298
% 0.20/0.50  #    Positive orientable unit clauses  : 223
% 0.20/0.50  #    Positive unorientable unit clauses: 0
% 0.20/0.50  #    Negative unit clauses             : 1
% 0.20/0.50  #    Non-unit-clauses                  : 74
% 0.20/0.50  # Current number of unprocessed clauses: 4821
% 0.20/0.50  # ...number of literals in the above   : 7406
% 0.20/0.50  # Current number of archived formulas  : 0
% 0.20/0.50  # Current number of archived clauses   : 38
% 0.20/0.50  # Clause-clause subsumption calls (NU) : 1998
% 0.20/0.50  # Rec. Clause-clause subsumption calls : 1997
% 0.20/0.50  # Non-unit clause-clause subsumptions  : 730
% 0.20/0.50  # Unit Clause-clause subsumption calls : 17
% 0.20/0.50  # Rewrite failures with RHS unbound    : 0
% 0.20/0.50  # BW rewrite match attempts            : 663
% 0.20/0.50  # BW rewrite match successes           : 20
% 0.20/0.50  # Condensation attempts                : 0
% 0.20/0.50  # Condensation successes               : 0
% 0.20/0.50  # Termbank termtop insertions          : 293789
% 0.20/0.51  
% 0.20/0.51  # -------------------------------------------------
% 0.20/0.51  # User time                : 0.147 s
% 0.20/0.51  # System time              : 0.009 s
% 0.20/0.51  # Total time               : 0.157 s
% 0.20/0.51  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------

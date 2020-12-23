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
% DateTime   : Thu Dec  3 10:55:10 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   58 (  94 expanded)
%              Number of clauses        :   31 (  36 expanded)
%              Number of leaves         :   13 (  24 expanded)
%              Depth                    :   10
%              Number of atoms          :  139 ( 314 expanded)
%              Number of equality atoms :   31 (  37 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t11_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X1,X2),X3)
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(t157_funct_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( ( r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X3,X2))
          & r1_tarski(X1,k1_relat_1(X3))
          & v2_funct_1(X3) )
       => r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_funct_1)).

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

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t146_funct_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(t149_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_relat_1)).

fof(t155_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( v2_funct_1(X2)
       => k10_relat_1(X2,X1) = k9_relat_1(k2_funct_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_1)).

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(c_0_13,plain,(
    ! [X11,X12] :
      ( ~ r1_tarski(X11,X12)
      | k2_xboole_0(X11,X12) = X12 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_14,plain,(
    ! [X14,X15] : r1_tarski(k4_xboole_0(X14,X15),X14) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_15,plain,(
    ! [X8,X9,X10] :
      ( ~ r1_tarski(k2_xboole_0(X8,X9),X10)
      | r1_tarski(X8,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

cnf(c_0_16,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => ( ( r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X3,X2))
            & r1_tarski(X1,k1_relat_1(X3))
            & v2_funct_1(X3) )
         => r1_tarski(X1,X2) ) ) ),
    inference(assume_negation,[status(cth)],[t157_funct_1])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),X1) = X1 ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

fof(c_0_21,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_funct_1(esk3_0)
    & r1_tarski(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk2_0))
    & r1_tarski(esk1_0,k1_relat_1(esk3_0))
    & v2_funct_1(esk3_0)
    & ~ r1_tarski(esk1_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

fof(c_0_22,plain,(
    ! [X20,X21,X22] :
      ( ~ v1_relat_1(X22)
      | ~ v1_funct_1(X22)
      | ~ v2_funct_1(X22)
      | k9_relat_1(X22,k6_subset_1(X20,X21)) = k6_subset_1(k9_relat_1(X22,X20),k9_relat_1(X22,X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_funct_1])])).

fof(c_0_23,plain,(
    ! [X16,X17] : k6_subset_1(X16,X17) = k4_xboole_0(X16,X17) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

fof(c_0_24,plain,(
    ! [X6,X7] :
      ( ( k4_xboole_0(X6,X7) != k1_xboole_0
        | r1_tarski(X6,X7) )
      & ( ~ r1_tarski(X6,X7)
        | k4_xboole_0(X6,X7) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_25,plain,(
    ! [X23,X24] :
      ( ~ v1_relat_1(X24)
      | ~ r1_tarski(X23,k1_relat_1(X24))
      | r1_tarski(X23,k10_relat_1(X24,k9_relat_1(X24,X23))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_funct_1])])).

cnf(c_0_26,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(esk1_0,k1_relat_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( k9_relat_1(X1,k6_subset_1(X2,X3)) = k6_subset_1(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,plain,
    ( r1_tarski(X2,k10_relat_1(X1,k9_relat_1(X1,X2)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk1_0,X1),k1_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_35,plain,
    ( k9_relat_1(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_29]),c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( k4_xboole_0(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk2_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( v2_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_38,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_39,plain,(
    ! [X18] :
      ( ~ v1_relat_1(X18)
      | k9_relat_1(X18,k1_xboole_0) = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t149_relat_1])])).

fof(c_0_40,plain,(
    ! [X25,X26] :
      ( ~ v1_relat_1(X26)
      | ~ v1_funct_1(X26)
      | ~ v2_funct_1(X26)
      | k10_relat_1(X26,X25) = k9_relat_1(k2_funct_1(X26),X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t155_funct_1])])).

fof(c_0_41,plain,(
    ! [X19] :
      ( ( v1_relat_1(k2_funct_1(X19))
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) )
      & ( v1_funct_1(k2_funct_1(X19))
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk1_0,X1),k10_relat_1(esk3_0,k9_relat_1(esk3_0,k4_xboole_0(esk1_0,X1)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])])).

cnf(c_0_43,negated_conjecture,
    ( k9_relat_1(esk3_0,k4_xboole_0(esk1_0,esk2_0)) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_38]),c_0_34])])).

cnf(c_0_44,plain,
    ( k9_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_45,plain,
    ( k10_relat_1(X1,X2) = k9_relat_1(k2_funct_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_46,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_47,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk1_0,esk2_0),k10_relat_1(esk3_0,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_49,plain,
    ( k10_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46])).

fof(c_0_50,plain,(
    ! [X13] : r1_tarski(k1_xboole_0,X13) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_51,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk1_0,esk2_0),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_37]),c_0_38]),c_0_34])])).

cnf(c_0_53,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_54,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_55,negated_conjecture,
    ( k4_xboole_0(esk1_0,esk2_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53])])).

cnf(c_0_56,negated_conjecture,
    ( ~ r1_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_57,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:39:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S4c
% 0.19/0.38  # and selection function SelectCQPrecWNTNp.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.027 s
% 0.19/0.38  # Presaturation interreduction done
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.19/0.38  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.19/0.38  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 0.19/0.38  fof(t157_funct_1, conjecture, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(((r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X3,X2))&r1_tarski(X1,k1_relat_1(X3)))&v2_funct_1(X3))=>r1_tarski(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t157_funct_1)).
% 0.19/0.38  fof(t123_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(v2_funct_1(X3)=>k9_relat_1(X3,k6_subset_1(X1,X2))=k6_subset_1(k9_relat_1(X3,X1),k9_relat_1(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_funct_1)).
% 0.19/0.38  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 0.19/0.38  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.19/0.38  fof(t146_funct_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 0.19/0.38  fof(t149_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k9_relat_1(X1,k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_relat_1)).
% 0.19/0.38  fof(t155_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(v2_funct_1(X2)=>k10_relat_1(X2,X1)=k9_relat_1(k2_funct_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t155_funct_1)).
% 0.19/0.38  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 0.19/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.38  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.19/0.38  fof(c_0_13, plain, ![X11, X12]:(~r1_tarski(X11,X12)|k2_xboole_0(X11,X12)=X12), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.19/0.38  fof(c_0_14, plain, ![X14, X15]:r1_tarski(k4_xboole_0(X14,X15),X14), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.19/0.38  fof(c_0_15, plain, ![X8, X9, X10]:(~r1_tarski(k2_xboole_0(X8,X9),X10)|r1_tarski(X8,X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 0.19/0.38  cnf(c_0_16, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  cnf(c_0_17, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.38  fof(c_0_18, negated_conjecture, ~(![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(((r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X3,X2))&r1_tarski(X1,k1_relat_1(X3)))&v2_funct_1(X3))=>r1_tarski(X1,X2)))), inference(assume_negation,[status(cth)],[t157_funct_1])).
% 0.19/0.38  cnf(c_0_19, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_20, plain, (k2_xboole_0(k4_xboole_0(X1,X2),X1)=X1), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.19/0.38  fof(c_0_21, negated_conjecture, ((v1_relat_1(esk3_0)&v1_funct_1(esk3_0))&(((r1_tarski(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk2_0))&r1_tarski(esk1_0,k1_relat_1(esk3_0)))&v2_funct_1(esk3_0))&~r1_tarski(esk1_0,esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 0.19/0.38  fof(c_0_22, plain, ![X20, X21, X22]:(~v1_relat_1(X22)|~v1_funct_1(X22)|(~v2_funct_1(X22)|k9_relat_1(X22,k6_subset_1(X20,X21))=k6_subset_1(k9_relat_1(X22,X20),k9_relat_1(X22,X21)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_funct_1])])).
% 0.19/0.38  fof(c_0_23, plain, ![X16, X17]:k6_subset_1(X16,X17)=k4_xboole_0(X16,X17), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 0.19/0.38  fof(c_0_24, plain, ![X6, X7]:((k4_xboole_0(X6,X7)!=k1_xboole_0|r1_tarski(X6,X7))&(~r1_tarski(X6,X7)|k4_xboole_0(X6,X7)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.19/0.38  fof(c_0_25, plain, ![X23, X24]:(~v1_relat_1(X24)|(~r1_tarski(X23,k1_relat_1(X24))|r1_tarski(X23,k10_relat_1(X24,k9_relat_1(X24,X23))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_funct_1])])).
% 0.19/0.38  cnf(c_0_26, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.19/0.38  cnf(c_0_27, negated_conjecture, (r1_tarski(esk1_0,k1_relat_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.38  cnf(c_0_28, plain, (k9_relat_1(X1,k6_subset_1(X2,X3))=k6_subset_1(k9_relat_1(X1,X2),k9_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.38  cnf(c_0_29, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.38  cnf(c_0_30, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.38  cnf(c_0_31, negated_conjecture, (r1_tarski(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.38  cnf(c_0_32, plain, (r1_tarski(X2,k10_relat_1(X1,k9_relat_1(X1,X2)))|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.38  cnf(c_0_33, negated_conjecture, (r1_tarski(k4_xboole_0(esk1_0,X1),k1_relat_1(esk3_0))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.19/0.38  cnf(c_0_34, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.38  cnf(c_0_35, plain, (k9_relat_1(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_29]), c_0_29])).
% 0.19/0.38  cnf(c_0_36, negated_conjecture, (k4_xboole_0(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk2_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.19/0.38  cnf(c_0_37, negated_conjecture, (v2_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.38  cnf(c_0_38, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.38  fof(c_0_39, plain, ![X18]:(~v1_relat_1(X18)|k9_relat_1(X18,k1_xboole_0)=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t149_relat_1])])).
% 0.19/0.38  fof(c_0_40, plain, ![X25, X26]:(~v1_relat_1(X26)|~v1_funct_1(X26)|(~v2_funct_1(X26)|k10_relat_1(X26,X25)=k9_relat_1(k2_funct_1(X26),X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t155_funct_1])])).
% 0.19/0.38  fof(c_0_41, plain, ![X19]:((v1_relat_1(k2_funct_1(X19))|(~v1_relat_1(X19)|~v1_funct_1(X19)))&(v1_funct_1(k2_funct_1(X19))|(~v1_relat_1(X19)|~v1_funct_1(X19)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 0.19/0.38  cnf(c_0_42, negated_conjecture, (r1_tarski(k4_xboole_0(esk1_0,X1),k10_relat_1(esk3_0,k9_relat_1(esk3_0,k4_xboole_0(esk1_0,X1))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34])])).
% 0.19/0.38  cnf(c_0_43, negated_conjecture, (k9_relat_1(esk3_0,k4_xboole_0(esk1_0,esk2_0))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37]), c_0_38]), c_0_34])])).
% 0.19/0.38  cnf(c_0_44, plain, (k9_relat_1(X1,k1_xboole_0)=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.38  cnf(c_0_45, plain, (k10_relat_1(X1,X2)=k9_relat_1(k2_funct_1(X1),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.38  cnf(c_0_46, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.38  fof(c_0_47, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.38  cnf(c_0_48, negated_conjecture, (r1_tarski(k4_xboole_0(esk1_0,esk2_0),k10_relat_1(esk3_0,k1_xboole_0))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.19/0.38  cnf(c_0_49, plain, (k10_relat_1(X1,k1_xboole_0)=k1_xboole_0|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46])).
% 0.19/0.38  fof(c_0_50, plain, ![X13]:r1_tarski(k1_xboole_0,X13), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.19/0.38  cnf(c_0_51, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.38  cnf(c_0_52, negated_conjecture, (r1_tarski(k4_xboole_0(esk1_0,esk2_0),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_37]), c_0_38]), c_0_34])])).
% 0.19/0.38  cnf(c_0_53, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.19/0.38  cnf(c_0_54, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.38  cnf(c_0_55, negated_conjecture, (k4_xboole_0(esk1_0,esk2_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53])])).
% 0.19/0.38  cnf(c_0_56, negated_conjecture, (~r1_tarski(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.38  cnf(c_0_57, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 58
% 0.19/0.38  # Proof object clause steps            : 31
% 0.19/0.38  # Proof object formula steps           : 27
% 0.19/0.38  # Proof object conjectures             : 17
% 0.19/0.38  # Proof object clause conjectures      : 14
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 19
% 0.19/0.38  # Proof object initial formulas used   : 13
% 0.19/0.38  # Proof object generating inferences   : 11
% 0.19/0.38  # Proof object simplifying inferences  : 16
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 13
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 22
% 0.19/0.38  # Removed in clause preprocessing      : 1
% 0.19/0.38  # Initial clauses in saturation        : 21
% 0.19/0.38  # Processed clauses                    : 275
% 0.19/0.38  # ...of these trivial                  : 16
% 0.19/0.38  # ...subsumed                          : 114
% 0.19/0.38  # ...remaining for further processing  : 145
% 0.19/0.38  # Other redundant clauses eliminated   : 2
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 0
% 0.19/0.38  # Backward-rewritten                   : 11
% 0.19/0.38  # Generated clauses                    : 1063
% 0.19/0.38  # ...of the previous two non-trivial   : 564
% 0.19/0.38  # Contextual simplify-reflections      : 5
% 0.19/0.38  # Paramodulations                      : 1061
% 0.19/0.38  # Factorizations                       : 0
% 0.19/0.38  # Equation resolutions                 : 2
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 112
% 0.19/0.38  #    Positive orientable unit clauses  : 62
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 1
% 0.19/0.38  #    Non-unit-clauses                  : 49
% 0.19/0.38  # Current number of unprocessed clauses: 325
% 0.19/0.38  # ...number of literals in the above   : 845
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 32
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 850
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 682
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 119
% 0.19/0.38  # Unit Clause-clause subsumption calls : 90
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 26
% 0.19/0.38  # BW rewrite match successes           : 3
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 12683
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.042 s
% 0.19/0.38  # System time              : 0.004 s
% 0.19/0.38  # Total time               : 0.046 s
% 0.19/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------

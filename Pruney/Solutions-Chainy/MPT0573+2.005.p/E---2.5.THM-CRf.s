%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:51:48 EST 2020

% Result     : Theorem 0.54s
% Output     : CNFRefutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :   48 (  90 expanded)
%              Number of clauses        :   25 (  42 expanded)
%              Number of leaves         :   11 (  23 expanded)
%              Depth                    :   10
%              Number of atoms          :   79 ( 127 expanded)
%              Number of equality atoms :   26 (  65 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t44_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X1,X2),X3)
     => r1_tarski(X1,k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t43_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_xboole_0(X2,X3))
     => r1_tarski(k4_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t175_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k10_relat_1(X3,k2_xboole_0(X1,X2)) = k2_xboole_0(k10_relat_1(X3,X1),k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t177_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => r1_tarski(k6_subset_1(k10_relat_1(X3,X1),k10_relat_1(X3,X2)),k10_relat_1(X3,k6_subset_1(X1,X2))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t177_relat_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(c_0_11,plain,(
    ! [X22,X23] : k1_setfam_1(k2_tarski(X22,X23)) = k3_xboole_0(X22,X23) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_12,plain,(
    ! [X18,X19] : k1_enumset1(X18,X18,X19) = k2_tarski(X18,X19) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_13,plain,(
    ! [X6,X7] : k4_xboole_0(X6,X7) = k5_xboole_0(X6,k3_xboole_0(X6,X7)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_14,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X13,X14,X15] :
      ( ~ r1_tarski(k4_xboole_0(X13,X14),X15)
      | r1_tarski(X13,k2_xboole_0(X14,X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).

cnf(c_0_17,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

fof(c_0_19,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_23,plain,(
    ! [X10,X11,X12] :
      ( ~ r1_tarski(X10,k2_xboole_0(X11,X12))
      | r1_tarski(k4_xboole_0(X10,X11),X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).

fof(c_0_24,plain,(
    ! [X16,X17] : r1_tarski(X16,k2_xboole_0(X16,X17)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_25,plain,(
    ! [X24,X25,X26] :
      ( ~ v1_relat_1(X26)
      | k10_relat_1(X26,k2_xboole_0(X24,X25)) = k2_xboole_0(k10_relat_1(X26,X24),k10_relat_1(X26,X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t175_relat_1])])).

fof(c_0_26,plain,(
    ! [X8,X9] :
      ( ~ r1_tarski(X8,X9)
      | k2_xboole_0(X8,X9) = X9 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))),X3) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_22])).

fof(c_0_29,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => r1_tarski(k6_subset_1(k10_relat_1(X3,X1),k10_relat_1(X3,X2)),k10_relat_1(X3,k6_subset_1(X1,X2))) ) ),
    inference(assume_negation,[status(cth)],[t177_relat_1])).

cnf(c_0_30,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( k10_relat_1(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

fof(c_0_35,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & ~ r1_tarski(k6_subset_1(k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk2_0)),k10_relat_1(esk3_0,k6_subset_1(esk1_0,esk2_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_29])])])).

fof(c_0_36,plain,(
    ! [X20,X21] : k6_subset_1(X20,X21) = k4_xboole_0(X20,X21) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

cnf(c_0_37,plain,
    ( r1_tarski(k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[c_0_30,c_0_21])).

cnf(c_0_38,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,k2_xboole_0(X2,X3)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_39,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))))) = k2_xboole_0(X2,k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( ~ r1_tarski(k6_subset_1(k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk2_0)),k10_relat_1(esk3_0,k6_subset_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_41,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_42,plain,
    ( r1_tarski(k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,k10_relat_1(X2,X3)))),k10_relat_1(X2,X4))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k10_relat_1(X2,k2_xboole_0(X3,X4))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_32])).

cnf(c_0_43,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,k2_xboole_0(X3,k5_xboole_0(X2,k1_setfam_1(k1_enumset1(X2,X2,X3))))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( ~ r1_tarski(k5_xboole_0(k10_relat_1(esk3_0,esk1_0),k1_setfam_1(k1_enumset1(k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk2_0)))),k10_relat_1(esk3_0,k5_xboole_0(esk1_0,k1_setfam_1(k1_enumset1(esk1_0,esk1_0,esk2_0))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_41]),c_0_41]),c_0_21]),c_0_21])).

cnf(c_0_45,plain,
    ( r1_tarski(k5_xboole_0(k10_relat_1(X1,X2),k1_setfam_1(k1_enumset1(k10_relat_1(X1,X2),k10_relat_1(X1,X2),k10_relat_1(X1,X3)))),k10_relat_1(X1,k5_xboole_0(X2,k1_setfam_1(k1_enumset1(X2,X2,X3)))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_46,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_47,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:17:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.54/0.76  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S081N
% 0.54/0.76  # and selection function SelectCQArNTNp.
% 0.54/0.76  #
% 0.54/0.76  # Preprocessing time       : 0.027 s
% 0.54/0.76  # Presaturation interreduction done
% 0.54/0.76  
% 0.54/0.76  # Proof found!
% 0.54/0.76  # SZS status Theorem
% 0.54/0.76  # SZS output start CNFRefutation
% 0.54/0.76  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.54/0.76  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.54/0.76  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.54/0.76  fof(t44_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k4_xboole_0(X1,X2),X3)=>r1_tarski(X1,k2_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 0.54/0.76  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.54/0.76  fof(t43_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_xboole_0(X2,X3))=>r1_tarski(k4_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 0.54/0.76  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.54/0.76  fof(t175_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k10_relat_1(X3,k2_xboole_0(X1,X2))=k2_xboole_0(k10_relat_1(X3,X1),k10_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_relat_1)).
% 0.54/0.76  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.54/0.76  fof(t177_relat_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>r1_tarski(k6_subset_1(k10_relat_1(X3,X1),k10_relat_1(X3,X2)),k10_relat_1(X3,k6_subset_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t177_relat_1)).
% 0.54/0.76  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 0.54/0.76  fof(c_0_11, plain, ![X22, X23]:k1_setfam_1(k2_tarski(X22,X23))=k3_xboole_0(X22,X23), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.54/0.76  fof(c_0_12, plain, ![X18, X19]:k1_enumset1(X18,X18,X19)=k2_tarski(X18,X19), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.54/0.76  fof(c_0_13, plain, ![X6, X7]:k4_xboole_0(X6,X7)=k5_xboole_0(X6,k3_xboole_0(X6,X7)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.54/0.76  cnf(c_0_14, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.54/0.76  cnf(c_0_15, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.54/0.76  fof(c_0_16, plain, ![X13, X14, X15]:(~r1_tarski(k4_xboole_0(X13,X14),X15)|r1_tarski(X13,k2_xboole_0(X14,X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).
% 0.54/0.76  cnf(c_0_17, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.54/0.76  cnf(c_0_18, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.54/0.76  fof(c_0_19, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.54/0.76  cnf(c_0_20, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.54/0.76  cnf(c_0_21, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.54/0.76  cnf(c_0_22, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.54/0.76  fof(c_0_23, plain, ![X10, X11, X12]:(~r1_tarski(X10,k2_xboole_0(X11,X12))|r1_tarski(k4_xboole_0(X10,X11),X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).
% 0.54/0.76  fof(c_0_24, plain, ![X16, X17]:r1_tarski(X16,k2_xboole_0(X16,X17)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.54/0.76  fof(c_0_25, plain, ![X24, X25, X26]:(~v1_relat_1(X26)|k10_relat_1(X26,k2_xboole_0(X24,X25))=k2_xboole_0(k10_relat_1(X26,X24),k10_relat_1(X26,X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t175_relat_1])])).
% 0.54/0.76  fof(c_0_26, plain, ![X8, X9]:(~r1_tarski(X8,X9)|k2_xboole_0(X8,X9)=X9), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.54/0.76  cnf(c_0_27, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))),X3)), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 0.54/0.76  cnf(c_0_28, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_22])).
% 0.54/0.76  fof(c_0_29, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>r1_tarski(k6_subset_1(k10_relat_1(X3,X1),k10_relat_1(X3,X2)),k10_relat_1(X3,k6_subset_1(X1,X2))))), inference(assume_negation,[status(cth)],[t177_relat_1])).
% 0.54/0.76  cnf(c_0_30, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.54/0.76  cnf(c_0_31, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.54/0.76  cnf(c_0_32, plain, (k10_relat_1(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.54/0.76  cnf(c_0_33, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.54/0.76  cnf(c_0_34, plain, (r1_tarski(X1,k2_xboole_0(X2,k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.54/0.76  fof(c_0_35, negated_conjecture, (v1_relat_1(esk3_0)&~r1_tarski(k6_subset_1(k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk2_0)),k10_relat_1(esk3_0,k6_subset_1(esk1_0,esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_29])])])).
% 0.54/0.76  fof(c_0_36, plain, ![X20, X21]:k6_subset_1(X20,X21)=k4_xboole_0(X20,X21), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 0.54/0.76  cnf(c_0_37, plain, (r1_tarski(k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))),X3)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(rw,[status(thm)],[c_0_30, c_0_21])).
% 0.54/0.76  cnf(c_0_38, plain, (r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,k2_xboole_0(X2,X3)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.54/0.76  cnf(c_0_39, plain, (k2_xboole_0(X1,k2_xboole_0(X2,k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))))=k2_xboole_0(X2,k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.54/0.76  cnf(c_0_40, negated_conjecture, (~r1_tarski(k6_subset_1(k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk2_0)),k10_relat_1(esk3_0,k6_subset_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.54/0.76  cnf(c_0_41, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.54/0.76  cnf(c_0_42, plain, (r1_tarski(k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,k10_relat_1(X2,X3)))),k10_relat_1(X2,X4))|~v1_relat_1(X2)|~r1_tarski(X1,k10_relat_1(X2,k2_xboole_0(X3,X4)))), inference(spm,[status(thm)],[c_0_37, c_0_32])).
% 0.54/0.76  cnf(c_0_43, plain, (r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,k2_xboole_0(X3,k5_xboole_0(X2,k1_setfam_1(k1_enumset1(X2,X2,X3))))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.54/0.76  cnf(c_0_44, negated_conjecture, (~r1_tarski(k5_xboole_0(k10_relat_1(esk3_0,esk1_0),k1_setfam_1(k1_enumset1(k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk2_0)))),k10_relat_1(esk3_0,k5_xboole_0(esk1_0,k1_setfam_1(k1_enumset1(esk1_0,esk1_0,esk2_0)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_41]), c_0_41]), c_0_21]), c_0_21])).
% 0.54/0.76  cnf(c_0_45, plain, (r1_tarski(k5_xboole_0(k10_relat_1(X1,X2),k1_setfam_1(k1_enumset1(k10_relat_1(X1,X2),k10_relat_1(X1,X2),k10_relat_1(X1,X3)))),k10_relat_1(X1,k5_xboole_0(X2,k1_setfam_1(k1_enumset1(X2,X2,X3)))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.54/0.76  cnf(c_0_46, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.54/0.76  cnf(c_0_47, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46])]), ['proof']).
% 0.54/0.76  # SZS output end CNFRefutation
% 0.54/0.76  # Proof object total steps             : 48
% 0.54/0.76  # Proof object clause steps            : 25
% 0.54/0.76  # Proof object formula steps           : 23
% 0.54/0.76  # Proof object conjectures             : 7
% 0.54/0.76  # Proof object clause conjectures      : 4
% 0.54/0.76  # Proof object formula conjectures     : 3
% 0.54/0.76  # Proof object initial clauses used    : 12
% 0.54/0.76  # Proof object initial formulas used   : 11
% 0.54/0.76  # Proof object generating inferences   : 7
% 0.54/0.76  # Proof object simplifying inferences  : 11
% 0.54/0.76  # Training examples: 0 positive, 0 negative
% 0.54/0.76  # Parsed axioms                        : 11
% 0.54/0.76  # Removed by relevancy pruning/SinE    : 0
% 0.54/0.76  # Initial clauses                      : 14
% 0.54/0.76  # Removed in clause preprocessing      : 4
% 0.54/0.76  # Initial clauses in saturation        : 10
% 0.54/0.76  # Processed clauses                    : 1997
% 0.54/0.76  # ...of these trivial                  : 85
% 0.54/0.76  # ...subsumed                          : 1614
% 0.54/0.76  # ...remaining for further processing  : 298
% 0.54/0.76  # Other redundant clauses eliminated   : 2
% 0.54/0.76  # Clauses deleted for lack of memory   : 0
% 0.54/0.76  # Backward-subsumed                    : 4
% 0.54/0.76  # Backward-rewritten                   : 15
% 0.54/0.76  # Generated clauses                    : 25289
% 0.54/0.76  # ...of the previous two non-trivial   : 18562
% 0.54/0.76  # Contextual simplify-reflections      : 0
% 0.54/0.76  # Paramodulations                      : 25287
% 0.54/0.76  # Factorizations                       : 0
% 0.54/0.76  # Equation resolutions                 : 2
% 0.54/0.76  # Propositional unsat checks           : 0
% 0.54/0.76  #    Propositional check models        : 0
% 0.54/0.76  #    Propositional check unsatisfiable : 0
% 0.54/0.76  #    Propositional clauses             : 0
% 0.54/0.76  #    Propositional clauses after purity: 0
% 0.54/0.76  #    Propositional unsat core size     : 0
% 0.54/0.76  #    Propositional preprocessing time  : 0.000
% 0.54/0.76  #    Propositional encoding time       : 0.000
% 0.54/0.76  #    Propositional solver time         : 0.000
% 0.54/0.76  #    Success case prop preproc time    : 0.000
% 0.54/0.76  #    Success case prop encoding time   : 0.000
% 0.54/0.76  #    Success case prop solver time     : 0.000
% 0.54/0.76  # Current number of processed clauses  : 268
% 0.54/0.76  #    Positive orientable unit clauses  : 109
% 0.54/0.76  #    Positive unorientable unit clauses: 3
% 0.54/0.76  #    Negative unit clauses             : 1
% 0.54/0.76  #    Non-unit-clauses                  : 155
% 0.54/0.76  # Current number of unprocessed clauses: 16455
% 0.54/0.76  # ...number of literals in the above   : 33190
% 0.54/0.76  # Current number of archived formulas  : 0
% 0.54/0.76  # Current number of archived clauses   : 32
% 0.54/0.76  # Clause-clause subsumption calls (NU) : 9373
% 0.54/0.76  # Rec. Clause-clause subsumption calls : 9126
% 0.54/0.76  # Non-unit clause-clause subsumptions  : 1566
% 0.54/0.76  # Unit Clause-clause subsumption calls : 530
% 0.54/0.76  # Rewrite failures with RHS unbound    : 1305
% 0.54/0.76  # BW rewrite match attempts            : 1018
% 0.54/0.76  # BW rewrite match successes           : 26
% 0.54/0.76  # Condensation attempts                : 0
% 0.54/0.76  # Condensation successes               : 0
% 0.54/0.76  # Termbank termtop insertions          : 746764
% 0.54/0.76  
% 0.54/0.76  # -------------------------------------------------
% 0.54/0.76  # User time                : 0.412 s
% 0.54/0.76  # System time              : 0.009 s
% 0.54/0.76  # Total time               : 0.420 s
% 0.54/0.76  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------

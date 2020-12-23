%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:50:55 EST 2020

% Result     : Theorem 13.96s
% Output     : CNFRefutation 13.96s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 138 expanded)
%              Number of clauses        :   30 (  64 expanded)
%              Number of leaves         :   11 (  36 expanded)
%              Depth                    :   10
%              Number of atoms          :   89 ( 211 expanded)
%              Number of equality atoms :   28 (  99 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t11_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X1,X2),X3)
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(t19_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(t153_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k9_relat_1(X3,k2_xboole_0(X1,X2)) = k2_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t153_relat_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t154_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => r1_tarski(k9_relat_1(X3,k3_xboole_0(X1,X2)),k3_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_relat_1)).

fof(c_0_11,plain,(
    ! [X23,X24] : k1_setfam_1(k2_tarski(X23,X24)) = k3_xboole_0(X23,X24) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_12,plain,(
    ! [X18,X19] : k1_enumset1(X18,X18,X19) = k2_tarski(X18,X19) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_13,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_14,plain,(
    ! [X11,X12] : r1_tarski(k3_xboole_0(X11,X12),X11) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_15,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,plain,(
    ! [X20,X21,X22] : k2_enumset1(X20,X20,X21,X22) = k1_enumset1(X20,X21,X22) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_18,plain,(
    ! [X16,X17] : k2_tarski(X16,X17) = k2_tarski(X17,X16) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

fof(c_0_19,plain,(
    ! [X6,X7,X8] :
      ( ~ r1_tarski(k2_xboole_0(X6,X7),X8)
      | r1_tarski(X6,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_23,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_25,plain,(
    ! [X13,X14,X15] :
      ( ~ r1_tarski(X13,X14)
      | ~ r1_tarski(X13,X15)
      | r1_tarski(X13,k3_xboole_0(X14,X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_20])).

fof(c_0_28,plain,(
    ! [X25,X26,X27] :
      ( ~ v1_relat_1(X27)
      | k9_relat_1(X27,k2_xboole_0(X25,X26)) = k2_xboole_0(k9_relat_1(X27,X25),k9_relat_1(X27,X26)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t153_relat_1])])).

fof(c_0_29,plain,(
    ! [X9,X10] :
      ( ~ r1_tarski(X9,X10)
      | k2_xboole_0(X9,X10) = X10 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_30,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_22]),c_0_23])).

cnf(c_0_31,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k2_enumset1(X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_16]),c_0_16]),c_0_23]),c_0_23])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_34,plain,
    ( k9_relat_1(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

fof(c_0_37,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => r1_tarski(k9_relat_1(X3,k3_xboole_0(X1,X2)),k3_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2))) ) ),
    inference(assume_negation,[status(cth)],[t154_relat_1])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_22]),c_0_23])).

cnf(c_0_39,plain,
    ( r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,k2_xboole_0(X2,X3)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_40,plain,
    ( k2_xboole_0(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X1) = X1 ),
    inference(spm,[status(thm)],[c_0_35,c_0_30])).

cnf(c_0_41,plain,
    ( k2_xboole_0(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X2) = X2 ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

fof(c_0_42,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & ~ r1_tarski(k9_relat_1(esk3_0,k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk2_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_37])])])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,k2_xboole_0(X1,X3))))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_38,c_0_33])).

cnf(c_0_44,plain,
    ( r1_tarski(k9_relat_1(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3))),k9_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_45,plain,
    ( r1_tarski(k9_relat_1(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3))),k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_41])).

cnf(c_0_46,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk3_0,k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_47,plain,
    ( r1_tarski(k9_relat_1(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3))),k1_setfam_1(k2_enumset1(k9_relat_1(X1,X2),k9_relat_1(X1,X2),k9_relat_1(X1,X2),k2_xboole_0(k9_relat_1(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3))),X4))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_48,plain,
    ( k2_xboole_0(k9_relat_1(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3))),k9_relat_1(X1,X3)) = k9_relat_1(X1,X3)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_45])).

cnf(c_0_49,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk3_0,k1_setfam_1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0))),k1_setfam_1(k2_enumset1(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk2_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_22]),c_0_22]),c_0_23]),c_0_23])).

cnf(c_0_50,plain,
    ( r1_tarski(k9_relat_1(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3))),k1_setfam_1(k2_enumset1(k9_relat_1(X1,X2),k9_relat_1(X1,X2),k9_relat_1(X1,X2),k9_relat_1(X1,X3))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_51,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_52,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:03:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 13.96/14.17  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S081N
% 13.96/14.17  # and selection function SelectCQArNTNp.
% 13.96/14.17  #
% 13.96/14.17  # Preprocessing time       : 0.027 s
% 13.96/14.17  # Presaturation interreduction done
% 13.96/14.17  
% 13.96/14.17  # Proof found!
% 13.96/14.17  # SZS status Theorem
% 13.96/14.17  # SZS output start CNFRefutation
% 13.96/14.17  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 13.96/14.17  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 13.96/14.17  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 13.96/14.17  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 13.96/14.17  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 13.96/14.17  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 13.96/14.17  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 13.96/14.17  fof(t19_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(X1,k3_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 13.96/14.17  fof(t153_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k9_relat_1(X3,k2_xboole_0(X1,X2))=k2_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t153_relat_1)).
% 13.96/14.17  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 13.96/14.17  fof(t154_relat_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>r1_tarski(k9_relat_1(X3,k3_xboole_0(X1,X2)),k3_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t154_relat_1)).
% 13.96/14.17  fof(c_0_11, plain, ![X23, X24]:k1_setfam_1(k2_tarski(X23,X24))=k3_xboole_0(X23,X24), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 13.96/14.17  fof(c_0_12, plain, ![X18, X19]:k1_enumset1(X18,X18,X19)=k2_tarski(X18,X19), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 13.96/14.17  fof(c_0_13, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 13.96/14.17  fof(c_0_14, plain, ![X11, X12]:r1_tarski(k3_xboole_0(X11,X12),X11), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 13.96/14.17  cnf(c_0_15, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 13.96/14.17  cnf(c_0_16, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 13.96/14.17  fof(c_0_17, plain, ![X20, X21, X22]:k2_enumset1(X20,X20,X21,X22)=k1_enumset1(X20,X21,X22), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 13.96/14.17  fof(c_0_18, plain, ![X16, X17]:k2_tarski(X16,X17)=k2_tarski(X17,X16), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 13.96/14.17  fof(c_0_19, plain, ![X6, X7, X8]:(~r1_tarski(k2_xboole_0(X6,X7),X8)|r1_tarski(X6,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 13.96/14.17  cnf(c_0_20, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_13])).
% 13.96/14.17  cnf(c_0_21, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 13.96/14.17  cnf(c_0_22, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 13.96/14.17  cnf(c_0_23, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 13.96/14.17  cnf(c_0_24, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 13.96/14.17  fof(c_0_25, plain, ![X13, X14, X15]:(~r1_tarski(X13,X14)|~r1_tarski(X13,X15)|r1_tarski(X13,k3_xboole_0(X14,X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).
% 13.96/14.17  cnf(c_0_26, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 13.96/14.17  cnf(c_0_27, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_20])).
% 13.96/14.17  fof(c_0_28, plain, ![X25, X26, X27]:(~v1_relat_1(X27)|k9_relat_1(X27,k2_xboole_0(X25,X26))=k2_xboole_0(k9_relat_1(X27,X25),k9_relat_1(X27,X26))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t153_relat_1])])).
% 13.96/14.17  fof(c_0_29, plain, ![X9, X10]:(~r1_tarski(X9,X10)|k2_xboole_0(X9,X10)=X10), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 13.96/14.17  cnf(c_0_30, plain, (r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_22]), c_0_23])).
% 13.96/14.17  cnf(c_0_31, plain, (k2_enumset1(X1,X1,X1,X2)=k2_enumset1(X2,X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_16]), c_0_16]), c_0_23]), c_0_23])).
% 13.96/14.17  cnf(c_0_32, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 13.96/14.17  cnf(c_0_33, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 13.96/14.17  cnf(c_0_34, plain, (k9_relat_1(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 13.96/14.17  cnf(c_0_35, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 13.96/14.17  cnf(c_0_36, plain, (r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X2)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 13.96/14.17  fof(c_0_37, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>r1_tarski(k9_relat_1(X3,k3_xboole_0(X1,X2)),k3_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2))))), inference(assume_negation,[status(cth)],[t154_relat_1])).
% 13.96/14.17  cnf(c_0_38, plain, (r1_tarski(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))|~r1_tarski(X1,X3)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_22]), c_0_23])).
% 13.96/14.17  cnf(c_0_39, plain, (r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,k2_xboole_0(X2,X3)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 13.96/14.17  cnf(c_0_40, plain, (k2_xboole_0(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X1)=X1), inference(spm,[status(thm)],[c_0_35, c_0_30])).
% 13.96/14.17  cnf(c_0_41, plain, (k2_xboole_0(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X2)=X2), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 13.96/14.17  fof(c_0_42, negated_conjecture, (v1_relat_1(esk3_0)&~r1_tarski(k9_relat_1(esk3_0,k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_37])])])).
% 13.96/14.17  cnf(c_0_43, plain, (r1_tarski(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,k2_xboole_0(X1,X3))))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_38, c_0_33])).
% 13.96/14.17  cnf(c_0_44, plain, (r1_tarski(k9_relat_1(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3))),k9_relat_1(X1,X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 13.96/14.17  cnf(c_0_45, plain, (r1_tarski(k9_relat_1(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3))),k9_relat_1(X1,X3))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_39, c_0_41])).
% 13.96/14.17  cnf(c_0_46, negated_conjecture, (~r1_tarski(k9_relat_1(esk3_0,k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 13.96/14.17  cnf(c_0_47, plain, (r1_tarski(k9_relat_1(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3))),k1_setfam_1(k2_enumset1(k9_relat_1(X1,X2),k9_relat_1(X1,X2),k9_relat_1(X1,X2),k2_xboole_0(k9_relat_1(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3))),X4))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 13.96/14.17  cnf(c_0_48, plain, (k2_xboole_0(k9_relat_1(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3))),k9_relat_1(X1,X3))=k9_relat_1(X1,X3)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_35, c_0_45])).
% 13.96/14.17  cnf(c_0_49, negated_conjecture, (~r1_tarski(k9_relat_1(esk3_0,k1_setfam_1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0))),k1_setfam_1(k2_enumset1(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk2_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_22]), c_0_22]), c_0_23]), c_0_23])).
% 13.96/14.17  cnf(c_0_50, plain, (r1_tarski(k9_relat_1(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3))),k1_setfam_1(k2_enumset1(k9_relat_1(X1,X2),k9_relat_1(X1,X2),k9_relat_1(X1,X2),k9_relat_1(X1,X3))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 13.96/14.17  cnf(c_0_51, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 13.96/14.17  cnf(c_0_52, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51])]), ['proof']).
% 13.96/14.17  # SZS output end CNFRefutation
% 13.96/14.17  # Proof object total steps             : 53
% 13.96/14.17  # Proof object clause steps            : 30
% 13.96/14.17  # Proof object formula steps           : 23
% 13.96/14.17  # Proof object conjectures             : 7
% 13.96/14.17  # Proof object clause conjectures      : 4
% 13.96/14.17  # Proof object formula conjectures     : 3
% 13.96/14.17  # Proof object initial clauses used    : 12
% 13.96/14.17  # Proof object initial formulas used   : 11
% 13.96/14.17  # Proof object generating inferences   : 12
% 13.96/14.17  # Proof object simplifying inferences  : 16
% 13.96/14.17  # Training examples: 0 positive, 0 negative
% 13.96/14.17  # Parsed axioms                        : 11
% 13.96/14.17  # Removed by relevancy pruning/SinE    : 0
% 13.96/14.17  # Initial clauses                      : 14
% 13.96/14.17  # Removed in clause preprocessing      : 3
% 13.96/14.17  # Initial clauses in saturation        : 11
% 13.96/14.17  # Processed clauses                    : 33457
% 13.96/14.17  # ...of these trivial                  : 1273
% 13.96/14.17  # ...subsumed                          : 29104
% 13.96/14.17  # ...remaining for further processing  : 3080
% 13.96/14.17  # Other redundant clauses eliminated   : 2
% 13.96/14.17  # Clauses deleted for lack of memory   : 0
% 13.96/14.17  # Backward-subsumed                    : 35
% 13.96/14.17  # Backward-rewritten                   : 73
% 13.96/14.17  # Generated clauses                    : 1122421
% 13.96/14.17  # ...of the previous two non-trivial   : 1030102
% 13.96/14.17  # Contextual simplify-reflections      : 0
% 13.96/14.17  # Paramodulations                      : 1122419
% 13.96/14.17  # Factorizations                       : 0
% 13.96/14.17  # Equation resolutions                 : 2
% 13.96/14.17  # Propositional unsat checks           : 0
% 13.96/14.17  #    Propositional check models        : 0
% 13.96/14.17  #    Propositional check unsatisfiable : 0
% 13.96/14.17  #    Propositional clauses             : 0
% 13.96/14.17  #    Propositional clauses after purity: 0
% 13.96/14.17  #    Propositional unsat core size     : 0
% 13.96/14.17  #    Propositional preprocessing time  : 0.000
% 13.96/14.17  #    Propositional encoding time       : 0.000
% 13.96/14.17  #    Propositional solver time         : 0.000
% 13.96/14.17  #    Success case prop preproc time    : 0.000
% 13.96/14.17  #    Success case prop encoding time   : 0.000
% 13.96/14.17  #    Success case prop solver time     : 0.000
% 13.96/14.17  # Current number of processed clauses  : 2960
% 13.96/14.17  #    Positive orientable unit clauses  : 738
% 13.96/14.17  #    Positive unorientable unit clauses: 1
% 13.96/14.17  #    Negative unit clauses             : 1
% 13.96/14.17  #    Non-unit-clauses                  : 2220
% 13.96/14.17  # Current number of unprocessed clauses: 996136
% 13.96/14.17  # ...number of literals in the above   : 2023980
% 13.96/14.17  # Current number of archived formulas  : 0
% 13.96/14.17  # Current number of archived clauses   : 121
% 13.96/14.17  # Clause-clause subsumption calls (NU) : 1390872
% 13.96/14.17  # Rec. Clause-clause subsumption calls : 1154977
% 13.96/14.17  # Non-unit clause-clause subsumptions  : 29122
% 13.96/14.17  # Unit Clause-clause subsumption calls : 14716
% 13.96/14.17  # Rewrite failures with RHS unbound    : 0
% 13.96/14.17  # BW rewrite match attempts            : 209627
% 13.96/14.17  # BW rewrite match successes           : 78
% 13.96/14.17  # Condensation attempts                : 0
% 13.96/14.17  # Condensation successes               : 0
% 13.96/14.17  # Termbank termtop insertions          : 41393521
% 14.04/14.21  
% 14.04/14.21  # -------------------------------------------------
% 14.04/14.21  # User time                : 13.381 s
% 14.04/14.21  # System time              : 0.485 s
% 14.04/14.21  # Total time               : 13.866 s
% 14.04/14.21  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------

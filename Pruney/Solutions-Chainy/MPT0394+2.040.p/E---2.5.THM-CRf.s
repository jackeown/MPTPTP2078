%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:47:18 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 558 expanded)
%              Number of clauses        :   31 ( 229 expanded)
%              Number of leaves         :   11 ( 164 expanded)
%              Depth                    :   14
%              Number of atoms          :   83 ( 678 expanded)
%              Number of equality atoms :   67 ( 622 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t10_setfam_1,axiom,(
    ! [X1,X2] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & k1_setfam_1(k2_xboole_0(X1,X2)) != k3_xboole_0(k1_setfam_1(X1),k1_setfam_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_setfam_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t46_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t11_setfam_1,axiom,(
    ! [X1] : k1_setfam_1(k1_tarski(X1)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t19_zfmisc_1,axiom,(
    ! [X1,X2] : k3_xboole_0(k1_tarski(X1),k2_tarski(X1,X2)) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_zfmisc_1)).

fof(t16_zfmisc_1,axiom,(
    ! [X1,X2] :
      ~ ( r1_xboole_0(k1_tarski(X1),k1_tarski(X2))
        & X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_zfmisc_1)).

fof(t12_setfam_1,conjecture,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(c_0_11,plain,(
    ! [X17,X18] : k3_tarski(k2_tarski(X17,X18)) = k2_xboole_0(X17,X18) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_12,plain,(
    ! [X12,X13] : k1_enumset1(X12,X12,X13) = k2_tarski(X12,X13) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_13,plain,(
    ! [X23,X24] :
      ( X23 = k1_xboole_0
      | X24 = k1_xboole_0
      | k1_setfam_1(k2_xboole_0(X23,X24)) = k3_xboole_0(k1_setfam_1(X23),k1_setfam_1(X24)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_setfam_1])])).

cnf(c_0_14,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X14,X15,X16] : k2_enumset1(X14,X14,X15,X16) = k1_enumset1(X14,X15,X16) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_17,plain,(
    ! [X7,X8,X9,X10] : k2_enumset1(X7,X8,X9,X10) = k2_xboole_0(k1_enumset1(X7,X8,X9),k1_tarski(X10)) ),
    inference(variable_rename,[status(thm)],[t46_enumset1])).

fof(c_0_18,plain,(
    ! [X11] : k2_tarski(X11,X11) = k1_tarski(X11) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_19,plain,(
    ! [X25] : k1_setfam_1(k1_tarski(X25)) = X25 ),
    inference(variable_rename,[status(thm)],[t11_setfam_1])).

cnf(c_0_20,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k1_setfam_1(k2_xboole_0(X1,X2)) = k3_xboole_0(k1_setfam_1(X1),k1_setfam_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_22,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( k1_setfam_1(k1_tarski(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_26,plain,(
    ! [X5,X6] :
      ( ( ~ r1_xboole_0(X5,X6)
        | k3_xboole_0(X5,X6) = k1_xboole_0 )
      & ( k3_xboole_0(X5,X6) != k1_xboole_0
        | r1_xboole_0(X5,X6) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_27,plain,
    ( X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k1_setfam_1(k3_tarski(k2_enumset1(X1,X1,X1,X2))) = k3_xboole_0(k1_setfam_1(X1),k1_setfam_1(X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21]),c_0_22])).

cnf(c_0_28,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k3_tarski(k2_enumset1(k2_enumset1(X1,X1,X2,X3),k2_enumset1(X1,X1,X2,X3),k2_enumset1(X1,X1,X2,X3),k2_enumset1(X4,X4,X4,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24]),c_0_15]),c_0_21]),c_0_22]),c_0_22]),c_0_22]),c_0_22])).

cnf(c_0_29,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_24]),c_0_15]),c_0_22])).

fof(c_0_30,plain,(
    ! [X21,X22] : k3_xboole_0(k1_tarski(X21),k2_tarski(X21,X22)) = k1_tarski(X21) ),
    inference(variable_rename,[status(thm)],[t19_zfmisc_1])).

cnf(c_0_31,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( k3_xboole_0(k1_setfam_1(k2_enumset1(X1,X1,X2,X3)),X4) = k1_setfam_1(k2_enumset1(X1,X2,X3,X4))
    | k2_enumset1(X1,X1,X2,X3) = k1_xboole_0
    | k2_enumset1(X4,X4,X4,X4) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])).

fof(c_0_33,plain,(
    ! [X19,X20] :
      ( ~ r1_xboole_0(k1_tarski(X19),k1_tarski(X20))
      | X19 != X20 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_zfmisc_1])])).

cnf(c_0_34,plain,
    ( k3_xboole_0(k1_tarski(X1),k2_tarski(X1,X2)) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_35,plain,
    ( k2_enumset1(X1,X1,X1,X1) = k1_xboole_0
    | k2_enumset1(X2,X2,X3,X4) = k1_xboole_0
    | r1_xboole_0(k1_setfam_1(k2_enumset1(X2,X2,X3,X4)),X1)
    | k1_setfam_1(k2_enumset1(X2,X3,X4,X1)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_36,plain,
    ( ~ r1_xboole_0(k1_tarski(X1),k1_tarski(X2))
    | X1 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_37,plain,
    ( k3_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X2)) = k2_enumset1(X1,X1,X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_24]),c_0_24]),c_0_15]),c_0_15]),c_0_15]),c_0_22]),c_0_22]),c_0_22])).

cnf(c_0_38,plain,
    ( k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(er,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_29]),c_0_29])])).

cnf(c_0_39,plain,
    ( X1 != X2
    | ~ r1_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_24]),c_0_24]),c_0_15]),c_0_15]),c_0_22]),c_0_22])).

cnf(c_0_40,plain,
    ( k3_xboole_0(k1_xboole_0,k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)) = k1_xboole_0
    | r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_41,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_42,negated_conjecture,(
    ~ ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(assume_negation,[status(cth)],[t12_setfam_1])).

cnf(c_0_43,plain,
    ( ~ r1_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1)) ),
    inference(er,[status(thm)],[c_0_39])).

cnf(c_0_44,plain,
    ( k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_38]),c_0_41])).

fof(c_0_45,negated_conjecture,(
    k1_setfam_1(k2_tarski(esk1_0,esk2_0)) != k3_xboole_0(esk1_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_42])])])).

cnf(c_0_46,plain,
    ( k3_xboole_0(k1_setfam_1(k2_enumset1(X1,X1,X2,X3)),X4) = k1_setfam_1(k2_enumset1(X1,X2,X3,X4))
    | k2_enumset1(X1,X1,X2,X3) = k1_xboole_0
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_32])).

cnf(c_0_47,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_44])).

cnf(c_0_48,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk1_0,esk2_0)) != k3_xboole_0(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_49,plain,
    ( k3_xboole_0(k1_setfam_1(k2_enumset1(X1,X1,X2,X3)),X4) = k1_setfam_1(k2_enumset1(X1,X2,X3,X4))
    | k2_enumset1(X1,X1,X2,X3) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_47])])).

cnf(c_0_50,negated_conjecture,
    ( k1_setfam_1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0)) != k3_xboole_0(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_15]),c_0_22])).

cnf(c_0_51,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) = k3_xboole_0(X1,X2)
    | k2_enumset1(X1,X1,X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_49,c_0_29])).

cnf(c_0_52,negated_conjecture,
    ( k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_53,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_52]),c_0_47])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:19:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S078N
% 0.21/0.38  # and selection function SelectCQIArNpEqFirst.
% 0.21/0.38  #
% 0.21/0.38  # Preprocessing time       : 0.027 s
% 0.21/0.38  # Presaturation interreduction done
% 0.21/0.38  
% 0.21/0.38  # Proof found!
% 0.21/0.38  # SZS status Theorem
% 0.21/0.38  # SZS output start CNFRefutation
% 0.21/0.38  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.21/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.21/0.38  fof(t10_setfam_1, axiom, ![X1, X2]:~(((X1!=k1_xboole_0&X2!=k1_xboole_0)&k1_setfam_1(k2_xboole_0(X1,X2))!=k3_xboole_0(k1_setfam_1(X1),k1_setfam_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_setfam_1)).
% 0.21/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.21/0.38  fof(t46_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 0.21/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.21/0.38  fof(t11_setfam_1, axiom, ![X1]:k1_setfam_1(k1_tarski(X1))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_setfam_1)).
% 0.21/0.38  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.21/0.38  fof(t19_zfmisc_1, axiom, ![X1, X2]:k3_xboole_0(k1_tarski(X1),k2_tarski(X1,X2))=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_zfmisc_1)).
% 0.21/0.38  fof(t16_zfmisc_1, axiom, ![X1, X2]:~((r1_xboole_0(k1_tarski(X1),k1_tarski(X2))&X1=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_zfmisc_1)).
% 0.21/0.38  fof(t12_setfam_1, conjecture, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.21/0.38  fof(c_0_11, plain, ![X17, X18]:k3_tarski(k2_tarski(X17,X18))=k2_xboole_0(X17,X18), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.21/0.38  fof(c_0_12, plain, ![X12, X13]:k1_enumset1(X12,X12,X13)=k2_tarski(X12,X13), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.21/0.38  fof(c_0_13, plain, ![X23, X24]:(X23=k1_xboole_0|X24=k1_xboole_0|k1_setfam_1(k2_xboole_0(X23,X24))=k3_xboole_0(k1_setfam_1(X23),k1_setfam_1(X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_setfam_1])])).
% 0.21/0.38  cnf(c_0_14, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.38  cnf(c_0_15, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.38  fof(c_0_16, plain, ![X14, X15, X16]:k2_enumset1(X14,X14,X15,X16)=k1_enumset1(X14,X15,X16), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.21/0.38  fof(c_0_17, plain, ![X7, X8, X9, X10]:k2_enumset1(X7,X8,X9,X10)=k2_xboole_0(k1_enumset1(X7,X8,X9),k1_tarski(X10)), inference(variable_rename,[status(thm)],[t46_enumset1])).
% 0.21/0.38  fof(c_0_18, plain, ![X11]:k2_tarski(X11,X11)=k1_tarski(X11), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.21/0.38  fof(c_0_19, plain, ![X25]:k1_setfam_1(k1_tarski(X25))=X25, inference(variable_rename,[status(thm)],[t11_setfam_1])).
% 0.21/0.38  cnf(c_0_20, plain, (X1=k1_xboole_0|X2=k1_xboole_0|k1_setfam_1(k2_xboole_0(X1,X2))=k3_xboole_0(k1_setfam_1(X1),k1_setfam_1(X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.38  cnf(c_0_21, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.21/0.38  cnf(c_0_22, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.38  cnf(c_0_23, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.38  cnf(c_0_24, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.38  cnf(c_0_25, plain, (k1_setfam_1(k1_tarski(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.38  fof(c_0_26, plain, ![X5, X6]:((~r1_xboole_0(X5,X6)|k3_xboole_0(X5,X6)=k1_xboole_0)&(k3_xboole_0(X5,X6)!=k1_xboole_0|r1_xboole_0(X5,X6))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.21/0.38  cnf(c_0_27, plain, (X2=k1_xboole_0|X1=k1_xboole_0|k1_setfam_1(k3_tarski(k2_enumset1(X1,X1,X1,X2)))=k3_xboole_0(k1_setfam_1(X1),k1_setfam_1(X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_21]), c_0_22])).
% 0.21/0.38  cnf(c_0_28, plain, (k2_enumset1(X1,X2,X3,X4)=k3_tarski(k2_enumset1(k2_enumset1(X1,X1,X2,X3),k2_enumset1(X1,X1,X2,X3),k2_enumset1(X1,X1,X2,X3),k2_enumset1(X4,X4,X4,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_24]), c_0_15]), c_0_21]), c_0_22]), c_0_22]), c_0_22]), c_0_22])).
% 0.21/0.38  cnf(c_0_29, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_24]), c_0_15]), c_0_22])).
% 0.21/0.38  fof(c_0_30, plain, ![X21, X22]:k3_xboole_0(k1_tarski(X21),k2_tarski(X21,X22))=k1_tarski(X21), inference(variable_rename,[status(thm)],[t19_zfmisc_1])).
% 0.21/0.38  cnf(c_0_31, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.38  cnf(c_0_32, plain, (k3_xboole_0(k1_setfam_1(k2_enumset1(X1,X1,X2,X3)),X4)=k1_setfam_1(k2_enumset1(X1,X2,X3,X4))|k2_enumset1(X1,X1,X2,X3)=k1_xboole_0|k2_enumset1(X4,X4,X4,X4)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29])).
% 0.21/0.38  fof(c_0_33, plain, ![X19, X20]:(~r1_xboole_0(k1_tarski(X19),k1_tarski(X20))|X19!=X20), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_zfmisc_1])])).
% 0.21/0.38  cnf(c_0_34, plain, (k3_xboole_0(k1_tarski(X1),k2_tarski(X1,X2))=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.38  cnf(c_0_35, plain, (k2_enumset1(X1,X1,X1,X1)=k1_xboole_0|k2_enumset1(X2,X2,X3,X4)=k1_xboole_0|r1_xboole_0(k1_setfam_1(k2_enumset1(X2,X2,X3,X4)),X1)|k1_setfam_1(k2_enumset1(X2,X3,X4,X1))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.21/0.38  cnf(c_0_36, plain, (~r1_xboole_0(k1_tarski(X1),k1_tarski(X2))|X1!=X2), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.21/0.38  cnf(c_0_37, plain, (k3_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X2))=k2_enumset1(X1,X1,X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_24]), c_0_24]), c_0_15]), c_0_15]), c_0_15]), c_0_22]), c_0_22]), c_0_22])).
% 0.21/0.38  cnf(c_0_38, plain, (k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)=k1_xboole_0|r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(er,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_29]), c_0_29])])).
% 0.21/0.38  cnf(c_0_39, plain, (X1!=X2|~r1_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_24]), c_0_24]), c_0_15]), c_0_15]), c_0_22]), c_0_22])).
% 0.21/0.38  cnf(c_0_40, plain, (k3_xboole_0(k1_xboole_0,k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X1))=k1_xboole_0|r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.21/0.38  cnf(c_0_41, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.38  fof(c_0_42, negated_conjecture, ~(![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(assume_negation,[status(cth)],[t12_setfam_1])).
% 0.21/0.38  cnf(c_0_43, plain, (~r1_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1))), inference(er,[status(thm)],[c_0_39])).
% 0.21/0.38  cnf(c_0_44, plain, (k3_xboole_0(k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_38]), c_0_41])).
% 0.21/0.38  fof(c_0_45, negated_conjecture, k1_setfam_1(k2_tarski(esk1_0,esk2_0))!=k3_xboole_0(esk1_0,esk2_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_42])])])).
% 0.21/0.38  cnf(c_0_46, plain, (k3_xboole_0(k1_setfam_1(k2_enumset1(X1,X1,X2,X3)),X4)=k1_setfam_1(k2_enumset1(X1,X2,X3,X4))|k2_enumset1(X1,X1,X2,X3)=k1_xboole_0|~r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_43, c_0_32])).
% 0.21/0.38  cnf(c_0_47, plain, (r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_31, c_0_44])).
% 0.21/0.38  cnf(c_0_48, negated_conjecture, (k1_setfam_1(k2_tarski(esk1_0,esk2_0))!=k3_xboole_0(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.21/0.38  cnf(c_0_49, plain, (k3_xboole_0(k1_setfam_1(k2_enumset1(X1,X1,X2,X3)),X4)=k1_setfam_1(k2_enumset1(X1,X2,X3,X4))|k2_enumset1(X1,X1,X2,X3)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_47])])).
% 0.21/0.38  cnf(c_0_50, negated_conjecture, (k1_setfam_1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0))!=k3_xboole_0(esk1_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_15]), c_0_22])).
% 0.21/0.38  cnf(c_0_51, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,X2))=k3_xboole_0(X1,X2)|k2_enumset1(X1,X1,X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_49, c_0_29])).
% 0.21/0.38  cnf(c_0_52, negated_conjecture, (k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.21/0.38  cnf(c_0_53, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_52]), c_0_47])]), ['proof']).
% 0.21/0.38  # SZS output end CNFRefutation
% 0.21/0.38  # Proof object total steps             : 54
% 0.21/0.38  # Proof object clause steps            : 31
% 0.21/0.38  # Proof object formula steps           : 23
% 0.21/0.38  # Proof object conjectures             : 7
% 0.21/0.38  # Proof object clause conjectures      : 4
% 0.21/0.38  # Proof object formula conjectures     : 3
% 0.21/0.38  # Proof object initial clauses used    : 12
% 0.21/0.38  # Proof object initial formulas used   : 11
% 0.21/0.38  # Proof object generating inferences   : 10
% 0.21/0.38  # Proof object simplifying inferences  : 38
% 0.21/0.38  # Training examples: 0 positive, 0 negative
% 0.21/0.38  # Parsed axioms                        : 11
% 0.21/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.38  # Initial clauses                      : 12
% 0.21/0.38  # Removed in clause preprocessing      : 4
% 0.21/0.38  # Initial clauses in saturation        : 8
% 0.21/0.38  # Processed clauses                    : 45
% 0.21/0.38  # ...of these trivial                  : 0
% 0.21/0.38  # ...subsumed                          : 4
% 0.21/0.38  # ...remaining for further processing  : 41
% 0.21/0.38  # Other redundant clauses eliminated   : 4
% 0.21/0.38  # Clauses deleted for lack of memory   : 0
% 0.21/0.38  # Backward-subsumed                    : 6
% 0.21/0.38  # Backward-rewritten                   : 10
% 0.21/0.38  # Generated clauses                    : 128
% 0.21/0.38  # ...of the previous two non-trivial   : 109
% 0.21/0.38  # Contextual simplify-reflections      : 1
% 0.21/0.38  # Paramodulations                      : 122
% 0.21/0.38  # Factorizations                       : 2
% 0.21/0.38  # Equation resolutions                 : 4
% 0.21/0.38  # Propositional unsat checks           : 0
% 0.21/0.38  #    Propositional check models        : 0
% 0.21/0.38  #    Propositional check unsatisfiable : 0
% 0.21/0.38  #    Propositional clauses             : 0
% 0.21/0.38  #    Propositional clauses after purity: 0
% 0.21/0.38  #    Propositional unsat core size     : 0
% 0.21/0.38  #    Propositional preprocessing time  : 0.000
% 0.21/0.38  #    Propositional encoding time       : 0.000
% 0.21/0.38  #    Propositional solver time         : 0.000
% 0.21/0.38  #    Success case prop preproc time    : 0.000
% 0.21/0.38  #    Success case prop encoding time   : 0.000
% 0.21/0.38  #    Success case prop solver time     : 0.000
% 0.21/0.38  # Current number of processed clauses  : 16
% 0.21/0.38  #    Positive orientable unit clauses  : 7
% 0.21/0.38  #    Positive unorientable unit clauses: 0
% 0.21/0.38  #    Negative unit clauses             : 2
% 0.21/0.38  #    Non-unit-clauses                  : 7
% 0.21/0.38  # Current number of unprocessed clauses: 67
% 0.21/0.38  # ...number of literals in the above   : 232
% 0.21/0.38  # Current number of archived formulas  : 0
% 0.21/0.38  # Current number of archived clauses   : 28
% 0.21/0.38  # Clause-clause subsumption calls (NU) : 48
% 0.21/0.38  # Rec. Clause-clause subsumption calls : 24
% 0.21/0.38  # Non-unit clause-clause subsumptions  : 9
% 0.21/0.38  # Unit Clause-clause subsumption calls : 16
% 0.21/0.38  # Rewrite failures with RHS unbound    : 0
% 0.21/0.38  # BW rewrite match attempts            : 6
% 0.21/0.38  # BW rewrite match successes           : 3
% 0.21/0.38  # Condensation attempts                : 0
% 0.21/0.38  # Condensation successes               : 0
% 0.21/0.38  # Termbank termtop insertions          : 2697
% 0.21/0.38  
% 0.21/0.38  # -------------------------------------------------
% 0.21/0.38  # User time                : 0.030 s
% 0.21/0.38  # System time              : 0.004 s
% 0.21/0.38  # Total time               : 0.034 s
% 0.21/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------

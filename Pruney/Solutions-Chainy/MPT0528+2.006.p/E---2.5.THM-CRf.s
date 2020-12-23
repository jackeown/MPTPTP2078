%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:50:06 EST 2020

% Result     : Theorem 0.22s
% Output     : CNFRefutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   33 ( 347 expanded)
%              Number of clauses        :   22 ( 144 expanded)
%              Number of leaves         :    5 (  88 expanded)
%              Depth                    :   13
%              Number of atoms          :   55 ( 652 expanded)
%              Number of equality atoms :   26 ( 277 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t128_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X1,k8_relat_1(X1,X2)) = k8_relat_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_relat_1)).

fof(t127_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k8_relat_1(X1,k8_relat_1(X2,X3)) = k8_relat_1(k3_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_relat_1)).

fof(t119_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k8_relat_1(X1,X2)) = k3_xboole_0(k2_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_relat_1)).

fof(t126_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(k2_relat_1(X1),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_relat_1)).

fof(dt_k8_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => v1_relat_1(k8_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => k8_relat_1(X1,k8_relat_1(X1,X2)) = k8_relat_1(X1,X2) ) ),
    inference(assume_negation,[status(cth)],[t128_relat_1])).

fof(c_0_6,plain,(
    ! [X9,X10,X11] :
      ( ~ v1_relat_1(X11)
      | k8_relat_1(X9,k8_relat_1(X10,X11)) = k8_relat_1(k3_xboole_0(X9,X10),X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t127_relat_1])])).

fof(c_0_7,plain,(
    ! [X6,X7] :
      ( ~ v1_relat_1(X7)
      | k2_relat_1(k8_relat_1(X6,X7)) = k3_xboole_0(k2_relat_1(X7),X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t119_relat_1])])).

fof(c_0_8,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & k8_relat_1(esk1_0,k8_relat_1(esk1_0,esk2_0)) != k8_relat_1(esk1_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_9,plain,(
    ! [X8] :
      ( ~ v1_relat_1(X8)
      | k8_relat_1(k2_relat_1(X8),X8) = X8 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t126_relat_1])])).

cnf(c_0_10,plain,
    ( k8_relat_1(X2,k8_relat_1(X3,X1)) = k8_relat_1(k3_xboole_0(X2,X3),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( k2_relat_1(k8_relat_1(X2,X1)) = k3_xboole_0(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_12,plain,(
    ! [X4,X5] :
      ( ~ v1_relat_1(X5)
      | v1_relat_1(k8_relat_1(X4,X5)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relat_1])])).

cnf(c_0_13,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( k8_relat_1(k2_relat_1(X1),X1) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(X1,X2)),X3) = k8_relat_1(k2_relat_1(X2),k8_relat_1(X1,X3))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_16,plain,
    ( v1_relat_1(k8_relat_1(X2,X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( k8_relat_1(k3_xboole_0(X1,X2),esk2_0) = k8_relat_1(X1,k8_relat_1(X2,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_10,c_0_13])).

cnf(c_0_18,plain,
    ( k8_relat_1(k2_relat_1(X1),k8_relat_1(X2,k8_relat_1(X2,X1))) = k8_relat_1(X2,X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( k8_relat_1(k2_relat_1(k8_relat_1(X1,X2)),esk2_0) = k8_relat_1(k2_relat_1(X2),k8_relat_1(X1,esk2_0))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_11])).

cnf(c_0_20,plain,
    ( k8_relat_1(k2_relat_1(X1),k8_relat_1(k2_relat_1(X1),X1)) = X1
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( k8_relat_1(k2_relat_1(X1),k8_relat_1(k2_relat_1(X1),esk2_0)) = k8_relat_1(k2_relat_1(X1),esk2_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( k8_relat_1(k2_relat_1(esk2_0),esk2_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_13])])).

cnf(c_0_23,negated_conjecture,
    ( k8_relat_1(k2_relat_1(esk2_0),k8_relat_1(k2_relat_1(esk2_0),X1)) = k8_relat_1(k2_relat_1(esk2_0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_22]),c_0_13])])).

cnf(c_0_24,negated_conjecture,
    ( v1_relat_1(k8_relat_1(X1,k8_relat_1(X2,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_13])])).

cnf(c_0_25,negated_conjecture,
    ( k8_relat_1(k2_relat_1(esk2_0),k8_relat_1(X1,esk2_0)) = k8_relat_1(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_18]),c_0_24]),c_0_13])])).

cnf(c_0_26,negated_conjecture,
    ( v1_relat_1(k8_relat_1(X1,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_14]),c_0_13])])).

cnf(c_0_27,negated_conjecture,
    ( k8_relat_1(k2_relat_1(k8_relat_1(X1,esk2_0)),k8_relat_1(X1,esk2_0)) = k8_relat_1(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_25]),c_0_25]),c_0_26])])).

cnf(c_0_28,negated_conjecture,
    ( k8_relat_1(k2_relat_1(esk2_0),k8_relat_1(X1,k8_relat_1(X1,esk2_0))) = k8_relat_1(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_27]),c_0_26]),c_0_13])])).

cnf(c_0_29,negated_conjecture,
    ( k8_relat_1(k2_relat_1(esk2_0),k8_relat_1(X1,k8_relat_1(X2,esk2_0))) = k8_relat_1(X1,k8_relat_1(X2,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_10]),c_0_13])])).

cnf(c_0_30,negated_conjecture,
    ( k8_relat_1(esk1_0,k8_relat_1(esk1_0,esk2_0)) != k8_relat_1(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_31,negated_conjecture,
    ( k8_relat_1(X1,k8_relat_1(X1,esk2_0)) = k8_relat_1(X1,esk2_0) ),
    inference(rw,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_32,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_31])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:31:15 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.22/0.39  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.22/0.39  # and selection function SelectCQIPrecWNTNp.
% 0.22/0.39  #
% 0.22/0.39  # Preprocessing time       : 0.026 s
% 0.22/0.39  # Presaturation interreduction done
% 0.22/0.39  
% 0.22/0.39  # Proof found!
% 0.22/0.39  # SZS status Theorem
% 0.22/0.39  # SZS output start CNFRefutation
% 0.22/0.39  fof(t128_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>k8_relat_1(X1,k8_relat_1(X1,X2))=k8_relat_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t128_relat_1)).
% 0.22/0.39  fof(t127_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k8_relat_1(X1,k8_relat_1(X2,X3))=k8_relat_1(k3_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t127_relat_1)).
% 0.22/0.39  fof(t119_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k8_relat_1(X1,X2))=k3_xboole_0(k2_relat_1(X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t119_relat_1)).
% 0.22/0.39  fof(t126_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k8_relat_1(k2_relat_1(X1),X1)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t126_relat_1)).
% 0.22/0.39  fof(dt_k8_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>v1_relat_1(k8_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 0.22/0.39  fof(c_0_5, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>k8_relat_1(X1,k8_relat_1(X1,X2))=k8_relat_1(X1,X2))), inference(assume_negation,[status(cth)],[t128_relat_1])).
% 0.22/0.39  fof(c_0_6, plain, ![X9, X10, X11]:(~v1_relat_1(X11)|k8_relat_1(X9,k8_relat_1(X10,X11))=k8_relat_1(k3_xboole_0(X9,X10),X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t127_relat_1])])).
% 0.22/0.39  fof(c_0_7, plain, ![X6, X7]:(~v1_relat_1(X7)|k2_relat_1(k8_relat_1(X6,X7))=k3_xboole_0(k2_relat_1(X7),X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t119_relat_1])])).
% 0.22/0.39  fof(c_0_8, negated_conjecture, (v1_relat_1(esk2_0)&k8_relat_1(esk1_0,k8_relat_1(esk1_0,esk2_0))!=k8_relat_1(esk1_0,esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).
% 0.22/0.39  fof(c_0_9, plain, ![X8]:(~v1_relat_1(X8)|k8_relat_1(k2_relat_1(X8),X8)=X8), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t126_relat_1])])).
% 0.22/0.39  cnf(c_0_10, plain, (k8_relat_1(X2,k8_relat_1(X3,X1))=k8_relat_1(k3_xboole_0(X2,X3),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.22/0.39  cnf(c_0_11, plain, (k2_relat_1(k8_relat_1(X2,X1))=k3_xboole_0(k2_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.22/0.39  fof(c_0_12, plain, ![X4, X5]:(~v1_relat_1(X5)|v1_relat_1(k8_relat_1(X4,X5))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relat_1])])).
% 0.22/0.39  cnf(c_0_13, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.22/0.39  cnf(c_0_14, plain, (k8_relat_1(k2_relat_1(X1),X1)=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.22/0.39  cnf(c_0_15, plain, (k8_relat_1(k2_relat_1(k8_relat_1(X1,X2)),X3)=k8_relat_1(k2_relat_1(X2),k8_relat_1(X1,X3))|~v1_relat_1(X3)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.22/0.39  cnf(c_0_16, plain, (v1_relat_1(k8_relat_1(X2,X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.22/0.39  cnf(c_0_17, negated_conjecture, (k8_relat_1(k3_xboole_0(X1,X2),esk2_0)=k8_relat_1(X1,k8_relat_1(X2,esk2_0))), inference(spm,[status(thm)],[c_0_10, c_0_13])).
% 0.22/0.39  cnf(c_0_18, plain, (k8_relat_1(k2_relat_1(X1),k8_relat_1(X2,k8_relat_1(X2,X1)))=k8_relat_1(X2,X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16])).
% 0.22/0.39  cnf(c_0_19, negated_conjecture, (k8_relat_1(k2_relat_1(k8_relat_1(X1,X2)),esk2_0)=k8_relat_1(k2_relat_1(X2),k8_relat_1(X1,esk2_0))|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_17, c_0_11])).
% 0.22/0.39  cnf(c_0_20, plain, (k8_relat_1(k2_relat_1(X1),k8_relat_1(k2_relat_1(X1),X1))=X1|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_18, c_0_14])).
% 0.22/0.39  cnf(c_0_21, negated_conjecture, (k8_relat_1(k2_relat_1(X1),k8_relat_1(k2_relat_1(X1),esk2_0))=k8_relat_1(k2_relat_1(X1),esk2_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_19, c_0_14])).
% 0.22/0.39  cnf(c_0_22, negated_conjecture, (k8_relat_1(k2_relat_1(esk2_0),esk2_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_13])])).
% 0.22/0.39  cnf(c_0_23, negated_conjecture, (k8_relat_1(k2_relat_1(esk2_0),k8_relat_1(k2_relat_1(esk2_0),X1))=k8_relat_1(k2_relat_1(esk2_0),X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_22]), c_0_13])])).
% 0.22/0.39  cnf(c_0_24, negated_conjecture, (v1_relat_1(k8_relat_1(X1,k8_relat_1(X2,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_13])])).
% 0.22/0.39  cnf(c_0_25, negated_conjecture, (k8_relat_1(k2_relat_1(esk2_0),k8_relat_1(X1,esk2_0))=k8_relat_1(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_18]), c_0_24]), c_0_13])])).
% 0.22/0.39  cnf(c_0_26, negated_conjecture, (v1_relat_1(k8_relat_1(X1,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_14]), c_0_13])])).
% 0.22/0.39  cnf(c_0_27, negated_conjecture, (k8_relat_1(k2_relat_1(k8_relat_1(X1,esk2_0)),k8_relat_1(X1,esk2_0))=k8_relat_1(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_25]), c_0_25]), c_0_26])])).
% 0.22/0.39  cnf(c_0_28, negated_conjecture, (k8_relat_1(k2_relat_1(esk2_0),k8_relat_1(X1,k8_relat_1(X1,esk2_0)))=k8_relat_1(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_27]), c_0_26]), c_0_13])])).
% 0.22/0.39  cnf(c_0_29, negated_conjecture, (k8_relat_1(k2_relat_1(esk2_0),k8_relat_1(X1,k8_relat_1(X2,esk2_0)))=k8_relat_1(X1,k8_relat_1(X2,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_10]), c_0_13])])).
% 0.22/0.39  cnf(c_0_30, negated_conjecture, (k8_relat_1(esk1_0,k8_relat_1(esk1_0,esk2_0))!=k8_relat_1(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.22/0.39  cnf(c_0_31, negated_conjecture, (k8_relat_1(X1,k8_relat_1(X1,esk2_0))=k8_relat_1(X1,esk2_0)), inference(rw,[status(thm)],[c_0_28, c_0_29])).
% 0.22/0.39  cnf(c_0_32, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_31])]), ['proof']).
% 0.22/0.39  # SZS output end CNFRefutation
% 0.22/0.39  # Proof object total steps             : 33
% 0.22/0.39  # Proof object clause steps            : 22
% 0.22/0.39  # Proof object formula steps           : 11
% 0.22/0.39  # Proof object conjectures             : 18
% 0.22/0.39  # Proof object clause conjectures      : 15
% 0.22/0.39  # Proof object formula conjectures     : 3
% 0.22/0.39  # Proof object initial clauses used    : 6
% 0.22/0.39  # Proof object initial formulas used   : 5
% 0.22/0.39  # Proof object generating inferences   : 14
% 0.22/0.39  # Proof object simplifying inferences  : 23
% 0.22/0.39  # Training examples: 0 positive, 0 negative
% 0.22/0.39  # Parsed axioms                        : 5
% 0.22/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.22/0.39  # Initial clauses                      : 6
% 0.22/0.39  # Removed in clause preprocessing      : 0
% 0.22/0.39  # Initial clauses in saturation        : 6
% 0.22/0.39  # Processed clauses                    : 80
% 0.22/0.39  # ...of these trivial                  : 12
% 0.22/0.39  # ...subsumed                          : 31
% 0.22/0.39  # ...remaining for further processing  : 37
% 0.22/0.39  # Other redundant clauses eliminated   : 0
% 0.22/0.39  # Clauses deleted for lack of memory   : 0
% 0.22/0.39  # Backward-subsumed                    : 0
% 0.22/0.39  # Backward-rewritten                   : 4
% 0.22/0.39  # Generated clauses                    : 525
% 0.22/0.39  # ...of the previous two non-trivial   : 297
% 0.22/0.39  # Contextual simplify-reflections      : 1
% 0.22/0.39  # Paramodulations                      : 525
% 0.22/0.39  # Factorizations                       : 0
% 0.22/0.39  # Equation resolutions                 : 0
% 0.22/0.39  # Propositional unsat checks           : 0
% 0.22/0.39  #    Propositional check models        : 0
% 0.22/0.39  #    Propositional check unsatisfiable : 0
% 0.22/0.39  #    Propositional clauses             : 0
% 0.22/0.39  #    Propositional clauses after purity: 0
% 0.22/0.39  #    Propositional unsat core size     : 0
% 0.22/0.39  #    Propositional preprocessing time  : 0.000
% 0.22/0.39  #    Propositional encoding time       : 0.000
% 0.22/0.39  #    Propositional solver time         : 0.000
% 0.22/0.39  #    Success case prop preproc time    : 0.000
% 0.22/0.39  #    Success case prop encoding time   : 0.000
% 0.22/0.39  #    Success case prop solver time     : 0.000
% 0.22/0.39  # Current number of processed clauses  : 27
% 0.22/0.39  #    Positive orientable unit clauses  : 14
% 0.22/0.39  #    Positive unorientable unit clauses: 0
% 0.22/0.39  #    Negative unit clauses             : 0
% 0.22/0.39  #    Non-unit-clauses                  : 13
% 0.22/0.39  # Current number of unprocessed clauses: 229
% 0.22/0.39  # ...number of literals in the above   : 434
% 0.22/0.39  # Current number of archived formulas  : 0
% 0.22/0.39  # Current number of archived clauses   : 10
% 0.22/0.39  # Clause-clause subsumption calls (NU) : 101
% 0.22/0.39  # Rec. Clause-clause subsumption calls : 99
% 0.22/0.39  # Non-unit clause-clause subsumptions  : 32
% 0.22/0.39  # Unit Clause-clause subsumption calls : 3
% 0.22/0.39  # Rewrite failures with RHS unbound    : 0
% 0.22/0.39  # BW rewrite match attempts            : 24
% 0.22/0.39  # BW rewrite match successes           : 4
% 0.22/0.39  # Condensation attempts                : 0
% 0.22/0.39  # Condensation successes               : 0
% 0.22/0.39  # Termbank termtop insertions          : 6702
% 0.22/0.39  
% 0.22/0.39  # -------------------------------------------------
% 0.22/0.39  # User time                : 0.031 s
% 0.22/0.39  # System time              : 0.005 s
% 0.22/0.39  # Total time               : 0.036 s
% 0.22/0.39  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------

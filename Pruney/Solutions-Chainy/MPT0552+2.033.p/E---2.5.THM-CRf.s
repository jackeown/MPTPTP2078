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
% DateTime   : Thu Dec  3 10:50:57 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   31 (  68 expanded)
%              Number of clauses        :   16 (  30 expanded)
%              Number of leaves         :    7 (  18 expanded)
%              Depth                    :    9
%              Number of atoms          :   60 ( 134 expanded)
%              Number of equality atoms :   11 (  31 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(t100_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k7_relat_1(k7_relat_1(X3,X1),X2) = k7_relat_1(X3,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(t144_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k9_relat_1(X2,X1),k2_relat_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t19_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(t154_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => r1_tarski(k9_relat_1(X3,k3_xboole_0(X1,X2)),k3_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_relat_1)).

fof(c_0_7,plain,(
    ! [X16,X17] :
      ( ~ v1_relat_1(X17)
      | k2_relat_1(k7_relat_1(X17,X16)) = k9_relat_1(X17,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

fof(c_0_8,plain,(
    ! [X11,X12,X13] :
      ( ~ v1_relat_1(X13)
      | k7_relat_1(k7_relat_1(X13,X11),X12) = k7_relat_1(X13,k3_xboole_0(X11,X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t100_relat_1])])).

fof(c_0_9,plain,(
    ! [X9,X10] :
      ( ~ v1_relat_1(X9)
      | v1_relat_1(k7_relat_1(X9,X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

fof(c_0_10,plain,(
    ! [X14,X15] :
      ( ~ v1_relat_1(X15)
      | r1_tarski(k9_relat_1(X15,X14),k2_relat_1(X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t144_relat_1])])).

cnf(c_0_11,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k7_relat_1(X1,k3_xboole_0(X2,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( r1_tarski(k9_relat_1(X1,X2),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( k2_relat_1(k7_relat_1(X1,k3_xboole_0(X2,X3))) = k9_relat_1(k7_relat_1(X1,X2),X3)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13])).

cnf(c_0_16,plain,
    ( r1_tarski(k9_relat_1(k7_relat_1(X1,X2),X3),k9_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_11]),c_0_13])).

cnf(c_0_17,plain,
    ( k9_relat_1(k7_relat_1(X1,X2),X3) = k9_relat_1(X1,k3_xboole_0(X2,X3))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_15])).

fof(c_0_18,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_19,plain,(
    ! [X6,X7,X8] :
      ( ~ r1_tarski(X6,X7)
      | ~ r1_tarski(X6,X8)
      | r1_tarski(X6,k3_xboole_0(X7,X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).

cnf(c_0_20,plain,
    ( r1_tarski(k9_relat_1(X1,k3_xboole_0(X2,X3)),k9_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_22,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => r1_tarski(k9_relat_1(X3,k3_xboole_0(X1,X2)),k3_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2))) ) ),
    inference(assume_negation,[status(cth)],[t154_relat_1])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( r1_tarski(k9_relat_1(X1,k3_xboole_0(X2,X3)),k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

fof(c_0_25,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & ~ r1_tarski(k9_relat_1(esk3_0,k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk2_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])).

cnf(c_0_26,plain,
    ( r1_tarski(k9_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(X4,k9_relat_1(X1,X3)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k9_relat_1(X1,k3_xboole_0(X2,X3)),X4) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_27,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk3_0,k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_28,plain,
    ( r1_tarski(k9_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,X3)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_20])).

cnf(c_0_29,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:35:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.42  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.20/0.42  # and selection function SelectCQIPrecWNTNp.
% 0.20/0.42  #
% 0.20/0.42  # Preprocessing time       : 0.026 s
% 0.20/0.42  # Presaturation interreduction done
% 0.20/0.42  
% 0.20/0.42  # Proof found!
% 0.20/0.42  # SZS status Theorem
% 0.20/0.42  # SZS output start CNFRefutation
% 0.20/0.42  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 0.20/0.42  fof(t100_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k7_relat_1(k7_relat_1(X3,X1),X2)=k7_relat_1(X3,k3_xboole_0(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 0.20/0.42  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.20/0.42  fof(t144_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k9_relat_1(X2,X1),k2_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 0.20/0.42  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.20/0.42  fof(t19_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(X1,k3_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 0.20/0.42  fof(t154_relat_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>r1_tarski(k9_relat_1(X3,k3_xboole_0(X1,X2)),k3_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t154_relat_1)).
% 0.20/0.42  fof(c_0_7, plain, ![X16, X17]:(~v1_relat_1(X17)|k2_relat_1(k7_relat_1(X17,X16))=k9_relat_1(X17,X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.20/0.42  fof(c_0_8, plain, ![X11, X12, X13]:(~v1_relat_1(X13)|k7_relat_1(k7_relat_1(X13,X11),X12)=k7_relat_1(X13,k3_xboole_0(X11,X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t100_relat_1])])).
% 0.20/0.42  fof(c_0_9, plain, ![X9, X10]:(~v1_relat_1(X9)|v1_relat_1(k7_relat_1(X9,X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.20/0.42  fof(c_0_10, plain, ![X14, X15]:(~v1_relat_1(X15)|r1_tarski(k9_relat_1(X15,X14),k2_relat_1(X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t144_relat_1])])).
% 0.20/0.42  cnf(c_0_11, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.42  cnf(c_0_12, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k7_relat_1(X1,k3_xboole_0(X2,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.42  cnf(c_0_13, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.42  cnf(c_0_14, plain, (r1_tarski(k9_relat_1(X1,X2),k2_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.42  cnf(c_0_15, plain, (k2_relat_1(k7_relat_1(X1,k3_xboole_0(X2,X3)))=k9_relat_1(k7_relat_1(X1,X2),X3)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12]), c_0_13])).
% 0.20/0.42  cnf(c_0_16, plain, (r1_tarski(k9_relat_1(k7_relat_1(X1,X2),X3),k9_relat_1(X1,X2))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_11]), c_0_13])).
% 0.20/0.42  cnf(c_0_17, plain, (k9_relat_1(k7_relat_1(X1,X2),X3)=k9_relat_1(X1,k3_xboole_0(X2,X3))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_11, c_0_15])).
% 0.20/0.42  fof(c_0_18, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.20/0.42  fof(c_0_19, plain, ![X6, X7, X8]:(~r1_tarski(X6,X7)|~r1_tarski(X6,X8)|r1_tarski(X6,k3_xboole_0(X7,X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).
% 0.20/0.42  cnf(c_0_20, plain, (r1_tarski(k9_relat_1(X1,k3_xboole_0(X2,X3)),k9_relat_1(X1,X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.20/0.42  cnf(c_0_21, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.42  fof(c_0_22, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>r1_tarski(k9_relat_1(X3,k3_xboole_0(X1,X2)),k3_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2))))), inference(assume_negation,[status(cth)],[t154_relat_1])).
% 0.20/0.42  cnf(c_0_23, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.42  cnf(c_0_24, plain, (r1_tarski(k9_relat_1(X1,k3_xboole_0(X2,X3)),k9_relat_1(X1,X3))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.20/0.42  fof(c_0_25, negated_conjecture, (v1_relat_1(esk3_0)&~r1_tarski(k9_relat_1(esk3_0,k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])).
% 0.20/0.42  cnf(c_0_26, plain, (r1_tarski(k9_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(X4,k9_relat_1(X1,X3)))|~v1_relat_1(X1)|~r1_tarski(k9_relat_1(X1,k3_xboole_0(X2,X3)),X4)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.20/0.42  cnf(c_0_27, negated_conjecture, (~r1_tarski(k9_relat_1(esk3_0,k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.42  cnf(c_0_28, plain, (r1_tarski(k9_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,X3)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_26, c_0_20])).
% 0.20/0.42  cnf(c_0_29, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.42  cnf(c_0_30, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29])]), ['proof']).
% 0.20/0.42  # SZS output end CNFRefutation
% 0.20/0.42  # Proof object total steps             : 31
% 0.20/0.42  # Proof object clause steps            : 16
% 0.20/0.42  # Proof object formula steps           : 15
% 0.20/0.42  # Proof object conjectures             : 6
% 0.20/0.42  # Proof object clause conjectures      : 3
% 0.20/0.42  # Proof object formula conjectures     : 3
% 0.20/0.42  # Proof object initial clauses used    : 8
% 0.20/0.42  # Proof object initial formulas used   : 7
% 0.20/0.42  # Proof object generating inferences   : 8
% 0.20/0.42  # Proof object simplifying inferences  : 4
% 0.20/0.42  # Training examples: 0 positive, 0 negative
% 0.20/0.42  # Parsed axioms                        : 7
% 0.20/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.42  # Initial clauses                      : 8
% 0.20/0.42  # Removed in clause preprocessing      : 0
% 0.20/0.42  # Initial clauses in saturation        : 8
% 0.20/0.42  # Processed clauses                    : 332
% 0.20/0.42  # ...of these trivial                  : 1
% 0.20/0.42  # ...subsumed                          : 215
% 0.20/0.42  # ...remaining for further processing  : 116
% 0.20/0.42  # Other redundant clauses eliminated   : 0
% 0.20/0.42  # Clauses deleted for lack of memory   : 0
% 0.20/0.42  # Backward-subsumed                    : 0
% 0.20/0.42  # Backward-rewritten                   : 0
% 0.20/0.42  # Generated clauses                    : 3729
% 0.20/0.42  # ...of the previous two non-trivial   : 3676
% 0.20/0.42  # Contextual simplify-reflections      : 53
% 0.20/0.42  # Paramodulations                      : 3729
% 0.20/0.42  # Factorizations                       : 0
% 0.20/0.42  # Equation resolutions                 : 0
% 0.20/0.42  # Propositional unsat checks           : 0
% 0.20/0.42  #    Propositional check models        : 0
% 0.20/0.42  #    Propositional check unsatisfiable : 0
% 0.20/0.42  #    Propositional clauses             : 0
% 0.20/0.42  #    Propositional clauses after purity: 0
% 0.20/0.42  #    Propositional unsat core size     : 0
% 0.20/0.42  #    Propositional preprocessing time  : 0.000
% 0.20/0.42  #    Propositional encoding time       : 0.000
% 0.20/0.42  #    Propositional solver time         : 0.000
% 0.20/0.42  #    Success case prop preproc time    : 0.000
% 0.20/0.42  #    Success case prop encoding time   : 0.000
% 0.20/0.42  #    Success case prop solver time     : 0.000
% 0.20/0.42  # Current number of processed clauses  : 108
% 0.20/0.42  #    Positive orientable unit clauses  : 1
% 0.20/0.42  #    Positive unorientable unit clauses: 1
% 0.20/0.42  #    Negative unit clauses             : 1
% 0.20/0.42  #    Non-unit-clauses                  : 105
% 0.20/0.42  # Current number of unprocessed clauses: 3351
% 0.20/0.42  # ...number of literals in the above   : 8773
% 0.20/0.42  # Current number of archived formulas  : 0
% 0.20/0.42  # Current number of archived clauses   : 8
% 0.20/0.42  # Clause-clause subsumption calls (NU) : 3505
% 0.20/0.42  # Rec. Clause-clause subsumption calls : 3492
% 0.20/0.42  # Non-unit clause-clause subsumptions  : 268
% 0.20/0.42  # Unit Clause-clause subsumption calls : 0
% 0.20/0.42  # Rewrite failures with RHS unbound    : 0
% 0.20/0.42  # BW rewrite match attempts            : 4
% 0.20/0.42  # BW rewrite match successes           : 4
% 0.20/0.42  # Condensation attempts                : 0
% 0.20/0.42  # Condensation successes               : 0
% 0.20/0.42  # Termbank termtop insertions          : 52727
% 0.20/0.42  
% 0.20/0.42  # -------------------------------------------------
% 0.20/0.42  # User time                : 0.069 s
% 0.20/0.42  # System time              : 0.007 s
% 0.20/0.42  # Total time               : 0.076 s
% 0.20/0.42  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------

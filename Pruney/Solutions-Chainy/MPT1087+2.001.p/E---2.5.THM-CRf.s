%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:08:26 EST 2020

% Result     : Theorem 0.73s
% Output     : CNFRefutation 0.73s
% Verified   : 
% Statistics : Number of formulae       :   39 ( 201 expanded)
%              Number of clauses        :   26 (  90 expanded)
%              Number of leaves         :    6 (  52 expanded)
%              Depth                    :   10
%              Number of atoms          :   96 ( 390 expanded)
%              Number of equality atoms :   25 ( 167 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t15_finset_1,conjecture,(
    ! [X1,X2] :
      ( v1_finset_1(X1)
     => v1_finset_1(k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_finset_1)).

fof(fc10_finset_1,axiom,(
    ! [X1,X2] :
      ( v1_finset_1(X2)
     => v1_finset_1(k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_finset_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(c_0_6,plain,(
    ! [X19,X20] : k1_setfam_1(k2_tarski(X19,X20)) = k3_xboole_0(X19,X20) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_7,plain,(
    ! [X14,X15] : k1_enumset1(X14,X14,X15) = k2_tarski(X14,X15) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_finset_1(X1)
       => v1_finset_1(k3_xboole_0(X1,X2)) ) ),
    inference(assume_negation,[status(cth)],[t15_finset_1])).

fof(c_0_9,plain,(
    ! [X21,X22] :
      ( ~ v1_finset_1(X22)
      | v1_finset_1(k3_xboole_0(X21,X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc10_finset_1])])).

cnf(c_0_10,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_12,plain,(
    ! [X16,X17,X18] : k2_enumset1(X16,X16,X17,X18) = k1_enumset1(X16,X17,X18) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_13,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( r2_hidden(X8,X5)
        | ~ r2_hidden(X8,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( r2_hidden(X8,X6)
        | ~ r2_hidden(X8,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | ~ r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k3_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k3_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X11)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k3_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_14,negated_conjecture,
    ( v1_finset_1(esk2_0)
    & ~ v1_finset_1(k3_xboole_0(esk2_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

cnf(c_0_15,plain,
    ( v1_finset_1(k3_xboole_0(X2,X1))
    | ~ v1_finset_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_17,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( ~ v1_finset_1(k3_xboole_0(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( v1_finset_1(k1_setfam_1(k2_enumset1(X2,X2,X2,X1)))
    | ~ v1_finset_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_16]),c_0_17])).

cnf(c_0_21,plain,
    ( X3 = k1_setfam_1(k2_enumset1(X1,X1,X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_16]),c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( ~ v1_finset_1(k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_16]),c_0_17])).

cnf(c_0_23,plain,
    ( v1_finset_1(X1)
    | r2_hidden(esk1_3(X2,X3,X1),X2)
    | r2_hidden(esk1_3(X2,X3,X1),X1)
    | ~ v1_finset_1(X3) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk1_3(X1,X2,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0))),k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0)))
    | r2_hidden(esk1_3(X1,X2,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0))),X1)
    | ~ v1_finset_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_21])).

cnf(c_0_26,plain,
    ( X3 = k3_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_27,plain,
    ( v1_finset_1(X1)
    | r2_hidden(esk1_3(X1,X2,X1),X1)
    | ~ v1_finset_1(X2) ),
    inference(ef,[status(thm)],[c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( v1_finset_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X2)
    | X3 != k1_setfam_1(k2_enumset1(X2,X2,X2,X4))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_16]),c_0_17])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk1_3(k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0)),X1,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0))),k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0)))
    | ~ v1_finset_1(k1_setfam_1(k2_enumset1(k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0)),k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0)),k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0)),X1))) ),
    inference(ef,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( X3 = k1_setfam_1(k2_enumset1(X1,X1,X1,X2))
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_16]),c_0_17])).

cnf(c_0_32,negated_conjecture,
    ( v1_finset_1(X1)
    | r2_hidden(esk1_3(X1,esk2_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3))) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk1_3(k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0)),X1,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0))),k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0)))
    | ~ v1_finset_1(X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_20])).

cnf(c_0_35,negated_conjecture,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,esk2_0)) = X1
    | v1_finset_1(X1)
    | ~ r2_hidden(esk1_3(X1,esk2_0,X1),esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk1_3(k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0)),X1,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0))),esk2_0)
    | ~ v1_finset_1(X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_37,negated_conjecture,
    ( k1_setfam_1(k2_enumset1(k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0)),k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0)),k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0)),esk2_0)) = k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_28])]),c_0_22])).

cnf(c_0_38,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_37]),c_0_28])]),c_0_22]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:44:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.73/0.91  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.73/0.91  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.73/0.91  #
% 0.73/0.91  # Preprocessing time       : 0.026 s
% 0.73/0.91  # Presaturation interreduction done
% 0.73/0.91  
% 0.73/0.91  # Proof found!
% 0.73/0.91  # SZS status Theorem
% 0.73/0.91  # SZS output start CNFRefutation
% 0.73/0.91  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.73/0.91  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.73/0.91  fof(t15_finset_1, conjecture, ![X1, X2]:(v1_finset_1(X1)=>v1_finset_1(k3_xboole_0(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_finset_1)).
% 0.73/0.91  fof(fc10_finset_1, axiom, ![X1, X2]:(v1_finset_1(X2)=>v1_finset_1(k3_xboole_0(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_finset_1)).
% 0.73/0.91  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.73/0.91  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.73/0.91  fof(c_0_6, plain, ![X19, X20]:k1_setfam_1(k2_tarski(X19,X20))=k3_xboole_0(X19,X20), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.73/0.91  fof(c_0_7, plain, ![X14, X15]:k1_enumset1(X14,X14,X15)=k2_tarski(X14,X15), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.73/0.91  fof(c_0_8, negated_conjecture, ~(![X1, X2]:(v1_finset_1(X1)=>v1_finset_1(k3_xboole_0(X1,X2)))), inference(assume_negation,[status(cth)],[t15_finset_1])).
% 0.73/0.91  fof(c_0_9, plain, ![X21, X22]:(~v1_finset_1(X22)|v1_finset_1(k3_xboole_0(X21,X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc10_finset_1])])).
% 0.73/0.91  cnf(c_0_10, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.73/0.91  cnf(c_0_11, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.73/0.91  fof(c_0_12, plain, ![X16, X17, X18]:k2_enumset1(X16,X16,X17,X18)=k1_enumset1(X16,X17,X18), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.73/0.91  fof(c_0_13, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6))&(r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|~r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k3_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|~r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k3_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))&(r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.73/0.91  fof(c_0_14, negated_conjecture, (v1_finset_1(esk2_0)&~v1_finset_1(k3_xboole_0(esk2_0,esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.73/0.91  cnf(c_0_15, plain, (v1_finset_1(k3_xboole_0(X2,X1))|~v1_finset_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.73/0.91  cnf(c_0_16, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_10, c_0_11])).
% 0.73/0.91  cnf(c_0_17, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.73/0.91  cnf(c_0_18, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.73/0.91  cnf(c_0_19, negated_conjecture, (~v1_finset_1(k3_xboole_0(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.73/0.91  cnf(c_0_20, plain, (v1_finset_1(k1_setfam_1(k2_enumset1(X2,X2,X2,X1)))|~v1_finset_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15, c_0_16]), c_0_17])).
% 0.73/0.91  cnf(c_0_21, plain, (X3=k1_setfam_1(k2_enumset1(X1,X1,X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_16]), c_0_17])).
% 0.73/0.91  cnf(c_0_22, negated_conjecture, (~v1_finset_1(k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_16]), c_0_17])).
% 0.73/0.91  cnf(c_0_23, plain, (v1_finset_1(X1)|r2_hidden(esk1_3(X2,X3,X1),X2)|r2_hidden(esk1_3(X2,X3,X1),X1)|~v1_finset_1(X3)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.73/0.91  cnf(c_0_24, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.73/0.91  cnf(c_0_25, negated_conjecture, (r2_hidden(esk1_3(X1,X2,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0))),k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0)))|r2_hidden(esk1_3(X1,X2,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0))),X1)|~v1_finset_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))), inference(spm,[status(thm)],[c_0_22, c_0_21])).
% 0.73/0.91  cnf(c_0_26, plain, (X3=k3_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.73/0.91  cnf(c_0_27, plain, (v1_finset_1(X1)|r2_hidden(esk1_3(X1,X2,X1),X1)|~v1_finset_1(X2)), inference(ef,[status(thm)],[c_0_23])).
% 0.73/0.91  cnf(c_0_28, negated_conjecture, (v1_finset_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.73/0.91  cnf(c_0_29, plain, (r2_hidden(X1,X2)|X3!=k1_setfam_1(k2_enumset1(X2,X2,X2,X4))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_16]), c_0_17])).
% 0.73/0.91  cnf(c_0_30, negated_conjecture, (r2_hidden(esk1_3(k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0)),X1,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0))),k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0)))|~v1_finset_1(k1_setfam_1(k2_enumset1(k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0)),k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0)),k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0)),X1)))), inference(ef,[status(thm)],[c_0_25])).
% 0.73/0.91  cnf(c_0_31, plain, (X3=k1_setfam_1(k2_enumset1(X1,X1,X1,X2))|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X2)|~r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_16]), c_0_17])).
% 0.73/0.91  cnf(c_0_32, negated_conjecture, (v1_finset_1(X1)|r2_hidden(esk1_3(X1,esk2_0,X1),X1)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.73/0.91  cnf(c_0_33, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))), inference(er,[status(thm)],[c_0_29])).
% 0.73/0.91  cnf(c_0_34, negated_conjecture, (r2_hidden(esk1_3(k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0)),X1,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0))),k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0)))|~v1_finset_1(X1)), inference(spm,[status(thm)],[c_0_30, c_0_20])).
% 0.73/0.91  cnf(c_0_35, negated_conjecture, (k1_setfam_1(k2_enumset1(X1,X1,X1,esk2_0))=X1|v1_finset_1(X1)|~r2_hidden(esk1_3(X1,esk2_0,X1),esk2_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_32])).
% 0.73/0.91  cnf(c_0_36, negated_conjecture, (r2_hidden(esk1_3(k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0)),X1,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0))),esk2_0)|~v1_finset_1(X1)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.73/0.91  cnf(c_0_37, negated_conjecture, (k1_setfam_1(k2_enumset1(k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0)),k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0)),k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0)),esk2_0))=k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_28])]), c_0_22])).
% 0.73/0.91  cnf(c_0_38, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_37]), c_0_28])]), c_0_22]), ['proof']).
% 0.73/0.91  # SZS output end CNFRefutation
% 0.73/0.91  # Proof object total steps             : 39
% 0.73/0.91  # Proof object clause steps            : 26
% 0.73/0.91  # Proof object formula steps           : 13
% 0.73/0.91  # Proof object conjectures             : 14
% 0.73/0.91  # Proof object clause conjectures      : 11
% 0.73/0.91  # Proof object formula conjectures     : 3
% 0.73/0.91  # Proof object initial clauses used    : 9
% 0.73/0.91  # Proof object initial formulas used   : 6
% 0.73/0.91  # Proof object generating inferences   : 10
% 0.73/0.91  # Proof object simplifying inferences  : 19
% 0.73/0.91  # Training examples: 0 positive, 0 negative
% 0.73/0.91  # Parsed axioms                        : 6
% 0.73/0.91  # Removed by relevancy pruning/SinE    : 0
% 0.73/0.91  # Initial clauses                      : 12
% 0.73/0.91  # Removed in clause preprocessing      : 3
% 0.73/0.91  # Initial clauses in saturation        : 9
% 0.73/0.91  # Processed clauses                    : 629
% 0.73/0.91  # ...of these trivial                  : 5
% 0.73/0.91  # ...subsumed                          : 392
% 0.73/0.91  # ...remaining for further processing  : 232
% 0.73/0.91  # Other redundant clauses eliminated   : 3
% 0.73/0.91  # Clauses deleted for lack of memory   : 0
% 0.73/0.91  # Backward-subsumed                    : 33
% 0.73/0.91  # Backward-rewritten                   : 5
% 0.73/0.91  # Generated clauses                    : 21642
% 0.73/0.91  # ...of the previous two non-trivial   : 20375
% 0.73/0.91  # Contextual simplify-reflections      : 11
% 0.73/0.91  # Paramodulations                      : 21358
% 0.73/0.91  # Factorizations                       : 281
% 0.73/0.91  # Equation resolutions                 : 3
% 0.73/0.91  # Propositional unsat checks           : 0
% 0.73/0.91  #    Propositional check models        : 0
% 0.73/0.91  #    Propositional check unsatisfiable : 0
% 0.73/0.91  #    Propositional clauses             : 0
% 0.73/0.91  #    Propositional clauses after purity: 0
% 0.73/0.91  #    Propositional unsat core size     : 0
% 0.73/0.91  #    Propositional preprocessing time  : 0.000
% 0.73/0.91  #    Propositional encoding time       : 0.000
% 0.73/0.91  #    Propositional solver time         : 0.000
% 0.73/0.91  #    Success case prop preproc time    : 0.000
% 0.73/0.91  #    Success case prop encoding time   : 0.000
% 0.73/0.91  #    Success case prop solver time     : 0.000
% 0.73/0.91  # Current number of processed clauses  : 182
% 0.73/0.91  #    Positive orientable unit clauses  : 9
% 0.73/0.91  #    Positive unorientable unit clauses: 0
% 0.73/0.91  #    Negative unit clauses             : 4
% 0.73/0.91  #    Non-unit-clauses                  : 169
% 0.73/0.91  # Current number of unprocessed clauses: 19656
% 0.73/0.91  # ...number of literals in the above   : 124285
% 0.73/0.91  # Current number of archived formulas  : 0
% 0.73/0.91  # Current number of archived clauses   : 50
% 0.73/0.91  # Clause-clause subsumption calls (NU) : 8929
% 0.73/0.91  # Rec. Clause-clause subsumption calls : 2644
% 0.73/0.91  # Non-unit clause-clause subsumptions  : 264
% 0.73/0.91  # Unit Clause-clause subsumption calls : 159
% 0.73/0.91  # Rewrite failures with RHS unbound    : 0
% 0.73/0.91  # BW rewrite match attempts            : 49
% 0.73/0.91  # BW rewrite match successes           : 3
% 0.73/0.91  # Condensation attempts                : 0
% 0.73/0.91  # Condensation successes               : 0
% 0.73/0.91  # Termbank termtop insertions          : 565111
% 0.73/0.92  
% 0.73/0.92  # -------------------------------------------------
% 0.73/0.92  # User time                : 0.558 s
% 0.73/0.92  # System time              : 0.018 s
% 0.73/0.92  # Total time               : 0.576 s
% 0.73/0.92  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------

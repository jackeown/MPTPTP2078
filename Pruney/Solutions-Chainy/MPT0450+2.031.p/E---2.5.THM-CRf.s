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
% DateTime   : Thu Dec  3 10:48:34 EST 2020

% Result     : Theorem 1.30s
% Output     : CNFRefutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 284 expanded)
%              Number of clauses        :   34 ( 124 expanded)
%              Number of leaves         :    9 (  76 expanded)
%              Depth                    :   12
%              Number of atoms          :  128 ( 536 expanded)
%              Number of equality atoms :   28 ( 219 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t34_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k3_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k3_relat_1(X1),k3_relat_1(X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_relat_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t19_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t31_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k3_relat_1(X1),k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

fof(fc1_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => r1_tarski(k3_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k3_relat_1(X1),k3_relat_1(X2))) ) ) ),
    inference(assume_negation,[status(cth)],[t34_relat_1])).

fof(c_0_10,plain,(
    ! [X24,X25] : k1_setfam_1(k2_tarski(X24,X25)) = k3_xboole_0(X24,X25) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_11,plain,(
    ! [X19,X20] : k1_enumset1(X19,X19,X20) = k2_tarski(X19,X20) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_12,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v1_relat_1(esk3_0)
    & ~ r1_tarski(k3_relat_1(k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k3_relat_1(esk2_0),k3_relat_1(esk3_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

cnf(c_0_13,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,plain,(
    ! [X21,X22,X23] : k2_enumset1(X21,X21,X22,X23) = k1_enumset1(X21,X22,X23) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_16,plain,(
    ! [X16,X17,X18] :
      ( ~ r1_tarski(X16,X17)
      | ~ r1_tarski(X16,X18)
      | r1_tarski(X16,k3_xboole_0(X17,X18)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).

cnf(c_0_17,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k3_relat_1(esk2_0),k3_relat_1(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_21,plain,(
    ! [X14,X15] : r1_tarski(k3_xboole_0(X14,X15),X14) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_22,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0))),k1_setfam_1(k2_enumset1(k3_relat_1(esk2_0),k3_relat_1(esk2_0),k3_relat_1(esk2_0),k3_relat_1(esk3_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_18]),c_0_18]),c_0_19]),c_0_19])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_18]),c_0_19])).

fof(c_0_24,plain,(
    ! [X28,X29] :
      ( ~ v1_relat_1(X28)
      | ~ v1_relat_1(X29)
      | ~ r1_tarski(X28,X29)
      | r1_tarski(k3_relat_1(X28),k3_relat_1(X29)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_relat_1])])])).

cnf(c_0_25,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0))),k3_relat_1(esk3_0))
    | ~ r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0))),k3_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_27,plain,
    ( r1_tarski(k3_relat_1(X1),k3_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_29,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_18]),c_0_19])).

fof(c_0_30,plain,(
    ! [X26,X27] :
      ( ~ v1_relat_1(X26)
      | v1_relat_1(k3_xboole_0(X26,X27)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_relat_1])])).

fof(c_0_31,plain,(
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

cnf(c_0_32,negated_conjecture,
    ( ~ v1_relat_1(k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0)))
    | ~ r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0))),k3_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29])])).

cnf(c_0_33,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_34,plain,
    ( v1_relat_1(k3_xboole_0(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_35,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( ~ v1_relat_1(k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0)))
    | ~ r1_tarski(k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_27]),c_0_33])])).

cnf(c_0_37,plain,
    ( v1_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_18]),c_0_19])).

cnf(c_0_38,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_40,plain,
    ( X3 = k3_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,plain,
    ( X3 = k1_setfam_1(k2_enumset1(X1,X1,X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_18]),c_0_19])).

cnf(c_0_42,negated_conjecture,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_28])])).

cnf(c_0_43,plain,
    ( X3 = k1_setfam_1(k2_enumset1(X1,X1,X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_18]),c_0_19])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,X2)
    | X3 != k1_setfam_1(k2_enumset1(X4,X4,X4,X2))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_18]),c_0_19])).

cnf(c_0_45,plain,
    ( X3 = k1_setfam_1(k2_enumset1(X1,X1,X1,X2))
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_18]),c_0_19])).

cnf(c_0_46,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) = X2
    | r2_hidden(esk1_3(X1,X2,X2),X2) ),
    inference(ef,[status(thm)],[c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk1_3(X1,X2,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0))),k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0)))
    | r2_hidden(esk1_3(X1,X2,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0))),X1)
    | ~ r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),esk3_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_setfam_1(k2_enumset1(X3,X3,X3,X2))) ),
    inference(er,[status(thm)],[c_0_44])).

cnf(c_0_49,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) = X2
    | ~ r2_hidden(esk1_3(X1,X2,X2),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_46])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk1_3(esk3_0,X1,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0))),esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_29]),c_0_48])).

cnf(c_0_51,negated_conjecture,
    ( k1_setfam_1(k2_enumset1(esk3_0,esk3_0,esk3_0,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0)))) = k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_52,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_51]),c_0_42]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:42:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 1.30/1.49  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 1.30/1.49  # and selection function SelectComplexExceptUniqMaxHorn.
% 1.30/1.49  #
% 1.30/1.49  # Preprocessing time       : 0.028 s
% 1.30/1.49  # Presaturation interreduction done
% 1.30/1.49  
% 1.30/1.49  # Proof found!
% 1.30/1.49  # SZS status Theorem
% 1.30/1.49  # SZS output start CNFRefutation
% 1.30/1.49  fof(t34_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k3_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k3_relat_1(X1),k3_relat_1(X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_relat_1)).
% 1.30/1.49  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 1.30/1.49  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 1.30/1.49  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 1.30/1.49  fof(t19_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(X1,k3_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 1.30/1.49  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.30/1.49  fof(t31_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>r1_tarski(k3_relat_1(X1),k3_relat_1(X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_relat_1)).
% 1.30/1.49  fof(fc1_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k3_xboole_0(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_relat_1)).
% 1.30/1.49  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 1.30/1.49  fof(c_0_9, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k3_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k3_relat_1(X1),k3_relat_1(X2)))))), inference(assume_negation,[status(cth)],[t34_relat_1])).
% 1.30/1.49  fof(c_0_10, plain, ![X24, X25]:k1_setfam_1(k2_tarski(X24,X25))=k3_xboole_0(X24,X25), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 1.30/1.49  fof(c_0_11, plain, ![X19, X20]:k1_enumset1(X19,X19,X20)=k2_tarski(X19,X20), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 1.30/1.49  fof(c_0_12, negated_conjecture, (v1_relat_1(esk2_0)&(v1_relat_1(esk3_0)&~r1_tarski(k3_relat_1(k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k3_relat_1(esk2_0),k3_relat_1(esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 1.30/1.49  cnf(c_0_13, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 1.30/1.49  cnf(c_0_14, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 1.30/1.49  fof(c_0_15, plain, ![X21, X22, X23]:k2_enumset1(X21,X21,X22,X23)=k1_enumset1(X21,X22,X23), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 1.30/1.49  fof(c_0_16, plain, ![X16, X17, X18]:(~r1_tarski(X16,X17)|~r1_tarski(X16,X18)|r1_tarski(X16,k3_xboole_0(X17,X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).
% 1.30/1.49  cnf(c_0_17, negated_conjecture, (~r1_tarski(k3_relat_1(k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k3_relat_1(esk2_0),k3_relat_1(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.30/1.49  cnf(c_0_18, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_13, c_0_14])).
% 1.30/1.49  cnf(c_0_19, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.30/1.49  cnf(c_0_20, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.30/1.49  fof(c_0_21, plain, ![X14, X15]:r1_tarski(k3_xboole_0(X14,X15),X14), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 1.30/1.49  cnf(c_0_22, negated_conjecture, (~r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0))),k1_setfam_1(k2_enumset1(k3_relat_1(esk2_0),k3_relat_1(esk2_0),k3_relat_1(esk2_0),k3_relat_1(esk3_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17, c_0_18]), c_0_18]), c_0_19]), c_0_19])).
% 1.30/1.49  cnf(c_0_23, plain, (r1_tarski(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))|~r1_tarski(X1,X3)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_18]), c_0_19])).
% 1.30/1.49  fof(c_0_24, plain, ![X28, X29]:(~v1_relat_1(X28)|(~v1_relat_1(X29)|(~r1_tarski(X28,X29)|r1_tarski(k3_relat_1(X28),k3_relat_1(X29))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_relat_1])])])).
% 1.30/1.49  cnf(c_0_25, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.30/1.49  cnf(c_0_26, negated_conjecture, (~r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0))),k3_relat_1(esk3_0))|~r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0))),k3_relat_1(esk2_0))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 1.30/1.49  cnf(c_0_27, plain, (r1_tarski(k3_relat_1(X1),k3_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.30/1.49  cnf(c_0_28, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.30/1.49  cnf(c_0_29, plain, (r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_18]), c_0_19])).
% 1.30/1.49  fof(c_0_30, plain, ![X26, X27]:(~v1_relat_1(X26)|v1_relat_1(k3_xboole_0(X26,X27))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_relat_1])])).
% 1.30/1.49  fof(c_0_31, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6))&(r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|~r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k3_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|~r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k3_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))&(r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 1.30/1.49  cnf(c_0_32, negated_conjecture, (~v1_relat_1(k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0)))|~r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0))),k3_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29])])).
% 1.30/1.49  cnf(c_0_33, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.30/1.49  cnf(c_0_34, plain, (v1_relat_1(k3_xboole_0(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 1.30/1.49  cnf(c_0_35, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 1.30/1.49  cnf(c_0_36, negated_conjecture, (~v1_relat_1(k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0)))|~r1_tarski(k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0)),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_27]), c_0_33])])).
% 1.30/1.49  cnf(c_0_37, plain, (v1_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_18]), c_0_19])).
% 1.30/1.49  cnf(c_0_38, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 1.30/1.49  cnf(c_0_39, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 1.30/1.49  cnf(c_0_40, plain, (X3=k3_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 1.30/1.49  cnf(c_0_41, plain, (X3=k1_setfam_1(k2_enumset1(X1,X1,X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_18]), c_0_19])).
% 1.30/1.49  cnf(c_0_42, negated_conjecture, (~r1_tarski(k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0)),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_28])])).
% 1.30/1.49  cnf(c_0_43, plain, (X3=k1_setfam_1(k2_enumset1(X1,X1,X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_18]), c_0_19])).
% 1.30/1.49  cnf(c_0_44, plain, (r2_hidden(X1,X2)|X3!=k1_setfam_1(k2_enumset1(X4,X4,X4,X2))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_18]), c_0_19])).
% 1.30/1.49  cnf(c_0_45, plain, (X3=k1_setfam_1(k2_enumset1(X1,X1,X1,X2))|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X2)|~r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_18]), c_0_19])).
% 1.30/1.49  cnf(c_0_46, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,X2))=X2|r2_hidden(esk1_3(X1,X2,X2),X2)), inference(ef,[status(thm)],[c_0_41])).
% 1.30/1.49  cnf(c_0_47, negated_conjecture, (r2_hidden(esk1_3(X1,X2,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0))),k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0)))|r2_hidden(esk1_3(X1,X2,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0))),X1)|~r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),esk3_0)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 1.30/1.49  cnf(c_0_48, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_setfam_1(k2_enumset1(X3,X3,X3,X2)))), inference(er,[status(thm)],[c_0_44])).
% 1.30/1.49  cnf(c_0_49, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,X2))=X2|~r2_hidden(esk1_3(X1,X2,X2),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_46])).
% 1.30/1.49  cnf(c_0_50, negated_conjecture, (r2_hidden(esk1_3(esk3_0,X1,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0))),esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_29]), c_0_48])).
% 1.30/1.49  cnf(c_0_51, negated_conjecture, (k1_setfam_1(k2_enumset1(esk3_0,esk3_0,esk3_0,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0))))=k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 1.30/1.49  cnf(c_0_52, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_51]), c_0_42]), ['proof']).
% 1.30/1.49  # SZS output end CNFRefutation
% 1.30/1.49  # Proof object total steps             : 53
% 1.30/1.49  # Proof object clause steps            : 34
% 1.30/1.49  # Proof object formula steps           : 19
% 1.30/1.49  # Proof object conjectures             : 15
% 1.30/1.49  # Proof object clause conjectures      : 12
% 1.30/1.49  # Proof object formula conjectures     : 3
% 1.30/1.49  # Proof object initial clauses used    : 14
% 1.30/1.49  # Proof object initial formulas used   : 9
% 1.30/1.49  # Proof object generating inferences   : 10
% 1.30/1.49  # Proof object simplifying inferences  : 30
% 1.30/1.49  # Training examples: 0 positive, 0 negative
% 1.30/1.49  # Parsed axioms                        : 9
% 1.30/1.49  # Removed by relevancy pruning/SinE    : 0
% 1.30/1.49  # Initial clauses                      : 16
% 1.30/1.49  # Removed in clause preprocessing      : 3
% 1.30/1.49  # Initial clauses in saturation        : 13
% 1.30/1.49  # Processed clauses                    : 1629
% 1.30/1.49  # ...of these trivial                  : 5
% 1.30/1.49  # ...subsumed                          : 945
% 1.30/1.49  # ...remaining for further processing  : 679
% 1.30/1.49  # Other redundant clauses eliminated   : 3
% 1.30/1.49  # Clauses deleted for lack of memory   : 0
% 1.30/1.49  # Backward-subsumed                    : 204
% 1.30/1.49  # Backward-rewritten                   : 68
% 1.30/1.49  # Generated clauses                    : 36922
% 1.30/1.49  # ...of the previous two non-trivial   : 34519
% 1.30/1.49  # Contextual simplify-reflections      : 86
% 1.30/1.49  # Paramodulations                      : 36725
% 1.30/1.49  # Factorizations                       : 194
% 1.30/1.49  # Equation resolutions                 : 3
% 1.30/1.49  # Propositional unsat checks           : 0
% 1.30/1.49  #    Propositional check models        : 0
% 1.30/1.49  #    Propositional check unsatisfiable : 0
% 1.30/1.49  #    Propositional clauses             : 0
% 1.30/1.49  #    Propositional clauses after purity: 0
% 1.30/1.49  #    Propositional unsat core size     : 0
% 1.30/1.49  #    Propositional preprocessing time  : 0.000
% 1.30/1.49  #    Propositional encoding time       : 0.000
% 1.30/1.49  #    Propositional solver time         : 0.000
% 1.30/1.49  #    Success case prop preproc time    : 0.000
% 1.30/1.49  #    Success case prop encoding time   : 0.000
% 1.30/1.49  #    Success case prop solver time     : 0.000
% 1.30/1.49  # Current number of processed clauses  : 391
% 1.30/1.49  #    Positive orientable unit clauses  : 17
% 1.30/1.49  #    Positive unorientable unit clauses: 0
% 1.30/1.49  #    Negative unit clauses             : 7
% 1.30/1.49  #    Non-unit-clauses                  : 367
% 1.30/1.49  # Current number of unprocessed clauses: 32732
% 1.30/1.49  # ...number of literals in the above   : 209445
% 1.30/1.49  # Current number of archived formulas  : 0
% 1.30/1.49  # Current number of archived clauses   : 288
% 1.30/1.49  # Clause-clause subsumption calls (NU) : 106865
% 1.30/1.49  # Rec. Clause-clause subsumption calls : 23819
% 1.30/1.49  # Non-unit clause-clause subsumptions  : 891
% 1.30/1.49  # Unit Clause-clause subsumption calls : 2350
% 1.30/1.49  # Rewrite failures with RHS unbound    : 0
% 1.30/1.49  # BW rewrite match attempts            : 73
% 1.30/1.49  # BW rewrite match successes           : 12
% 1.30/1.49  # Condensation attempts                : 0
% 1.30/1.49  # Condensation successes               : 0
% 1.30/1.49  # Termbank termtop insertions          : 1158587
% 1.30/1.49  
% 1.30/1.49  # -------------------------------------------------
% 1.30/1.49  # User time                : 1.124 s
% 1.30/1.49  # System time              : 0.033 s
% 1.30/1.49  # Total time               : 1.157 s
% 1.30/1.49  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------

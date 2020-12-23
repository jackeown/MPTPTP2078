%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:48:18 EST 2020

% Result     : Theorem 0.76s
% Output     : CNFRefutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 149 expanded)
%              Number of clauses        :   31 (  71 expanded)
%              Number of leaves         :    8 (  37 expanded)
%              Depth                    :    9
%              Number of atoms          :  123 ( 354 expanded)
%              Number of equality atoms :   24 ( 128 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t27_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k2_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k2_relat_1(X1),k2_relat_1(X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_relat_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t19_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t25_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
              & r1_tarski(k2_relat_1(X1),k2_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(fc1_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => r1_tarski(k2_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k2_relat_1(X1),k2_relat_1(X2))) ) ) ),
    inference(assume_negation,[status(cth)],[t27_relat_1])).

fof(c_0_9,plain,(
    ! [X21,X22] : k1_setfam_1(k2_tarski(X21,X22)) = k3_xboole_0(X21,X22) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_10,plain,(
    ! [X19,X20] : k1_enumset1(X19,X19,X20) = k2_tarski(X19,X20) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_11,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v1_relat_1(esk3_0)
    & ~ r1_tarski(k2_relat_1(k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k2_relat_1(esk2_0),k2_relat_1(esk3_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

cnf(c_0_12,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,plain,(
    ! [X16,X17,X18] :
      ( ~ r1_tarski(X16,X17)
      | ~ r1_tarski(X16,X18)
      | r1_tarski(X16,k3_xboole_0(X17,X18)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).

fof(c_0_15,plain,(
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

cnf(c_0_16,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k2_relat_1(esk2_0),k2_relat_1(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,plain,(
    ! [X14,X15] : r1_tarski(k3_xboole_0(X14,X15),X14) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_20,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(k1_setfam_1(k1_enumset1(esk2_0,esk2_0,esk3_0))),k1_setfam_1(k1_enumset1(k2_relat_1(esk2_0),k2_relat_1(esk2_0),k2_relat_1(esk3_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_17]),c_0_17])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,k1_setfam_1(k1_enumset1(X2,X2,X3)))
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_18,c_0_17])).

fof(c_0_24,plain,(
    ! [X25,X26] :
      ( ( r1_tarski(k1_relat_1(X25),k1_relat_1(X26))
        | ~ r1_tarski(X25,X26)
        | ~ v1_relat_1(X26)
        | ~ v1_relat_1(X25) )
      & ( r1_tarski(k2_relat_1(X25),k2_relat_1(X26))
        | ~ r1_tarski(X25,X26)
        | ~ v1_relat_1(X26)
        | ~ v1_relat_1(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).

cnf(c_0_25,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( X3 = k3_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_27,plain,
    ( X3 = k1_setfam_1(k1_enumset1(X1,X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(rw,[status(thm)],[c_0_20,c_0_17])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,X2)
    | X3 != k1_setfam_1(k1_enumset1(X4,X4,X2))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_21,c_0_17])).

cnf(c_0_29,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(k1_setfam_1(k1_enumset1(esk2_0,esk2_0,esk3_0))),k2_relat_1(esk3_0))
    | ~ r1_tarski(k2_relat_1(k1_setfam_1(k1_enumset1(esk2_0,esk2_0,esk3_0))),k2_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_30,plain,
    ( r1_tarski(k2_relat_1(X1),k2_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_32,plain,
    ( r1_tarski(k1_setfam_1(k1_enumset1(X1,X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_25,c_0_17])).

fof(c_0_33,plain,(
    ! [X23,X24] :
      ( ~ v1_relat_1(X23)
      | v1_relat_1(k3_xboole_0(X23,X24)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_relat_1])])).

cnf(c_0_34,plain,
    ( X3 = k1_setfam_1(k1_enumset1(X1,X1,X2))
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_26,c_0_17])).

cnf(c_0_35,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = X2
    | r2_hidden(esk1_3(X1,X2,X2),X2) ),
    inference(ef,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_setfam_1(k1_enumset1(X3,X3,X2))) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_37,negated_conjecture,
    ( ~ v1_relat_1(k1_setfam_1(k1_enumset1(esk2_0,esk2_0,esk3_0)))
    | ~ r1_tarski(k2_relat_1(k1_setfam_1(k1_enumset1(esk2_0,esk2_0,esk3_0))),k2_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_32])])).

cnf(c_0_38,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_39,plain,
    ( v1_relat_1(k3_xboole_0(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_40,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = X2
    | ~ r2_hidden(esk1_3(X1,X2,X2),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_35])).

cnf(c_0_41,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,k1_setfam_1(k1_enumset1(X2,X2,X3)))) = k1_setfam_1(k1_enumset1(X2,X2,X3))
    | r2_hidden(esk1_3(X1,k1_setfam_1(k1_enumset1(X2,X2,X3)),k1_setfam_1(k1_enumset1(X2,X2,X3))),X3) ),
    inference(spm,[status(thm)],[c_0_36,c_0_35])).

cnf(c_0_42,negated_conjecture,
    ( ~ v1_relat_1(k1_setfam_1(k1_enumset1(esk2_0,esk2_0,esk3_0)))
    | ~ r1_tarski(k1_setfam_1(k1_enumset1(esk2_0,esk2_0,esk3_0)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_30]),c_0_38])])).

cnf(c_0_43,plain,
    ( v1_relat_1(k1_setfam_1(k1_enumset1(X1,X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_39,c_0_17])).

cnf(c_0_44,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,k1_setfam_1(k1_enumset1(X2,X2,X1)))) = k1_setfam_1(k1_enumset1(X2,X2,X1)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_45,negated_conjecture,
    ( ~ r1_tarski(k1_setfam_1(k1_enumset1(esk2_0,esk2_0,esk3_0)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_31])])).

cnf(c_0_46,plain,
    ( r1_tarski(k1_setfam_1(k1_enumset1(X1,X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_44])).

cnf(c_0_47,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_46])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:18:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.76/0.94  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.76/0.94  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.76/0.94  #
% 0.76/0.94  # Preprocessing time       : 0.027 s
% 0.76/0.94  # Presaturation interreduction done
% 0.76/0.94  
% 0.76/0.94  # Proof found!
% 0.76/0.94  # SZS status Theorem
% 0.76/0.94  # SZS output start CNFRefutation
% 0.76/0.94  fof(t27_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k2_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k2_relat_1(X1),k2_relat_1(X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_relat_1)).
% 0.76/0.94  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.76/0.94  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.76/0.94  fof(t19_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(X1,k3_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 0.76/0.94  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.76/0.94  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.76/0.94  fof(t25_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>(r1_tarski(k1_relat_1(X1),k1_relat_1(X2))&r1_tarski(k2_relat_1(X1),k2_relat_1(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 0.76/0.94  fof(fc1_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k3_xboole_0(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_relat_1)).
% 0.76/0.94  fof(c_0_8, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k2_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k2_relat_1(X1),k2_relat_1(X2)))))), inference(assume_negation,[status(cth)],[t27_relat_1])).
% 0.76/0.94  fof(c_0_9, plain, ![X21, X22]:k1_setfam_1(k2_tarski(X21,X22))=k3_xboole_0(X21,X22), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.76/0.94  fof(c_0_10, plain, ![X19, X20]:k1_enumset1(X19,X19,X20)=k2_tarski(X19,X20), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.76/0.94  fof(c_0_11, negated_conjecture, (v1_relat_1(esk2_0)&(v1_relat_1(esk3_0)&~r1_tarski(k2_relat_1(k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k2_relat_1(esk2_0),k2_relat_1(esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.76/0.94  cnf(c_0_12, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.76/0.94  cnf(c_0_13, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.76/0.94  fof(c_0_14, plain, ![X16, X17, X18]:(~r1_tarski(X16,X17)|~r1_tarski(X16,X18)|r1_tarski(X16,k3_xboole_0(X17,X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).
% 0.76/0.94  fof(c_0_15, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6))&(r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|~r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k3_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|~r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k3_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))&(r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.76/0.94  cnf(c_0_16, negated_conjecture, (~r1_tarski(k2_relat_1(k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k2_relat_1(esk2_0),k2_relat_1(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.76/0.94  cnf(c_0_17, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_12, c_0_13])).
% 0.76/0.94  cnf(c_0_18, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.76/0.94  fof(c_0_19, plain, ![X14, X15]:r1_tarski(k3_xboole_0(X14,X15),X14), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.76/0.94  cnf(c_0_20, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.76/0.94  cnf(c_0_21, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.76/0.94  cnf(c_0_22, negated_conjecture, (~r1_tarski(k2_relat_1(k1_setfam_1(k1_enumset1(esk2_0,esk2_0,esk3_0))),k1_setfam_1(k1_enumset1(k2_relat_1(esk2_0),k2_relat_1(esk2_0),k2_relat_1(esk3_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16, c_0_17]), c_0_17])).
% 0.76/0.94  cnf(c_0_23, plain, (r1_tarski(X1,k1_setfam_1(k1_enumset1(X2,X2,X3)))|~r1_tarski(X1,X3)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_18, c_0_17])).
% 0.76/0.94  fof(c_0_24, plain, ![X25, X26]:((r1_tarski(k1_relat_1(X25),k1_relat_1(X26))|~r1_tarski(X25,X26)|~v1_relat_1(X26)|~v1_relat_1(X25))&(r1_tarski(k2_relat_1(X25),k2_relat_1(X26))|~r1_tarski(X25,X26)|~v1_relat_1(X26)|~v1_relat_1(X25))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).
% 0.76/0.94  cnf(c_0_25, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.76/0.94  cnf(c_0_26, plain, (X3=k3_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.76/0.94  cnf(c_0_27, plain, (X3=k1_setfam_1(k1_enumset1(X1,X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X2)), inference(rw,[status(thm)],[c_0_20, c_0_17])).
% 0.76/0.94  cnf(c_0_28, plain, (r2_hidden(X1,X2)|X3!=k1_setfam_1(k1_enumset1(X4,X4,X2))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_21, c_0_17])).
% 0.76/0.94  cnf(c_0_29, negated_conjecture, (~r1_tarski(k2_relat_1(k1_setfam_1(k1_enumset1(esk2_0,esk2_0,esk3_0))),k2_relat_1(esk3_0))|~r1_tarski(k2_relat_1(k1_setfam_1(k1_enumset1(esk2_0,esk2_0,esk3_0))),k2_relat_1(esk2_0))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.76/0.94  cnf(c_0_30, plain, (r1_tarski(k2_relat_1(X1),k2_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.76/0.94  cnf(c_0_31, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.76/0.94  cnf(c_0_32, plain, (r1_tarski(k1_setfam_1(k1_enumset1(X1,X1,X2)),X1)), inference(rw,[status(thm)],[c_0_25, c_0_17])).
% 0.76/0.94  fof(c_0_33, plain, ![X23, X24]:(~v1_relat_1(X23)|v1_relat_1(k3_xboole_0(X23,X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_relat_1])])).
% 0.76/0.94  cnf(c_0_34, plain, (X3=k1_setfam_1(k1_enumset1(X1,X1,X2))|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X2)|~r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_26, c_0_17])).
% 0.76/0.94  cnf(c_0_35, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=X2|r2_hidden(esk1_3(X1,X2,X2),X2)), inference(ef,[status(thm)],[c_0_27])).
% 0.76/0.94  cnf(c_0_36, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_setfam_1(k1_enumset1(X3,X3,X2)))), inference(er,[status(thm)],[c_0_28])).
% 0.76/0.94  cnf(c_0_37, negated_conjecture, (~v1_relat_1(k1_setfam_1(k1_enumset1(esk2_0,esk2_0,esk3_0)))|~r1_tarski(k2_relat_1(k1_setfam_1(k1_enumset1(esk2_0,esk2_0,esk3_0))),k2_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31]), c_0_32])])).
% 0.76/0.94  cnf(c_0_38, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.76/0.94  cnf(c_0_39, plain, (v1_relat_1(k3_xboole_0(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.76/0.94  cnf(c_0_40, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=X2|~r2_hidden(esk1_3(X1,X2,X2),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_35])).
% 0.76/0.94  cnf(c_0_41, plain, (k1_setfam_1(k1_enumset1(X1,X1,k1_setfam_1(k1_enumset1(X2,X2,X3))))=k1_setfam_1(k1_enumset1(X2,X2,X3))|r2_hidden(esk1_3(X1,k1_setfam_1(k1_enumset1(X2,X2,X3)),k1_setfam_1(k1_enumset1(X2,X2,X3))),X3)), inference(spm,[status(thm)],[c_0_36, c_0_35])).
% 0.76/0.94  cnf(c_0_42, negated_conjecture, (~v1_relat_1(k1_setfam_1(k1_enumset1(esk2_0,esk2_0,esk3_0)))|~r1_tarski(k1_setfam_1(k1_enumset1(esk2_0,esk2_0,esk3_0)),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_30]), c_0_38])])).
% 0.76/0.94  cnf(c_0_43, plain, (v1_relat_1(k1_setfam_1(k1_enumset1(X1,X1,X2)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_39, c_0_17])).
% 0.76/0.94  cnf(c_0_44, plain, (k1_setfam_1(k1_enumset1(X1,X1,k1_setfam_1(k1_enumset1(X2,X2,X1))))=k1_setfam_1(k1_enumset1(X2,X2,X1))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.76/0.94  cnf(c_0_45, negated_conjecture, (~r1_tarski(k1_setfam_1(k1_enumset1(esk2_0,esk2_0,esk3_0)),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_31])])).
% 0.76/0.94  cnf(c_0_46, plain, (r1_tarski(k1_setfam_1(k1_enumset1(X1,X1,X2)),X2)), inference(spm,[status(thm)],[c_0_32, c_0_44])).
% 0.76/0.94  cnf(c_0_47, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_46])]), ['proof']).
% 0.76/0.94  # SZS output end CNFRefutation
% 0.76/0.94  # Proof object total steps             : 48
% 0.76/0.94  # Proof object clause steps            : 31
% 0.76/0.94  # Proof object formula steps           : 17
% 0.76/0.94  # Proof object conjectures             : 12
% 0.76/0.94  # Proof object clause conjectures      : 9
% 0.76/0.94  # Proof object formula conjectures     : 3
% 0.76/0.94  # Proof object initial clauses used    : 12
% 0.76/0.94  # Proof object initial formulas used   : 8
% 0.76/0.94  # Proof object generating inferences   : 9
% 0.76/0.94  # Proof object simplifying inferences  : 20
% 0.76/0.94  # Training examples: 0 positive, 0 negative
% 0.76/0.94  # Parsed axioms                        : 8
% 0.76/0.94  # Removed by relevancy pruning/SinE    : 0
% 0.76/0.94  # Initial clauses                      : 16
% 0.76/0.94  # Removed in clause preprocessing      : 2
% 0.76/0.94  # Initial clauses in saturation        : 14
% 0.76/0.94  # Processed clauses                    : 1272
% 0.76/0.94  # ...of these trivial                  : 41
% 0.76/0.94  # ...subsumed                          : 634
% 0.76/0.94  # ...remaining for further processing  : 597
% 0.76/0.94  # Other redundant clauses eliminated   : 3
% 0.76/0.94  # Clauses deleted for lack of memory   : 0
% 0.76/0.94  # Backward-subsumed                    : 108
% 0.76/0.94  # Backward-rewritten                   : 40
% 0.76/0.94  # Generated clauses                    : 26130
% 0.76/0.94  # ...of the previous two non-trivial   : 23574
% 0.76/0.94  # Contextual simplify-reflections      : 80
% 0.76/0.94  # Paramodulations                      : 25923
% 0.76/0.94  # Factorizations                       : 204
% 0.76/0.94  # Equation resolutions                 : 3
% 0.76/0.94  # Propositional unsat checks           : 0
% 0.76/0.94  #    Propositional check models        : 0
% 0.76/0.94  #    Propositional check unsatisfiable : 0
% 0.76/0.94  #    Propositional clauses             : 0
% 0.76/0.94  #    Propositional clauses after purity: 0
% 0.76/0.94  #    Propositional unsat core size     : 0
% 0.76/0.94  #    Propositional preprocessing time  : 0.000
% 0.76/0.94  #    Propositional encoding time       : 0.000
% 0.76/0.94  #    Propositional solver time         : 0.000
% 0.76/0.94  #    Success case prop preproc time    : 0.000
% 0.76/0.94  #    Success case prop encoding time   : 0.000
% 0.76/0.94  #    Success case prop solver time     : 0.000
% 0.76/0.94  # Current number of processed clauses  : 432
% 0.76/0.94  #    Positive orientable unit clauses  : 16
% 0.76/0.94  #    Positive unorientable unit clauses: 0
% 0.76/0.94  #    Negative unit clauses             : 5
% 0.76/0.94  #    Non-unit-clauses                  : 411
% 0.76/0.94  # Current number of unprocessed clauses: 22181
% 0.76/0.94  # ...number of literals in the above   : 135445
% 0.76/0.94  # Current number of archived formulas  : 0
% 0.76/0.94  # Current number of archived clauses   : 164
% 0.76/0.94  # Clause-clause subsumption calls (NU) : 96135
% 0.76/0.94  # Rec. Clause-clause subsumption calls : 21748
% 0.76/0.94  # Non-unit clause-clause subsumptions  : 726
% 0.76/0.94  # Unit Clause-clause subsumption calls : 2128
% 0.76/0.94  # Rewrite failures with RHS unbound    : 0
% 0.76/0.94  # BW rewrite match attempts            : 162
% 0.76/0.94  # BW rewrite match successes           : 13
% 0.76/0.94  # Condensation attempts                : 0
% 0.76/0.94  # Condensation successes               : 0
% 0.76/0.94  # Termbank termtop insertions          : 713501
% 0.76/0.95  
% 0.76/0.95  # -------------------------------------------------
% 0.76/0.95  # User time                : 0.579 s
% 0.76/0.95  # System time              : 0.015 s
% 0.76/0.95  # Total time               : 0.595 s
% 0.76/0.95  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------

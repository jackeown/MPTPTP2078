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
% DateTime   : Thu Dec  3 10:50:55 EST 2020

% Result     : Theorem 0.80s
% Output     : CNFRefutation 0.80s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 233 expanded)
%              Number of clauses        :   29 ( 101 expanded)
%              Number of leaves         :   12 (  65 expanded)
%              Depth                    :   12
%              Number of atoms          :  102 ( 323 expanded)
%              Number of equality atoms :   21 ( 178 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(fc1_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

fof(t25_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
              & r1_tarski(k2_relat_1(X1),k2_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(t108_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k7_relat_1(X3,k3_xboole_0(X1,X2)) = k3_xboole_0(k7_relat_1(X3,X1),k7_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_relat_1)).

fof(t19_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(t154_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => r1_tarski(k9_relat_1(X3,k3_xboole_0(X1,X2)),k3_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_relat_1)).

fof(c_0_12,plain,(
    ! [X18,X19] : k1_setfam_1(k2_tarski(X18,X19)) = k3_xboole_0(X18,X19) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_13,plain,(
    ! [X13,X14] : k1_enumset1(X13,X13,X14) = k2_tarski(X13,X14) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_14,plain,(
    ! [X6,X7] : r1_tarski(k3_xboole_0(X6,X7),X6) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_15,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_17,plain,(
    ! [X15,X16,X17] : k2_enumset1(X15,X15,X16,X17) = k1_enumset1(X15,X16,X17) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_18,plain,(
    ! [X22,X23] :
      ( ~ v1_relat_1(X22)
      | v1_relat_1(k3_xboole_0(X22,X23)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_relat_1])])).

fof(c_0_19,plain,(
    ! [X29,X30] :
      ( ( r1_tarski(k1_relat_1(X29),k1_relat_1(X30))
        | ~ r1_tarski(X29,X30)
        | ~ v1_relat_1(X30)
        | ~ v1_relat_1(X29) )
      & ( r1_tarski(k2_relat_1(X29),k2_relat_1(X30))
        | ~ r1_tarski(X29,X30)
        | ~ v1_relat_1(X30)
        | ~ v1_relat_1(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).

cnf(c_0_20,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_22,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( v1_relat_1(k3_xboole_0(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_24,plain,(
    ! [X11,X12] : k2_tarski(X11,X12) = k2_tarski(X12,X11) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_25,plain,
    ( r1_tarski(k2_relat_1(X1),k2_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21]),c_0_22])).

cnf(c_0_27,plain,
    ( v1_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_21]),c_0_22])).

cnf(c_0_28,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,plain,
    ( r1_tarski(k2_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2))),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])).

cnf(c_0_30,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k2_enumset1(X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_16]),c_0_16]),c_0_22]),c_0_22])).

fof(c_0_31,plain,(
    ! [X27,X28] :
      ( ~ v1_relat_1(X28)
      | k2_relat_1(k7_relat_1(X28,X27)) = k9_relat_1(X28,X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

fof(c_0_32,plain,(
    ! [X20,X21] :
      ( ~ v1_relat_1(X20)
      | v1_relat_1(k7_relat_1(X20,X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

fof(c_0_33,plain,(
    ! [X24,X25,X26] :
      ( ~ v1_relat_1(X26)
      | k7_relat_1(X26,k3_xboole_0(X24,X25)) = k3_xboole_0(k7_relat_1(X26,X24),k7_relat_1(X26,X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t108_relat_1])])).

cnf(c_0_34,plain,
    ( r1_tarski(k2_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2))),k2_relat_1(X2))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_36,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_37,plain,
    ( k7_relat_1(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(k7_relat_1(X1,X2),k7_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_38,plain,(
    ! [X8,X9,X10] :
      ( ~ r1_tarski(X8,X9)
      | ~ r1_tarski(X8,X10)
      | r1_tarski(X8,k3_xboole_0(X9,X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).

cnf(c_0_39,plain,
    ( r1_tarski(k2_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,k7_relat_1(X2,X3)))),k9_relat_1(X2,X3))
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])).

cnf(c_0_40,plain,
    ( k7_relat_1(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3))) = k1_setfam_1(k2_enumset1(k7_relat_1(X1,X2),k7_relat_1(X1,X2),k7_relat_1(X1,X2),k7_relat_1(X1,X3)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_21]),c_0_21]),c_0_22]),c_0_22])).

fof(c_0_41,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => r1_tarski(k9_relat_1(X3,k3_xboole_0(X1,X2)),k3_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2))) ) ),
    inference(assume_negation,[status(cth)],[t154_relat_1])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_43,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))),k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

fof(c_0_44,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & ~ r1_tarski(k9_relat_1(esk3_0,k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk2_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_41])])])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_21]),c_0_22])).

cnf(c_0_46,plain,
    ( r1_tarski(k9_relat_1(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3))),k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_35])).

cnf(c_0_47,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk3_0,k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_48,plain,
    ( r1_tarski(k9_relat_1(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3))),k1_setfam_1(k2_enumset1(X4,X4,X4,k9_relat_1(X1,X3))))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k9_relat_1(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3))),X4) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_49,plain,
    ( r1_tarski(k9_relat_1(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3))),k9_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_30])).

cnf(c_0_50,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk3_0,k1_setfam_1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0))),k1_setfam_1(k2_enumset1(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk2_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_21]),c_0_21]),c_0_22]),c_0_22])).

cnf(c_0_51,plain,
    ( r1_tarski(k9_relat_1(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3))),k1_setfam_1(k2_enumset1(k9_relat_1(X1,X2),k9_relat_1(X1,X2),k9_relat_1(X1,X2),k9_relat_1(X1,X3))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_52,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_53,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:24:39 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.80/0.99  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S081N
% 0.80/0.99  # and selection function SelectCQArNTNp.
% 0.80/0.99  #
% 0.80/0.99  # Preprocessing time       : 0.027 s
% 0.80/0.99  # Presaturation interreduction done
% 0.80/0.99  
% 0.80/0.99  # Proof found!
% 0.80/0.99  # SZS status Theorem
% 0.80/0.99  # SZS output start CNFRefutation
% 0.80/0.99  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.80/0.99  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.80/0.99  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.80/0.99  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.80/0.99  fof(fc1_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k3_xboole_0(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_relat_1)).
% 0.80/0.99  fof(t25_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>(r1_tarski(k1_relat_1(X1),k1_relat_1(X2))&r1_tarski(k2_relat_1(X1),k2_relat_1(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 0.80/0.99  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.80/0.99  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 0.80/0.99  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.80/0.99  fof(t108_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k7_relat_1(X3,k3_xboole_0(X1,X2))=k3_xboole_0(k7_relat_1(X3,X1),k7_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_relat_1)).
% 0.80/0.99  fof(t19_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(X1,k3_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 0.80/0.99  fof(t154_relat_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>r1_tarski(k9_relat_1(X3,k3_xboole_0(X1,X2)),k3_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t154_relat_1)).
% 0.80/0.99  fof(c_0_12, plain, ![X18, X19]:k1_setfam_1(k2_tarski(X18,X19))=k3_xboole_0(X18,X19), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.80/0.99  fof(c_0_13, plain, ![X13, X14]:k1_enumset1(X13,X13,X14)=k2_tarski(X13,X14), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.80/0.99  fof(c_0_14, plain, ![X6, X7]:r1_tarski(k3_xboole_0(X6,X7),X6), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.80/0.99  cnf(c_0_15, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.80/0.99  cnf(c_0_16, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.80/0.99  fof(c_0_17, plain, ![X15, X16, X17]:k2_enumset1(X15,X15,X16,X17)=k1_enumset1(X15,X16,X17), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.80/0.99  fof(c_0_18, plain, ![X22, X23]:(~v1_relat_1(X22)|v1_relat_1(k3_xboole_0(X22,X23))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_relat_1])])).
% 0.80/0.99  fof(c_0_19, plain, ![X29, X30]:((r1_tarski(k1_relat_1(X29),k1_relat_1(X30))|~r1_tarski(X29,X30)|~v1_relat_1(X30)|~v1_relat_1(X29))&(r1_tarski(k2_relat_1(X29),k2_relat_1(X30))|~r1_tarski(X29,X30)|~v1_relat_1(X30)|~v1_relat_1(X29))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).
% 0.80/0.99  cnf(c_0_20, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.80/0.99  cnf(c_0_21, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 0.80/0.99  cnf(c_0_22, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.80/0.99  cnf(c_0_23, plain, (v1_relat_1(k3_xboole_0(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.80/0.99  fof(c_0_24, plain, ![X11, X12]:k2_tarski(X11,X12)=k2_tarski(X12,X11), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.80/0.99  cnf(c_0_25, plain, (r1_tarski(k2_relat_1(X1),k2_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.80/0.99  cnf(c_0_26, plain, (r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_21]), c_0_22])).
% 0.80/0.99  cnf(c_0_27, plain, (v1_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_21]), c_0_22])).
% 0.80/0.99  cnf(c_0_28, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.80/0.99  cnf(c_0_29, plain, (r1_tarski(k2_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2))),k2_relat_1(X1))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27])).
% 0.80/0.99  cnf(c_0_30, plain, (k2_enumset1(X1,X1,X1,X2)=k2_enumset1(X2,X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_16]), c_0_16]), c_0_22]), c_0_22])).
% 0.80/0.99  fof(c_0_31, plain, ![X27, X28]:(~v1_relat_1(X28)|k2_relat_1(k7_relat_1(X28,X27))=k9_relat_1(X28,X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.80/0.99  fof(c_0_32, plain, ![X20, X21]:(~v1_relat_1(X20)|v1_relat_1(k7_relat_1(X20,X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.80/0.99  fof(c_0_33, plain, ![X24, X25, X26]:(~v1_relat_1(X26)|k7_relat_1(X26,k3_xboole_0(X24,X25))=k3_xboole_0(k7_relat_1(X26,X24),k7_relat_1(X26,X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t108_relat_1])])).
% 0.80/0.99  cnf(c_0_34, plain, (r1_tarski(k2_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2))),k2_relat_1(X2))|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.80/0.99  cnf(c_0_35, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.80/0.99  cnf(c_0_36, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.80/0.99  cnf(c_0_37, plain, (k7_relat_1(X1,k3_xboole_0(X2,X3))=k3_xboole_0(k7_relat_1(X1,X2),k7_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.80/0.99  fof(c_0_38, plain, ![X8, X9, X10]:(~r1_tarski(X8,X9)|~r1_tarski(X8,X10)|r1_tarski(X8,k3_xboole_0(X9,X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).
% 0.80/0.99  cnf(c_0_39, plain, (r1_tarski(k2_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,k7_relat_1(X2,X3)))),k9_relat_1(X2,X3))|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])).
% 0.80/0.99  cnf(c_0_40, plain, (k7_relat_1(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))=k1_setfam_1(k2_enumset1(k7_relat_1(X1,X2),k7_relat_1(X1,X2),k7_relat_1(X1,X2),k7_relat_1(X1,X3)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_21]), c_0_21]), c_0_22]), c_0_22])).
% 0.80/0.99  fof(c_0_41, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>r1_tarski(k9_relat_1(X3,k3_xboole_0(X1,X2)),k3_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2))))), inference(assume_negation,[status(cth)],[t154_relat_1])).
% 0.80/0.99  cnf(c_0_42, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.80/0.99  cnf(c_0_43, plain, (r1_tarski(k2_relat_1(k7_relat_1(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))),k9_relat_1(X1,X3))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.80/0.99  fof(c_0_44, negated_conjecture, (v1_relat_1(esk3_0)&~r1_tarski(k9_relat_1(esk3_0,k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_41])])])).
% 0.80/0.99  cnf(c_0_45, plain, (r1_tarski(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))|~r1_tarski(X1,X3)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_21]), c_0_22])).
% 0.80/0.99  cnf(c_0_46, plain, (r1_tarski(k9_relat_1(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3))),k9_relat_1(X1,X3))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_43, c_0_35])).
% 0.80/0.99  cnf(c_0_47, negated_conjecture, (~r1_tarski(k9_relat_1(esk3_0,k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.80/0.99  cnf(c_0_48, plain, (r1_tarski(k9_relat_1(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3))),k1_setfam_1(k2_enumset1(X4,X4,X4,k9_relat_1(X1,X3))))|~v1_relat_1(X1)|~r1_tarski(k9_relat_1(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3))),X4)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.80/0.99  cnf(c_0_49, plain, (r1_tarski(k9_relat_1(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3))),k9_relat_1(X1,X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_46, c_0_30])).
% 0.80/0.99  cnf(c_0_50, negated_conjecture, (~r1_tarski(k9_relat_1(esk3_0,k1_setfam_1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0))),k1_setfam_1(k2_enumset1(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk2_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_21]), c_0_21]), c_0_22]), c_0_22])).
% 0.80/0.99  cnf(c_0_51, plain, (r1_tarski(k9_relat_1(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3))),k1_setfam_1(k2_enumset1(k9_relat_1(X1,X2),k9_relat_1(X1,X2),k9_relat_1(X1,X2),k9_relat_1(X1,X3))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.80/0.99  cnf(c_0_52, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.80/0.99  cnf(c_0_53, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52])]), ['proof']).
% 0.80/0.99  # SZS output end CNFRefutation
% 0.80/0.99  # Proof object total steps             : 54
% 0.80/0.99  # Proof object clause steps            : 29
% 0.80/0.99  # Proof object formula steps           : 25
% 0.80/0.99  # Proof object conjectures             : 7
% 0.80/0.99  # Proof object clause conjectures      : 4
% 0.80/0.99  # Proof object formula conjectures     : 3
% 0.80/0.99  # Proof object initial clauses used    : 13
% 0.80/0.99  # Proof object initial formulas used   : 12
% 0.80/0.99  # Proof object generating inferences   : 9
% 0.80/0.99  # Proof object simplifying inferences  : 23
% 0.80/0.99  # Training examples: 0 positive, 0 negative
% 0.80/0.99  # Parsed axioms                        : 13
% 0.80/0.99  # Removed by relevancy pruning/SinE    : 0
% 0.80/0.99  # Initial clauses                      : 17
% 0.80/0.99  # Removed in clause preprocessing      : 3
% 0.80/0.99  # Initial clauses in saturation        : 14
% 0.80/0.99  # Processed clauses                    : 3930
% 0.80/0.99  # ...of these trivial                  : 7
% 0.80/0.99  # ...subsumed                          : 2947
% 0.80/0.99  # ...remaining for further processing  : 976
% 0.80/0.99  # Other redundant clauses eliminated   : 2
% 0.80/0.99  # Clauses deleted for lack of memory   : 0
% 0.80/0.99  # Backward-subsumed                    : 29
% 0.80/0.99  # Backward-rewritten                   : 3
% 0.80/0.99  # Generated clauses                    : 37361
% 0.80/0.99  # ...of the previous two non-trivial   : 35644
% 0.80/0.99  # Contextual simplify-reflections      : 128
% 0.80/0.99  # Paramodulations                      : 37359
% 0.80/0.99  # Factorizations                       : 0
% 0.80/0.99  # Equation resolutions                 : 2
% 0.80/0.99  # Propositional unsat checks           : 0
% 0.80/0.99  #    Propositional check models        : 0
% 0.80/0.99  #    Propositional check unsatisfiable : 0
% 0.80/0.99  #    Propositional clauses             : 0
% 0.80/0.99  #    Propositional clauses after purity: 0
% 0.80/0.99  #    Propositional unsat core size     : 0
% 0.80/0.99  #    Propositional preprocessing time  : 0.000
% 0.80/0.99  #    Propositional encoding time       : 0.000
% 0.80/0.99  #    Propositional solver time         : 0.000
% 0.80/0.99  #    Success case prop preproc time    : 0.000
% 0.80/0.99  #    Success case prop encoding time   : 0.000
% 0.80/0.99  #    Success case prop solver time     : 0.000
% 0.80/0.99  # Current number of processed clauses  : 929
% 0.80/0.99  #    Positive orientable unit clauses  : 10
% 0.80/0.99  #    Positive unorientable unit clauses: 1
% 0.80/0.99  #    Negative unit clauses             : 1
% 0.80/0.99  #    Non-unit-clauses                  : 917
% 0.80/0.99  # Current number of unprocessed clauses: 31694
% 0.80/0.99  # ...number of literals in the above   : 147868
% 0.80/0.99  # Current number of archived formulas  : 0
% 0.80/0.99  # Current number of archived clauses   : 48
% 0.80/0.99  # Clause-clause subsumption calls (NU) : 222949
% 0.80/0.99  # Rec. Clause-clause subsumption calls : 84236
% 0.80/0.99  # Non-unit clause-clause subsumptions  : 3096
% 0.80/0.99  # Unit Clause-clause subsumption calls : 13
% 0.80/0.99  # Rewrite failures with RHS unbound    : 0
% 0.80/0.99  # BW rewrite match attempts            : 72
% 0.80/0.99  # BW rewrite match successes           : 19
% 0.80/0.99  # Condensation attempts                : 0
% 0.80/0.99  # Condensation successes               : 0
% 0.80/0.99  # Termbank termtop insertions          : 1109122
% 0.80/0.99  
% 0.80/0.99  # -------------------------------------------------
% 0.80/0.99  # User time                : 0.625 s
% 0.80/0.99  # System time              : 0.022 s
% 0.80/0.99  # Total time               : 0.647 s
% 0.80/0.99  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------

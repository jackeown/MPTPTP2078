%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:50:57 EST 2020

% Result     : Theorem 2.84s
% Output     : CNFRefutation 2.84s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 172 expanded)
%              Number of clauses        :   33 (  76 expanded)
%              Number of leaves         :   10 (  43 expanded)
%              Depth                    :   11
%              Number of atoms          :   98 ( 280 expanded)
%              Number of equality atoms :   17 (  81 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t154_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => r1_tarski(k9_relat_1(X3,k3_xboole_0(X1,X2)),k3_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_relat_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(fc1_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(t25_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
              & r1_tarski(k2_relat_1(X1),k2_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(t108_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k7_relat_1(X3,k3_xboole_0(X1,X2)) = k3_xboole_0(k7_relat_1(X3,X1),k7_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_relat_1)).

fof(t19_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => r1_tarski(k9_relat_1(X3,k3_xboole_0(X1,X2)),k3_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2))) ) ),
    inference(assume_negation,[status(cth)],[t154_relat_1])).

fof(c_0_11,plain,(
    ! [X11,X12] : r1_tarski(k3_xboole_0(X11,X12),X11) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_12,plain,(
    ! [X16,X17] : k4_xboole_0(X16,k4_xboole_0(X16,X17)) = k3_xboole_0(X16,X17) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_13,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_14,plain,(
    ! [X20,X21] :
      ( ~ v1_relat_1(X20)
      | v1_relat_1(k3_xboole_0(X20,X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_relat_1])])).

fof(c_0_15,plain,(
    ! [X18,X19] :
      ( ~ v1_relat_1(X18)
      | v1_relat_1(k7_relat_1(X18,X19)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

fof(c_0_16,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & ~ r1_tarski(k9_relat_1(esk3_0,k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk2_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

cnf(c_0_17,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( v1_relat_1(k3_xboole_0(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_23,plain,(
    ! [X27,X28] :
      ( ( r1_tarski(k1_relat_1(X27),k1_relat_1(X28))
        | ~ r1_tarski(X27,X28)
        | ~ v1_relat_1(X28)
        | ~ v1_relat_1(X27) )
      & ( r1_tarski(k2_relat_1(X27),k2_relat_1(X28))
        | ~ r1_tarski(X27,X28)
        | ~ v1_relat_1(X28)
        | ~ v1_relat_1(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).

cnf(c_0_24,plain,
    ( r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_18]),c_0_18])).

cnf(c_0_26,plain,
    ( v1_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_20,c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( v1_relat_1(k7_relat_1(esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_28,plain,(
    ! [X25,X26] :
      ( ~ v1_relat_1(X26)
      | k2_relat_1(k7_relat_1(X26,X25)) = k9_relat_1(X26,X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

fof(c_0_29,plain,(
    ! [X22,X23,X24] :
      ( ~ v1_relat_1(X24)
      | k7_relat_1(X24,k3_xboole_0(X22,X23)) = k3_xboole_0(k7_relat_1(X24,X22),k7_relat_1(X24,X23)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t108_relat_1])])).

fof(c_0_30,plain,(
    ! [X13,X14,X15] :
      ( ~ r1_tarski(X13,X14)
      | ~ r1_tarski(X13,X15)
      | r1_tarski(X13,k3_xboole_0(X14,X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).

cnf(c_0_31,plain,
    ( r1_tarski(k2_relat_1(X1),k2_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( v1_relat_1(k4_xboole_0(k7_relat_1(esk3_0,X1),k4_xboole_0(k7_relat_1(esk3_0,X1),X2))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_34,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,plain,
    ( k7_relat_1(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(k7_relat_1(X1,X2),k7_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,plain,
    ( r1_tarski(k2_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,X2))),k2_relat_1(X2))
    | ~ v1_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_38,negated_conjecture,
    ( v1_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,k7_relat_1(esk3_0,X2)))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_25])).

cnf(c_0_39,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk3_0,X1)) = k9_relat_1(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_22])).

cnf(c_0_40,plain,
    ( k7_relat_1(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k4_xboole_0(k7_relat_1(X1,X2),k4_xboole_0(k7_relat_1(X1,X2),k7_relat_1(X1,X3)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_18]),c_0_18])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_36,c_0_18])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(k2_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,k7_relat_1(esk3_0,X2)))),k9_relat_1(esk3_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39]),c_0_27])])).

cnf(c_0_43,negated_conjecture,
    ( k7_relat_1(esk3_0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(k7_relat_1(esk3_0,X1),k4_xboole_0(k7_relat_1(esk3_0,X1),k7_relat_1(esk3_0,X2))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_22])).

cnf(c_0_44,plain,
    ( r1_tarski(k2_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,X2))),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_24]),c_0_26])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(k2_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,k7_relat_1(esk3_0,X2)))),k4_xboole_0(X3,k4_xboole_0(X3,k9_relat_1(esk3_0,X2))))
    | ~ r1_tarski(k2_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,k7_relat_1(esk3_0,X2)))),X3) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_46,negated_conjecture,
    ( k2_relat_1(k4_xboole_0(k7_relat_1(esk3_0,X1),k4_xboole_0(k7_relat_1(esk3_0,X1),k7_relat_1(esk3_0,X2)))) = k9_relat_1(esk3_0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_43])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(k2_relat_1(k4_xboole_0(k7_relat_1(esk3_0,X1),k4_xboole_0(k7_relat_1(esk3_0,X1),X2))),k9_relat_1(esk3_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_27]),c_0_39])).

cnf(c_0_48,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk3_0,k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk3_0,k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(X3,k4_xboole_0(X3,k9_relat_1(esk3_0,X2))))
    | ~ r1_tarski(k9_relat_1(esk3_0,k4_xboole_0(X1,k4_xboole_0(X1,X2))),X3) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk3_0,k4_xboole_0(X1,k4_xboole_0(X1,X2))),k9_relat_1(esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_46])).

cnf(c_0_51,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk3_0,k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0))),k4_xboole_0(k9_relat_1(esk3_0,esk1_0),k4_xboole_0(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk2_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_18]),c_0_18])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk3_0,k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(k9_relat_1(esk3_0,X1),k4_xboole_0(k9_relat_1(esk3_0,X1),k9_relat_1(esk3_0,X2)))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_53,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_52])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:49:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 2.84/3.01  # AutoSched0-Mode selected heuristic G_E___208_B01_00_F1_SE_CS_SP_PS_S064A
% 2.84/3.01  # and selection function SelectComplexG.
% 2.84/3.01  #
% 2.84/3.01  # Preprocessing time       : 0.016 s
% 2.84/3.01  # Presaturation interreduction done
% 2.84/3.01  
% 2.84/3.01  # Proof found!
% 2.84/3.01  # SZS status Theorem
% 2.84/3.01  # SZS output start CNFRefutation
% 2.84/3.01  fof(t154_relat_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>r1_tarski(k9_relat_1(X3,k3_xboole_0(X1,X2)),k3_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t154_relat_1)).
% 2.84/3.01  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.84/3.01  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.84/3.01  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.84/3.01  fof(fc1_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k3_xboole_0(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_relat_1)).
% 2.84/3.01  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.84/3.01  fof(t25_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>(r1_tarski(k1_relat_1(X1),k1_relat_1(X2))&r1_tarski(k2_relat_1(X1),k2_relat_1(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 2.84/3.01  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.84/3.01  fof(t108_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k7_relat_1(X3,k3_xboole_0(X1,X2))=k3_xboole_0(k7_relat_1(X3,X1),k7_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_relat_1)).
% 2.84/3.01  fof(t19_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(X1,k3_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.84/3.01  fof(c_0_10, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>r1_tarski(k9_relat_1(X3,k3_xboole_0(X1,X2)),k3_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2))))), inference(assume_negation,[status(cth)],[t154_relat_1])).
% 2.84/3.01  fof(c_0_11, plain, ![X11, X12]:r1_tarski(k3_xboole_0(X11,X12),X11), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 2.84/3.01  fof(c_0_12, plain, ![X16, X17]:k4_xboole_0(X16,k4_xboole_0(X16,X17))=k3_xboole_0(X16,X17), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 2.84/3.01  fof(c_0_13, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 2.84/3.01  fof(c_0_14, plain, ![X20, X21]:(~v1_relat_1(X20)|v1_relat_1(k3_xboole_0(X20,X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_relat_1])])).
% 2.84/3.01  fof(c_0_15, plain, ![X18, X19]:(~v1_relat_1(X18)|v1_relat_1(k7_relat_1(X18,X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 2.84/3.01  fof(c_0_16, negated_conjecture, (v1_relat_1(esk3_0)&~r1_tarski(k9_relat_1(esk3_0,k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 2.84/3.01  cnf(c_0_17, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 2.84/3.01  cnf(c_0_18, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 2.84/3.01  cnf(c_0_19, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 2.84/3.01  cnf(c_0_20, plain, (v1_relat_1(k3_xboole_0(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.84/3.01  cnf(c_0_21, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 2.84/3.01  cnf(c_0_22, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 2.84/3.01  fof(c_0_23, plain, ![X27, X28]:((r1_tarski(k1_relat_1(X27),k1_relat_1(X28))|~r1_tarski(X27,X28)|~v1_relat_1(X28)|~v1_relat_1(X27))&(r1_tarski(k2_relat_1(X27),k2_relat_1(X28))|~r1_tarski(X27,X28)|~v1_relat_1(X28)|~v1_relat_1(X27))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).
% 2.84/3.01  cnf(c_0_24, plain, (r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 2.84/3.01  cnf(c_0_25, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_18]), c_0_18])).
% 2.84/3.01  cnf(c_0_26, plain, (v1_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_20, c_0_18])).
% 2.84/3.01  cnf(c_0_27, negated_conjecture, (v1_relat_1(k7_relat_1(esk3_0,X1))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 2.84/3.01  fof(c_0_28, plain, ![X25, X26]:(~v1_relat_1(X26)|k2_relat_1(k7_relat_1(X26,X25))=k9_relat_1(X26,X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 2.84/3.01  fof(c_0_29, plain, ![X22, X23, X24]:(~v1_relat_1(X24)|k7_relat_1(X24,k3_xboole_0(X22,X23))=k3_xboole_0(k7_relat_1(X24,X22),k7_relat_1(X24,X23))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t108_relat_1])])).
% 2.84/3.01  fof(c_0_30, plain, ![X13, X14, X15]:(~r1_tarski(X13,X14)|~r1_tarski(X13,X15)|r1_tarski(X13,k3_xboole_0(X14,X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).
% 2.84/3.01  cnf(c_0_31, plain, (r1_tarski(k2_relat_1(X1),k2_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 2.84/3.01  cnf(c_0_32, plain, (r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 2.84/3.01  cnf(c_0_33, negated_conjecture, (v1_relat_1(k4_xboole_0(k7_relat_1(esk3_0,X1),k4_xboole_0(k7_relat_1(esk3_0,X1),X2)))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 2.84/3.01  cnf(c_0_34, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 2.84/3.01  cnf(c_0_35, plain, (k7_relat_1(X1,k3_xboole_0(X2,X3))=k3_xboole_0(k7_relat_1(X1,X2),k7_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 2.84/3.01  cnf(c_0_36, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 2.84/3.01  cnf(c_0_37, plain, (r1_tarski(k2_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,X2))),k2_relat_1(X2))|~v1_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)))|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 2.84/3.01  cnf(c_0_38, negated_conjecture, (v1_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,k7_relat_1(esk3_0,X2))))), inference(spm,[status(thm)],[c_0_33, c_0_25])).
% 2.84/3.01  cnf(c_0_39, negated_conjecture, (k2_relat_1(k7_relat_1(esk3_0,X1))=k9_relat_1(esk3_0,X1)), inference(spm,[status(thm)],[c_0_34, c_0_22])).
% 2.84/3.01  cnf(c_0_40, plain, (k7_relat_1(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))=k4_xboole_0(k7_relat_1(X1,X2),k4_xboole_0(k7_relat_1(X1,X2),k7_relat_1(X1,X3)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_18]), c_0_18])).
% 2.84/3.01  cnf(c_0_41, plain, (r1_tarski(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))|~r1_tarski(X1,X3)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_36, c_0_18])).
% 2.84/3.01  cnf(c_0_42, negated_conjecture, (r1_tarski(k2_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,k7_relat_1(esk3_0,X2)))),k9_relat_1(esk3_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39]), c_0_27])])).
% 2.84/3.01  cnf(c_0_43, negated_conjecture, (k7_relat_1(esk3_0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(k7_relat_1(esk3_0,X1),k4_xboole_0(k7_relat_1(esk3_0,X1),k7_relat_1(esk3_0,X2)))), inference(spm,[status(thm)],[c_0_40, c_0_22])).
% 2.84/3.01  cnf(c_0_44, plain, (r1_tarski(k2_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,X2))),k2_relat_1(X1))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_24]), c_0_26])).
% 2.84/3.01  cnf(c_0_45, negated_conjecture, (r1_tarski(k2_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,k7_relat_1(esk3_0,X2)))),k4_xboole_0(X3,k4_xboole_0(X3,k9_relat_1(esk3_0,X2))))|~r1_tarski(k2_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,k7_relat_1(esk3_0,X2)))),X3)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 2.84/3.01  cnf(c_0_46, negated_conjecture, (k2_relat_1(k4_xboole_0(k7_relat_1(esk3_0,X1),k4_xboole_0(k7_relat_1(esk3_0,X1),k7_relat_1(esk3_0,X2))))=k9_relat_1(esk3_0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_39, c_0_43])).
% 2.84/3.01  cnf(c_0_47, negated_conjecture, (r1_tarski(k2_relat_1(k4_xboole_0(k7_relat_1(esk3_0,X1),k4_xboole_0(k7_relat_1(esk3_0,X1),X2))),k9_relat_1(esk3_0,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_27]), c_0_39])).
% 2.84/3.01  cnf(c_0_48, negated_conjecture, (~r1_tarski(k9_relat_1(esk3_0,k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 2.84/3.01  cnf(c_0_49, negated_conjecture, (r1_tarski(k9_relat_1(esk3_0,k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(X3,k4_xboole_0(X3,k9_relat_1(esk3_0,X2))))|~r1_tarski(k9_relat_1(esk3_0,k4_xboole_0(X1,k4_xboole_0(X1,X2))),X3)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 2.84/3.01  cnf(c_0_50, negated_conjecture, (r1_tarski(k9_relat_1(esk3_0,k4_xboole_0(X1,k4_xboole_0(X1,X2))),k9_relat_1(esk3_0,X1))), inference(spm,[status(thm)],[c_0_47, c_0_46])).
% 2.84/3.01  cnf(c_0_51, negated_conjecture, (~r1_tarski(k9_relat_1(esk3_0,k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0))),k4_xboole_0(k9_relat_1(esk3_0,esk1_0),k4_xboole_0(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk2_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_18]), c_0_18])).
% 2.84/3.01  cnf(c_0_52, negated_conjecture, (r1_tarski(k9_relat_1(esk3_0,k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(k9_relat_1(esk3_0,X1),k4_xboole_0(k9_relat_1(esk3_0,X1),k9_relat_1(esk3_0,X2))))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 2.84/3.01  cnf(c_0_53, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_52])]), ['proof']).
% 2.84/3.01  # SZS output end CNFRefutation
% 2.84/3.01  # Proof object total steps             : 54
% 2.84/3.01  # Proof object clause steps            : 33
% 2.84/3.01  # Proof object formula steps           : 21
% 2.84/3.01  # Proof object conjectures             : 19
% 2.84/3.01  # Proof object clause conjectures      : 16
% 2.84/3.01  # Proof object formula conjectures     : 3
% 2.84/3.01  # Proof object initial clauses used    : 11
% 2.84/3.01  # Proof object initial formulas used   : 10
% 2.84/3.01  # Proof object generating inferences   : 15
% 2.84/3.01  # Proof object simplifying inferences  : 16
% 2.84/3.01  # Training examples: 0 positive, 0 negative
% 2.84/3.01  # Parsed axioms                        : 12
% 2.84/3.01  # Removed by relevancy pruning/SinE    : 0
% 2.84/3.01  # Initial clauses                      : 16
% 2.84/3.01  # Removed in clause preprocessing      : 1
% 2.84/3.01  # Initial clauses in saturation        : 15
% 2.84/3.01  # Processed clauses                    : 5974
% 2.84/3.01  # ...of these trivial                  : 1389
% 2.84/3.01  # ...subsumed                          : 1956
% 2.84/3.01  # ...remaining for further processing  : 2629
% 2.84/3.01  # Other redundant clauses eliminated   : 2
% 2.84/3.01  # Clauses deleted for lack of memory   : 0
% 2.84/3.01  # Backward-subsumed                    : 0
% 2.84/3.01  # Backward-rewritten                   : 83
% 2.84/3.01  # Generated clauses                    : 210345
% 2.84/3.01  # ...of the previous two non-trivial   : 192646
% 2.84/3.01  # Contextual simplify-reflections      : 2
% 2.84/3.01  # Paramodulations                      : 210343
% 2.84/3.01  # Factorizations                       : 0
% 2.84/3.01  # Equation resolutions                 : 2
% 2.84/3.01  # Propositional unsat checks           : 0
% 2.84/3.01  #    Propositional check models        : 0
% 2.84/3.01  #    Propositional check unsatisfiable : 0
% 2.84/3.01  #    Propositional clauses             : 0
% 2.84/3.01  #    Propositional clauses after purity: 0
% 2.84/3.01  #    Propositional unsat core size     : 0
% 2.84/3.01  #    Propositional preprocessing time  : 0.000
% 2.84/3.01  #    Propositional encoding time       : 0.000
% 2.84/3.01  #    Propositional solver time         : 0.000
% 2.84/3.01  #    Success case prop preproc time    : 0.000
% 2.84/3.01  #    Success case prop encoding time   : 0.000
% 2.84/3.01  #    Success case prop solver time     : 0.000
% 2.84/3.01  # Current number of processed clauses  : 2530
% 2.84/3.01  #    Positive orientable unit clauses  : 1557
% 2.84/3.01  #    Positive unorientable unit clauses: 1
% 2.84/3.01  #    Negative unit clauses             : 0
% 2.84/3.01  #    Non-unit-clauses                  : 972
% 2.84/3.01  # Current number of unprocessed clauses: 186643
% 2.84/3.01  # ...number of literals in the above   : 198931
% 2.84/3.01  # Current number of archived formulas  : 0
% 2.84/3.01  # Current number of archived clauses   : 98
% 2.84/3.01  # Clause-clause subsumption calls (NU) : 102317
% 2.84/3.01  # Rec. Clause-clause subsumption calls : 102313
% 2.84/3.01  # Non-unit clause-clause subsumptions  : 1925
% 2.84/3.01  # Unit Clause-clause subsumption calls : 11743
% 2.84/3.01  # Rewrite failures with RHS unbound    : 0
% 2.84/3.01  # BW rewrite match attempts            : 75875
% 2.84/3.01  # BW rewrite match successes           : 70
% 2.84/3.01  # Condensation attempts                : 0
% 2.84/3.01  # Condensation successes               : 0
% 2.84/3.01  # Termbank termtop insertions          : 14509430
% 2.84/3.02  
% 2.84/3.02  # -------------------------------------------------
% 2.84/3.02  # User time                : 2.586 s
% 2.84/3.02  # System time              : 0.090 s
% 2.84/3.02  # Total time               : 2.676 s
% 2.84/3.02  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------

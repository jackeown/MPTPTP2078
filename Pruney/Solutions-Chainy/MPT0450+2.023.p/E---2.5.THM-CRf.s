%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:48:33 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 201 expanded)
%              Number of clauses        :   33 (  91 expanded)
%              Number of leaves         :    9 (  51 expanded)
%              Depth                    :   11
%              Number of atoms          :  112 ( 376 expanded)
%              Number of equality atoms :   11 ( 100 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t34_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k3_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k3_relat_1(X1),k3_relat_1(X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relat_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(fc1_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

fof(t19_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(d3_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r1_tarski(X1,X2)
        <=> ! [X3,X4] :
              ( r2_hidden(k4_tarski(X3,X4),X1)
             => r2_hidden(k4_tarski(X3,X4),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).

fof(t18_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k3_xboole_0(X2,X3))
     => r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

fof(t31_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k3_relat_1(X1),k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => r1_tarski(k3_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k3_relat_1(X1),k3_relat_1(X2))) ) ) ),
    inference(assume_negation,[status(cth)],[t34_relat_1])).

fof(c_0_10,plain,(
    ! [X15,X16] : k1_setfam_1(k2_tarski(X15,X16)) = k3_xboole_0(X15,X16) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_11,plain,(
    ! [X13,X14] : k1_enumset1(X13,X13,X14) = k2_tarski(X13,X14) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_12,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_relat_1(esk4_0)
    & ~ r1_tarski(k3_relat_1(k3_xboole_0(esk3_0,esk4_0)),k3_xboole_0(k3_relat_1(esk3_0),k3_relat_1(esk4_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

cnf(c_0_13,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,plain,(
    ! [X11,X12] : k2_tarski(X11,X12) = k2_tarski(X12,X11) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

fof(c_0_16,plain,(
    ! [X24,X25] :
      ( ~ v1_relat_1(X24)
      | v1_relat_1(k3_xboole_0(X24,X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_relat_1])])).

cnf(c_0_17,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0(esk3_0,esk4_0)),k3_xboole_0(k3_relat_1(esk3_0),k3_relat_1(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_20,plain,(
    ! [X8,X9,X10] :
      ( ~ r1_tarski(X8,X9)
      | ~ r1_tarski(X8,X10)
      | r1_tarski(X8,k3_xboole_0(X9,X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).

fof(c_0_21,plain,(
    ! [X17,X18,X19,X20,X21] :
      ( ( ~ r1_tarski(X17,X18)
        | ~ r2_hidden(k4_tarski(X19,X20),X17)
        | r2_hidden(k4_tarski(X19,X20),X18)
        | ~ v1_relat_1(X17) )
      & ( r2_hidden(k4_tarski(esk1_2(X17,X21),esk2_2(X17,X21)),X17)
        | r1_tarski(X17,X21)
        | ~ v1_relat_1(X17) )
      & ( ~ r2_hidden(k4_tarski(esk1_2(X17,X21),esk2_2(X17,X21)),X21)
        | r1_tarski(X17,X21)
        | ~ v1_relat_1(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_relat_1])])])])])])).

cnf(c_0_22,plain,
    ( v1_relat_1(k3_xboole_0(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(k1_setfam_1(k1_enumset1(esk3_0,esk3_0,esk4_0))),k1_setfam_1(k1_enumset1(k3_relat_1(esk3_0),k3_relat_1(esk3_0),k3_relat_1(esk4_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_18]),c_0_18])).

cnf(c_0_24,plain,
    ( k1_enumset1(X1,X1,X2) = k1_enumset1(X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_14]),c_0_14])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_26,plain,(
    ! [X5,X6,X7] :
      ( ~ r1_tarski(X5,k3_xboole_0(X6,X7))
      | r1_tarski(X5,X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_xboole_1])])).

cnf(c_0_27,plain,
    ( r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X1)
    | r1_tarski(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( v1_relat_1(k1_setfam_1(k1_enumset1(X1,X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_22,c_0_18])).

cnf(c_0_29,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(k1_setfam_1(k1_enumset1(esk4_0,esk4_0,esk3_0))),k1_setfam_1(k1_enumset1(k3_relat_1(esk4_0),k3_relat_1(esk4_0),k3_relat_1(esk3_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24]),c_0_24])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,k1_setfam_1(k1_enumset1(X2,X2,X3)))
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_25,c_0_18])).

fof(c_0_31,plain,(
    ! [X26,X27] :
      ( ~ v1_relat_1(X26)
      | ~ v1_relat_1(X27)
      | ~ r1_tarski(X26,X27)
      | r1_tarski(k3_relat_1(X26),k3_relat_1(X27)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_relat_1])])])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( r2_hidden(k4_tarski(esk1_2(k1_setfam_1(k1_enumset1(X1,X1,X2)),X3),esk2_2(k1_setfam_1(k1_enumset1(X1,X1,X2)),X3)),k1_setfam_1(k1_enumset1(X1,X1,X2)))
    | r1_tarski(k1_setfam_1(k1_enumset1(X1,X1,X2)),X3)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_35,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(k1_setfam_1(k1_enumset1(esk4_0,esk4_0,esk3_0))),k3_relat_1(esk3_0))
    | ~ r1_tarski(k3_relat_1(k1_setfam_1(k1_enumset1(esk4_0,esk4_0,esk3_0))),k3_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_36,plain,
    ( r1_tarski(k3_relat_1(X1),k3_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k1_setfam_1(k1_enumset1(X2,X2,X3))) ),
    inference(rw,[status(thm)],[c_0_32,c_0_18])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(k1_setfam_1(k1_enumset1(esk4_0,esk4_0,X1)),X2),esk2_2(k1_setfam_1(k1_enumset1(esk4_0,esk4_0,X1)),X2)),k1_setfam_1(k1_enumset1(esk4_0,esk4_0,X1)))
    | r1_tarski(k1_setfam_1(k1_enumset1(esk4_0,esk4_0,X1)),X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_41,negated_conjecture,
    ( ~ v1_relat_1(k1_setfam_1(k1_enumset1(esk4_0,esk4_0,esk3_0)))
    | ~ r1_tarski(k3_relat_1(k1_setfam_1(k1_enumset1(esk4_0,esk4_0,esk3_0))),k3_relat_1(esk4_0))
    | ~ r1_tarski(k1_setfam_1(k1_enumset1(esk4_0,esk4_0,esk3_0)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k1_setfam_1(k1_enumset1(X3,X3,X2))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_24])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(k1_setfam_1(k1_enumset1(esk4_0,esk4_0,X1)),k1_setfam_1(k1_enumset1(esk4_0,esk4_0,X1)))
    | ~ v1_relat_1(k1_setfam_1(k1_enumset1(esk4_0,esk4_0,X1))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_44,negated_conjecture,
    ( ~ v1_relat_1(k1_setfam_1(k1_enumset1(esk4_0,esk4_0,esk3_0)))
    | ~ r1_tarski(k1_setfam_1(k1_enumset1(esk4_0,esk4_0,esk3_0)),esk3_0)
    | ~ r1_tarski(k1_setfam_1(k1_enumset1(esk4_0,esk4_0,esk3_0)),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_36]),c_0_34])])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(k1_setfam_1(k1_enumset1(esk4_0,esk4_0,X1)),X1)
    | ~ v1_relat_1(k1_setfam_1(k1_enumset1(esk4_0,esk4_0,X1))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_46,negated_conjecture,
    ( ~ r1_tarski(k1_setfam_1(k1_enumset1(esk4_0,esk4_0,esk3_0)),esk3_0)
    | ~ r1_tarski(k1_setfam_1(k1_enumset1(esk4_0,esk4_0,esk3_0)),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_28]),c_0_34])])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(k1_setfam_1(k1_enumset1(esk4_0,esk4_0,X1)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_28]),c_0_34])])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(k1_setfam_1(k1_enumset1(esk4_0,esk4_0,X1)),esk4_0)
    | ~ v1_relat_1(k1_setfam_1(k1_enumset1(esk4_0,esk4_0,X1))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_43])).

cnf(c_0_49,negated_conjecture,
    ( ~ r1_tarski(k1_setfam_1(k1_enumset1(esk4_0,esk4_0,esk3_0)),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_47])])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(k1_setfam_1(k1_enumset1(esk4_0,esk4_0,X1)),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_28]),c_0_34])])).

cnf(c_0_51,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_50])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:53:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.14/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.027 s
% 0.14/0.38  # Presaturation interreduction done
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(t34_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k3_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k3_relat_1(X1),k3_relat_1(X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_relat_1)).
% 0.14/0.38  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.14/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.14/0.38  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.14/0.38  fof(fc1_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k3_xboole_0(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_relat_1)).
% 0.14/0.38  fof(t19_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(X1,k3_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 0.14/0.38  fof(d3_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(r1_tarski(X1,X2)<=>![X3, X4]:(r2_hidden(k4_tarski(X3,X4),X1)=>r2_hidden(k4_tarski(X3,X4),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_relat_1)).
% 0.14/0.38  fof(t18_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k3_xboole_0(X2,X3))=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_xboole_1)).
% 0.14/0.38  fof(t31_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>r1_tarski(k3_relat_1(X1),k3_relat_1(X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_relat_1)).
% 0.14/0.38  fof(c_0_9, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k3_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k3_relat_1(X1),k3_relat_1(X2)))))), inference(assume_negation,[status(cth)],[t34_relat_1])).
% 0.14/0.38  fof(c_0_10, plain, ![X15, X16]:k1_setfam_1(k2_tarski(X15,X16))=k3_xboole_0(X15,X16), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.14/0.38  fof(c_0_11, plain, ![X13, X14]:k1_enumset1(X13,X13,X14)=k2_tarski(X13,X14), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.14/0.38  fof(c_0_12, negated_conjecture, (v1_relat_1(esk3_0)&(v1_relat_1(esk4_0)&~r1_tarski(k3_relat_1(k3_xboole_0(esk3_0,esk4_0)),k3_xboole_0(k3_relat_1(esk3_0),k3_relat_1(esk4_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.14/0.38  cnf(c_0_13, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.38  cnf(c_0_14, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.38  fof(c_0_15, plain, ![X11, X12]:k2_tarski(X11,X12)=k2_tarski(X12,X11), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.14/0.38  fof(c_0_16, plain, ![X24, X25]:(~v1_relat_1(X24)|v1_relat_1(k3_xboole_0(X24,X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_relat_1])])).
% 0.14/0.38  cnf(c_0_17, negated_conjecture, (~r1_tarski(k3_relat_1(k3_xboole_0(esk3_0,esk4_0)),k3_xboole_0(k3_relat_1(esk3_0),k3_relat_1(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.38  cnf(c_0_18, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_13, c_0_14])).
% 0.14/0.38  cnf(c_0_19, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.38  fof(c_0_20, plain, ![X8, X9, X10]:(~r1_tarski(X8,X9)|~r1_tarski(X8,X10)|r1_tarski(X8,k3_xboole_0(X9,X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).
% 0.14/0.38  fof(c_0_21, plain, ![X17, X18, X19, X20, X21]:((~r1_tarski(X17,X18)|(~r2_hidden(k4_tarski(X19,X20),X17)|r2_hidden(k4_tarski(X19,X20),X18))|~v1_relat_1(X17))&((r2_hidden(k4_tarski(esk1_2(X17,X21),esk2_2(X17,X21)),X17)|r1_tarski(X17,X21)|~v1_relat_1(X17))&(~r2_hidden(k4_tarski(esk1_2(X17,X21),esk2_2(X17,X21)),X21)|r1_tarski(X17,X21)|~v1_relat_1(X17)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_relat_1])])])])])])).
% 0.14/0.38  cnf(c_0_22, plain, (v1_relat_1(k3_xboole_0(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.38  cnf(c_0_23, negated_conjecture, (~r1_tarski(k3_relat_1(k1_setfam_1(k1_enumset1(esk3_0,esk3_0,esk4_0))),k1_setfam_1(k1_enumset1(k3_relat_1(esk3_0),k3_relat_1(esk3_0),k3_relat_1(esk4_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17, c_0_18]), c_0_18])).
% 0.14/0.38  cnf(c_0_24, plain, (k1_enumset1(X1,X1,X2)=k1_enumset1(X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_14]), c_0_14])).
% 0.14/0.38  cnf(c_0_25, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.38  fof(c_0_26, plain, ![X5, X6, X7]:(~r1_tarski(X5,k3_xboole_0(X6,X7))|r1_tarski(X5,X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_xboole_1])])).
% 0.14/0.38  cnf(c_0_27, plain, (r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X1)|r1_tarski(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.38  cnf(c_0_28, plain, (v1_relat_1(k1_setfam_1(k1_enumset1(X1,X1,X2)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_22, c_0_18])).
% 0.14/0.38  cnf(c_0_29, negated_conjecture, (~r1_tarski(k3_relat_1(k1_setfam_1(k1_enumset1(esk4_0,esk4_0,esk3_0))),k1_setfam_1(k1_enumset1(k3_relat_1(esk4_0),k3_relat_1(esk4_0),k3_relat_1(esk3_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_24]), c_0_24])).
% 0.14/0.38  cnf(c_0_30, plain, (r1_tarski(X1,k1_setfam_1(k1_enumset1(X2,X2,X3)))|~r1_tarski(X1,X3)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_25, c_0_18])).
% 0.14/0.38  fof(c_0_31, plain, ![X26, X27]:(~v1_relat_1(X26)|(~v1_relat_1(X27)|(~r1_tarski(X26,X27)|r1_tarski(k3_relat_1(X26),k3_relat_1(X27))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_relat_1])])])).
% 0.14/0.38  cnf(c_0_32, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.14/0.38  cnf(c_0_33, plain, (r2_hidden(k4_tarski(esk1_2(k1_setfam_1(k1_enumset1(X1,X1,X2)),X3),esk2_2(k1_setfam_1(k1_enumset1(X1,X1,X2)),X3)),k1_setfam_1(k1_enumset1(X1,X1,X2)))|r1_tarski(k1_setfam_1(k1_enumset1(X1,X1,X2)),X3)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.14/0.38  cnf(c_0_34, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.38  cnf(c_0_35, negated_conjecture, (~r1_tarski(k3_relat_1(k1_setfam_1(k1_enumset1(esk4_0,esk4_0,esk3_0))),k3_relat_1(esk3_0))|~r1_tarski(k3_relat_1(k1_setfam_1(k1_enumset1(esk4_0,esk4_0,esk3_0))),k3_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.14/0.38  cnf(c_0_36, plain, (r1_tarski(k3_relat_1(X1),k3_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.14/0.38  cnf(c_0_37, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.38  cnf(c_0_38, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k1_setfam_1(k1_enumset1(X2,X2,X3)))), inference(rw,[status(thm)],[c_0_32, c_0_18])).
% 0.14/0.38  cnf(c_0_39, plain, (r1_tarski(X1,X2)|~r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.38  cnf(c_0_40, negated_conjecture, (r2_hidden(k4_tarski(esk1_2(k1_setfam_1(k1_enumset1(esk4_0,esk4_0,X1)),X2),esk2_2(k1_setfam_1(k1_enumset1(esk4_0,esk4_0,X1)),X2)),k1_setfam_1(k1_enumset1(esk4_0,esk4_0,X1)))|r1_tarski(k1_setfam_1(k1_enumset1(esk4_0,esk4_0,X1)),X2)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.14/0.38  cnf(c_0_41, negated_conjecture, (~v1_relat_1(k1_setfam_1(k1_enumset1(esk4_0,esk4_0,esk3_0)))|~r1_tarski(k3_relat_1(k1_setfam_1(k1_enumset1(esk4_0,esk4_0,esk3_0))),k3_relat_1(esk4_0))|~r1_tarski(k1_setfam_1(k1_enumset1(esk4_0,esk4_0,esk3_0)),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37])])).
% 0.14/0.38  cnf(c_0_42, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k1_setfam_1(k1_enumset1(X3,X3,X2)))), inference(spm,[status(thm)],[c_0_38, c_0_24])).
% 0.14/0.38  cnf(c_0_43, negated_conjecture, (r1_tarski(k1_setfam_1(k1_enumset1(esk4_0,esk4_0,X1)),k1_setfam_1(k1_enumset1(esk4_0,esk4_0,X1)))|~v1_relat_1(k1_setfam_1(k1_enumset1(esk4_0,esk4_0,X1)))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.14/0.38  cnf(c_0_44, negated_conjecture, (~v1_relat_1(k1_setfam_1(k1_enumset1(esk4_0,esk4_0,esk3_0)))|~r1_tarski(k1_setfam_1(k1_enumset1(esk4_0,esk4_0,esk3_0)),esk3_0)|~r1_tarski(k1_setfam_1(k1_enumset1(esk4_0,esk4_0,esk3_0)),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_36]), c_0_34])])).
% 0.14/0.38  cnf(c_0_45, negated_conjecture, (r1_tarski(k1_setfam_1(k1_enumset1(esk4_0,esk4_0,X1)),X1)|~v1_relat_1(k1_setfam_1(k1_enumset1(esk4_0,esk4_0,X1)))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.14/0.38  cnf(c_0_46, negated_conjecture, (~r1_tarski(k1_setfam_1(k1_enumset1(esk4_0,esk4_0,esk3_0)),esk3_0)|~r1_tarski(k1_setfam_1(k1_enumset1(esk4_0,esk4_0,esk3_0)),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_28]), c_0_34])])).
% 0.14/0.38  cnf(c_0_47, negated_conjecture, (r1_tarski(k1_setfam_1(k1_enumset1(esk4_0,esk4_0,X1)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_28]), c_0_34])])).
% 0.14/0.38  cnf(c_0_48, negated_conjecture, (r1_tarski(k1_setfam_1(k1_enumset1(esk4_0,esk4_0,X1)),esk4_0)|~v1_relat_1(k1_setfam_1(k1_enumset1(esk4_0,esk4_0,X1)))), inference(spm,[status(thm)],[c_0_38, c_0_43])).
% 0.14/0.38  cnf(c_0_49, negated_conjecture, (~r1_tarski(k1_setfam_1(k1_enumset1(esk4_0,esk4_0,esk3_0)),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_47])])).
% 0.14/0.38  cnf(c_0_50, negated_conjecture, (r1_tarski(k1_setfam_1(k1_enumset1(esk4_0,esk4_0,X1)),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_28]), c_0_34])])).
% 0.14/0.38  cnf(c_0_51, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_50])]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 52
% 0.14/0.38  # Proof object clause steps            : 33
% 0.14/0.38  # Proof object formula steps           : 19
% 0.14/0.38  # Proof object conjectures             : 20
% 0.14/0.38  # Proof object clause conjectures      : 17
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 12
% 0.14/0.38  # Proof object initial formulas used   : 9
% 0.14/0.38  # Proof object generating inferences   : 12
% 0.14/0.38  # Proof object simplifying inferences  : 24
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 9
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 13
% 0.14/0.38  # Removed in clause preprocessing      : 2
% 0.14/0.38  # Initial clauses in saturation        : 11
% 0.14/0.38  # Processed clauses                    : 113
% 0.14/0.38  # ...of these trivial                  : 0
% 0.14/0.38  # ...subsumed                          : 33
% 0.14/0.38  # ...remaining for further processing  : 80
% 0.14/0.38  # Other redundant clauses eliminated   : 0
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 7
% 0.14/0.38  # Backward-rewritten                   : 6
% 0.14/0.38  # Generated clauses                    : 214
% 0.14/0.38  # ...of the previous two non-trivial   : 194
% 0.14/0.38  # Contextual simplify-reflections      : 0
% 0.14/0.38  # Paramodulations                      : 214
% 0.14/0.38  # Factorizations                       : 0
% 0.14/0.38  # Equation resolutions                 : 0
% 0.14/0.38  # Propositional unsat checks           : 0
% 0.14/0.38  #    Propositional check models        : 0
% 0.14/0.38  #    Propositional check unsatisfiable : 0
% 0.14/0.38  #    Propositional clauses             : 0
% 0.14/0.38  #    Propositional clauses after purity: 0
% 0.14/0.38  #    Propositional unsat core size     : 0
% 0.14/0.38  #    Propositional preprocessing time  : 0.000
% 0.14/0.38  #    Propositional encoding time       : 0.000
% 0.14/0.38  #    Propositional solver time         : 0.000
% 0.14/0.38  #    Success case prop preproc time    : 0.000
% 0.14/0.38  #    Success case prop encoding time   : 0.000
% 0.14/0.38  #    Success case prop solver time     : 0.000
% 0.14/0.38  # Current number of processed clauses  : 56
% 0.14/0.38  #    Positive orientable unit clauses  : 10
% 0.14/0.38  #    Positive unorientable unit clauses: 1
% 0.14/0.38  #    Negative unit clauses             : 1
% 0.14/0.38  #    Non-unit-clauses                  : 44
% 0.14/0.38  # Current number of unprocessed clauses: 87
% 0.14/0.38  # ...number of literals in the above   : 236
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 26
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 823
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 482
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 39
% 0.14/0.38  # Unit Clause-clause subsumption calls : 99
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 29
% 0.14/0.38  # BW rewrite match successes           : 18
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 6405
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.034 s
% 0.14/0.38  # System time              : 0.004 s
% 0.14/0.38  # Total time               : 0.038 s
% 0.14/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------

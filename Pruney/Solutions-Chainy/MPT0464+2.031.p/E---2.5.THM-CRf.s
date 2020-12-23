%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:48:41 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 299 expanded)
%              Number of clauses        :   33 ( 132 expanded)
%              Number of leaves         :   11 (  81 expanded)
%              Depth                    :   12
%              Number of atoms          :   95 ( 394 expanded)
%              Number of equality atoms :   19 ( 234 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    5 (   1 average)
%              Maximal term depth       :    4 (   2 average)

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

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(fc1_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

fof(t48_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => ( r1_tarski(X1,X2)
               => r1_tarski(k5_relat_1(X3,X1),k5_relat_1(X3,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relat_1)).

fof(t52_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relat_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t85_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_xboole_0(X1,k4_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

fof(t86_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) )
     => r1_tarski(X1,k4_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

fof(c_0_11,plain,(
    ! [X21,X22] : k1_setfam_1(k2_tarski(X21,X22)) = k3_xboole_0(X21,X22) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_12,plain,(
    ! [X16,X17] : k1_enumset1(X16,X16,X17) = k2_tarski(X16,X17) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_13,plain,(
    ! [X4,X5] : r1_tarski(k3_xboole_0(X4,X5),X4) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_14,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X18,X19,X20] : k2_enumset1(X18,X18,X19,X20) = k1_enumset1(X18,X19,X20) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_17,plain,(
    ! [X6,X7] : k4_xboole_0(X6,k4_xboole_0(X6,X7)) = k3_xboole_0(X6,X7) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_18,plain,(
    ! [X23,X24] :
      ( ~ v1_relat_1(X23)
      | v1_relat_1(k3_xboole_0(X23,X24)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_relat_1])])).

cnf(c_0_19,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_21,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( v1_relat_1(k3_xboole_0(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_24,plain,(
    ! [X25,X26,X27] :
      ( ~ v1_relat_1(X25)
      | ~ v1_relat_1(X26)
      | ~ v1_relat_1(X27)
      | ~ r1_tarski(X25,X26)
      | r1_tarski(k5_relat_1(X27,X25),k5_relat_1(X27,X26)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_relat_1])])])).

cnf(c_0_25,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_20]),c_0_21])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_20]),c_0_21])).

cnf(c_0_27,plain,
    ( v1_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_20]),c_0_21])).

fof(c_0_28,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ! [X3] :
                ( v1_relat_1(X3)
               => r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t52_relat_1])).

cnf(c_0_29,plain,
    ( r1_tarski(k5_relat_1(X3,X1),k5_relat_1(X3,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,plain,
    ( r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_31,plain,
    ( v1_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_27,c_0_26])).

fof(c_0_32,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_relat_1(esk2_0)
    & v1_relat_1(esk3_0)
    & ~ r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk3_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_28])])])).

cnf(c_0_33,plain,
    ( r1_tarski(k5_relat_1(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))),k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])).

cnf(c_0_34,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_35,plain,(
    ! [X14,X15] : k2_tarski(X14,X15) = k2_tarski(X15,X14) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

fof(c_0_36,plain,(
    ! [X8,X9,X10] :
      ( ~ r1_tarski(X8,X9)
      | r1_xboole_0(X8,k4_xboole_0(X10,X9)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_xboole_1])])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk1_0,k4_xboole_0(X1,k4_xboole_0(X1,X2))),k5_relat_1(esk1_0,X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_38,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_40,plain,(
    ! [X11,X12,X13] :
      ( ~ r1_tarski(X11,X12)
      | ~ r1_xboole_0(X11,X13)
      | r1_tarski(X11,k4_xboole_0(X12,X13)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_xboole_1])])).

cnf(c_0_41,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk1_0,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,X1))),k5_relat_1(esk1_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_44,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k2_enumset1(X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_15]),c_0_15]),c_0_21]),c_0_21])).

cnf(c_0_45,negated_conjecture,
    ( ~ r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_46,plain,
    ( r1_tarski(X1,k4_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_47,negated_conjecture,
    ( r1_xboole_0(k5_relat_1(esk1_0,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,X1))),k4_xboole_0(X2,k5_relat_1(esk1_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk1_0,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,X1))),k5_relat_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_43])).

cnf(c_0_49,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_44]),c_0_26])).

cnf(c_0_50,negated_conjecture,
    ( ~ r1_tarski(k5_relat_1(esk1_0,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0))),k1_setfam_1(k2_enumset1(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk3_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_20]),c_0_20]),c_0_21]),c_0_21])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk1_0,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,X1))),k4_xboole_0(X2,k4_xboole_0(X3,k5_relat_1(esk1_0,esk3_0))))
    | ~ r1_tarski(k5_relat_1(esk1_0,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,X1))),X2) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk1_0,k4_xboole_0(X1,k4_xboole_0(X1,esk2_0))),k5_relat_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_53,negated_conjecture,
    ( ~ r1_tarski(k5_relat_1(esk1_0,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0))),k4_xboole_0(k5_relat_1(esk1_0,esk2_0),k4_xboole_0(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk3_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_26]),c_0_26])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk1_0,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0))),k4_xboole_0(k5_relat_1(esk1_0,esk2_0),k4_xboole_0(X1,k5_relat_1(esk1_0,esk3_0)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_49])).

cnf(c_0_55,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_54])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:54:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.42  # AutoSched0-Mode selected heuristic G_E___107_B00_00_F1_PI_AE_Q4_CS_SP_PS_S064A
% 0.19/0.42  # and selection function SelectComplexG.
% 0.19/0.42  #
% 0.19/0.42  # Preprocessing time       : 0.027 s
% 0.19/0.42  # Presaturation interreduction done
% 0.19/0.42  
% 0.19/0.42  # Proof found!
% 0.19/0.42  # SZS status Theorem
% 0.19/0.42  # SZS output start CNFRefutation
% 0.19/0.42  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.19/0.42  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.42  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.19/0.42  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.42  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.19/0.42  fof(fc1_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k3_xboole_0(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_relat_1)).
% 0.19/0.42  fof(t48_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>r1_tarski(k5_relat_1(X3,X1),k5_relat_1(X3,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_relat_1)).
% 0.19/0.42  fof(t52_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_relat_1)).
% 0.19/0.42  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.19/0.42  fof(t85_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_xboole_0(X1,k4_xboole_0(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 0.19/0.42  fof(t86_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X1,X3))=>r1_tarski(X1,k4_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_xboole_1)).
% 0.19/0.42  fof(c_0_11, plain, ![X21, X22]:k1_setfam_1(k2_tarski(X21,X22))=k3_xboole_0(X21,X22), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.19/0.42  fof(c_0_12, plain, ![X16, X17]:k1_enumset1(X16,X16,X17)=k2_tarski(X16,X17), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.42  fof(c_0_13, plain, ![X4, X5]:r1_tarski(k3_xboole_0(X4,X5),X4), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.19/0.42  cnf(c_0_14, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.42  cnf(c_0_15, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.42  fof(c_0_16, plain, ![X18, X19, X20]:k2_enumset1(X18,X18,X19,X20)=k1_enumset1(X18,X19,X20), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.42  fof(c_0_17, plain, ![X6, X7]:k4_xboole_0(X6,k4_xboole_0(X6,X7))=k3_xboole_0(X6,X7), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.19/0.42  fof(c_0_18, plain, ![X23, X24]:(~v1_relat_1(X23)|v1_relat_1(k3_xboole_0(X23,X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_relat_1])])).
% 0.19/0.42  cnf(c_0_19, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.42  cnf(c_0_20, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.19/0.42  cnf(c_0_21, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.42  cnf(c_0_22, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.42  cnf(c_0_23, plain, (v1_relat_1(k3_xboole_0(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.42  fof(c_0_24, plain, ![X25, X26, X27]:(~v1_relat_1(X25)|(~v1_relat_1(X26)|(~v1_relat_1(X27)|(~r1_tarski(X25,X26)|r1_tarski(k5_relat_1(X27,X25),k5_relat_1(X27,X26)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_relat_1])])])).
% 0.19/0.42  cnf(c_0_25, plain, (r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_20]), c_0_21])).
% 0.19/0.42  cnf(c_0_26, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_setfam_1(k2_enumset1(X1,X1,X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_20]), c_0_21])).
% 0.19/0.42  cnf(c_0_27, plain, (v1_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_20]), c_0_21])).
% 0.19/0.42  fof(c_0_28, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3))))))), inference(assume_negation,[status(cth)],[t52_relat_1])).
% 0.19/0.42  cnf(c_0_29, plain, (r1_tarski(k5_relat_1(X3,X1),k5_relat_1(X3,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X3)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.42  cnf(c_0_30, plain, (r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 0.19/0.42  cnf(c_0_31, plain, (v1_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_27, c_0_26])).
% 0.19/0.42  fof(c_0_32, negated_conjecture, (v1_relat_1(esk1_0)&(v1_relat_1(esk2_0)&(v1_relat_1(esk3_0)&~r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_28])])])).
% 0.19/0.42  cnf(c_0_33, plain, (r1_tarski(k5_relat_1(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))),k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])).
% 0.19/0.42  cnf(c_0_34, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.42  fof(c_0_35, plain, ![X14, X15]:k2_tarski(X14,X15)=k2_tarski(X15,X14), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.19/0.42  fof(c_0_36, plain, ![X8, X9, X10]:(~r1_tarski(X8,X9)|r1_xboole_0(X8,k4_xboole_0(X10,X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_xboole_1])])).
% 0.19/0.42  cnf(c_0_37, negated_conjecture, (r1_tarski(k5_relat_1(esk1_0,k4_xboole_0(X1,k4_xboole_0(X1,X2))),k5_relat_1(esk1_0,X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.19/0.42  cnf(c_0_38, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.42  cnf(c_0_39, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.42  fof(c_0_40, plain, ![X11, X12, X13]:(~r1_tarski(X11,X12)|~r1_xboole_0(X11,X13)|r1_tarski(X11,k4_xboole_0(X12,X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_xboole_1])])).
% 0.19/0.42  cnf(c_0_41, plain, (r1_xboole_0(X1,k4_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.42  cnf(c_0_42, negated_conjecture, (r1_tarski(k5_relat_1(esk1_0,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,X1))),k5_relat_1(esk1_0,esk3_0))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.19/0.42  cnf(c_0_43, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.42  cnf(c_0_44, plain, (k2_enumset1(X1,X1,X1,X2)=k2_enumset1(X2,X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_15]), c_0_15]), c_0_21]), c_0_21])).
% 0.19/0.42  cnf(c_0_45, negated_conjecture, (~r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.42  cnf(c_0_46, plain, (r1_tarski(X1,k4_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.42  cnf(c_0_47, negated_conjecture, (r1_xboole_0(k5_relat_1(esk1_0,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,X1))),k4_xboole_0(X2,k5_relat_1(esk1_0,esk3_0)))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.19/0.42  cnf(c_0_48, negated_conjecture, (r1_tarski(k5_relat_1(esk1_0,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,X1))),k5_relat_1(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_37, c_0_43])).
% 0.19/0.42  cnf(c_0_49, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_44]), c_0_26])).
% 0.19/0.42  cnf(c_0_50, negated_conjecture, (~r1_tarski(k5_relat_1(esk1_0,k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0))),k1_setfam_1(k2_enumset1(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk3_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_20]), c_0_20]), c_0_21]), c_0_21])).
% 0.19/0.42  cnf(c_0_51, negated_conjecture, (r1_tarski(k5_relat_1(esk1_0,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,X1))),k4_xboole_0(X2,k4_xboole_0(X3,k5_relat_1(esk1_0,esk3_0))))|~r1_tarski(k5_relat_1(esk1_0,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,X1))),X2)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.19/0.42  cnf(c_0_52, negated_conjecture, (r1_tarski(k5_relat_1(esk1_0,k4_xboole_0(X1,k4_xboole_0(X1,esk2_0))),k5_relat_1(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.19/0.42  cnf(c_0_53, negated_conjecture, (~r1_tarski(k5_relat_1(esk1_0,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0))),k4_xboole_0(k5_relat_1(esk1_0,esk2_0),k4_xboole_0(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk3_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_26]), c_0_26])).
% 0.19/0.42  cnf(c_0_54, negated_conjecture, (r1_tarski(k5_relat_1(esk1_0,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0))),k4_xboole_0(k5_relat_1(esk1_0,esk2_0),k4_xboole_0(X1,k5_relat_1(esk1_0,esk3_0))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_49])).
% 0.19/0.42  cnf(c_0_55, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_54])]), ['proof']).
% 0.19/0.42  # SZS output end CNFRefutation
% 0.19/0.42  # Proof object total steps             : 56
% 0.19/0.42  # Proof object clause steps            : 33
% 0.19/0.42  # Proof object formula steps           : 23
% 0.19/0.42  # Proof object conjectures             : 17
% 0.19/0.42  # Proof object clause conjectures      : 14
% 0.19/0.42  # Proof object formula conjectures     : 3
% 0.19/0.42  # Proof object initial clauses used    : 14
% 0.19/0.42  # Proof object initial formulas used   : 11
% 0.19/0.42  # Proof object generating inferences   : 9
% 0.19/0.42  # Proof object simplifying inferences  : 24
% 0.19/0.42  # Training examples: 0 positive, 0 negative
% 0.19/0.42  # Parsed axioms                        : 11
% 0.19/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.42  # Initial clauses                      : 14
% 0.19/0.42  # Removed in clause preprocessing      : 3
% 0.19/0.42  # Initial clauses in saturation        : 11
% 0.19/0.42  # Processed clauses                    : 443
% 0.19/0.42  # ...of these trivial                  : 140
% 0.19/0.42  # ...subsumed                          : 10
% 0.19/0.42  # ...remaining for further processing  : 293
% 0.19/0.42  # Other redundant clauses eliminated   : 0
% 0.19/0.42  # Clauses deleted for lack of memory   : 0
% 0.19/0.42  # Backward-subsumed                    : 0
% 0.19/0.42  # Backward-rewritten                   : 14
% 0.19/0.42  # Generated clauses                    : 3600
% 0.19/0.42  # ...of the previous two non-trivial   : 3159
% 0.19/0.42  # Contextual simplify-reflections      : 1
% 0.19/0.42  # Paramodulations                      : 3600
% 0.19/0.42  # Factorizations                       : 0
% 0.19/0.42  # Equation resolutions                 : 0
% 0.19/0.42  # Propositional unsat checks           : 0
% 0.19/0.42  #    Propositional check models        : 0
% 0.19/0.42  #    Propositional check unsatisfiable : 0
% 0.19/0.42  #    Propositional clauses             : 0
% 0.19/0.42  #    Propositional clauses after purity: 0
% 0.19/0.42  #    Propositional unsat core size     : 0
% 0.19/0.42  #    Propositional preprocessing time  : 0.000
% 0.19/0.42  #    Propositional encoding time       : 0.000
% 0.19/0.42  #    Propositional solver time         : 0.000
% 0.19/0.42  #    Success case prop preproc time    : 0.000
% 0.19/0.42  #    Success case prop encoding time   : 0.000
% 0.19/0.42  #    Success case prop solver time     : 0.000
% 0.19/0.42  # Current number of processed clauses  : 268
% 0.19/0.42  #    Positive orientable unit clauses  : 158
% 0.19/0.42  #    Positive unorientable unit clauses: 2
% 0.19/0.42  #    Negative unit clauses             : 0
% 0.19/0.42  #    Non-unit-clauses                  : 108
% 0.19/0.42  # Current number of unprocessed clauses: 2737
% 0.19/0.42  # ...number of literals in the above   : 3292
% 0.19/0.42  # Current number of archived formulas  : 0
% 0.19/0.42  # Current number of archived clauses   : 28
% 0.19/0.42  # Clause-clause subsumption calls (NU) : 6250
% 0.19/0.42  # Rec. Clause-clause subsumption calls : 5042
% 0.19/0.42  # Non-unit clause-clause subsumptions  : 10
% 0.19/0.42  # Unit Clause-clause subsumption calls : 496
% 0.19/0.42  # Rewrite failures with RHS unbound    : 0
% 0.19/0.42  # BW rewrite match attempts            : 753
% 0.19/0.42  # BW rewrite match successes           : 27
% 0.19/0.42  # Condensation attempts                : 0
% 0.19/0.42  # Condensation successes               : 0
% 0.19/0.42  # Termbank termtop insertions          : 92645
% 0.19/0.42  
% 0.19/0.42  # -------------------------------------------------
% 0.19/0.42  # User time                : 0.079 s
% 0.19/0.42  # System time              : 0.007 s
% 0.19/0.42  # Total time               : 0.086 s
% 0.19/0.42  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------

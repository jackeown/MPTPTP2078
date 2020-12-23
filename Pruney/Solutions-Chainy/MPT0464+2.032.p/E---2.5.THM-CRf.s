%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:48:41 EST 2020

% Result     : Theorem 0.61s
% Output     : CNFRefutation 0.61s
% Verified   : 
% Statistics : Number of formulae       :   48 (  90 expanded)
%              Number of clauses        :   29 (  40 expanded)
%              Number of leaves         :    9 (  22 expanded)
%              Depth                    :   11
%              Number of atoms          :   95 ( 200 expanded)
%              Number of equality atoms :    9 (  21 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t43_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_xboole_0(X2,X3))
     => r1_tarski(k4_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t52_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relat_1)).

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

fof(fc2_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_relat_1)).

fof(t19_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(c_0_9,plain,(
    ! [X13,X14,X15] :
      ( ~ r1_tarski(X13,k2_xboole_0(X14,X15))
      | r1_tarski(k4_xboole_0(X13,X14),X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).

fof(c_0_10,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_11,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_13,plain,(
    ! [X11,X12] : k2_xboole_0(X11,k4_xboole_0(X12,X11)) = k2_xboole_0(X11,X12) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

fof(c_0_14,plain,(
    ! [X18,X19] : r1_tarski(X18,k2_xboole_0(X18,X19)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_15,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_16,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ! [X3] :
                ( v1_relat_1(X3)
               => r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t52_relat_1])).

fof(c_0_19,plain,(
    ! [X22,X23,X24] :
      ( ~ v1_relat_1(X22)
      | ~ v1_relat_1(X23)
      | ~ v1_relat_1(X24)
      | ~ r1_tarski(X22,X23)
      | r1_tarski(k5_relat_1(X24,X22),k5_relat_1(X24,X23)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_relat_1])])])).

cnf(c_0_20,plain,
    ( r1_tarski(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_12])).

fof(c_0_22,plain,(
    ! [X20,X21] :
      ( ~ v1_relat_1(X20)
      | v1_relat_1(k4_xboole_0(X20,X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_relat_1])])).

fof(c_0_23,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_relat_1(esk2_0)
    & v1_relat_1(esk3_0)
    & ~ r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk3_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

cnf(c_0_24,plain,
    ( r1_tarski(k5_relat_1(X3,X1),k5_relat_1(X3,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_26,plain,
    ( v1_relat_1(k4_xboole_0(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,plain,
    ( r1_tarski(k5_relat_1(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))),k5_relat_1(X1,X3))
    | ~ v1_relat_1(k4_xboole_0(X2,k4_xboole_0(X2,X3)))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X3) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( v1_relat_1(k4_xboole_0(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

fof(c_0_30,plain,(
    ! [X8,X9,X10] :
      ( ~ r1_tarski(X8,X9)
      | ~ r1_tarski(X8,X10)
      | r1_tarski(X8,k3_xboole_0(X9,X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).

fof(c_0_31,plain,(
    ! [X16,X17] : k4_xboole_0(X16,k4_xboole_0(X16,X17)) = k3_xboole_0(X16,X17) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(k5_relat_1(X1,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,X2))),k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_21])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk1_0,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,X1))),k5_relat_1(esk1_0,X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_39,plain,
    ( r1_tarski(k5_relat_1(X1,k4_xboole_0(X2,X3)),k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_34]),c_0_26])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk1_0,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0))),k5_relat_1(esk1_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk1_0,k4_xboole_0(X1,X2)),k5_relat_1(esk1_0,X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_33])).

cnf(c_0_43,negated_conjecture,
    ( ~ r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk1_0,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0))),k4_xboole_0(X1,k4_xboole_0(X1,k5_relat_1(esk1_0,esk3_0))))
    | ~ r1_tarski(k5_relat_1(esk1_0,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0))),X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk1_0,k4_xboole_0(esk2_0,X1)),k5_relat_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_27])).

cnf(c_0_46,negated_conjecture,
    ( ~ r1_tarski(k5_relat_1(esk1_0,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0))),k4_xboole_0(k5_relat_1(esk1_0,esk2_0),k4_xboole_0(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk3_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_36]),c_0_36])).

cnf(c_0_47,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:16:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.61/0.83  # AutoSched0-Mode selected heuristic G_E___200_B02_F1_AE_CS_SP_PI_S0S
% 0.61/0.83  # and selection function SelectComplexG.
% 0.61/0.83  #
% 0.61/0.83  # Preprocessing time       : 0.027 s
% 0.61/0.83  
% 0.61/0.83  # Proof found!
% 0.61/0.83  # SZS status Theorem
% 0.61/0.83  # SZS output start CNFRefutation
% 0.61/0.83  fof(t43_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_xboole_0(X2,X3))=>r1_tarski(k4_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 0.61/0.83  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.61/0.83  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.61/0.83  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.61/0.83  fof(t52_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_relat_1)).
% 0.61/0.83  fof(t48_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>r1_tarski(k5_relat_1(X3,X1),k5_relat_1(X3,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_relat_1)).
% 0.61/0.83  fof(fc2_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k4_xboole_0(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_relat_1)).
% 0.61/0.83  fof(t19_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(X1,k3_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 0.61/0.83  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.61/0.83  fof(c_0_9, plain, ![X13, X14, X15]:(~r1_tarski(X13,k2_xboole_0(X14,X15))|r1_tarski(k4_xboole_0(X13,X14),X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).
% 0.61/0.83  fof(c_0_10, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.61/0.83  cnf(c_0_11, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.61/0.83  cnf(c_0_12, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.61/0.83  fof(c_0_13, plain, ![X11, X12]:k2_xboole_0(X11,k4_xboole_0(X12,X11))=k2_xboole_0(X11,X12), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.61/0.83  fof(c_0_14, plain, ![X18, X19]:r1_tarski(X18,k2_xboole_0(X18,X19)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.61/0.83  cnf(c_0_15, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k2_xboole_0(X3,X2))), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.61/0.83  cnf(c_0_16, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.61/0.83  cnf(c_0_17, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.61/0.83  fof(c_0_18, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3))))))), inference(assume_negation,[status(cth)],[t52_relat_1])).
% 0.61/0.83  fof(c_0_19, plain, ![X22, X23, X24]:(~v1_relat_1(X22)|(~v1_relat_1(X23)|(~v1_relat_1(X24)|(~r1_tarski(X22,X23)|r1_tarski(k5_relat_1(X24,X22),k5_relat_1(X24,X23)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_relat_1])])])).
% 0.61/0.83  cnf(c_0_20, plain, (r1_tarski(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X3)|~r1_tarski(X1,k2_xboole_0(X3,X2))), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.61/0.83  cnf(c_0_21, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_17, c_0_12])).
% 0.61/0.83  fof(c_0_22, plain, ![X20, X21]:(~v1_relat_1(X20)|v1_relat_1(k4_xboole_0(X20,X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_relat_1])])).
% 0.61/0.83  fof(c_0_23, negated_conjecture, (v1_relat_1(esk1_0)&(v1_relat_1(esk2_0)&(v1_relat_1(esk3_0)&~r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 0.61/0.83  cnf(c_0_24, plain, (r1_tarski(k5_relat_1(X3,X1),k5_relat_1(X3,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X3)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.61/0.83  cnf(c_0_25, plain, (r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.61/0.83  cnf(c_0_26, plain, (v1_relat_1(k4_xboole_0(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.61/0.83  cnf(c_0_27, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.61/0.83  cnf(c_0_28, plain, (r1_tarski(k5_relat_1(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))),k5_relat_1(X1,X3))|~v1_relat_1(k4_xboole_0(X2,k4_xboole_0(X2,X3)))|~v1_relat_1(X1)|~v1_relat_1(X3)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.61/0.83  cnf(c_0_29, negated_conjecture, (v1_relat_1(k4_xboole_0(esk2_0,X1))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.61/0.83  fof(c_0_30, plain, ![X8, X9, X10]:(~r1_tarski(X8,X9)|~r1_tarski(X8,X10)|r1_tarski(X8,k3_xboole_0(X9,X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).
% 0.61/0.83  fof(c_0_31, plain, ![X16, X17]:k4_xboole_0(X16,k4_xboole_0(X16,X17))=k3_xboole_0(X16,X17), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.61/0.83  cnf(c_0_32, negated_conjecture, (r1_tarski(k5_relat_1(X1,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,X2))),k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.61/0.83  cnf(c_0_33, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.61/0.83  cnf(c_0_34, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_11, c_0_21])).
% 0.61/0.83  cnf(c_0_35, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.61/0.83  cnf(c_0_36, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.61/0.83  cnf(c_0_37, negated_conjecture, (r1_tarski(k5_relat_1(esk1_0,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,X1))),k5_relat_1(esk1_0,X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.61/0.83  cnf(c_0_38, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.61/0.83  cnf(c_0_39, plain, (r1_tarski(k5_relat_1(X1,k4_xboole_0(X2,X3)),k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_34]), c_0_26])).
% 0.61/0.83  cnf(c_0_40, plain, (r1_tarski(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))|~r1_tarski(X1,X3)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_35, c_0_36])).
% 0.61/0.83  cnf(c_0_41, negated_conjecture, (r1_tarski(k5_relat_1(esk1_0,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0))),k5_relat_1(esk1_0,esk3_0))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.61/0.83  cnf(c_0_42, negated_conjecture, (r1_tarski(k5_relat_1(esk1_0,k4_xboole_0(X1,X2)),k5_relat_1(esk1_0,X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_39, c_0_33])).
% 0.61/0.83  cnf(c_0_43, negated_conjecture, (~r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.61/0.83  cnf(c_0_44, negated_conjecture, (r1_tarski(k5_relat_1(esk1_0,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0))),k4_xboole_0(X1,k4_xboole_0(X1,k5_relat_1(esk1_0,esk3_0))))|~r1_tarski(k5_relat_1(esk1_0,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0))),X1)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.61/0.83  cnf(c_0_45, negated_conjecture, (r1_tarski(k5_relat_1(esk1_0,k4_xboole_0(esk2_0,X1)),k5_relat_1(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_42, c_0_27])).
% 0.61/0.83  cnf(c_0_46, negated_conjecture, (~r1_tarski(k5_relat_1(esk1_0,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0))),k4_xboole_0(k5_relat_1(esk1_0,esk2_0),k4_xboole_0(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk3_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_36]), c_0_36])).
% 0.61/0.83  cnf(c_0_47, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46]), ['proof']).
% 0.61/0.83  # SZS output end CNFRefutation
% 0.61/0.83  # Proof object total steps             : 48
% 0.61/0.83  # Proof object clause steps            : 29
% 0.61/0.83  # Proof object formula steps           : 19
% 0.61/0.83  # Proof object conjectures             : 16
% 0.61/0.83  # Proof object clause conjectures      : 13
% 0.61/0.83  # Proof object formula conjectures     : 3
% 0.61/0.83  # Proof object initial clauses used    : 12
% 0.61/0.83  # Proof object initial formulas used   : 9
% 0.61/0.83  # Proof object generating inferences   : 15
% 0.61/0.83  # Proof object simplifying inferences  : 5
% 0.61/0.83  # Training examples: 0 positive, 0 negative
% 0.61/0.83  # Parsed axioms                        : 10
% 0.61/0.83  # Removed by relevancy pruning/SinE    : 0
% 0.61/0.83  # Initial clauses                      : 13
% 0.61/0.83  # Removed in clause preprocessing      : 1
% 0.61/0.83  # Initial clauses in saturation        : 12
% 0.61/0.83  # Processed clauses                    : 2516
% 0.61/0.83  # ...of these trivial                  : 143
% 0.61/0.83  # ...subsumed                          : 134
% 0.61/0.83  # ...remaining for further processing  : 2239
% 0.61/0.83  # Other redundant clauses eliminated   : 0
% 0.61/0.83  # Clauses deleted for lack of memory   : 0
% 0.61/0.83  # Backward-subsumed                    : 0
% 0.61/0.83  # Backward-rewritten                   : 40
% 0.61/0.83  # Generated clauses                    : 38539
% 0.61/0.83  # ...of the previous two non-trivial   : 37351
% 0.61/0.83  # Contextual simplify-reflections      : 2
% 0.61/0.83  # Paramodulations                      : 38539
% 0.61/0.83  # Factorizations                       : 0
% 0.61/0.83  # Equation resolutions                 : 0
% 0.61/0.83  # Propositional unsat checks           : 0
% 0.61/0.83  #    Propositional check models        : 0
% 0.61/0.83  #    Propositional check unsatisfiable : 0
% 0.61/0.83  #    Propositional clauses             : 0
% 0.61/0.83  #    Propositional clauses after purity: 0
% 0.61/0.83  #    Propositional unsat core size     : 0
% 0.61/0.83  #    Propositional preprocessing time  : 0.000
% 0.61/0.83  #    Propositional encoding time       : 0.000
% 0.61/0.83  #    Propositional solver time         : 0.000
% 0.61/0.83  #    Success case prop preproc time    : 0.000
% 0.61/0.83  #    Success case prop encoding time   : 0.000
% 0.61/0.83  #    Success case prop solver time     : 0.000
% 0.61/0.83  # Current number of processed clauses  : 2199
% 0.61/0.83  #    Positive orientable unit clauses  : 1391
% 0.61/0.83  #    Positive unorientable unit clauses: 1
% 0.61/0.83  #    Negative unit clauses             : 1
% 0.61/0.83  #    Non-unit-clauses                  : 806
% 0.61/0.83  # Current number of unprocessed clauses: 34803
% 0.61/0.83  # ...number of literals in the above   : 41419
% 0.61/0.83  # Current number of archived formulas  : 0
% 0.61/0.83  # Current number of archived clauses   : 41
% 0.61/0.83  # Clause-clause subsumption calls (NU) : 126450
% 0.61/0.83  # Rec. Clause-clause subsumption calls : 120217
% 0.61/0.83  # Non-unit clause-clause subsumptions  : 136
% 0.61/0.83  # Unit Clause-clause subsumption calls : 65100
% 0.61/0.83  # Rewrite failures with RHS unbound    : 0
% 0.61/0.83  # BW rewrite match attempts            : 55469
% 0.61/0.83  # BW rewrite match successes           : 42
% 0.61/0.83  # Condensation attempts                : 0
% 0.61/0.83  # Condensation successes               : 0
% 0.61/0.83  # Termbank termtop insertions          : 1132209
% 0.61/0.83  
% 0.61/0.83  # -------------------------------------------------
% 0.61/0.83  # User time                : 0.440 s
% 0.61/0.83  # System time              : 0.040 s
% 0.61/0.83  # Total time               : 0.480 s
% 0.61/0.83  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------

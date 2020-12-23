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
% DateTime   : Thu Dec  3 10:50:10 EST 2020

% Result     : Theorem 2.05s
% Output     : CNFRefutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 227 expanded)
%              Number of clauses        :   28 ( 109 expanded)
%              Number of leaves         :    9 (  54 expanded)
%              Depth                    :   12
%              Number of atoms          :  113 ( 565 expanded)
%              Number of equality atoms :   39 ( 231 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t127_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k8_relat_1(X1,k8_relat_1(X2,X3)) = k8_relat_1(k3_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_relat_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t130_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => k8_relat_1(X1,k8_relat_1(X2,X3)) = k8_relat_1(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_relat_1)).

fof(t2_tarski,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
        <=> r2_hidden(X3,X2) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(c_0_9,plain,(
    ! [X32,X33] : k1_setfam_1(k2_tarski(X32,X33)) = k3_xboole_0(X32,X33) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_10,plain,(
    ! [X26,X27] : k1_enumset1(X26,X26,X27) = k2_tarski(X26,X27) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_11,plain,(
    ! [X34,X35,X36] :
      ( ~ v1_relat_1(X36)
      | k8_relat_1(X34,k8_relat_1(X35,X36)) = k8_relat_1(k3_xboole_0(X34,X35),X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t127_relat_1])])).

cnf(c_0_12,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,plain,(
    ! [X24,X25] : k4_xboole_0(X24,k4_xboole_0(X24,X25)) = k3_xboole_0(X24,X25) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_15,plain,
    ( k8_relat_1(X2,k8_relat_1(X3,X1)) = k8_relat_1(k3_xboole_0(X2,X3),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( r1_tarski(X1,X2)
         => k8_relat_1(X1,k8_relat_1(X2,X3)) = k8_relat_1(X1,X3) ) ) ),
    inference(assume_negation,[status(cth)],[t130_relat_1])).

cnf(c_0_19,plain,
    ( k8_relat_1(X2,k8_relat_1(X3,X1)) = k8_relat_1(k1_setfam_1(k1_enumset1(X2,X2,X3)),X1)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_20,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_setfam_1(k1_enumset1(X1,X1,X2)) ),
    inference(rw,[status(thm)],[c_0_17,c_0_16])).

fof(c_0_21,negated_conjecture,
    ( v1_relat_1(esk7_0)
    & r1_tarski(esk5_0,esk6_0)
    & k8_relat_1(esk5_0,k8_relat_1(esk6_0,esk7_0)) != k8_relat_1(esk5_0,esk7_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

cnf(c_0_22,plain,
    ( k8_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3) = k8_relat_1(X1,k8_relat_1(X2,X3))
    | ~ v1_relat_1(X3) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_23,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_24,plain,(
    ! [X20,X21] :
      ( ( ~ r2_hidden(esk3_2(X20,X21),X20)
        | ~ r2_hidden(esk3_2(X20,X21),X21)
        | X20 = X21 )
      & ( r2_hidden(esk3_2(X20,X21),X20)
        | r2_hidden(esk3_2(X20,X21),X21)
        | X20 = X21 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).

cnf(c_0_25,negated_conjecture,
    ( k8_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),esk7_0) = k8_relat_1(X1,k8_relat_1(X2,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_26,plain,
    ( r2_hidden(esk3_2(X1,X2),X1)
    | r2_hidden(esk3_2(X1,X2),X2)
    | X1 = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_27,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17,X18] :
      ( ( r2_hidden(X14,X11)
        | ~ r2_hidden(X14,X13)
        | X13 != k4_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X14,X12)
        | ~ r2_hidden(X14,X13)
        | X13 != k4_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X15,X11)
        | r2_hidden(X15,X12)
        | r2_hidden(X15,X13)
        | X13 != k4_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk2_3(X16,X17,X18),X18)
        | ~ r2_hidden(esk2_3(X16,X17,X18),X16)
        | r2_hidden(esk2_3(X16,X17,X18),X17)
        | X18 = k4_xboole_0(X16,X17) )
      & ( r2_hidden(esk2_3(X16,X17,X18),X16)
        | r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k4_xboole_0(X16,X17) )
      & ( ~ r2_hidden(esk2_3(X16,X17,X18),X17)
        | r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k4_xboole_0(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_28,negated_conjecture,
    ( k8_relat_1(esk5_0,k8_relat_1(esk6_0,esk7_0)) != k8_relat_1(esk5_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( k8_relat_1(k4_xboole_0(X1,X2),esk7_0) = k8_relat_1(X1,k8_relat_1(X3,esk7_0))
    | r2_hidden(esk3_2(k4_xboole_0(X1,X3),X2),k4_xboole_0(X1,X3))
    | r2_hidden(esk3_2(k4_xboole_0(X1,X3),X2),X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_30,plain,(
    ! [X23] : k4_xboole_0(X23,k1_xboole_0) = X23 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_31,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_32,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk3_2(k4_xboole_0(esk5_0,esk6_0),X1),k4_xboole_0(esk5_0,esk6_0))
    | r2_hidden(esk3_2(k4_xboole_0(esk5_0,esk6_0),X1),X1)
    | k8_relat_1(k4_xboole_0(esk5_0,X1),esk7_0) != k8_relat_1(esk5_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_35,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_37,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk3_2(k4_xboole_0(esk5_0,esk6_0),k1_xboole_0),k4_xboole_0(esk5_0,esk6_0))
    | r2_hidden(esk3_2(k4_xboole_0(esk5_0,esk6_0),k1_xboole_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_41,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_36,c_0_35])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk3_2(k4_xboole_0(esk5_0,esk6_0),k1_xboole_0),k1_xboole_0)
    | r2_hidden(esk3_2(k4_xboole_0(esk5_0,esk6_0),k1_xboole_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_44,negated_conjecture,
    ( ~ r2_hidden(esk3_2(k4_xboole_0(esk5_0,esk6_0),k1_xboole_0),esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_40]),c_0_41])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk3_2(k4_xboole_0(esk5_0,esk6_0),k1_xboole_0),k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])).

cnf(c_0_46,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_45]),c_0_45])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:31:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 2.05/2.22  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 2.05/2.22  # and selection function SelectNegativeLiterals.
% 2.05/2.22  #
% 2.05/2.22  # Preprocessing time       : 0.028 s
% 2.05/2.22  # Presaturation interreduction done
% 2.05/2.22  
% 2.05/2.22  # Proof found!
% 2.05/2.22  # SZS status Theorem
% 2.05/2.22  # SZS output start CNFRefutation
% 2.05/2.22  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.05/2.22  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.05/2.22  fof(t127_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k8_relat_1(X1,k8_relat_1(X2,X3))=k8_relat_1(k3_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t127_relat_1)).
% 2.05/2.22  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.05/2.22  fof(t130_relat_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>k8_relat_1(X1,k8_relat_1(X2,X3))=k8_relat_1(X1,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t130_relat_1)).
% 2.05/2.22  fof(t2_tarski, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)<=>r2_hidden(X3,X2))=>X1=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 2.05/2.22  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.05/2.22  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.05/2.22  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.05/2.22  fof(c_0_9, plain, ![X32, X33]:k1_setfam_1(k2_tarski(X32,X33))=k3_xboole_0(X32,X33), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 2.05/2.22  fof(c_0_10, plain, ![X26, X27]:k1_enumset1(X26,X26,X27)=k2_tarski(X26,X27), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 2.05/2.22  fof(c_0_11, plain, ![X34, X35, X36]:(~v1_relat_1(X36)|k8_relat_1(X34,k8_relat_1(X35,X36))=k8_relat_1(k3_xboole_0(X34,X35),X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t127_relat_1])])).
% 2.05/2.22  cnf(c_0_12, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 2.05/2.22  cnf(c_0_13, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 2.05/2.22  fof(c_0_14, plain, ![X24, X25]:k4_xboole_0(X24,k4_xboole_0(X24,X25))=k3_xboole_0(X24,X25), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 2.05/2.22  cnf(c_0_15, plain, (k8_relat_1(X2,k8_relat_1(X3,X1))=k8_relat_1(k3_xboole_0(X2,X3),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 2.05/2.22  cnf(c_0_16, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_12, c_0_13])).
% 2.05/2.22  cnf(c_0_17, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.05/2.22  fof(c_0_18, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>k8_relat_1(X1,k8_relat_1(X2,X3))=k8_relat_1(X1,X3)))), inference(assume_negation,[status(cth)],[t130_relat_1])).
% 2.05/2.22  cnf(c_0_19, plain, (k8_relat_1(X2,k8_relat_1(X3,X1))=k8_relat_1(k1_setfam_1(k1_enumset1(X2,X2,X3)),X1)|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 2.05/2.22  cnf(c_0_20, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_setfam_1(k1_enumset1(X1,X1,X2))), inference(rw,[status(thm)],[c_0_17, c_0_16])).
% 2.05/2.22  fof(c_0_21, negated_conjecture, (v1_relat_1(esk7_0)&(r1_tarski(esk5_0,esk6_0)&k8_relat_1(esk5_0,k8_relat_1(esk6_0,esk7_0))!=k8_relat_1(esk5_0,esk7_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 2.05/2.22  cnf(c_0_22, plain, (k8_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)=k8_relat_1(X1,k8_relat_1(X2,X3))|~v1_relat_1(X3)), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 2.05/2.22  cnf(c_0_23, negated_conjecture, (v1_relat_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 2.05/2.22  fof(c_0_24, plain, ![X20, X21]:((~r2_hidden(esk3_2(X20,X21),X20)|~r2_hidden(esk3_2(X20,X21),X21)|X20=X21)&(r2_hidden(esk3_2(X20,X21),X20)|r2_hidden(esk3_2(X20,X21),X21)|X20=X21)), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).
% 2.05/2.22  cnf(c_0_25, negated_conjecture, (k8_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),esk7_0)=k8_relat_1(X1,k8_relat_1(X2,esk7_0))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 2.05/2.22  cnf(c_0_26, plain, (r2_hidden(esk3_2(X1,X2),X1)|r2_hidden(esk3_2(X1,X2),X2)|X1=X2), inference(split_conjunct,[status(thm)],[c_0_24])).
% 2.05/2.22  fof(c_0_27, plain, ![X11, X12, X13, X14, X15, X16, X17, X18]:((((r2_hidden(X14,X11)|~r2_hidden(X14,X13)|X13!=k4_xboole_0(X11,X12))&(~r2_hidden(X14,X12)|~r2_hidden(X14,X13)|X13!=k4_xboole_0(X11,X12)))&(~r2_hidden(X15,X11)|r2_hidden(X15,X12)|r2_hidden(X15,X13)|X13!=k4_xboole_0(X11,X12)))&((~r2_hidden(esk2_3(X16,X17,X18),X18)|(~r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X17))|X18=k4_xboole_0(X16,X17))&((r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k4_xboole_0(X16,X17))&(~r2_hidden(esk2_3(X16,X17,X18),X17)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k4_xboole_0(X16,X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 2.05/2.22  cnf(c_0_28, negated_conjecture, (k8_relat_1(esk5_0,k8_relat_1(esk6_0,esk7_0))!=k8_relat_1(esk5_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 2.05/2.22  cnf(c_0_29, negated_conjecture, (k8_relat_1(k4_xboole_0(X1,X2),esk7_0)=k8_relat_1(X1,k8_relat_1(X3,esk7_0))|r2_hidden(esk3_2(k4_xboole_0(X1,X3),X2),k4_xboole_0(X1,X3))|r2_hidden(esk3_2(k4_xboole_0(X1,X3),X2),X2)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 2.05/2.22  fof(c_0_30, plain, ![X23]:k4_xboole_0(X23,k1_xboole_0)=X23, inference(variable_rename,[status(thm)],[t3_boole])).
% 2.05/2.22  cnf(c_0_31, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 2.05/2.22  fof(c_0_32, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 2.05/2.22  cnf(c_0_33, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 2.05/2.22  cnf(c_0_34, negated_conjecture, (r2_hidden(esk3_2(k4_xboole_0(esk5_0,esk6_0),X1),k4_xboole_0(esk5_0,esk6_0))|r2_hidden(esk3_2(k4_xboole_0(esk5_0,esk6_0),X1),X1)|k8_relat_1(k4_xboole_0(esk5_0,X1),esk7_0)!=k8_relat_1(esk5_0,esk7_0)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 2.05/2.22  cnf(c_0_35, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_30])).
% 2.05/2.22  cnf(c_0_36, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_31])).
% 2.05/2.22  cnf(c_0_37, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 2.05/2.22  cnf(c_0_38, negated_conjecture, (r1_tarski(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 2.05/2.22  cnf(c_0_39, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_33])).
% 2.05/2.22  cnf(c_0_40, negated_conjecture, (r2_hidden(esk3_2(k4_xboole_0(esk5_0,esk6_0),k1_xboole_0),k4_xboole_0(esk5_0,esk6_0))|r2_hidden(esk3_2(k4_xboole_0(esk5_0,esk6_0),k1_xboole_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 2.05/2.22  cnf(c_0_41, plain, (~r2_hidden(X1,k1_xboole_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_36, c_0_35])).
% 2.05/2.22  cnf(c_0_42, negated_conjecture, (r2_hidden(X1,esk6_0)|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 2.05/2.22  cnf(c_0_43, negated_conjecture, (r2_hidden(esk3_2(k4_xboole_0(esk5_0,esk6_0),k1_xboole_0),k1_xboole_0)|r2_hidden(esk3_2(k4_xboole_0(esk5_0,esk6_0),k1_xboole_0),esk5_0)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 2.05/2.22  cnf(c_0_44, negated_conjecture, (~r2_hidden(esk3_2(k4_xboole_0(esk5_0,esk6_0),k1_xboole_0),esk6_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_40]), c_0_41])).
% 2.05/2.22  cnf(c_0_45, negated_conjecture, (r2_hidden(esk3_2(k4_xboole_0(esk5_0,esk6_0),k1_xboole_0),k1_xboole_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44])).
% 2.05/2.22  cnf(c_0_46, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_45]), c_0_45])]), ['proof']).
% 2.05/2.22  # SZS output end CNFRefutation
% 2.05/2.22  # Proof object total steps             : 47
% 2.05/2.22  # Proof object clause steps            : 28
% 2.05/2.22  # Proof object formula steps           : 19
% 2.05/2.22  # Proof object conjectures             : 15
% 2.05/2.22  # Proof object clause conjectures      : 12
% 2.05/2.22  # Proof object formula conjectures     : 3
% 2.05/2.22  # Proof object initial clauses used    : 12
% 2.05/2.22  # Proof object initial formulas used   : 9
% 2.05/2.22  # Proof object generating inferences   : 10
% 2.05/2.22  # Proof object simplifying inferences  : 10
% 2.05/2.22  # Training examples: 0 positive, 0 negative
% 2.05/2.22  # Parsed axioms                        : 10
% 2.05/2.22  # Removed by relevancy pruning/SinE    : 0
% 2.05/2.22  # Initial clauses                      : 21
% 2.05/2.22  # Removed in clause preprocessing      : 2
% 2.05/2.22  # Initial clauses in saturation        : 19
% 2.05/2.22  # Processed clauses                    : 4424
% 2.05/2.22  # ...of these trivial                  : 0
% 2.05/2.22  # ...subsumed                          : 2349
% 2.05/2.22  # ...remaining for further processing  : 2075
% 2.05/2.22  # Other redundant clauses eliminated   : 704
% 2.05/2.22  # Clauses deleted for lack of memory   : 0
% 2.05/2.22  # Backward-subsumed                    : 20
% 2.05/2.22  # Backward-rewritten                   : 2
% 2.05/2.22  # Generated clauses                    : 181460
% 2.05/2.22  # ...of the previous two non-trivial   : 180438
% 2.05/2.22  # Contextual simplify-reflections      : 99
% 2.05/2.22  # Paramodulations                      : 180662
% 2.05/2.22  # Factorizations                       : 76
% 2.05/2.22  # Equation resolutions                 : 722
% 2.05/2.22  # Propositional unsat checks           : 0
% 2.05/2.22  #    Propositional check models        : 0
% 2.05/2.22  #    Propositional check unsatisfiable : 0
% 2.05/2.22  #    Propositional clauses             : 0
% 2.05/2.22  #    Propositional clauses after purity: 0
% 2.05/2.22  #    Propositional unsat core size     : 0
% 2.05/2.22  #    Propositional preprocessing time  : 0.000
% 2.05/2.22  #    Propositional encoding time       : 0.000
% 2.05/2.22  #    Propositional solver time         : 0.000
% 2.05/2.22  #    Success case prop preproc time    : 0.000
% 2.05/2.22  #    Success case prop encoding time   : 0.000
% 2.05/2.22  #    Success case prop solver time     : 0.000
% 2.05/2.22  # Current number of processed clauses  : 2031
% 2.05/2.22  #    Positive orientable unit clauses  : 6
% 2.05/2.22  #    Positive unorientable unit clauses: 1
% 2.05/2.22  #    Negative unit clauses             : 10
% 2.05/2.22  #    Non-unit-clauses                  : 2014
% 2.05/2.22  # Current number of unprocessed clauses: 175993
% 2.05/2.22  # ...number of literals in the above   : 977755
% 2.05/2.22  # Current number of archived formulas  : 0
% 2.05/2.22  # Current number of archived clauses   : 43
% 2.05/2.22  # Clause-clause subsumption calls (NU) : 976828
% 2.05/2.22  # Rec. Clause-clause subsumption calls : 266707
% 2.05/2.22  # Non-unit clause-clause subsumptions  : 2443
% 2.05/2.22  # Unit Clause-clause subsumption calls : 206
% 2.05/2.22  # Rewrite failures with RHS unbound    : 0
% 2.05/2.22  # BW rewrite match attempts            : 2
% 2.05/2.22  # BW rewrite match successes           : 1
% 2.05/2.22  # Condensation attempts                : 0
% 2.05/2.22  # Condensation successes               : 0
% 2.05/2.22  # Termbank termtop insertions          : 5609382
% 2.05/2.23  
% 2.05/2.23  # -------------------------------------------------
% 2.05/2.23  # User time                : 1.783 s
% 2.05/2.23  # System time              : 0.095 s
% 2.05/2.23  # Total time               : 1.878 s
% 2.05/2.23  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------

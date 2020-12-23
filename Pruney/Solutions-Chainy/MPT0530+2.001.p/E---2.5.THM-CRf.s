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
% DateTime   : Thu Dec  3 10:50:09 EST 2020

% Result     : Theorem 4.04s
% Output     : CNFRefutation 4.04s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 240 expanded)
%              Number of clauses        :   31 ( 109 expanded)
%              Number of leaves         :    9 (  62 expanded)
%              Depth                    :   13
%              Number of atoms          :  109 ( 464 expanded)
%              Number of equality atoms :   43 ( 254 expanded)
%              Maximal formula depth    :   16 (   3 average)
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

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t130_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => k8_relat_1(X1,k8_relat_1(X2,X3)) = k8_relat_1(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_relat_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(c_0_9,plain,(
    ! [X34,X35] : k1_setfam_1(k2_tarski(X34,X35)) = k3_xboole_0(X34,X35) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_10,plain,(
    ! [X29,X30] : k1_enumset1(X29,X29,X30) = k2_tarski(X29,X30) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_11,plain,(
    ! [X36,X37,X38] :
      ( ~ v1_relat_1(X38)
      | k8_relat_1(X36,k8_relat_1(X37,X38)) = k8_relat_1(k3_xboole_0(X36,X37),X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t127_relat_1])])).

cnf(c_0_12,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,plain,(
    ! [X31,X32,X33] : k2_enumset1(X31,X31,X32,X33) = k1_enumset1(X31,X32,X33) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_15,plain,(
    ! [X27,X28] : k4_xboole_0(X27,k4_xboole_0(X27,X28)) = k3_xboole_0(X27,X28) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_16,plain,
    ( k8_relat_1(X2,k8_relat_1(X3,X1)) = k8_relat_1(k3_xboole_0(X2,X3),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( r1_tarski(X1,X2)
         => k8_relat_1(X1,k8_relat_1(X2,X3)) = k8_relat_1(X1,X3) ) ) ),
    inference(assume_negation,[status(cth)],[t130_relat_1])).

cnf(c_0_21,plain,
    ( k8_relat_1(X2,k8_relat_1(X3,X1)) = k8_relat_1(k1_setfam_1(k2_enumset1(X2,X2,X2,X3)),X1)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_17]),c_0_18])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_17]),c_0_18])).

fof(c_0_23,negated_conjecture,
    ( v1_relat_1(esk6_0)
    & r1_tarski(esk4_0,esk5_0)
    & k8_relat_1(esk4_0,k8_relat_1(esk5_0,esk6_0)) != k8_relat_1(esk4_0,esk6_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).

cnf(c_0_24,plain,
    ( k8_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3) = k8_relat_1(X1,k8_relat_1(X2,X3))
    | ~ v1_relat_1(X3) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_25,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_26,plain,(
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

fof(c_0_27,plain,(
    ! [X20] : k3_xboole_0(X20,X20) = X20 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_28,negated_conjecture,
    ( k8_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),esk6_0) = k8_relat_1(X1,k8_relat_1(X2,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_29,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_30,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_31,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_32,negated_conjecture,
    ( k8_relat_1(esk4_0,k8_relat_1(esk5_0,esk6_0)) != k8_relat_1(esk4_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,negated_conjecture,
    ( k8_relat_1(k4_xboole_0(X1,X2),esk6_0) = k8_relat_1(X1,k8_relat_1(X3,esk6_0))
    | r2_hidden(esk2_3(X1,X3,X2),X1)
    | r2_hidden(esk2_3(X1,X3,X2),X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_34,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_17]),c_0_18])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk2_3(esk4_0,esk5_0,X1),esk4_0)
    | r2_hidden(esk2_3(esk4_0,esk5_0,X1),X1)
    | k8_relat_1(k4_xboole_0(esk4_0,X1),esk6_0) != k8_relat_1(esk4_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_39,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_34,c_0_22])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk2_3(esk4_0,esk5_0,k4_xboole_0(esk4_0,esk4_0)),esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])).

cnf(c_0_43,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk2_3(esk4_0,esk5_0,k4_xboole_0(esk4_0,esk4_0)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_45,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_46,negated_conjecture,
    ( k4_xboole_0(esk4_0,esk5_0) = k4_xboole_0(esk4_0,esk4_0)
    | r2_hidden(esk2_3(esk4_0,esk5_0,k4_xboole_0(esk4_0,esk4_0)),k4_xboole_0(esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_47,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_45])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk2_3(esk4_0,esk5_0,k4_xboole_0(esk4_0,esk4_0)),k4_xboole_0(esk4_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_46]),c_0_39]),c_0_32])).

cnf(c_0_49,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_42])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:07:04 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  # Version: 2.5pre002
% 0.19/0.34  # No SInE strategy applied
% 0.19/0.34  # Trying AutoSched0 for 299 seconds
% 4.04/4.24  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 4.04/4.24  # and selection function SelectNegativeLiterals.
% 4.04/4.24  #
% 4.04/4.24  # Preprocessing time       : 0.027 s
% 4.04/4.24  # Presaturation interreduction done
% 4.04/4.24  
% 4.04/4.24  # Proof found!
% 4.04/4.24  # SZS status Theorem
% 4.04/4.24  # SZS output start CNFRefutation
% 4.04/4.24  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 4.04/4.24  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 4.04/4.24  fof(t127_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k8_relat_1(X1,k8_relat_1(X2,X3))=k8_relat_1(k3_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t127_relat_1)).
% 4.04/4.24  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 4.04/4.24  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.04/4.24  fof(t130_relat_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>k8_relat_1(X1,k8_relat_1(X2,X3))=k8_relat_1(X1,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t130_relat_1)).
% 4.04/4.24  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 4.04/4.24  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 4.04/4.24  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.04/4.24  fof(c_0_9, plain, ![X34, X35]:k1_setfam_1(k2_tarski(X34,X35))=k3_xboole_0(X34,X35), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 4.04/4.24  fof(c_0_10, plain, ![X29, X30]:k1_enumset1(X29,X29,X30)=k2_tarski(X29,X30), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 4.04/4.24  fof(c_0_11, plain, ![X36, X37, X38]:(~v1_relat_1(X38)|k8_relat_1(X36,k8_relat_1(X37,X38))=k8_relat_1(k3_xboole_0(X36,X37),X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t127_relat_1])])).
% 4.04/4.24  cnf(c_0_12, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 4.04/4.24  cnf(c_0_13, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 4.04/4.24  fof(c_0_14, plain, ![X31, X32, X33]:k2_enumset1(X31,X31,X32,X33)=k1_enumset1(X31,X32,X33), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 4.04/4.24  fof(c_0_15, plain, ![X27, X28]:k4_xboole_0(X27,k4_xboole_0(X27,X28))=k3_xboole_0(X27,X28), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 4.04/4.24  cnf(c_0_16, plain, (k8_relat_1(X2,k8_relat_1(X3,X1))=k8_relat_1(k3_xboole_0(X2,X3),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 4.04/4.24  cnf(c_0_17, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_12, c_0_13])).
% 4.04/4.24  cnf(c_0_18, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 4.04/4.24  cnf(c_0_19, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 4.04/4.24  fof(c_0_20, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>k8_relat_1(X1,k8_relat_1(X2,X3))=k8_relat_1(X1,X3)))), inference(assume_negation,[status(cth)],[t130_relat_1])).
% 4.04/4.24  cnf(c_0_21, plain, (k8_relat_1(X2,k8_relat_1(X3,X1))=k8_relat_1(k1_setfam_1(k2_enumset1(X2,X2,X2,X3)),X1)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16, c_0_17]), c_0_18])).
% 4.04/4.24  cnf(c_0_22, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_setfam_1(k2_enumset1(X1,X1,X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_17]), c_0_18])).
% 4.04/4.24  fof(c_0_23, negated_conjecture, (v1_relat_1(esk6_0)&(r1_tarski(esk4_0,esk5_0)&k8_relat_1(esk4_0,k8_relat_1(esk5_0,esk6_0))!=k8_relat_1(esk4_0,esk6_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).
% 4.04/4.24  cnf(c_0_24, plain, (k8_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)=k8_relat_1(X1,k8_relat_1(X2,X3))|~v1_relat_1(X3)), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 4.04/4.24  cnf(c_0_25, negated_conjecture, (v1_relat_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 4.04/4.24  fof(c_0_26, plain, ![X11, X12, X13, X14, X15, X16, X17, X18]:((((r2_hidden(X14,X11)|~r2_hidden(X14,X13)|X13!=k4_xboole_0(X11,X12))&(~r2_hidden(X14,X12)|~r2_hidden(X14,X13)|X13!=k4_xboole_0(X11,X12)))&(~r2_hidden(X15,X11)|r2_hidden(X15,X12)|r2_hidden(X15,X13)|X13!=k4_xboole_0(X11,X12)))&((~r2_hidden(esk2_3(X16,X17,X18),X18)|(~r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X17))|X18=k4_xboole_0(X16,X17))&((r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k4_xboole_0(X16,X17))&(~r2_hidden(esk2_3(X16,X17,X18),X17)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k4_xboole_0(X16,X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 4.04/4.24  fof(c_0_27, plain, ![X20]:k3_xboole_0(X20,X20)=X20, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 4.04/4.24  cnf(c_0_28, negated_conjecture, (k8_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),esk6_0)=k8_relat_1(X1,k8_relat_1(X2,esk6_0))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 4.04/4.24  cnf(c_0_29, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 4.04/4.24  cnf(c_0_30, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_27])).
% 4.04/4.24  fof(c_0_31, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 4.04/4.24  cnf(c_0_32, negated_conjecture, (k8_relat_1(esk4_0,k8_relat_1(esk5_0,esk6_0))!=k8_relat_1(esk4_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 4.04/4.24  cnf(c_0_33, negated_conjecture, (k8_relat_1(k4_xboole_0(X1,X2),esk6_0)=k8_relat_1(X1,k8_relat_1(X3,esk6_0))|r2_hidden(esk2_3(X1,X3,X2),X1)|r2_hidden(esk2_3(X1,X3,X2),X2)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 4.04/4.24  cnf(c_0_34, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_17]), c_0_18])).
% 4.04/4.24  cnf(c_0_35, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 4.04/4.24  cnf(c_0_36, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 4.04/4.24  cnf(c_0_37, negated_conjecture, (r1_tarski(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 4.04/4.24  cnf(c_0_38, negated_conjecture, (r2_hidden(esk2_3(esk4_0,esk5_0,X1),esk4_0)|r2_hidden(esk2_3(esk4_0,esk5_0,X1),X1)|k8_relat_1(k4_xboole_0(esk4_0,X1),esk6_0)!=k8_relat_1(esk4_0,esk6_0)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 4.04/4.24  cnf(c_0_39, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X1))=X1), inference(rw,[status(thm)],[c_0_34, c_0_22])).
% 4.04/4.24  cnf(c_0_40, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_35])).
% 4.04/4.24  cnf(c_0_41, negated_conjecture, (r2_hidden(X1,esk5_0)|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 4.04/4.24  cnf(c_0_42, negated_conjecture, (r2_hidden(esk2_3(esk4_0,esk5_0,k4_xboole_0(esk4_0,esk4_0)),esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40])).
% 4.04/4.24  cnf(c_0_43, plain, (r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 4.04/4.24  cnf(c_0_44, negated_conjecture, (r2_hidden(esk2_3(esk4_0,esk5_0,k4_xboole_0(esk4_0,esk4_0)),esk5_0)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 4.04/4.24  cnf(c_0_45, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 4.04/4.24  cnf(c_0_46, negated_conjecture, (k4_xboole_0(esk4_0,esk5_0)=k4_xboole_0(esk4_0,esk4_0)|r2_hidden(esk2_3(esk4_0,esk5_0,k4_xboole_0(esk4_0,esk4_0)),k4_xboole_0(esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 4.04/4.24  cnf(c_0_47, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_45])).
% 4.04/4.24  cnf(c_0_48, negated_conjecture, (r2_hidden(esk2_3(esk4_0,esk5_0,k4_xboole_0(esk4_0,esk4_0)),k4_xboole_0(esk4_0,esk4_0))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_46]), c_0_39]), c_0_32])).
% 4.04/4.24  cnf(c_0_49, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_42])]), ['proof']).
% 4.04/4.24  # SZS output end CNFRefutation
% 4.04/4.24  # Proof object total steps             : 50
% 4.04/4.24  # Proof object clause steps            : 31
% 4.04/4.24  # Proof object formula steps           : 19
% 4.04/4.24  # Proof object conjectures             : 15
% 4.04/4.24  # Proof object clause conjectures      : 12
% 4.04/4.24  # Proof object formula conjectures     : 3
% 4.04/4.24  # Proof object initial clauses used    : 14
% 4.04/4.24  # Proof object initial formulas used   : 9
% 4.04/4.24  # Proof object generating inferences   : 9
% 4.04/4.24  # Proof object simplifying inferences  : 16
% 4.04/4.24  # Training examples: 0 positive, 0 negative
% 4.04/4.24  # Parsed axioms                        : 12
% 4.04/4.24  # Removed by relevancy pruning/SinE    : 0
% 4.04/4.24  # Initial clauses                      : 24
% 4.04/4.24  # Removed in clause preprocessing      : 3
% 4.04/4.24  # Initial clauses in saturation        : 21
% 4.04/4.24  # Processed clauses                    : 6207
% 4.04/4.24  # ...of these trivial                  : 156
% 4.04/4.24  # ...subsumed                          : 3513
% 4.04/4.24  # ...remaining for further processing  : 2538
% 4.04/4.24  # Other redundant clauses eliminated   : 14326
% 4.04/4.24  # Clauses deleted for lack of memory   : 0
% 4.04/4.24  # Backward-subsumed                    : 283
% 4.04/4.24  # Backward-rewritten                   : 354
% 4.04/4.24  # Generated clauses                    : 629485
% 4.04/4.24  # ...of the previous two non-trivial   : 505557
% 4.04/4.24  # Contextual simplify-reflections      : 62
% 4.04/4.24  # Paramodulations                      : 615028
% 4.04/4.24  # Factorizations                       : 74
% 4.04/4.24  # Equation resolutions                 : 14383
% 4.04/4.24  # Propositional unsat checks           : 0
% 4.04/4.24  #    Propositional check models        : 0
% 4.04/4.24  #    Propositional check unsatisfiable : 0
% 4.04/4.24  #    Propositional clauses             : 0
% 4.04/4.24  #    Propositional clauses after purity: 0
% 4.04/4.24  #    Propositional unsat core size     : 0
% 4.04/4.24  #    Propositional preprocessing time  : 0.000
% 4.04/4.24  #    Propositional encoding time       : 0.000
% 4.04/4.24  #    Propositional solver time         : 0.000
% 4.04/4.24  #    Success case prop preproc time    : 0.000
% 4.04/4.24  #    Success case prop encoding time   : 0.000
% 4.04/4.24  #    Success case prop solver time     : 0.000
% 4.04/4.24  # Current number of processed clauses  : 1876
% 4.04/4.24  #    Positive orientable unit clauses  : 46
% 4.04/4.24  #    Positive unorientable unit clauses: 0
% 4.04/4.24  #    Negative unit clauses             : 1
% 4.04/4.24  #    Non-unit-clauses                  : 1829
% 4.04/4.24  # Current number of unprocessed clauses: 498332
% 4.04/4.24  # ...number of literals in the above   : 2519858
% 4.04/4.24  # Current number of archived formulas  : 0
% 4.04/4.24  # Current number of archived clauses   : 660
% 4.04/4.24  # Clause-clause subsumption calls (NU) : 1278675
% 4.04/4.24  # Rec. Clause-clause subsumption calls : 375271
% 4.04/4.24  # Non-unit clause-clause subsumptions  : 3817
% 4.04/4.24  # Unit Clause-clause subsumption calls : 13793
% 4.04/4.24  # Rewrite failures with RHS unbound    : 0
% 4.04/4.24  # BW rewrite match attempts            : 119
% 4.04/4.24  # BW rewrite match successes           : 38
% 4.04/4.24  # Condensation attempts                : 0
% 4.04/4.24  # Condensation successes               : 0
% 4.04/4.24  # Termbank termtop insertions          : 14628267
% 4.04/4.26  
% 4.04/4.26  # -------------------------------------------------
% 4.04/4.26  # User time                : 3.734 s
% 4.04/4.26  # System time              : 0.186 s
% 4.04/4.26  # Total time               : 3.920 s
% 4.04/4.26  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------

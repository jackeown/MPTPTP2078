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
% DateTime   : Thu Dec  3 10:52:47 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   37 ( 121 expanded)
%              Number of clauses        :   22 (  51 expanded)
%              Number of leaves         :    7 (  30 expanded)
%              Depth                    :   11
%              Number of atoms          :   74 ( 294 expanded)
%              Number of equality atoms :   11 (  37 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t88_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k7_relat_1(X2,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

fof(t98_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,k1_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

fof(t219_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(X1,k7_relat_1(X2,k1_relat_1(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t219_relat_1)).

fof(t108_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k3_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t105_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( r1_tarski(X2,X3)
           => r1_tarski(k7_relat_1(X2,X1),k7_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_relat_1)).

fof(c_0_7,plain,(
    ! [X14,X15] :
      ( ~ v1_relat_1(X15)
      | r1_tarski(k7_relat_1(X15,X14),X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_relat_1])])).

fof(c_0_8,plain,(
    ! [X16] :
      ( ~ v1_relat_1(X16)
      | k7_relat_1(X16,k1_relat_1(X16)) = X16 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_relat_1])])).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ( r1_tarski(X1,X2)
            <=> r1_tarski(X1,k7_relat_1(X2,k1_relat_1(X1))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t219_relat_1])).

cnf(c_0_10,plain,
    ( r1_tarski(k7_relat_1(X1,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( k7_relat_1(X1,k1_relat_1(X1)) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_12,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_relat_1(esk2_0)
    & ( ~ r1_tarski(esk1_0,esk2_0)
      | ~ r1_tarski(esk1_0,k7_relat_1(esk2_0,k1_relat_1(esk1_0))) )
    & ( r1_tarski(esk1_0,esk2_0)
      | r1_tarski(esk1_0,k7_relat_1(esk2_0,k1_relat_1(esk1_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_13,plain,(
    ! [X6,X7,X8] :
      ( ~ r1_tarski(X6,X7)
      | r1_tarski(k3_xboole_0(X6,X8),X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t108_xboole_1])])).

cnf(c_0_14,plain,
    ( r1_tarski(X1,X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( r1_tarski(k3_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( r1_tarski(esk2_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_18,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk2_0,X1),esk2_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

fof(c_0_19,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_20,plain,(
    ! [X9,X10] :
      ( ~ r1_tarski(X9,X10)
      | k3_xboole_0(X9,X10) = X9 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_21,negated_conjecture,
    ( r1_tarski(k3_xboole_0(k3_xboole_0(esk2_0,X1),X2),esk2_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_18])).

cnf(c_0_22,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( r1_tarski(k3_xboole_0(X1,k3_xboole_0(esk2_0,X2)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_25,plain,
    ( k3_xboole_0(X1,k7_relat_1(X1,X2)) = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_10]),c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0)
    | r1_tarski(esk1_0,k7_relat_1(esk2_0,k1_relat_1(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_27,plain,(
    ! [X11,X12,X13] :
      ( ~ v1_relat_1(X12)
      | ~ v1_relat_1(X13)
      | ~ r1_tarski(X12,X13)
      | r1_tarski(k7_relat_1(X12,X11),k7_relat_1(X13,X11)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t105_relat_1])])])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(k3_xboole_0(X1,k7_relat_1(esk2_0,X2)),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_15])])).

cnf(c_0_29,negated_conjecture,
    ( k3_xboole_0(esk1_0,k7_relat_1(esk2_0,k1_relat_1(esk1_0))) = esk1_0
    | r1_tarski(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_26])).

cnf(c_0_30,plain,
    ( r1_tarski(k7_relat_1(X1,X3),k7_relat_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_32,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_33,negated_conjecture,
    ( ~ r1_tarski(esk1_0,esk2_0)
    | ~ r1_tarski(esk1_0,k7_relat_1(esk2_0,k1_relat_1(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(k7_relat_1(esk1_0,X1),k7_relat_1(esk2_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_15]),c_0_32])])).

cnf(c_0_35,negated_conjecture,
    ( ~ r1_tarski(esk1_0,k7_relat_1(esk2_0,k1_relat_1(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_31])])).

cnf(c_0_36,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_11]),c_0_32])]),c_0_35]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:16:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic H_____047_C18_F1_PI_AE_R8_CS_SP_S2S
% 0.20/0.38  # and selection function SelectNewComplexAHP.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.026 s
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(t88_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k7_relat_1(X2,X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 0.20/0.38  fof(t98_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k7_relat_1(X1,k1_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 0.20/0.38  fof(t219_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)<=>r1_tarski(X1,k7_relat_1(X2,k1_relat_1(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t219_relat_1)).
% 0.20/0.38  fof(t108_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(k3_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_xboole_1)).
% 0.20/0.38  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.20/0.38  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.20/0.38  fof(t105_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(r1_tarski(X2,X3)=>r1_tarski(k7_relat_1(X2,X1),k7_relat_1(X3,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_relat_1)).
% 0.20/0.38  fof(c_0_7, plain, ![X14, X15]:(~v1_relat_1(X15)|r1_tarski(k7_relat_1(X15,X14),X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_relat_1])])).
% 0.20/0.38  fof(c_0_8, plain, ![X16]:(~v1_relat_1(X16)|k7_relat_1(X16,k1_relat_1(X16))=X16), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_relat_1])])).
% 0.20/0.38  fof(c_0_9, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)<=>r1_tarski(X1,k7_relat_1(X2,k1_relat_1(X1))))))), inference(assume_negation,[status(cth)],[t219_relat_1])).
% 0.20/0.38  cnf(c_0_10, plain, (r1_tarski(k7_relat_1(X1,X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.38  cnf(c_0_11, plain, (k7_relat_1(X1,k1_relat_1(X1))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.38  fof(c_0_12, negated_conjecture, (v1_relat_1(esk1_0)&(v1_relat_1(esk2_0)&((~r1_tarski(esk1_0,esk2_0)|~r1_tarski(esk1_0,k7_relat_1(esk2_0,k1_relat_1(esk1_0))))&(r1_tarski(esk1_0,esk2_0)|r1_tarski(esk1_0,k7_relat_1(esk2_0,k1_relat_1(esk1_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.20/0.38  fof(c_0_13, plain, ![X6, X7, X8]:(~r1_tarski(X6,X7)|r1_tarski(k3_xboole_0(X6,X8),X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t108_xboole_1])])).
% 0.20/0.38  cnf(c_0_14, plain, (r1_tarski(X1,X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.20/0.38  cnf(c_0_15, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  cnf(c_0_16, plain, (r1_tarski(k3_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  cnf(c_0_17, negated_conjecture, (r1_tarski(esk2_0,esk2_0)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.20/0.38  cnf(c_0_18, negated_conjecture, (r1_tarski(k3_xboole_0(esk2_0,X1),esk2_0)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.20/0.38  fof(c_0_19, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.20/0.38  fof(c_0_20, plain, ![X9, X10]:(~r1_tarski(X9,X10)|k3_xboole_0(X9,X10)=X9), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.20/0.38  cnf(c_0_21, negated_conjecture, (r1_tarski(k3_xboole_0(k3_xboole_0(esk2_0,X1),X2),esk2_0)), inference(spm,[status(thm)],[c_0_16, c_0_18])).
% 0.20/0.38  cnf(c_0_22, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.38  cnf(c_0_23, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.38  cnf(c_0_24, negated_conjecture, (r1_tarski(k3_xboole_0(X1,k3_xboole_0(esk2_0,X2)),esk2_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.38  cnf(c_0_25, plain, (k3_xboole_0(X1,k7_relat_1(X1,X2))=k7_relat_1(X1,X2)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_10]), c_0_22])).
% 0.20/0.38  cnf(c_0_26, negated_conjecture, (r1_tarski(esk1_0,esk2_0)|r1_tarski(esk1_0,k7_relat_1(esk2_0,k1_relat_1(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  fof(c_0_27, plain, ![X11, X12, X13]:(~v1_relat_1(X12)|(~v1_relat_1(X13)|(~r1_tarski(X12,X13)|r1_tarski(k7_relat_1(X12,X11),k7_relat_1(X13,X11))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t105_relat_1])])])).
% 0.20/0.38  cnf(c_0_28, negated_conjecture, (r1_tarski(k3_xboole_0(X1,k7_relat_1(esk2_0,X2)),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_15])])).
% 0.20/0.38  cnf(c_0_29, negated_conjecture, (k3_xboole_0(esk1_0,k7_relat_1(esk2_0,k1_relat_1(esk1_0)))=esk1_0|r1_tarski(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_23, c_0_26])).
% 0.20/0.38  cnf(c_0_30, plain, (r1_tarski(k7_relat_1(X1,X3),k7_relat_1(X2,X3))|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.38  cnf(c_0_31, negated_conjecture, (r1_tarski(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.20/0.38  cnf(c_0_32, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  cnf(c_0_33, negated_conjecture, (~r1_tarski(esk1_0,esk2_0)|~r1_tarski(esk1_0,k7_relat_1(esk2_0,k1_relat_1(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  cnf(c_0_34, negated_conjecture, (r1_tarski(k7_relat_1(esk1_0,X1),k7_relat_1(esk2_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_15]), c_0_32])])).
% 0.20/0.38  cnf(c_0_35, negated_conjecture, (~r1_tarski(esk1_0,k7_relat_1(esk2_0,k1_relat_1(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_31])])).
% 0.20/0.38  cnf(c_0_36, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_11]), c_0_32])]), c_0_35]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 37
% 0.20/0.38  # Proof object clause steps            : 22
% 0.20/0.38  # Proof object formula steps           : 15
% 0.20/0.38  # Proof object conjectures             : 17
% 0.20/0.38  # Proof object clause conjectures      : 14
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 10
% 0.20/0.38  # Proof object initial formulas used   : 7
% 0.20/0.38  # Proof object generating inferences   : 11
% 0.20/0.38  # Proof object simplifying inferences  : 11
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 7
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 10
% 0.20/0.38  # Removed in clause preprocessing      : 0
% 0.20/0.38  # Initial clauses in saturation        : 10
% 0.20/0.38  # Processed clauses                    : 183
% 0.20/0.38  # ...of these trivial                  : 50
% 0.20/0.38  # ...subsumed                          : 56
% 0.20/0.38  # ...remaining for further processing  : 77
% 0.20/0.38  # Other redundant clauses eliminated   : 0
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 0
% 0.20/0.38  # Backward-rewritten                   : 4
% 0.20/0.38  # Generated clauses                    : 664
% 0.20/0.38  # ...of the previous two non-trivial   : 390
% 0.20/0.38  # Contextual simplify-reflections      : 0
% 0.20/0.38  # Paramodulations                      : 664
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 0
% 0.20/0.38  # Propositional unsat checks           : 0
% 0.20/0.38  #    Propositional check models        : 0
% 0.20/0.38  #    Propositional check unsatisfiable : 0
% 0.20/0.38  #    Propositional clauses             : 0
% 0.20/0.38  #    Propositional clauses after purity: 0
% 0.20/0.38  #    Propositional unsat core size     : 0
% 0.20/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 73
% 0.20/0.38  #    Positive orientable unit clauses  : 41
% 0.20/0.38  #    Positive unorientable unit clauses: 1
% 0.20/0.38  #    Negative unit clauses             : 1
% 0.20/0.38  #    Non-unit-clauses                  : 30
% 0.20/0.38  # Current number of unprocessed clauses: 213
% 0.20/0.38  # ...number of literals in the above   : 423
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 4
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 455
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 452
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 56
% 0.20/0.38  # Unit Clause-clause subsumption calls : 22
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 5
% 0.20/0.38  # BW rewrite match successes           : 1
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 6666
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.034 s
% 0.20/0.38  # System time              : 0.003 s
% 0.20/0.38  # Total time               : 0.038 s
% 0.20/0.38  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------

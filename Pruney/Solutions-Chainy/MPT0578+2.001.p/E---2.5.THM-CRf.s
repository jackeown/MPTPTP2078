%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:51:53 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   39 ( 108 expanded)
%              Number of clauses        :   24 (  45 expanded)
%              Number of leaves         :    7 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :   71 ( 239 expanded)
%              Number of equality atoms :   33 (  89 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t182_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(t168_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(X2,X1) = k10_relat_1(X2,k3_xboole_0(k2_relat_1(X2),X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t169_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(t181_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => k10_relat_1(k5_relat_1(X2,X3),X1) = k10_relat_1(X2,k10_relat_1(X3,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t181_relat_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2)) ) ) ),
    inference(assume_negation,[status(cth)],[t182_relat_1])).

fof(c_0_8,plain,(
    ! [X10,X11] :
      ( ~ v1_relat_1(X11)
      | k10_relat_1(X11,X10) = k10_relat_1(X11,k3_xboole_0(k2_relat_1(X11),X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t168_relat_1])])).

fof(c_0_9,plain,(
    ! [X6,X7] : k1_setfam_1(k2_tarski(X6,X7)) = k3_xboole_0(X6,X7) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_10,plain,(
    ! [X12] :
      ( ~ v1_relat_1(X12)
      | k10_relat_1(X12,k2_relat_1(X12)) = k1_relat_1(X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).

fof(c_0_11,plain,(
    ! [X8,X9] :
      ( ~ v1_relat_1(X8)
      | ~ v1_relat_1(X9)
      | v1_relat_1(k5_relat_1(X8,X9)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

fof(c_0_12,plain,(
    ! [X13,X14,X15] :
      ( ~ v1_relat_1(X14)
      | ~ v1_relat_1(X15)
      | k10_relat_1(k5_relat_1(X14,X15),X13) = k10_relat_1(X14,k10_relat_1(X15,X13)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t181_relat_1])])])).

fof(c_0_13,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_relat_1(esk2_0)
    & k1_relat_1(k5_relat_1(esk1_0,esk2_0)) != k10_relat_1(esk1_0,k1_relat_1(esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

cnf(c_0_14,plain,
    ( k10_relat_1(X1,X2) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( k10_relat_1(k5_relat_1(X1,X2),X3) = k10_relat_1(X1,k10_relat_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( k10_relat_1(X1,X2) = k10_relat_1(X1,k1_setfam_1(k2_tarski(k2_relat_1(X1),X2)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(k5_relat_1(X1,X2),k2_relat_1(k5_relat_1(X1,X2)))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( k10_relat_1(k5_relat_1(esk1_0,X1),X2) = k10_relat_1(esk1_0,k10_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_24,plain,
    ( k10_relat_1(k5_relat_1(X1,X2),k1_setfam_1(k2_tarski(k2_relat_1(k5_relat_1(X1,X2)),X3))) = k10_relat_1(k5_relat_1(X1,X2),X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_17])).

fof(c_0_25,plain,(
    ! [X4,X5] : k2_tarski(X4,X5) = k2_tarski(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_26,negated_conjecture,
    ( k1_relat_1(k5_relat_1(esk1_0,esk2_0)) != k10_relat_1(esk1_0,k1_relat_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_27,negated_conjecture,
    ( k1_relat_1(esk2_0) = k10_relat_1(esk2_0,k2_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( k1_relat_1(k5_relat_1(esk1_0,X1)) = k10_relat_1(k5_relat_1(esk1_0,X1),k2_relat_1(k5_relat_1(esk1_0,X1)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_19])).

cnf(c_0_29,negated_conjecture,
    ( k10_relat_1(k5_relat_1(esk1_0,esk2_0),X1) = k10_relat_1(esk1_0,k10_relat_1(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_21])).

cnf(c_0_30,negated_conjecture,
    ( k10_relat_1(k5_relat_1(esk1_0,X1),k1_setfam_1(k2_tarski(k2_relat_1(k5_relat_1(esk1_0,X1)),X2))) = k10_relat_1(k5_relat_1(esk1_0,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_19])).

cnf(c_0_31,negated_conjecture,
    ( k10_relat_1(esk2_0,k1_setfam_1(k2_tarski(k2_relat_1(esk2_0),X1))) = k10_relat_1(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_32,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( k1_relat_1(k5_relat_1(esk1_0,esk2_0)) != k10_relat_1(esk1_0,k10_relat_1(esk2_0,k2_relat_1(esk2_0))) ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( k1_relat_1(k5_relat_1(esk1_0,esk2_0)) = k10_relat_1(esk1_0,k10_relat_1(esk2_0,k2_relat_1(k5_relat_1(esk1_0,esk2_0)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_21]),c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( k10_relat_1(esk1_0,k10_relat_1(esk2_0,k1_setfam_1(k2_tarski(k2_relat_1(k5_relat_1(esk1_0,esk2_0)),X1)))) = k10_relat_1(esk1_0,k10_relat_1(esk2_0,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_21]),c_0_29]),c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( k10_relat_1(esk2_0,k1_setfam_1(k2_tarski(X1,k2_relat_1(esk2_0)))) = k10_relat_1(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( k10_relat_1(esk1_0,k10_relat_1(esk2_0,k2_relat_1(k5_relat_1(esk1_0,esk2_0)))) != k10_relat_1(esk1_0,k10_relat_1(esk2_0,k2_relat_1(esk2_0))) ),
    inference(rw,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_38,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:37:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.47  # AutoSched0-Mode selected heuristic G_E___208_B00_00_F1_SE_CS_SP_PS_S070I
% 0.19/0.47  # and selection function SelectVGNonCR.
% 0.19/0.47  #
% 0.19/0.47  # Preprocessing time       : 0.026 s
% 0.19/0.47  # Presaturation interreduction done
% 0.19/0.47  
% 0.19/0.47  # Proof found!
% 0.19/0.47  # SZS status Theorem
% 0.19/0.47  # SZS output start CNFRefutation
% 0.19/0.47  fof(t182_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 0.19/0.47  fof(t168_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k10_relat_1(X2,X1)=k10_relat_1(X2,k3_xboole_0(k2_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t168_relat_1)).
% 0.19/0.47  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.19/0.47  fof(t169_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 0.19/0.47  fof(dt_k5_relat_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_relat_1(X2))=>v1_relat_1(k5_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 0.19/0.47  fof(t181_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>k10_relat_1(k5_relat_1(X2,X3),X1)=k10_relat_1(X2,k10_relat_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t181_relat_1)).
% 0.19/0.47  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.19/0.47  fof(c_0_7, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2))))), inference(assume_negation,[status(cth)],[t182_relat_1])).
% 0.19/0.47  fof(c_0_8, plain, ![X10, X11]:(~v1_relat_1(X11)|k10_relat_1(X11,X10)=k10_relat_1(X11,k3_xboole_0(k2_relat_1(X11),X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t168_relat_1])])).
% 0.19/0.47  fof(c_0_9, plain, ![X6, X7]:k1_setfam_1(k2_tarski(X6,X7))=k3_xboole_0(X6,X7), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.19/0.47  fof(c_0_10, plain, ![X12]:(~v1_relat_1(X12)|k10_relat_1(X12,k2_relat_1(X12))=k1_relat_1(X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).
% 0.19/0.47  fof(c_0_11, plain, ![X8, X9]:(~v1_relat_1(X8)|~v1_relat_1(X9)|v1_relat_1(k5_relat_1(X8,X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).
% 0.19/0.47  fof(c_0_12, plain, ![X13, X14, X15]:(~v1_relat_1(X14)|(~v1_relat_1(X15)|k10_relat_1(k5_relat_1(X14,X15),X13)=k10_relat_1(X14,k10_relat_1(X15,X13)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t181_relat_1])])])).
% 0.19/0.47  fof(c_0_13, negated_conjecture, (v1_relat_1(esk1_0)&(v1_relat_1(esk2_0)&k1_relat_1(k5_relat_1(esk1_0,esk2_0))!=k10_relat_1(esk1_0,k1_relat_1(esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.19/0.47  cnf(c_0_14, plain, (k10_relat_1(X1,X2)=k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.47  cnf(c_0_15, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.47  cnf(c_0_16, plain, (k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.47  cnf(c_0_17, plain, (v1_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.47  cnf(c_0_18, plain, (k10_relat_1(k5_relat_1(X1,X2),X3)=k10_relat_1(X1,k10_relat_1(X2,X3))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.47  cnf(c_0_19, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.47  cnf(c_0_20, plain, (k10_relat_1(X1,X2)=k10_relat_1(X1,k1_setfam_1(k2_tarski(k2_relat_1(X1),X2)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.19/0.47  cnf(c_0_21, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.47  cnf(c_0_22, plain, (k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(k5_relat_1(X1,X2),k2_relat_1(k5_relat_1(X1,X2)))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.19/0.47  cnf(c_0_23, negated_conjecture, (k10_relat_1(k5_relat_1(esk1_0,X1),X2)=k10_relat_1(esk1_0,k10_relat_1(X1,X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.19/0.47  cnf(c_0_24, plain, (k10_relat_1(k5_relat_1(X1,X2),k1_setfam_1(k2_tarski(k2_relat_1(k5_relat_1(X1,X2)),X3)))=k10_relat_1(k5_relat_1(X1,X2),X3)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_20, c_0_17])).
% 0.19/0.47  fof(c_0_25, plain, ![X4, X5]:k2_tarski(X4,X5)=k2_tarski(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.19/0.47  cnf(c_0_26, negated_conjecture, (k1_relat_1(k5_relat_1(esk1_0,esk2_0))!=k10_relat_1(esk1_0,k1_relat_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.47  cnf(c_0_27, negated_conjecture, (k1_relat_1(esk2_0)=k10_relat_1(esk2_0,k2_relat_1(esk2_0))), inference(spm,[status(thm)],[c_0_16, c_0_21])).
% 0.19/0.47  cnf(c_0_28, negated_conjecture, (k1_relat_1(k5_relat_1(esk1_0,X1))=k10_relat_1(k5_relat_1(esk1_0,X1),k2_relat_1(k5_relat_1(esk1_0,X1)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_22, c_0_19])).
% 0.19/0.47  cnf(c_0_29, negated_conjecture, (k10_relat_1(k5_relat_1(esk1_0,esk2_0),X1)=k10_relat_1(esk1_0,k10_relat_1(esk2_0,X1))), inference(spm,[status(thm)],[c_0_23, c_0_21])).
% 0.19/0.47  cnf(c_0_30, negated_conjecture, (k10_relat_1(k5_relat_1(esk1_0,X1),k1_setfam_1(k2_tarski(k2_relat_1(k5_relat_1(esk1_0,X1)),X2)))=k10_relat_1(k5_relat_1(esk1_0,X1),X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_24, c_0_19])).
% 0.19/0.47  cnf(c_0_31, negated_conjecture, (k10_relat_1(esk2_0,k1_setfam_1(k2_tarski(k2_relat_1(esk2_0),X1)))=k10_relat_1(esk2_0,X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.47  cnf(c_0_32, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.47  cnf(c_0_33, negated_conjecture, (k1_relat_1(k5_relat_1(esk1_0,esk2_0))!=k10_relat_1(esk1_0,k10_relat_1(esk2_0,k2_relat_1(esk2_0)))), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 0.19/0.47  cnf(c_0_34, negated_conjecture, (k1_relat_1(k5_relat_1(esk1_0,esk2_0))=k10_relat_1(esk1_0,k10_relat_1(esk2_0,k2_relat_1(k5_relat_1(esk1_0,esk2_0))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_21]), c_0_29])).
% 0.19/0.47  cnf(c_0_35, negated_conjecture, (k10_relat_1(esk1_0,k10_relat_1(esk2_0,k1_setfam_1(k2_tarski(k2_relat_1(k5_relat_1(esk1_0,esk2_0)),X1))))=k10_relat_1(esk1_0,k10_relat_1(esk2_0,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_21]), c_0_29]), c_0_29])).
% 0.19/0.47  cnf(c_0_36, negated_conjecture, (k10_relat_1(esk2_0,k1_setfam_1(k2_tarski(X1,k2_relat_1(esk2_0))))=k10_relat_1(esk2_0,X1)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.19/0.47  cnf(c_0_37, negated_conjecture, (k10_relat_1(esk1_0,k10_relat_1(esk2_0,k2_relat_1(k5_relat_1(esk1_0,esk2_0))))!=k10_relat_1(esk1_0,k10_relat_1(esk2_0,k2_relat_1(esk2_0)))), inference(rw,[status(thm)],[c_0_33, c_0_34])).
% 0.19/0.47  cnf(c_0_38, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37]), ['proof']).
% 0.19/0.47  # SZS output end CNFRefutation
% 0.19/0.47  # Proof object total steps             : 39
% 0.19/0.47  # Proof object clause steps            : 24
% 0.19/0.47  # Proof object formula steps           : 15
% 0.19/0.47  # Proof object conjectures             : 18
% 0.19/0.47  # Proof object clause conjectures      : 15
% 0.19/0.47  # Proof object formula conjectures     : 3
% 0.19/0.47  # Proof object initial clauses used    : 9
% 0.19/0.47  # Proof object initial formulas used   : 7
% 0.19/0.47  # Proof object generating inferences   : 12
% 0.19/0.47  # Proof object simplifying inferences  : 7
% 0.19/0.47  # Training examples: 0 positive, 0 negative
% 0.19/0.47  # Parsed axioms                        : 7
% 0.19/0.47  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.47  # Initial clauses                      : 9
% 0.19/0.47  # Removed in clause preprocessing      : 1
% 0.19/0.47  # Initial clauses in saturation        : 8
% 0.19/0.47  # Processed clauses                    : 1140
% 0.19/0.47  # ...of these trivial                  : 106
% 0.19/0.47  # ...subsumed                          : 315
% 0.19/0.47  # ...remaining for further processing  : 719
% 0.19/0.47  # Other redundant clauses eliminated   : 0
% 0.19/0.47  # Clauses deleted for lack of memory   : 0
% 0.19/0.47  # Backward-subsumed                    : 0
% 0.19/0.47  # Backward-rewritten                   : 4
% 0.19/0.47  # Generated clauses                    : 2321
% 0.19/0.47  # ...of the previous two non-trivial   : 2056
% 0.19/0.47  # Contextual simplify-reflections      : 0
% 0.19/0.47  # Paramodulations                      : 2321
% 0.19/0.47  # Factorizations                       : 0
% 0.19/0.47  # Equation resolutions                 : 0
% 0.19/0.47  # Propositional unsat checks           : 0
% 0.19/0.47  #    Propositional check models        : 0
% 0.19/0.47  #    Propositional check unsatisfiable : 0
% 0.19/0.47  #    Propositional clauses             : 0
% 0.19/0.47  #    Propositional clauses after purity: 0
% 0.19/0.47  #    Propositional unsat core size     : 0
% 0.19/0.47  #    Propositional preprocessing time  : 0.000
% 0.19/0.47  #    Propositional encoding time       : 0.000
% 0.19/0.47  #    Propositional solver time         : 0.000
% 0.19/0.47  #    Success case prop preproc time    : 0.000
% 0.19/0.47  #    Success case prop encoding time   : 0.000
% 0.19/0.47  #    Success case prop solver time     : 0.000
% 0.19/0.47  # Current number of processed clauses  : 707
% 0.19/0.47  #    Positive orientable unit clauses  : 213
% 0.19/0.47  #    Positive unorientable unit clauses: 1
% 0.19/0.47  #    Negative unit clauses             : 1
% 0.19/0.47  #    Non-unit-clauses                  : 492
% 0.19/0.47  # Current number of unprocessed clauses: 930
% 0.19/0.47  # ...number of literals in the above   : 3542
% 0.19/0.47  # Current number of archived formulas  : 0
% 0.19/0.47  # Current number of archived clauses   : 13
% 0.19/0.47  # Clause-clause subsumption calls (NU) : 28089
% 0.19/0.47  # Rec. Clause-clause subsumption calls : 26595
% 0.19/0.47  # Non-unit clause-clause subsumptions  : 315
% 0.19/0.47  # Unit Clause-clause subsumption calls : 0
% 0.19/0.47  # Rewrite failures with RHS unbound    : 0
% 0.19/0.47  # BW rewrite match attempts            : 6808
% 0.19/0.47  # BW rewrite match successes           : 4
% 0.19/0.47  # Condensation attempts                : 0
% 0.19/0.47  # Condensation successes               : 0
% 0.19/0.47  # Termbank termtop insertions          : 68428
% 0.19/0.47  
% 0.19/0.47  # -------------------------------------------------
% 0.19/0.47  # User time                : 0.122 s
% 0.19/0.47  # System time              : 0.006 s
% 0.19/0.47  # Total time               : 0.128 s
% 0.19/0.47  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------

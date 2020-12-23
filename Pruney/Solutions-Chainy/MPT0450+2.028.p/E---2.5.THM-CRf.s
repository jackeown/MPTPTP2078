%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:48:34 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   34 (  92 expanded)
%              Number of clauses        :   19 (  39 expanded)
%              Number of leaves         :    7 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :   62 ( 145 expanded)
%              Number of equality atoms :    7 (  49 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t31_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k3_relat_1(X1),k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(fc2_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_relat_1)).

fof(t34_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k3_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k3_relat_1(X1),k3_relat_1(X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relat_1)).

fof(t19_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(c_0_7,plain,(
    ! [X15,X16] :
      ( ~ v1_relat_1(X15)
      | ~ v1_relat_1(X16)
      | ~ r1_tarski(X15,X16)
      | r1_tarski(k3_relat_1(X15),k3_relat_1(X16)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_relat_1])])])).

fof(c_0_8,plain,(
    ! [X9,X10] : r1_tarski(k4_xboole_0(X9,X10),X9) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_9,plain,(
    ! [X13,X14] :
      ( ~ v1_relat_1(X13)
      | v1_relat_1(k4_xboole_0(X13,X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_relat_1])])).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => r1_tarski(k3_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k3_relat_1(X1),k3_relat_1(X2))) ) ) ),
    inference(assume_negation,[status(cth)],[t34_relat_1])).

fof(c_0_11,plain,(
    ! [X6,X7,X8] :
      ( ~ r1_tarski(X6,X7)
      | ~ r1_tarski(X6,X8)
      | r1_tarski(X6,k3_xboole_0(X7,X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).

fof(c_0_12,plain,(
    ! [X11,X12] : k4_xboole_0(X11,k4_xboole_0(X11,X12)) = k3_xboole_0(X11,X12) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_13,plain,
    ( r1_tarski(k3_relat_1(X1),k3_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( v1_relat_1(k4_xboole_0(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_16,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_relat_1(esk2_0)
    & ~ r1_tarski(k3_relat_1(k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(k3_relat_1(esk1_0),k3_relat_1(esk2_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

fof(c_0_17,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( r1_tarski(k3_relat_1(k4_xboole_0(X1,X2)),k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(k3_relat_1(esk1_0),k3_relat_1(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( r1_tarski(k3_relat_1(k4_xboole_0(esk2_0,X1)),k3_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(k3_relat_1(k4_xboole_0(esk1_0,X1)),k3_relat_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_22])).

cnf(c_0_28,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_19]),c_0_19])).

cnf(c_0_29,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0))),k4_xboole_0(k3_relat_1(esk1_0),k4_xboole_0(k3_relat_1(esk1_0),k3_relat_1(esk2_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_19]),c_0_19])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(k3_relat_1(k4_xboole_0(esk2_0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,k3_relat_1(esk2_0))))
    | ~ r1_tarski(k3_relat_1(k4_xboole_0(esk2_0,X1)),X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(k3_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,esk1_0))),k3_relat_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_32,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk1_0))),k4_xboole_0(k3_relat_1(esk2_0),k4_xboole_0(k3_relat_1(esk2_0),k3_relat_1(esk1_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_28]),c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_28]),c_0_32]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:22:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.40  # AutoSched0-Mode selected heuristic G_E___208_B01_00_F1_SE_CS_SP_PS_S064A
% 0.13/0.40  # and selection function SelectComplexG.
% 0.13/0.40  #
% 0.13/0.40  # Preprocessing time       : 0.039 s
% 0.13/0.40  # Presaturation interreduction done
% 0.13/0.40  
% 0.13/0.40  # Proof found!
% 0.13/0.40  # SZS status Theorem
% 0.13/0.40  # SZS output start CNFRefutation
% 0.13/0.40  fof(t31_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>r1_tarski(k3_relat_1(X1),k3_relat_1(X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_relat_1)).
% 0.13/0.40  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.13/0.40  fof(fc2_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k4_xboole_0(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_relat_1)).
% 0.13/0.40  fof(t34_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k3_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k3_relat_1(X1),k3_relat_1(X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_relat_1)).
% 0.13/0.40  fof(t19_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(X1,k3_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 0.13/0.40  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.13/0.40  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.13/0.40  fof(c_0_7, plain, ![X15, X16]:(~v1_relat_1(X15)|(~v1_relat_1(X16)|(~r1_tarski(X15,X16)|r1_tarski(k3_relat_1(X15),k3_relat_1(X16))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_relat_1])])])).
% 0.13/0.40  fof(c_0_8, plain, ![X9, X10]:r1_tarski(k4_xboole_0(X9,X10),X9), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.13/0.40  fof(c_0_9, plain, ![X13, X14]:(~v1_relat_1(X13)|v1_relat_1(k4_xboole_0(X13,X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_relat_1])])).
% 0.13/0.40  fof(c_0_10, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k3_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k3_relat_1(X1),k3_relat_1(X2)))))), inference(assume_negation,[status(cth)],[t34_relat_1])).
% 0.13/0.40  fof(c_0_11, plain, ![X6, X7, X8]:(~r1_tarski(X6,X7)|~r1_tarski(X6,X8)|r1_tarski(X6,k3_xboole_0(X7,X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).
% 0.13/0.40  fof(c_0_12, plain, ![X11, X12]:k4_xboole_0(X11,k4_xboole_0(X11,X12))=k3_xboole_0(X11,X12), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.13/0.40  cnf(c_0_13, plain, (r1_tarski(k3_relat_1(X1),k3_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.40  cnf(c_0_14, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.40  cnf(c_0_15, plain, (v1_relat_1(k4_xboole_0(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.40  fof(c_0_16, negated_conjecture, (v1_relat_1(esk1_0)&(v1_relat_1(esk2_0)&~r1_tarski(k3_relat_1(k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(k3_relat_1(esk1_0),k3_relat_1(esk2_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 0.13/0.40  fof(c_0_17, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.13/0.40  cnf(c_0_18, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.40  cnf(c_0_19, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.40  cnf(c_0_20, plain, (r1_tarski(k3_relat_1(k4_xboole_0(X1,X2)),k3_relat_1(X1))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15])).
% 0.13/0.40  cnf(c_0_21, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.40  cnf(c_0_22, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.40  cnf(c_0_23, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.40  cnf(c_0_24, negated_conjecture, (~r1_tarski(k3_relat_1(k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(k3_relat_1(esk1_0),k3_relat_1(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.40  cnf(c_0_25, plain, (r1_tarski(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))|~r1_tarski(X1,X3)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 0.13/0.40  cnf(c_0_26, negated_conjecture, (r1_tarski(k3_relat_1(k4_xboole_0(esk2_0,X1)),k3_relat_1(esk2_0))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.13/0.40  cnf(c_0_27, negated_conjecture, (r1_tarski(k3_relat_1(k4_xboole_0(esk1_0,X1)),k3_relat_1(esk1_0))), inference(spm,[status(thm)],[c_0_20, c_0_22])).
% 0.13/0.40  cnf(c_0_28, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_19]), c_0_19])).
% 0.13/0.40  cnf(c_0_29, negated_conjecture, (~r1_tarski(k3_relat_1(k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0))),k4_xboole_0(k3_relat_1(esk1_0),k4_xboole_0(k3_relat_1(esk1_0),k3_relat_1(esk2_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_19]), c_0_19])).
% 0.13/0.40  cnf(c_0_30, negated_conjecture, (r1_tarski(k3_relat_1(k4_xboole_0(esk2_0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,k3_relat_1(esk2_0))))|~r1_tarski(k3_relat_1(k4_xboole_0(esk2_0,X1)),X2)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.13/0.40  cnf(c_0_31, negated_conjecture, (r1_tarski(k3_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,esk1_0))),k3_relat_1(esk1_0))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.13/0.40  cnf(c_0_32, negated_conjecture, (~r1_tarski(k3_relat_1(k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk1_0))),k4_xboole_0(k3_relat_1(esk2_0),k4_xboole_0(k3_relat_1(esk2_0),k3_relat_1(esk1_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_28]), c_0_28])).
% 0.13/0.40  cnf(c_0_33, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_28]), c_0_32]), ['proof']).
% 0.13/0.40  # SZS output end CNFRefutation
% 0.13/0.40  # Proof object total steps             : 34
% 0.13/0.40  # Proof object clause steps            : 19
% 0.13/0.40  # Proof object formula steps           : 15
% 0.13/0.40  # Proof object conjectures             : 13
% 0.13/0.40  # Proof object clause conjectures      : 10
% 0.13/0.40  # Proof object formula conjectures     : 3
% 0.13/0.40  # Proof object initial clauses used    : 9
% 0.13/0.40  # Proof object initial formulas used   : 7
% 0.13/0.40  # Proof object generating inferences   : 6
% 0.13/0.40  # Proof object simplifying inferences  : 10
% 0.13/0.40  # Training examples: 0 positive, 0 negative
% 0.13/0.40  # Parsed axioms                        : 7
% 0.13/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.40  # Initial clauses                      : 9
% 0.13/0.40  # Removed in clause preprocessing      : 1
% 0.13/0.40  # Initial clauses in saturation        : 8
% 0.13/0.40  # Processed clauses                    : 92
% 0.13/0.40  # ...of these trivial                  : 22
% 0.13/0.40  # ...subsumed                          : 2
% 0.13/0.40  # ...remaining for further processing  : 68
% 0.13/0.40  # Other redundant clauses eliminated   : 0
% 0.13/0.40  # Clauses deleted for lack of memory   : 0
% 0.13/0.40  # Backward-subsumed                    : 0
% 0.13/0.40  # Backward-rewritten                   : 1
% 0.13/0.40  # Generated clauses                    : 384
% 0.13/0.40  # ...of the previous two non-trivial   : 323
% 0.13/0.40  # Contextual simplify-reflections      : 1
% 0.13/0.40  # Paramodulations                      : 384
% 0.13/0.40  # Factorizations                       : 0
% 0.13/0.40  # Equation resolutions                 : 0
% 0.13/0.40  # Propositional unsat checks           : 0
% 0.13/0.40  #    Propositional check models        : 0
% 0.13/0.40  #    Propositional check unsatisfiable : 0
% 0.13/0.40  #    Propositional clauses             : 0
% 0.13/0.40  #    Propositional clauses after purity: 0
% 0.13/0.40  #    Propositional unsat core size     : 0
% 0.13/0.40  #    Propositional preprocessing time  : 0.000
% 0.13/0.40  #    Propositional encoding time       : 0.000
% 0.13/0.40  #    Propositional solver time         : 0.000
% 0.13/0.40  #    Success case prop preproc time    : 0.000
% 0.13/0.40  #    Success case prop encoding time   : 0.000
% 0.13/0.40  #    Success case prop solver time     : 0.000
% 0.13/0.40  # Current number of processed clauses  : 59
% 0.13/0.40  #    Positive orientable unit clauses  : 37
% 0.13/0.40  #    Positive unorientable unit clauses: 1
% 0.13/0.40  #    Negative unit clauses             : 1
% 0.13/0.40  #    Non-unit-clauses                  : 20
% 0.13/0.40  # Current number of unprocessed clauses: 243
% 0.13/0.40  # ...number of literals in the above   : 313
% 0.13/0.40  # Current number of archived formulas  : 0
% 0.13/0.40  # Current number of archived clauses   : 10
% 0.13/0.40  # Clause-clause subsumption calls (NU) : 128
% 0.13/0.40  # Rec. Clause-clause subsumption calls : 128
% 0.13/0.40  # Non-unit clause-clause subsumptions  : 3
% 0.13/0.40  # Unit Clause-clause subsumption calls : 4
% 0.13/0.40  # Rewrite failures with RHS unbound    : 0
% 0.13/0.40  # BW rewrite match attempts            : 122
% 0.13/0.40  # BW rewrite match successes           : 8
% 0.13/0.40  # Condensation attempts                : 0
% 0.13/0.40  # Condensation successes               : 0
% 0.13/0.40  # Termbank termtop insertions          : 6590
% 0.13/0.40  
% 0.13/0.40  # -------------------------------------------------
% 0.13/0.40  # User time                : 0.053 s
% 0.13/0.40  # System time              : 0.002 s
% 0.13/0.40  # Total time               : 0.055 s
% 0.13/0.40  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------

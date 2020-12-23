%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:48:42 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   33 (  65 expanded)
%              Number of clauses        :   20 (  27 expanded)
%              Number of leaves         :    6 (  16 expanded)
%              Depth                    :    8
%              Number of atoms          :   71 ( 163 expanded)
%              Number of equality atoms :    3 (   9 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t52_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relat_1)).

fof(t48_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => ( r1_tarski(X1,X2)
               => r1_tarski(k5_relat_1(X3,X1),k5_relat_1(X3,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relat_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(fc1_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t19_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ! [X3] :
                ( v1_relat_1(X3)
               => r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t52_relat_1])).

fof(c_0_7,plain,(
    ! [X13,X14,X15] :
      ( ~ v1_relat_1(X13)
      | ~ v1_relat_1(X14)
      | ~ v1_relat_1(X15)
      | ~ r1_tarski(X13,X14)
      | r1_tarski(k5_relat_1(X15,X13),k5_relat_1(X15,X14)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_relat_1])])])).

fof(c_0_8,plain,(
    ! [X6,X7] : r1_tarski(k3_xboole_0(X6,X7),X6) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_9,plain,(
    ! [X11,X12] :
      ( ~ v1_relat_1(X11)
      | v1_relat_1(k3_xboole_0(X11,X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_relat_1])])).

fof(c_0_10,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_11,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_relat_1(esk2_0)
    & v1_relat_1(esk3_0)
    & ~ r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk3_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

cnf(c_0_12,plain,
    ( r1_tarski(k5_relat_1(X3,X1),k5_relat_1(X3,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( v1_relat_1(k3_xboole_0(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_13,c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( v1_relat_1(k3_xboole_0(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_16])).

fof(c_0_21,plain,(
    ! [X8,X9,X10] :
      ( ~ r1_tarski(X8,X9)
      | ~ r1_tarski(X8,X10)
      | r1_tarski(X8,k3_xboole_0(X9,X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).

cnf(c_0_22,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(X1,X2)),k5_relat_1(esk1_0,X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_24,plain,
    ( r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k5_relat_1(X1,X3))
    | ~ v1_relat_1(k3_xboole_0(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X3) ),
    inference(spm,[status(thm)],[c_0_12,c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( v1_relat_1(k3_xboole_0(X1,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_15])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(esk3_0,X1)),k5_relat_1(esk1_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,esk2_0)),k5_relat_1(X1,esk2_0))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_16])])).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(esk3_0,X1)),k3_xboole_0(X2,k5_relat_1(esk1_0,esk3_0)))
    | ~ r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(esk3_0,X1)),X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(X1,esk2_0)),k5_relat_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_18])).

cnf(c_0_31,negated_conjecture,
    ( ~ r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_32,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_15]),c_0_31]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:34:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.54  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_PS_S0i
% 0.19/0.54  # and selection function SelectDiffNegLit.
% 0.19/0.54  #
% 0.19/0.54  # Preprocessing time       : 0.026 s
% 0.19/0.54  # Presaturation interreduction done
% 0.19/0.54  
% 0.19/0.54  # Proof found!
% 0.19/0.54  # SZS status Theorem
% 0.19/0.54  # SZS output start CNFRefutation
% 0.19/0.54  fof(t52_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_relat_1)).
% 0.19/0.54  fof(t48_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>r1_tarski(k5_relat_1(X3,X1),k5_relat_1(X3,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_relat_1)).
% 0.19/0.54  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.19/0.54  fof(fc1_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k3_xboole_0(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_relat_1)).
% 0.19/0.54  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.19/0.54  fof(t19_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(X1,k3_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 0.19/0.54  fof(c_0_6, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3))))))), inference(assume_negation,[status(cth)],[t52_relat_1])).
% 0.19/0.54  fof(c_0_7, plain, ![X13, X14, X15]:(~v1_relat_1(X13)|(~v1_relat_1(X14)|(~v1_relat_1(X15)|(~r1_tarski(X13,X14)|r1_tarski(k5_relat_1(X15,X13),k5_relat_1(X15,X14)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_relat_1])])])).
% 0.19/0.54  fof(c_0_8, plain, ![X6, X7]:r1_tarski(k3_xboole_0(X6,X7),X6), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.19/0.54  fof(c_0_9, plain, ![X11, X12]:(~v1_relat_1(X11)|v1_relat_1(k3_xboole_0(X11,X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_relat_1])])).
% 0.19/0.54  fof(c_0_10, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.19/0.54  fof(c_0_11, negated_conjecture, (v1_relat_1(esk1_0)&(v1_relat_1(esk2_0)&(v1_relat_1(esk3_0)&~r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.19/0.54  cnf(c_0_12, plain, (r1_tarski(k5_relat_1(X3,X1),k5_relat_1(X3,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X3)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.54  cnf(c_0_13, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.54  cnf(c_0_14, plain, (v1_relat_1(k3_xboole_0(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.54  cnf(c_0_15, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.54  cnf(c_0_16, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.54  cnf(c_0_17, plain, (r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_14])).
% 0.19/0.54  cnf(c_0_18, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.54  cnf(c_0_19, plain, (r1_tarski(k3_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_13, c_0_15])).
% 0.19/0.54  cnf(c_0_20, negated_conjecture, (v1_relat_1(k3_xboole_0(esk2_0,X1))), inference(spm,[status(thm)],[c_0_14, c_0_16])).
% 0.19/0.54  fof(c_0_21, plain, ![X8, X9, X10]:(~r1_tarski(X8,X9)|~r1_tarski(X8,X10)|r1_tarski(X8,k3_xboole_0(X9,X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).
% 0.19/0.54  cnf(c_0_22, negated_conjecture, (r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(X1,X2)),k5_relat_1(esk1_0,X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.19/0.54  cnf(c_0_23, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.54  cnf(c_0_24, plain, (r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k5_relat_1(X1,X3))|~v1_relat_1(k3_xboole_0(X2,X3))|~v1_relat_1(X1)|~v1_relat_1(X3)), inference(spm,[status(thm)],[c_0_12, c_0_19])).
% 0.19/0.54  cnf(c_0_25, negated_conjecture, (v1_relat_1(k3_xboole_0(X1,esk2_0))), inference(spm,[status(thm)],[c_0_20, c_0_15])).
% 0.19/0.54  cnf(c_0_26, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.54  cnf(c_0_27, negated_conjecture, (r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(esk3_0,X1)),k5_relat_1(esk1_0,esk3_0))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.19/0.54  cnf(c_0_28, negated_conjecture, (r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,esk2_0)),k5_relat_1(X1,esk2_0))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_16])])).
% 0.19/0.54  cnf(c_0_29, negated_conjecture, (r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(esk3_0,X1)),k3_xboole_0(X2,k5_relat_1(esk1_0,esk3_0)))|~r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(esk3_0,X1)),X2)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.19/0.54  cnf(c_0_30, negated_conjecture, (r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(X1,esk2_0)),k5_relat_1(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_28, c_0_18])).
% 0.19/0.54  cnf(c_0_31, negated_conjecture, (~r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.54  cnf(c_0_32, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_15]), c_0_31]), ['proof']).
% 0.19/0.54  # SZS output end CNFRefutation
% 0.19/0.54  # Proof object total steps             : 33
% 0.19/0.54  # Proof object clause steps            : 20
% 0.19/0.54  # Proof object formula steps           : 13
% 0.19/0.54  # Proof object conjectures             : 15
% 0.19/0.54  # Proof object clause conjectures      : 12
% 0.19/0.54  # Proof object formula conjectures     : 3
% 0.19/0.54  # Proof object initial clauses used    : 9
% 0.19/0.54  # Proof object initial formulas used   : 6
% 0.19/0.54  # Proof object generating inferences   : 11
% 0.19/0.54  # Proof object simplifying inferences  : 5
% 0.19/0.54  # Training examples: 0 positive, 0 negative
% 0.19/0.54  # Parsed axioms                        : 6
% 0.19/0.54  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.54  # Initial clauses                      : 9
% 0.19/0.54  # Removed in clause preprocessing      : 0
% 0.19/0.54  # Initial clauses in saturation        : 9
% 0.19/0.54  # Processed clauses                    : 1231
% 0.19/0.54  # ...of these trivial                  : 526
% 0.19/0.54  # ...subsumed                          : 44
% 0.19/0.54  # ...remaining for further processing  : 661
% 0.19/0.54  # Other redundant clauses eliminated   : 0
% 0.19/0.54  # Clauses deleted for lack of memory   : 0
% 0.19/0.54  # Backward-subsumed                    : 0
% 0.19/0.54  # Backward-rewritten                   : 6
% 0.19/0.54  # Generated clauses                    : 18353
% 0.19/0.54  # ...of the previous two non-trivial   : 17002
% 0.19/0.54  # Contextual simplify-reflections      : 1
% 0.19/0.54  # Paramodulations                      : 18353
% 0.19/0.54  # Factorizations                       : 0
% 0.19/0.54  # Equation resolutions                 : 0
% 0.19/0.54  # Propositional unsat checks           : 0
% 0.19/0.54  #    Propositional check models        : 0
% 0.19/0.54  #    Propositional check unsatisfiable : 0
% 0.19/0.54  #    Propositional clauses             : 0
% 0.19/0.54  #    Propositional clauses after purity: 0
% 0.19/0.54  #    Propositional unsat core size     : 0
% 0.19/0.54  #    Propositional preprocessing time  : 0.000
% 0.19/0.54  #    Propositional encoding time       : 0.000
% 0.19/0.54  #    Propositional solver time         : 0.000
% 0.19/0.54  #    Success case prop preproc time    : 0.000
% 0.19/0.54  #    Success case prop encoding time   : 0.000
% 0.19/0.54  #    Success case prop solver time     : 0.000
% 0.19/0.54  # Current number of processed clauses  : 646
% 0.19/0.54  #    Positive orientable unit clauses  : 445
% 0.19/0.54  #    Positive unorientable unit clauses: 1
% 0.19/0.54  #    Negative unit clauses             : 1
% 0.19/0.54  #    Non-unit-clauses                  : 199
% 0.19/0.54  # Current number of unprocessed clauses: 15785
% 0.19/0.54  # ...number of literals in the above   : 19605
% 0.19/0.54  # Current number of archived formulas  : 0
% 0.19/0.54  # Current number of archived clauses   : 15
% 0.19/0.54  # Clause-clause subsumption calls (NU) : 2958
% 0.19/0.54  # Rec. Clause-clause subsumption calls : 2832
% 0.19/0.54  # Non-unit clause-clause subsumptions  : 45
% 0.19/0.54  # Unit Clause-clause subsumption calls : 205
% 0.19/0.54  # Rewrite failures with RHS unbound    : 0
% 0.19/0.54  # BW rewrite match attempts            : 9838
% 0.19/0.54  # BW rewrite match successes           : 18
% 0.19/0.54  # Condensation attempts                : 0
% 0.19/0.54  # Condensation successes               : 0
% 0.19/0.54  # Termbank termtop insertions          : 357052
% 0.19/0.54  
% 0.19/0.54  # -------------------------------------------------
% 0.19/0.54  # User time                : 0.188 s
% 0.19/0.54  # System time              : 0.016 s
% 0.19/0.54  # Total time               : 0.203 s
% 0.19/0.54  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------

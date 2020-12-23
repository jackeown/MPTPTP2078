%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:48:42 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 131 expanded)
%              Number of clauses        :   30 (  62 expanded)
%              Number of leaves         :    8 (  31 expanded)
%              Depth                    :   12
%              Number of atoms          :  102 ( 338 expanded)
%              Number of equality atoms :   13 (  67 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t31_xboole_1,axiom,(
    ! [X1,X2,X3] : r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).

fof(t52_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relat_1)).

fof(fc1_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

fof(t19_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

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

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(c_0_8,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_9,plain,(
    ! [X6,X7] :
      ( ~ r1_tarski(X6,X7)
      | k2_xboole_0(X6,X7) = X7 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_10,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_11,plain,(
    ! [X13,X14,X15] : r1_tarski(k2_xboole_0(k3_xboole_0(X13,X14),k3_xboole_0(X13,X15)),k2_xboole_0(X14,X15)) ),
    inference(variable_rename,[status(thm)],[t31_xboole_1])).

cnf(c_0_12,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_10])).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ! [X3] :
                ( v1_relat_1(X3)
               => r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t52_relat_1])).

cnf(c_0_15,plain,
    ( r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

fof(c_0_17,plain,(
    ! [X16,X17] :
      ( ~ v1_relat_1(X16)
      | v1_relat_1(k3_xboole_0(X16,X17)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_relat_1])])).

fof(c_0_18,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_relat_1(esk2_0)
    & v1_relat_1(esk3_0)
    & ~ r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk3_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

cnf(c_0_19,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_20,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_16])).

fof(c_0_21,plain,(
    ! [X10,X11,X12] :
      ( ~ r1_tarski(X10,X11)
      | ~ r1_tarski(X10,X12)
      | r1_tarski(X10,k3_xboole_0(X11,X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).

fof(c_0_22,plain,(
    ! [X19,X20,X21] :
      ( ~ v1_relat_1(X19)
      | ~ v1_relat_1(X20)
      | ~ v1_relat_1(X21)
      | ~ r1_tarski(X19,X20)
      | r1_tarski(k5_relat_1(X21,X19),k5_relat_1(X21,X20)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_relat_1])])])).

cnf(c_0_23,plain,
    ( v1_relat_1(k3_xboole_0(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( k3_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X2,k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( r1_tarski(k5_relat_1(X3,X1),k5_relat_1(X3,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( v1_relat_1(k3_xboole_0(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

fof(c_0_29,plain,(
    ! [X8,X9] : r1_tarski(k3_xboole_0(X8,X9),X8) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_30,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_31,plain,
    ( k3_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_13])])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(k5_relat_1(X1,k3_xboole_0(esk2_0,X2)),k5_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(k3_xboole_0(esk2_0,X2),X3) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( v1_relat_1(k3_xboole_0(esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_30])).

cnf(c_0_35,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X1)) = k3_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_20])).

cnf(c_0_36,negated_conjecture,
    ( ~ r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(k5_relat_1(X1,k3_xboole_0(esk2_0,X2)),k5_relat_1(X1,esk2_0))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_24]),c_0_33])])).

cnf(c_0_38,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(k5_relat_1(X1,X2),k5_relat_1(X1,esk3_0))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X2,esk3_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_30])).

cnf(c_0_40,negated_conjecture,
    ( v1_relat_1(k3_xboole_0(X1,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( ~ r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(esk2_0,esk3_0)),k5_relat_1(esk1_0,esk3_0))
    | ~ r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(esk2_0,esk3_0)),k5_relat_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_26])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(esk2_0,X1)),k5_relat_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,esk3_0)),k5_relat_1(X1,esk3_0))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_20])])).

cnf(c_0_44,negated_conjecture,
    ( ~ r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(esk2_0,esk3_0)),k5_relat_1(esk1_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_42])])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(X1,esk3_0)),k5_relat_1(esk1_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_38])).

cnf(c_0_46,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_45])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:41:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.44  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S02AI
% 0.21/0.44  # and selection function SelectNonStrongRROptimalLit.
% 0.21/0.44  #
% 0.21/0.44  # Preprocessing time       : 0.029 s
% 0.21/0.44  # Presaturation interreduction done
% 0.21/0.44  
% 0.21/0.44  # Proof found!
% 0.21/0.44  # SZS status Theorem
% 0.21/0.44  # SZS output start CNFRefutation
% 0.21/0.44  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.21/0.44  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.21/0.44  fof(t31_xboole_1, axiom, ![X1, X2, X3]:r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_xboole_1)).
% 0.21/0.44  fof(t52_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_relat_1)).
% 0.21/0.44  fof(fc1_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k3_xboole_0(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_relat_1)).
% 0.21/0.44  fof(t19_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(X1,k3_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 0.21/0.44  fof(t48_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>r1_tarski(k5_relat_1(X3,X1),k5_relat_1(X3,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_relat_1)).
% 0.21/0.44  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.21/0.44  fof(c_0_8, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.21/0.44  fof(c_0_9, plain, ![X6, X7]:(~r1_tarski(X6,X7)|k2_xboole_0(X6,X7)=X7), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.21/0.44  cnf(c_0_10, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.44  fof(c_0_11, plain, ![X13, X14, X15]:r1_tarski(k2_xboole_0(k3_xboole_0(X13,X14),k3_xboole_0(X13,X15)),k2_xboole_0(X14,X15)), inference(variable_rename,[status(thm)],[t31_xboole_1])).
% 0.21/0.44  cnf(c_0_12, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.44  cnf(c_0_13, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_10])).
% 0.21/0.44  fof(c_0_14, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3))))))), inference(assume_negation,[status(cth)],[t52_relat_1])).
% 0.21/0.44  cnf(c_0_15, plain, (r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.44  cnf(c_0_16, plain, (k2_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.21/0.44  fof(c_0_17, plain, ![X16, X17]:(~v1_relat_1(X16)|v1_relat_1(k3_xboole_0(X16,X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_relat_1])])).
% 0.21/0.44  fof(c_0_18, negated_conjecture, (v1_relat_1(esk1_0)&(v1_relat_1(esk2_0)&(v1_relat_1(esk3_0)&~r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.21/0.44  cnf(c_0_19, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.44  cnf(c_0_20, plain, (r1_tarski(k3_xboole_0(X1,X2),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_16])).
% 0.21/0.44  fof(c_0_21, plain, ![X10, X11, X12]:(~r1_tarski(X10,X11)|~r1_tarski(X10,X12)|r1_tarski(X10,k3_xboole_0(X11,X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).
% 0.21/0.44  fof(c_0_22, plain, ![X19, X20, X21]:(~v1_relat_1(X19)|(~v1_relat_1(X20)|(~v1_relat_1(X21)|(~r1_tarski(X19,X20)|r1_tarski(k5_relat_1(X21,X19),k5_relat_1(X21,X20)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_relat_1])])])).
% 0.21/0.44  cnf(c_0_23, plain, (v1_relat_1(k3_xboole_0(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.44  cnf(c_0_24, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.44  cnf(c_0_25, plain, (k3_xboole_0(X1,X2)=X2|~r1_tarski(X2,k3_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.21/0.44  cnf(c_0_26, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.44  cnf(c_0_27, plain, (r1_tarski(k5_relat_1(X3,X1),k5_relat_1(X3,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X3)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.44  cnf(c_0_28, negated_conjecture, (v1_relat_1(k3_xboole_0(esk2_0,X1))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.21/0.44  fof(c_0_29, plain, ![X8, X9]:r1_tarski(k3_xboole_0(X8,X9),X8), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.21/0.44  cnf(c_0_30, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.44  cnf(c_0_31, plain, (k3_xboole_0(X1,X2)=X2|~r1_tarski(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_13])])).
% 0.21/0.44  cnf(c_0_32, negated_conjecture, (r1_tarski(k5_relat_1(X1,k3_xboole_0(esk2_0,X2)),k5_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_relat_1(X3)|~r1_tarski(k3_xboole_0(esk2_0,X2),X3)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.21/0.44  cnf(c_0_33, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.21/0.44  cnf(c_0_34, negated_conjecture, (v1_relat_1(k3_xboole_0(esk3_0,X1))), inference(spm,[status(thm)],[c_0_23, c_0_30])).
% 0.21/0.44  cnf(c_0_35, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X1))=k3_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_31, c_0_20])).
% 0.21/0.44  cnf(c_0_36, negated_conjecture, (~r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.44  cnf(c_0_37, negated_conjecture, (r1_tarski(k5_relat_1(X1,k3_xboole_0(esk2_0,X2)),k5_relat_1(X1,esk2_0))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_24]), c_0_33])])).
% 0.21/0.44  cnf(c_0_38, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.44  cnf(c_0_39, negated_conjecture, (r1_tarski(k5_relat_1(X1,X2),k5_relat_1(X1,esk3_0))|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X2,esk3_0)), inference(spm,[status(thm)],[c_0_27, c_0_30])).
% 0.21/0.44  cnf(c_0_40, negated_conjecture, (v1_relat_1(k3_xboole_0(X1,esk3_0))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.21/0.44  cnf(c_0_41, negated_conjecture, (~r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(esk2_0,esk3_0)),k5_relat_1(esk1_0,esk3_0))|~r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(esk2_0,esk3_0)),k5_relat_1(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_36, c_0_26])).
% 0.21/0.44  cnf(c_0_42, negated_conjecture, (r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(esk2_0,X1)),k5_relat_1(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.21/0.44  cnf(c_0_43, negated_conjecture, (r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,esk3_0)),k5_relat_1(X1,esk3_0))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_20])])).
% 0.21/0.44  cnf(c_0_44, negated_conjecture, (~r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(esk2_0,esk3_0)),k5_relat_1(esk1_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_42])])).
% 0.21/0.44  cnf(c_0_45, negated_conjecture, (r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(X1,esk3_0)),k5_relat_1(esk1_0,esk3_0))), inference(spm,[status(thm)],[c_0_43, c_0_38])).
% 0.21/0.44  cnf(c_0_46, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_45])]), ['proof']).
% 0.21/0.44  # SZS output end CNFRefutation
% 0.21/0.44  # Proof object total steps             : 47
% 0.21/0.44  # Proof object clause steps            : 30
% 0.21/0.44  # Proof object formula steps           : 17
% 0.21/0.44  # Proof object conjectures             : 19
% 0.21/0.44  # Proof object clause conjectures      : 16
% 0.21/0.44  # Proof object formula conjectures     : 3
% 0.21/0.44  # Proof object initial clauses used    : 12
% 0.21/0.44  # Proof object initial formulas used   : 8
% 0.21/0.44  # Proof object generating inferences   : 15
% 0.21/0.44  # Proof object simplifying inferences  : 12
% 0.21/0.44  # Training examples: 0 positive, 0 negative
% 0.21/0.44  # Parsed axioms                        : 9
% 0.21/0.44  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.44  # Initial clauses                      : 14
% 0.21/0.44  # Removed in clause preprocessing      : 0
% 0.21/0.44  # Initial clauses in saturation        : 14
% 0.21/0.44  # Processed clauses                    : 444
% 0.21/0.44  # ...of these trivial                  : 30
% 0.21/0.44  # ...subsumed                          : 131
% 0.21/0.44  # ...remaining for further processing  : 283
% 0.21/0.44  # Other redundant clauses eliminated   : 2
% 0.21/0.44  # Clauses deleted for lack of memory   : 0
% 0.21/0.44  # Backward-subsumed                    : 0
% 0.21/0.44  # Backward-rewritten                   : 4
% 0.21/0.44  # Generated clauses                    : 5420
% 0.21/0.44  # ...of the previous two non-trivial   : 4292
% 0.21/0.44  # Contextual simplify-reflections      : 0
% 0.21/0.44  # Paramodulations                      : 5418
% 0.21/0.44  # Factorizations                       : 0
% 0.21/0.44  # Equation resolutions                 : 2
% 0.21/0.44  # Propositional unsat checks           : 0
% 0.21/0.44  #    Propositional check models        : 0
% 0.21/0.44  #    Propositional check unsatisfiable : 0
% 0.21/0.44  #    Propositional clauses             : 0
% 0.21/0.44  #    Propositional clauses after purity: 0
% 0.21/0.44  #    Propositional unsat core size     : 0
% 0.21/0.44  #    Propositional preprocessing time  : 0.000
% 0.21/0.44  #    Propositional encoding time       : 0.000
% 0.21/0.44  #    Propositional solver time         : 0.000
% 0.21/0.44  #    Success case prop preproc time    : 0.000
% 0.21/0.44  #    Success case prop encoding time   : 0.000
% 0.21/0.44  #    Success case prop solver time     : 0.000
% 0.21/0.44  # Current number of processed clauses  : 264
% 0.21/0.44  #    Positive orientable unit clauses  : 90
% 0.21/0.44  #    Positive unorientable unit clauses: 0
% 0.21/0.44  #    Negative unit clauses             : 1
% 0.21/0.44  #    Non-unit-clauses                  : 173
% 0.21/0.44  # Current number of unprocessed clauses: 3875
% 0.21/0.44  # ...number of literals in the above   : 9299
% 0.21/0.44  # Current number of archived formulas  : 0
% 0.21/0.44  # Current number of archived clauses   : 17
% 0.21/0.44  # Clause-clause subsumption calls (NU) : 3305
% 0.21/0.44  # Rec. Clause-clause subsumption calls : 2788
% 0.21/0.44  # Non-unit clause-clause subsumptions  : 131
% 0.21/0.44  # Unit Clause-clause subsumption calls : 277
% 0.21/0.44  # Rewrite failures with RHS unbound    : 0
% 0.21/0.44  # BW rewrite match attempts            : 304
% 0.21/0.44  # BW rewrite match successes           : 4
% 0.21/0.44  # Condensation attempts                : 0
% 0.21/0.44  # Condensation successes               : 0
% 0.21/0.44  # Termbank termtop insertions          : 86719
% 0.21/0.44  
% 0.21/0.44  # -------------------------------------------------
% 0.21/0.44  # User time                : 0.085 s
% 0.21/0.44  # System time              : 0.012 s
% 0.21/0.44  # Total time               : 0.096 s
% 0.21/0.44  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------

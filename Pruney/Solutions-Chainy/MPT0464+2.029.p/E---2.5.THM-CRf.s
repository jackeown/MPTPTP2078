%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:48:41 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 135 expanded)
%              Number of clauses        :   28 (  62 expanded)
%              Number of leaves         :    9 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :  104 ( 265 expanded)
%              Number of equality atoms :   16 (  79 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :    7 (   2 average)
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

fof(fc1_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

fof(t50_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => ! [X4] :
                  ( v1_relat_1(X4)
                 => ( ( r1_tarski(X1,X2)
                      & r1_tarski(X3,X4) )
                   => r1_tarski(k5_relat_1(X1,X3),k5_relat_1(X2,X4)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t52_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relat_1)).

fof(t19_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(c_0_9,plain,(
    ! [X16,X17] : k1_setfam_1(k2_tarski(X16,X17)) = k3_xboole_0(X16,X17) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_10,plain,(
    ! [X14,X15] : k1_enumset1(X14,X14,X15) = k2_tarski(X14,X15) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_11,plain,(
    ! [X7,X8] : r1_tarski(k3_xboole_0(X7,X8),X7) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_12,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,plain,(
    ! [X18,X19] :
      ( ~ v1_relat_1(X18)
      | v1_relat_1(k3_xboole_0(X18,X19)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_relat_1])])).

fof(c_0_15,plain,(
    ! [X20,X21,X22,X23] :
      ( ~ v1_relat_1(X20)
      | ~ v1_relat_1(X21)
      | ~ v1_relat_1(X22)
      | ~ v1_relat_1(X23)
      | ~ r1_tarski(X20,X21)
      | ~ r1_tarski(X22,X23)
      | r1_tarski(k5_relat_1(X20,X22),k5_relat_1(X21,X23)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_relat_1])])])).

cnf(c_0_16,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,plain,
    ( v1_relat_1(k3_xboole_0(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_20,plain,
    ( r1_tarski(k5_relat_1(X1,X3),k5_relat_1(X2,X4))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X4)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( r1_tarski(k1_setfam_1(k1_enumset1(X1,X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_22,plain,
    ( v1_relat_1(k1_setfam_1(k1_enumset1(X1,X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_18,c_0_17])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_24,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ! [X3] :
                ( v1_relat_1(X3)
               => r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t52_relat_1])).

cnf(c_0_25,plain,
    ( r1_tarski(k5_relat_1(X1,k1_setfam_1(k1_enumset1(X2,X2,X3))),k5_relat_1(X4,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,X4) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_23])).

fof(c_0_27,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_relat_1(esk2_0)
    & v1_relat_1(esk3_0)
    & ~ r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk3_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).

fof(c_0_28,plain,(
    ! [X9,X10,X11] :
      ( ~ r1_tarski(X9,X10)
      | ~ r1_tarski(X9,X11)
      | r1_tarski(X9,k3_xboole_0(X10,X11)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).

cnf(c_0_29,plain,
    ( r1_tarski(k5_relat_1(X1,k1_setfam_1(k1_enumset1(X2,X2,X3))),k5_relat_1(X1,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_32,plain,(
    ! [X12,X13] : k2_tarski(X12,X13) = k2_tarski(X13,X12) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(k5_relat_1(X1,k1_setfam_1(k1_enumset1(esk3_0,esk3_0,X2))),k5_relat_1(X1,esk3_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(k5_relat_1(X1,k1_setfam_1(k1_enumset1(esk2_0,esk2_0,X2))),k5_relat_1(X1,esk2_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_31])).

cnf(c_0_37,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,k1_setfam_1(k1_enumset1(X2,X2,X3)))
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_33,c_0_17])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk1_0,k1_setfam_1(k1_enumset1(esk3_0,esk3_0,X1))),k5_relat_1(esk1_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk1_0,k1_setfam_1(k1_enumset1(esk2_0,esk2_0,X1))),k5_relat_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_35])).

cnf(c_0_41,plain,
    ( k1_enumset1(X1,X1,X2) = k1_enumset1(X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_13]),c_0_13])).

cnf(c_0_42,negated_conjecture,
    ( ~ r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk1_0,k1_setfam_1(k1_enumset1(esk3_0,esk3_0,X1))),k1_setfam_1(k1_enumset1(X2,X2,k5_relat_1(esk1_0,esk3_0))))
    | ~ r1_tarski(k5_relat_1(esk1_0,k1_setfam_1(k1_enumset1(esk3_0,esk3_0,X1))),X2) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk1_0,k1_setfam_1(k1_enumset1(X1,X1,esk2_0))),k5_relat_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_45,negated_conjecture,
    ( ~ r1_tarski(k5_relat_1(esk1_0,k1_setfam_1(k1_enumset1(esk2_0,esk2_0,esk3_0))),k1_setfam_1(k1_enumset1(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk3_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_17]),c_0_17])).

cnf(c_0_46,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_41]),c_0_45]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:21:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.54  # AutoSched0-Mode selected heuristic G_E___107_B00_00_F1_PI_AE_Q4_CS_SP_PS_S064A
% 0.20/0.54  # and selection function SelectComplexG.
% 0.20/0.54  #
% 0.20/0.54  # Preprocessing time       : 0.027 s
% 0.20/0.54  # Presaturation interreduction done
% 0.20/0.54  
% 0.20/0.54  # Proof found!
% 0.20/0.54  # SZS status Theorem
% 0.20/0.54  # SZS output start CNFRefutation
% 0.20/0.54  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.20/0.54  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.54  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.20/0.54  fof(fc1_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k3_xboole_0(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_relat_1)).
% 0.20/0.54  fof(t50_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>![X4]:(v1_relat_1(X4)=>((r1_tarski(X1,X2)&r1_tarski(X3,X4))=>r1_tarski(k5_relat_1(X1,X3),k5_relat_1(X2,X4))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_relat_1)).
% 0.20/0.54  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.54  fof(t52_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_relat_1)).
% 0.20/0.54  fof(t19_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(X1,k3_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 0.20/0.54  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.20/0.54  fof(c_0_9, plain, ![X16, X17]:k1_setfam_1(k2_tarski(X16,X17))=k3_xboole_0(X16,X17), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.20/0.54  fof(c_0_10, plain, ![X14, X15]:k1_enumset1(X14,X14,X15)=k2_tarski(X14,X15), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.54  fof(c_0_11, plain, ![X7, X8]:r1_tarski(k3_xboole_0(X7,X8),X7), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.20/0.54  cnf(c_0_12, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.54  cnf(c_0_13, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.54  fof(c_0_14, plain, ![X18, X19]:(~v1_relat_1(X18)|v1_relat_1(k3_xboole_0(X18,X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_relat_1])])).
% 0.20/0.54  fof(c_0_15, plain, ![X20, X21, X22, X23]:(~v1_relat_1(X20)|(~v1_relat_1(X21)|(~v1_relat_1(X22)|(~v1_relat_1(X23)|(~r1_tarski(X20,X21)|~r1_tarski(X22,X23)|r1_tarski(k5_relat_1(X20,X22),k5_relat_1(X21,X23))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_relat_1])])])).
% 0.20/0.54  cnf(c_0_16, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.54  cnf(c_0_17, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_12, c_0_13])).
% 0.20/0.54  cnf(c_0_18, plain, (v1_relat_1(k3_xboole_0(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.54  fof(c_0_19, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.54  cnf(c_0_20, plain, (r1_tarski(k5_relat_1(X1,X3),k5_relat_1(X2,X4))|~v1_relat_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X3)|~v1_relat_1(X4)|~r1_tarski(X1,X2)|~r1_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.54  cnf(c_0_21, plain, (r1_tarski(k1_setfam_1(k1_enumset1(X1,X1,X2)),X1)), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 0.20/0.54  cnf(c_0_22, plain, (v1_relat_1(k1_setfam_1(k1_enumset1(X1,X1,X2)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_18, c_0_17])).
% 0.20/0.54  cnf(c_0_23, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.54  fof(c_0_24, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3))))))), inference(assume_negation,[status(cth)],[t52_relat_1])).
% 0.20/0.54  cnf(c_0_25, plain, (r1_tarski(k5_relat_1(X1,k1_setfam_1(k1_enumset1(X2,X2,X3))),k5_relat_1(X4,X2))|~v1_relat_1(X2)|~v1_relat_1(X4)|~v1_relat_1(X1)|~r1_tarski(X1,X4)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])).
% 0.20/0.54  cnf(c_0_26, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_23])).
% 0.20/0.54  fof(c_0_27, negated_conjecture, (v1_relat_1(esk1_0)&(v1_relat_1(esk2_0)&(v1_relat_1(esk3_0)&~r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).
% 0.20/0.54  fof(c_0_28, plain, ![X9, X10, X11]:(~r1_tarski(X9,X10)|~r1_tarski(X9,X11)|r1_tarski(X9,k3_xboole_0(X10,X11))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).
% 0.20/0.54  cnf(c_0_29, plain, (r1_tarski(k5_relat_1(X1,k1_setfam_1(k1_enumset1(X2,X2,X3))),k5_relat_1(X1,X2))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.20/0.54  cnf(c_0_30, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.54  cnf(c_0_31, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.54  fof(c_0_32, plain, ![X12, X13]:k2_tarski(X12,X13)=k2_tarski(X13,X12), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.20/0.54  cnf(c_0_33, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.54  cnf(c_0_34, negated_conjecture, (r1_tarski(k5_relat_1(X1,k1_setfam_1(k1_enumset1(esk3_0,esk3_0,X2))),k5_relat_1(X1,esk3_0))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.20/0.54  cnf(c_0_35, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.54  cnf(c_0_36, negated_conjecture, (r1_tarski(k5_relat_1(X1,k1_setfam_1(k1_enumset1(esk2_0,esk2_0,X2))),k5_relat_1(X1,esk2_0))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_29, c_0_31])).
% 0.20/0.54  cnf(c_0_37, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.54  cnf(c_0_38, plain, (r1_tarski(X1,k1_setfam_1(k1_enumset1(X2,X2,X3)))|~r1_tarski(X1,X3)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_33, c_0_17])).
% 0.20/0.54  cnf(c_0_39, negated_conjecture, (r1_tarski(k5_relat_1(esk1_0,k1_setfam_1(k1_enumset1(esk3_0,esk3_0,X1))),k5_relat_1(esk1_0,esk3_0))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.20/0.54  cnf(c_0_40, negated_conjecture, (r1_tarski(k5_relat_1(esk1_0,k1_setfam_1(k1_enumset1(esk2_0,esk2_0,X1))),k5_relat_1(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_36, c_0_35])).
% 0.20/0.54  cnf(c_0_41, plain, (k1_enumset1(X1,X1,X2)=k1_enumset1(X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_13]), c_0_13])).
% 0.20/0.54  cnf(c_0_42, negated_conjecture, (~r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.54  cnf(c_0_43, negated_conjecture, (r1_tarski(k5_relat_1(esk1_0,k1_setfam_1(k1_enumset1(esk3_0,esk3_0,X1))),k1_setfam_1(k1_enumset1(X2,X2,k5_relat_1(esk1_0,esk3_0))))|~r1_tarski(k5_relat_1(esk1_0,k1_setfam_1(k1_enumset1(esk3_0,esk3_0,X1))),X2)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.20/0.54  cnf(c_0_44, negated_conjecture, (r1_tarski(k5_relat_1(esk1_0,k1_setfam_1(k1_enumset1(X1,X1,esk2_0))),k5_relat_1(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.20/0.54  cnf(c_0_45, negated_conjecture, (~r1_tarski(k5_relat_1(esk1_0,k1_setfam_1(k1_enumset1(esk2_0,esk2_0,esk3_0))),k1_setfam_1(k1_enumset1(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk3_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_17]), c_0_17])).
% 0.20/0.54  cnf(c_0_46, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_41]), c_0_45]), ['proof']).
% 0.20/0.54  # SZS output end CNFRefutation
% 0.20/0.54  # Proof object total steps             : 47
% 0.20/0.54  # Proof object clause steps            : 28
% 0.20/0.54  # Proof object formula steps           : 19
% 0.20/0.54  # Proof object conjectures             : 15
% 0.20/0.54  # Proof object clause conjectures      : 12
% 0.20/0.54  # Proof object formula conjectures     : 3
% 0.20/0.54  # Proof object initial clauses used    : 12
% 0.20/0.54  # Proof object initial formulas used   : 9
% 0.20/0.54  # Proof object generating inferences   : 9
% 0.20/0.54  # Proof object simplifying inferences  : 12
% 0.20/0.54  # Training examples: 0 positive, 0 negative
% 0.20/0.54  # Parsed axioms                        : 9
% 0.20/0.54  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.54  # Initial clauses                      : 14
% 0.20/0.54  # Removed in clause preprocessing      : 2
% 0.20/0.54  # Initial clauses in saturation        : 12
% 0.20/0.54  # Processed clauses                    : 918
% 0.20/0.54  # ...of these trivial                  : 234
% 0.20/0.54  # ...subsumed                          : 157
% 0.20/0.54  # ...remaining for further processing  : 527
% 0.20/0.54  # Other redundant clauses eliminated   : 2
% 0.20/0.54  # Clauses deleted for lack of memory   : 0
% 0.20/0.54  # Backward-subsumed                    : 0
% 0.20/0.54  # Backward-rewritten                   : 29
% 0.20/0.54  # Generated clauses                    : 13903
% 0.20/0.54  # ...of the previous two non-trivial   : 11818
% 0.20/0.54  # Contextual simplify-reflections      : 3
% 0.20/0.54  # Paramodulations                      : 13901
% 0.20/0.54  # Factorizations                       : 0
% 0.20/0.54  # Equation resolutions                 : 2
% 0.20/0.54  # Propositional unsat checks           : 0
% 0.20/0.54  #    Propositional check models        : 0
% 0.20/0.54  #    Propositional check unsatisfiable : 0
% 0.20/0.54  #    Propositional clauses             : 0
% 0.20/0.54  #    Propositional clauses after purity: 0
% 0.20/0.54  #    Propositional unsat core size     : 0
% 0.20/0.54  #    Propositional preprocessing time  : 0.000
% 0.20/0.54  #    Propositional encoding time       : 0.000
% 0.20/0.54  #    Propositional solver time         : 0.000
% 0.20/0.54  #    Success case prop preproc time    : 0.000
% 0.20/0.54  #    Success case prop encoding time   : 0.000
% 0.20/0.54  #    Success case prop solver time     : 0.000
% 0.20/0.54  # Current number of processed clauses  : 485
% 0.20/0.54  #    Positive orientable unit clauses  : 259
% 0.20/0.54  #    Positive unorientable unit clauses: 1
% 0.20/0.54  #    Negative unit clauses             : 1
% 0.20/0.54  #    Non-unit-clauses                  : 224
% 0.20/0.54  # Current number of unprocessed clauses: 10906
% 0.20/0.54  # ...number of literals in the above   : 21149
% 0.20/0.54  # Current number of archived formulas  : 0
% 0.20/0.54  # Current number of archived clauses   : 42
% 0.20/0.54  # Clause-clause subsumption calls (NU) : 20086
% 0.20/0.54  # Rec. Clause-clause subsumption calls : 15610
% 0.20/0.54  # Non-unit clause-clause subsumptions  : 141
% 0.20/0.54  # Unit Clause-clause subsumption calls : 11959
% 0.20/0.54  # Rewrite failures with RHS unbound    : 0
% 0.20/0.54  # BW rewrite match attempts            : 1796
% 0.20/0.54  # BW rewrite match successes           : 33
% 0.20/0.54  # Condensation attempts                : 0
% 0.20/0.54  # Condensation successes               : 0
% 0.20/0.54  # Termbank termtop insertions          : 449999
% 0.20/0.54  
% 0.20/0.54  # -------------------------------------------------
% 0.20/0.54  # User time                : 0.183 s
% 0.20/0.54  # System time              : 0.010 s
% 0.20/0.54  # Total time               : 0.194 s
% 0.20/0.54  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------

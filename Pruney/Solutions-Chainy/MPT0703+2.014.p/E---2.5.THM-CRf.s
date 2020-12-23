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
% DateTime   : Thu Dec  3 10:55:15 EST 2020

% Result     : Theorem 0.54s
% Output     : CNFRefutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :   41 (  72 expanded)
%              Number of clauses        :   22 (  28 expanded)
%              Number of leaves         :    9 (  18 expanded)
%              Depth                    :    6
%              Number of atoms          :   92 ( 207 expanded)
%              Number of equality atoms :   20 (  27 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t158_funct_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( ( r1_tarski(k10_relat_1(X3,X1),k10_relat_1(X3,X2))
          & r1_tarski(X1,k2_relat_1(X3)) )
       => r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t145_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

fof(t148_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => k9_relat_1(X2,k10_relat_1(X2,X1)) = k3_xboole_0(X1,k9_relat_1(X2,k1_relat_1(X2))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t146_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(t156_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

fof(c_0_9,plain,(
    ! [X15,X16] : k1_setfam_1(k2_tarski(X15,X16)) = k3_xboole_0(X15,X16) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_10,plain,(
    ! [X13,X14] : k1_enumset1(X13,X13,X14) = k2_tarski(X13,X14) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => ( ( r1_tarski(k10_relat_1(X3,X1),k10_relat_1(X3,X2))
            & r1_tarski(X1,k2_relat_1(X3)) )
         => r1_tarski(X1,X2) ) ) ),
    inference(assume_negation,[status(cth)],[t158_funct_1])).

fof(c_0_12,plain,(
    ! [X8,X9,X10] :
      ( ~ r1_tarski(X8,X9)
      | ~ r1_tarski(X9,X10)
      | r1_tarski(X8,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_13,plain,(
    ! [X36,X37] :
      ( ~ v1_relat_1(X37)
      | ~ v1_funct_1(X37)
      | r1_tarski(k9_relat_1(X37,k10_relat_1(X37,X36)),X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).

fof(c_0_14,plain,(
    ! [X40,X41] :
      ( ~ v1_relat_1(X41)
      | ~ v1_funct_1(X41)
      | k9_relat_1(X41,k10_relat_1(X41,X40)) = k3_xboole_0(X40,k9_relat_1(X41,k1_relat_1(X41))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_funct_1])])).

cnf(c_0_15,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_17,plain,(
    ! [X11,X12] :
      ( ~ r1_tarski(X11,X12)
      | k3_xboole_0(X11,X12) = X11 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_18,negated_conjecture,
    ( v1_relat_1(esk4_0)
    & v1_funct_1(esk4_0)
    & r1_tarski(k10_relat_1(esk4_0,esk2_0),k10_relat_1(esk4_0,esk3_0))
    & r1_tarski(esk2_0,k2_relat_1(esk4_0))
    & ~ r1_tarski(esk2_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

fof(c_0_19,plain,(
    ! [X17] :
      ( ~ v1_relat_1(X17)
      | k9_relat_1(X17,k1_relat_1(X17)) = k2_relat_1(X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,plain,
    ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_22,plain,(
    ! [X18,X19,X20] :
      ( ~ v1_relat_1(X20)
      | ~ r1_tarski(X18,X19)
      | r1_tarski(k9_relat_1(X20,X18),k9_relat_1(X20,X19)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t156_relat_1])])).

cnf(c_0_23,plain,
    ( k9_relat_1(X1,k10_relat_1(X1,X2)) = k3_xboole_0(X2,k9_relat_1(X1,k1_relat_1(X1)))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_25,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,negated_conjecture,
    ( r1_tarski(esk2_0,k2_relat_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(X1,k9_relat_1(X3,k10_relat_1(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_30,plain,
    ( r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( k9_relat_1(X1,k10_relat_1(X1,X2)) = k1_setfam_1(k1_enumset1(X2,X2,k9_relat_1(X1,k1_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_33,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_25,c_0_24])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(esk2_0,k9_relat_1(esk4_0,k1_relat_1(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])])).

cnf(c_0_35,plain,
    ( r1_tarski(k9_relat_1(X1,X2),X3)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k10_relat_1(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk4_0,esk2_0),k10_relat_1(esk4_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_37,negated_conjecture,
    ( k9_relat_1(esk4_0,k10_relat_1(esk4_0,X1)) = k1_setfam_1(k1_enumset1(X1,X1,k9_relat_1(esk4_0,k1_relat_1(esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_28])])).

cnf(c_0_38,negated_conjecture,
    ( k1_setfam_1(k1_enumset1(esk2_0,esk2_0,k9_relat_1(esk4_0,k1_relat_1(esk4_0)))) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( ~ r1_tarski(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_40,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_38]),c_0_32]),c_0_28])]),c_0_39]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:53:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.54/0.72  # AutoSched0-Mode selected heuristic G_E___107_C36_F1_PI_AE_Q4_CS_SP_PS_S0Y
% 0.54/0.72  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.54/0.72  #
% 0.54/0.72  # Preprocessing time       : 0.028 s
% 0.54/0.72  # Presaturation interreduction done
% 0.54/0.72  
% 0.54/0.72  # Proof found!
% 0.54/0.72  # SZS status Theorem
% 0.54/0.72  # SZS output start CNFRefutation
% 0.54/0.72  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.54/0.72  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.54/0.72  fof(t158_funct_1, conjecture, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((r1_tarski(k10_relat_1(X3,X1),k10_relat_1(X3,X2))&r1_tarski(X1,k2_relat_1(X3)))=>r1_tarski(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t158_funct_1)).
% 0.54/0.72  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.54/0.72  fof(t145_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 0.54/0.72  fof(t148_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>k9_relat_1(X2,k10_relat_1(X2,X1))=k3_xboole_0(X1,k9_relat_1(X2,k1_relat_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_funct_1)).
% 0.54/0.72  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.54/0.72  fof(t146_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 0.54/0.72  fof(t156_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t156_relat_1)).
% 0.54/0.72  fof(c_0_9, plain, ![X15, X16]:k1_setfam_1(k2_tarski(X15,X16))=k3_xboole_0(X15,X16), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.54/0.72  fof(c_0_10, plain, ![X13, X14]:k1_enumset1(X13,X13,X14)=k2_tarski(X13,X14), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.54/0.72  fof(c_0_11, negated_conjecture, ~(![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((r1_tarski(k10_relat_1(X3,X1),k10_relat_1(X3,X2))&r1_tarski(X1,k2_relat_1(X3)))=>r1_tarski(X1,X2)))), inference(assume_negation,[status(cth)],[t158_funct_1])).
% 0.54/0.72  fof(c_0_12, plain, ![X8, X9, X10]:(~r1_tarski(X8,X9)|~r1_tarski(X9,X10)|r1_tarski(X8,X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.54/0.72  fof(c_0_13, plain, ![X36, X37]:(~v1_relat_1(X37)|~v1_funct_1(X37)|r1_tarski(k9_relat_1(X37,k10_relat_1(X37,X36)),X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).
% 0.54/0.72  fof(c_0_14, plain, ![X40, X41]:(~v1_relat_1(X41)|~v1_funct_1(X41)|k9_relat_1(X41,k10_relat_1(X41,X40))=k3_xboole_0(X40,k9_relat_1(X41,k1_relat_1(X41)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_funct_1])])).
% 0.54/0.72  cnf(c_0_15, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.54/0.72  cnf(c_0_16, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.54/0.72  fof(c_0_17, plain, ![X11, X12]:(~r1_tarski(X11,X12)|k3_xboole_0(X11,X12)=X11), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.54/0.72  fof(c_0_18, negated_conjecture, ((v1_relat_1(esk4_0)&v1_funct_1(esk4_0))&((r1_tarski(k10_relat_1(esk4_0,esk2_0),k10_relat_1(esk4_0,esk3_0))&r1_tarski(esk2_0,k2_relat_1(esk4_0)))&~r1_tarski(esk2_0,esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 0.54/0.72  fof(c_0_19, plain, ![X17]:(~v1_relat_1(X17)|k9_relat_1(X17,k1_relat_1(X17))=k2_relat_1(X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).
% 0.54/0.72  cnf(c_0_20, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.54/0.72  cnf(c_0_21, plain, (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.54/0.72  fof(c_0_22, plain, ![X18, X19, X20]:(~v1_relat_1(X20)|(~r1_tarski(X18,X19)|r1_tarski(k9_relat_1(X20,X18),k9_relat_1(X20,X19)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t156_relat_1])])).
% 0.54/0.72  cnf(c_0_23, plain, (k9_relat_1(X1,k10_relat_1(X1,X2))=k3_xboole_0(X2,k9_relat_1(X1,k1_relat_1(X1)))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.54/0.72  cnf(c_0_24, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 0.54/0.72  cnf(c_0_25, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.54/0.72  cnf(c_0_26, negated_conjecture, (r1_tarski(esk2_0,k2_relat_1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.54/0.72  cnf(c_0_27, plain, (k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.54/0.72  cnf(c_0_28, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.54/0.72  cnf(c_0_29, plain, (r1_tarski(X1,X2)|~v1_funct_1(X3)|~v1_relat_1(X3)|~r1_tarski(X1,k9_relat_1(X3,k10_relat_1(X3,X2)))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.54/0.72  cnf(c_0_30, plain, (r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,X3))|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.54/0.72  cnf(c_0_31, plain, (k9_relat_1(X1,k10_relat_1(X1,X2))=k1_setfam_1(k1_enumset1(X2,X2,k9_relat_1(X1,k1_relat_1(X1))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 0.54/0.72  cnf(c_0_32, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.54/0.72  cnf(c_0_33, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_25, c_0_24])).
% 0.54/0.72  cnf(c_0_34, negated_conjecture, (r1_tarski(esk2_0,k9_relat_1(esk4_0,k1_relat_1(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])])).
% 0.54/0.72  cnf(c_0_35, plain, (r1_tarski(k9_relat_1(X1,X2),X3)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(X2,k10_relat_1(X1,X3))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.54/0.72  cnf(c_0_36, negated_conjecture, (r1_tarski(k10_relat_1(esk4_0,esk2_0),k10_relat_1(esk4_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.54/0.72  cnf(c_0_37, negated_conjecture, (k9_relat_1(esk4_0,k10_relat_1(esk4_0,X1))=k1_setfam_1(k1_enumset1(X1,X1,k9_relat_1(esk4_0,k1_relat_1(esk4_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_28])])).
% 0.54/0.72  cnf(c_0_38, negated_conjecture, (k1_setfam_1(k1_enumset1(esk2_0,esk2_0,k9_relat_1(esk4_0,k1_relat_1(esk4_0))))=esk2_0), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.54/0.72  cnf(c_0_39, negated_conjecture, (~r1_tarski(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.54/0.72  cnf(c_0_40, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37]), c_0_38]), c_0_32]), c_0_28])]), c_0_39]), ['proof']).
% 0.54/0.72  # SZS output end CNFRefutation
% 0.54/0.72  # Proof object total steps             : 41
% 0.54/0.72  # Proof object clause steps            : 22
% 0.54/0.72  # Proof object formula steps           : 19
% 0.54/0.72  # Proof object conjectures             : 12
% 0.54/0.72  # Proof object clause conjectures      : 9
% 0.54/0.72  # Proof object formula conjectures     : 3
% 0.54/0.72  # Proof object initial clauses used    : 13
% 0.54/0.72  # Proof object initial formulas used   : 9
% 0.54/0.72  # Proof object generating inferences   : 6
% 0.54/0.72  # Proof object simplifying inferences  : 13
% 0.54/0.72  # Training examples: 0 positive, 0 negative
% 0.54/0.72  # Parsed axioms                        : 19
% 0.54/0.72  # Removed by relevancy pruning/SinE    : 0
% 0.54/0.72  # Initial clauses                      : 29
% 0.54/0.72  # Removed in clause preprocessing      : 2
% 0.54/0.72  # Initial clauses in saturation        : 27
% 0.54/0.72  # Processed clauses                    : 3051
% 0.54/0.72  # ...of these trivial                  : 73
% 0.54/0.72  # ...subsumed                          : 2191
% 0.54/0.72  # ...remaining for further processing  : 787
% 0.54/0.72  # Other redundant clauses eliminated   : 2
% 0.54/0.72  # Clauses deleted for lack of memory   : 0
% 0.54/0.72  # Backward-subsumed                    : 89
% 0.54/0.72  # Backward-rewritten                   : 41
% 0.54/0.72  # Generated clauses                    : 30015
% 0.54/0.72  # ...of the previous two non-trivial   : 24398
% 0.54/0.72  # Contextual simplify-reflections      : 5
% 0.54/0.72  # Paramodulations                      : 29999
% 0.54/0.72  # Factorizations                       : 14
% 0.54/0.72  # Equation resolutions                 : 2
% 0.54/0.72  # Propositional unsat checks           : 0
% 0.54/0.72  #    Propositional check models        : 0
% 0.54/0.72  #    Propositional check unsatisfiable : 0
% 0.54/0.72  #    Propositional clauses             : 0
% 0.54/0.72  #    Propositional clauses after purity: 0
% 0.54/0.72  #    Propositional unsat core size     : 0
% 0.54/0.72  #    Propositional preprocessing time  : 0.000
% 0.54/0.72  #    Propositional encoding time       : 0.000
% 0.54/0.72  #    Propositional solver time         : 0.000
% 0.54/0.72  #    Success case prop preproc time    : 0.000
% 0.54/0.72  #    Success case prop encoding time   : 0.000
% 0.54/0.72  #    Success case prop solver time     : 0.000
% 0.54/0.72  # Current number of processed clauses  : 629
% 0.54/0.72  #    Positive orientable unit clauses  : 101
% 0.54/0.72  #    Positive unorientable unit clauses: 2
% 0.54/0.72  #    Negative unit clauses             : 4
% 0.54/0.72  #    Non-unit-clauses                  : 522
% 0.54/0.72  # Current number of unprocessed clauses: 20970
% 0.54/0.72  # ...number of literals in the above   : 74606
% 0.54/0.72  # Current number of archived formulas  : 0
% 0.54/0.72  # Current number of archived clauses   : 158
% 0.54/0.72  # Clause-clause subsumption calls (NU) : 68876
% 0.54/0.72  # Rec. Clause-clause subsumption calls : 54078
% 0.54/0.72  # Non-unit clause-clause subsumptions  : 1799
% 0.54/0.72  # Unit Clause-clause subsumption calls : 679
% 0.54/0.72  # Rewrite failures with RHS unbound    : 0
% 0.54/0.72  # BW rewrite match attempts            : 199
% 0.54/0.72  # BW rewrite match successes           : 43
% 0.54/0.72  # Condensation attempts                : 0
% 0.54/0.72  # Condensation successes               : 0
% 0.54/0.72  # Termbank termtop insertions          : 458352
% 0.54/0.72  
% 0.54/0.72  # -------------------------------------------------
% 0.54/0.72  # User time                : 0.334 s
% 0.54/0.72  # System time              : 0.025 s
% 0.54/0.72  # Total time               : 0.359 s
% 0.54/0.72  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------

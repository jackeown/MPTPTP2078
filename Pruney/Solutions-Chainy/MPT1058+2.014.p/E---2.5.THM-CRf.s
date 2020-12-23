%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:07:28 EST 2020

% Result     : Theorem 1.29s
% Output     : CNFRefutation 1.29s
% Verified   : 
% Statistics : Number of formulae       :   36 (  77 expanded)
%              Number of clauses        :   19 (  34 expanded)
%              Number of leaves         :    8 (  20 expanded)
%              Depth                    :    8
%              Number of atoms          :   58 ( 117 expanded)
%              Number of equality atoms :   34 (  75 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t139_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k10_relat_1(k7_relat_1(X3,X1),X2) = k3_xboole_0(X1,k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t175_funct_2,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( r1_tarski(k10_relat_1(X1,X3),X2)
         => k10_relat_1(X1,X3) = k10_relat_1(k7_relat_1(X1,X2),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(c_0_8,plain,(
    ! [X29,X30] : k1_setfam_1(k2_tarski(X29,X30)) = k3_xboole_0(X29,X30) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_9,plain,(
    ! [X25,X26] : k1_enumset1(X25,X25,X26) = k2_tarski(X25,X26) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_10,plain,(
    ! [X47,X48,X49] :
      ( ~ v1_relat_1(X49)
      | k10_relat_1(k7_relat_1(X49,X47),X48) = k3_xboole_0(X47,k10_relat_1(X49,X48)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).

cnf(c_0_11,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_13,plain,(
    ! [X21,X22] : k4_xboole_0(X21,k4_xboole_0(X21,X22)) = k3_xboole_0(X21,X22) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_14,plain,(
    ! [X23,X24] : k2_tarski(X23,X24) = k2_tarski(X24,X23) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_15,plain,
    ( k10_relat_1(k7_relat_1(X1,X2),X3) = k3_xboole_0(X2,k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_17,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( k10_relat_1(k7_relat_1(X1,X2),X3) = k1_setfam_1(k1_enumset1(X2,X2,k10_relat_1(X1,X3)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_20,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_setfam_1(k1_enumset1(X1,X1,X2)) ),
    inference(rw,[status(thm)],[c_0_17,c_0_16])).

cnf(c_0_21,plain,
    ( k1_enumset1(X1,X1,X2) = k1_enumset1(X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_12]),c_0_12])).

fof(c_0_22,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ! [X2,X3] :
            ( r1_tarski(k10_relat_1(X1,X3),X2)
           => k10_relat_1(X1,X3) = k10_relat_1(k7_relat_1(X1,X2),X3) ) ) ),
    inference(assume_negation,[status(cth)],[t175_funct_2])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k10_relat_1(X2,X3))) = k10_relat_1(k7_relat_1(X2,X1),X3)
    | ~ v1_relat_1(X2) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_20])).

fof(c_0_25,plain,(
    ! [X11,X12] :
      ( ( k4_xboole_0(X11,X12) != k1_xboole_0
        | r1_tarski(X11,X12) )
      & ( ~ r1_tarski(X11,X12)
        | k4_xboole_0(X11,X12) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_26,plain,(
    ! [X19] : k4_xboole_0(X19,k1_xboole_0) = X19 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_27,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_funct_1(esk3_0)
    & r1_tarski(k10_relat_1(esk3_0,esk5_0),esk4_0)
    & k10_relat_1(esk3_0,esk5_0) != k10_relat_1(k7_relat_1(esk3_0,esk4_0),esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])).

cnf(c_0_28,plain,
    ( k4_xboole_0(k10_relat_1(X1,X2),k4_xboole_0(k10_relat_1(X1,X2),X3)) = k10_relat_1(k7_relat_1(X1,X3),X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( k10_relat_1(esk3_0,esk5_0) != k10_relat_1(k7_relat_1(esk3_0,esk4_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,plain,
    ( k10_relat_1(k7_relat_1(X1,X2),X3) = k10_relat_1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k10_relat_1(X1,X3),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])).

cnf(c_0_33,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk3_0,esk5_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:48:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 1.29/1.46  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 1.29/1.46  # and selection function PSelectComplexExceptUniqMaxHorn.
% 1.29/1.46  #
% 1.29/1.46  # Preprocessing time       : 0.028 s
% 1.29/1.46  
% 1.29/1.46  # Proof found!
% 1.29/1.46  # SZS status Theorem
% 1.29/1.46  # SZS output start CNFRefutation
% 1.29/1.46  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 1.29/1.46  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 1.29/1.46  fof(t139_funct_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k10_relat_1(k7_relat_1(X3,X1),X2)=k3_xboole_0(X1,k10_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 1.29/1.46  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.29/1.46  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 1.29/1.46  fof(t175_funct_2, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:(r1_tarski(k10_relat_1(X1,X3),X2)=>k10_relat_1(X1,X3)=k10_relat_1(k7_relat_1(X1,X2),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_funct_2)).
% 1.29/1.46  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.29/1.46  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 1.29/1.46  fof(c_0_8, plain, ![X29, X30]:k1_setfam_1(k2_tarski(X29,X30))=k3_xboole_0(X29,X30), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 1.29/1.46  fof(c_0_9, plain, ![X25, X26]:k1_enumset1(X25,X25,X26)=k2_tarski(X25,X26), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 1.29/1.46  fof(c_0_10, plain, ![X47, X48, X49]:(~v1_relat_1(X49)|k10_relat_1(k7_relat_1(X49,X47),X48)=k3_xboole_0(X47,k10_relat_1(X49,X48))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).
% 1.29/1.46  cnf(c_0_11, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 1.29/1.46  cnf(c_0_12, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 1.29/1.46  fof(c_0_13, plain, ![X21, X22]:k4_xboole_0(X21,k4_xboole_0(X21,X22))=k3_xboole_0(X21,X22), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 1.29/1.46  fof(c_0_14, plain, ![X23, X24]:k2_tarski(X23,X24)=k2_tarski(X24,X23), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 1.29/1.46  cnf(c_0_15, plain, (k10_relat_1(k7_relat_1(X1,X2),X3)=k3_xboole_0(X2,k10_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 1.29/1.46  cnf(c_0_16, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_11, c_0_12])).
% 1.29/1.46  cnf(c_0_17, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 1.29/1.46  cnf(c_0_18, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.29/1.46  cnf(c_0_19, plain, (k10_relat_1(k7_relat_1(X1,X2),X3)=k1_setfam_1(k1_enumset1(X2,X2,k10_relat_1(X1,X3)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 1.29/1.46  cnf(c_0_20, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_setfam_1(k1_enumset1(X1,X1,X2))), inference(rw,[status(thm)],[c_0_17, c_0_16])).
% 1.29/1.46  cnf(c_0_21, plain, (k1_enumset1(X1,X1,X2)=k1_enumset1(X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_12]), c_0_12])).
% 1.29/1.46  fof(c_0_22, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:(r1_tarski(k10_relat_1(X1,X3),X2)=>k10_relat_1(X1,X3)=k10_relat_1(k7_relat_1(X1,X2),X3)))), inference(assume_negation,[status(cth)],[t175_funct_2])).
% 1.29/1.46  cnf(c_0_23, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k10_relat_1(X2,X3)))=k10_relat_1(k7_relat_1(X2,X1),X3)|~v1_relat_1(X2)), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 1.29/1.46  cnf(c_0_24, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_20])).
% 1.29/1.46  fof(c_0_25, plain, ![X11, X12]:((k4_xboole_0(X11,X12)!=k1_xboole_0|r1_tarski(X11,X12))&(~r1_tarski(X11,X12)|k4_xboole_0(X11,X12)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 1.29/1.46  fof(c_0_26, plain, ![X19]:k4_xboole_0(X19,k1_xboole_0)=X19, inference(variable_rename,[status(thm)],[t3_boole])).
% 1.29/1.46  fof(c_0_27, negated_conjecture, ((v1_relat_1(esk3_0)&v1_funct_1(esk3_0))&(r1_tarski(k10_relat_1(esk3_0,esk5_0),esk4_0)&k10_relat_1(esk3_0,esk5_0)!=k10_relat_1(k7_relat_1(esk3_0,esk4_0),esk5_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])).
% 1.29/1.46  cnf(c_0_28, plain, (k4_xboole_0(k10_relat_1(X1,X2),k4_xboole_0(k10_relat_1(X1,X2),X3))=k10_relat_1(k7_relat_1(X1,X3),X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 1.29/1.46  cnf(c_0_29, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 1.29/1.46  cnf(c_0_30, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_26])).
% 1.29/1.46  cnf(c_0_31, negated_conjecture, (k10_relat_1(esk3_0,esk5_0)!=k10_relat_1(k7_relat_1(esk3_0,esk4_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 1.29/1.46  cnf(c_0_32, plain, (k10_relat_1(k7_relat_1(X1,X2),X3)=k10_relat_1(X1,X3)|~v1_relat_1(X1)|~r1_tarski(k10_relat_1(X1,X3),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30])).
% 1.29/1.46  cnf(c_0_33, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 1.29/1.46  cnf(c_0_34, negated_conjecture, (r1_tarski(k10_relat_1(esk3_0,esk5_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 1.29/1.46  cnf(c_0_35, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33]), c_0_34])]), ['proof']).
% 1.29/1.46  # SZS output end CNFRefutation
% 1.29/1.46  # Proof object total steps             : 36
% 1.29/1.46  # Proof object clause steps            : 19
% 1.29/1.46  # Proof object formula steps           : 17
% 1.29/1.46  # Proof object conjectures             : 7
% 1.29/1.46  # Proof object clause conjectures      : 4
% 1.29/1.46  # Proof object formula conjectures     : 3
% 1.29/1.46  # Proof object initial clauses used    : 10
% 1.29/1.46  # Proof object initial formulas used   : 8
% 1.29/1.46  # Proof object generating inferences   : 4
% 1.29/1.46  # Proof object simplifying inferences  : 11
% 1.29/1.46  # Training examples: 0 positive, 0 negative
% 1.29/1.46  # Parsed axioms                        : 22
% 1.29/1.46  # Removed by relevancy pruning/SinE    : 0
% 1.29/1.46  # Initial clauses                      : 35
% 1.29/1.46  # Removed in clause preprocessing      : 3
% 1.29/1.46  # Initial clauses in saturation        : 32
% 1.29/1.46  # Processed clauses                    : 3602
% 1.29/1.46  # ...of these trivial                  : 56
% 1.29/1.46  # ...subsumed                          : 2582
% 1.29/1.46  # ...remaining for further processing  : 964
% 1.29/1.46  # Other redundant clauses eliminated   : 50
% 1.29/1.46  # Clauses deleted for lack of memory   : 0
% 1.29/1.46  # Backward-subsumed                    : 31
% 1.29/1.46  # Backward-rewritten                   : 70
% 1.29/1.46  # Generated clauses                    : 69423
% 1.29/1.46  # ...of the previous two non-trivial   : 63405
% 1.29/1.46  # Contextual simplify-reflections      : 18
% 1.29/1.46  # Paramodulations                      : 69318
% 1.29/1.46  # Factorizations                       : 28
% 1.29/1.46  # Equation resolutions                 : 77
% 1.29/1.46  # Propositional unsat checks           : 0
% 1.29/1.46  #    Propositional check models        : 0
% 1.29/1.46  #    Propositional check unsatisfiable : 0
% 1.29/1.46  #    Propositional clauses             : 0
% 1.29/1.46  #    Propositional clauses after purity: 0
% 1.29/1.46  #    Propositional unsat core size     : 0
% 1.29/1.46  #    Propositional preprocessing time  : 0.000
% 1.29/1.46  #    Propositional encoding time       : 0.000
% 1.29/1.46  #    Propositional solver time         : 0.000
% 1.29/1.46  #    Success case prop preproc time    : 0.000
% 1.29/1.46  #    Success case prop encoding time   : 0.000
% 1.29/1.46  #    Success case prop solver time     : 0.000
% 1.29/1.46  # Current number of processed clauses  : 863
% 1.29/1.46  #    Positive orientable unit clauses  : 78
% 1.29/1.46  #    Positive unorientable unit clauses: 2
% 1.29/1.46  #    Negative unit clauses             : 31
% 1.29/1.46  #    Non-unit-clauses                  : 752
% 1.29/1.46  # Current number of unprocessed clauses: 59182
% 1.29/1.46  # ...number of literals in the above   : 312287
% 1.29/1.46  # Current number of archived formulas  : 0
% 1.29/1.46  # Current number of archived clauses   : 104
% 1.29/1.46  # Clause-clause subsumption calls (NU) : 63735
% 1.29/1.46  # Rec. Clause-clause subsumption calls : 16347
% 1.29/1.46  # Non-unit clause-clause subsumptions  : 1382
% 1.29/1.46  # Unit Clause-clause subsumption calls : 2225
% 1.29/1.46  # Rewrite failures with RHS unbound    : 14
% 1.29/1.46  # BW rewrite match attempts            : 613
% 1.29/1.46  # BW rewrite match successes           : 39
% 1.29/1.46  # Condensation attempts                : 0
% 1.29/1.46  # Condensation successes               : 0
% 1.29/1.46  # Termbank termtop insertions          : 1656879
% 1.30/1.46  
% 1.30/1.46  # -------------------------------------------------
% 1.30/1.46  # User time                : 1.051 s
% 1.30/1.46  # System time              : 0.064 s
% 1.30/1.46  # Total time               : 1.115 s
% 1.30/1.46  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------

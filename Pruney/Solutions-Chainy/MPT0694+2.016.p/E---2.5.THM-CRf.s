%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:54:58 EST 2020

% Result     : Theorem 0.51s
% Output     : CNFRefutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 234 expanded)
%              Number of clauses        :   30 ( 102 expanded)
%              Number of leaves         :   12 (  64 expanded)
%              Depth                    :    9
%              Number of atoms          :  117 ( 335 expanded)
%              Number of equality atoms :   24 ( 188 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t149_funct_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => r1_tarski(k9_relat_1(X3,k3_xboole_0(X1,k10_relat_1(X3,X2))),k3_xboole_0(k9_relat_1(X3,X1),X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_funct_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t19_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

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

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t158_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ! [X4] :
          ( v1_relat_1(X4)
         => ( ( r1_tarski(X3,X4)
              & r1_tarski(X1,X2) )
           => r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X4,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_relat_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(c_0_12,plain,(
    ! [X24,X25] : k1_setfam_1(k2_tarski(X24,X25)) = k3_xboole_0(X24,X25) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_13,plain,(
    ! [X19,X20] : k1_enumset1(X19,X19,X20) = k2_tarski(X19,X20) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => r1_tarski(k9_relat_1(X3,k3_xboole_0(X1,k10_relat_1(X3,X2))),k3_xboole_0(k9_relat_1(X3,X1),X2)) ) ),
    inference(assume_negation,[status(cth)],[t149_funct_1])).

fof(c_0_15,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_16,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_18,plain,(
    ! [X21,X22,X23] : k2_enumset1(X21,X21,X22,X23) = k1_enumset1(X21,X22,X23) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_19,plain,(
    ! [X17,X18] : k4_xboole_0(X17,k4_xboole_0(X17,X18)) = k3_xboole_0(X17,X18) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_20,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_funct_1(esk3_0)
    & ~ r1_tarski(k9_relat_1(esk3_0,k3_xboole_0(esk1_0,k10_relat_1(esk3_0,esk2_0))),k3_xboole_0(k9_relat_1(esk3_0,esk1_0),esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

cnf(c_0_21,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_25,plain,(
    ! [X9,X10,X11] :
      ( ~ r1_tarski(X9,X10)
      | ~ r1_tarski(X9,X11)
      | r1_tarski(X9,k3_xboole_0(X10,X11)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).

cnf(c_0_26,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk3_0,k3_xboole_0(esk1_0,k10_relat_1(esk3_0,esk2_0))),k3_xboole_0(k9_relat_1(esk3_0,esk1_0),esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) = k1_setfam_1(k2_enumset1(X2,X2,X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_22]),c_0_22]),c_0_23]),c_0_23])).

cnf(c_0_28,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_22]),c_0_23])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_30,plain,(
    ! [X12,X13,X14] :
      ( ~ r1_tarski(X12,X13)
      | ~ r1_tarski(X13,X14)
      | r1_tarski(X12,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_31,plain,(
    ! [X40,X41] :
      ( ~ v1_relat_1(X41)
      | ~ v1_funct_1(X41)
      | r1_tarski(k9_relat_1(X41,k10_relat_1(X41,X40)),X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).

cnf(c_0_32,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk3_0,k1_setfam_1(k2_enumset1(esk1_0,esk1_0,esk1_0,k10_relat_1(esk3_0,esk2_0)))),k1_setfam_1(k2_enumset1(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk1_0),esk2_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_22]),c_0_22]),c_0_23]),c_0_23])).

cnf(c_0_33,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_28]),c_0_28])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_22]),c_0_23])).

fof(c_0_35,plain,(
    ! [X7,X8] :
      ( ( r1_tarski(X7,X8)
        | X7 != X8 )
      & ( r1_tarski(X8,X7)
        | X7 != X8 )
      & ( ~ r1_tarski(X7,X8)
        | ~ r1_tarski(X8,X7)
        | X7 = X8 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,plain,
    ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_38,plain,(
    ! [X33,X34,X35,X36] :
      ( ~ v1_relat_1(X35)
      | ~ v1_relat_1(X36)
      | ~ r1_tarski(X35,X36)
      | ~ r1_tarski(X33,X34)
      | r1_tarski(k9_relat_1(X35,X33),k9_relat_1(X36,X34)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t158_relat_1])])])).

fof(c_0_39,plain,(
    ! [X15,X16] : r1_tarski(k4_xboole_0(X15,X16),X15) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_40,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk3_0,k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,k10_relat_1(esk3_0,esk2_0)))),k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,k9_relat_1(esk3_0,esk1_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_28]),c_0_28]),c_0_33])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_34,c_0_28])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(X1,k9_relat_1(X3,k10_relat_1(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_44,plain,
    ( r1_tarski(k9_relat_1(X1,X3),k9_relat_1(X2,X4))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_45,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk3_0,k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,k10_relat_1(esk3_0,esk2_0)))),k9_relat_1(esk3_0,esk1_0))
    | ~ r1_tarski(k9_relat_1(esk3_0,k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,k10_relat_1(esk3_0,esk2_0)))),esk2_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_42])).

cnf(c_0_49,plain,
    ( r1_tarski(k9_relat_1(X1,X2),X3)
    | ~ v1_funct_1(X4)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k10_relat_1(X4,X3))
    | ~ r1_tarski(X1,X4) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_50,plain,
    ( r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_45,c_0_33])).

cnf(c_0_51,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk3_0,k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,k10_relat_1(esk3_0,esk2_0)))),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_44]),c_0_47]),c_0_45]),c_0_48])])).

cnf(c_0_52,plain,
    ( r1_tarski(k9_relat_1(X1,k4_xboole_0(X2,k4_xboole_0(X2,k10_relat_1(X3,X4)))),X4)
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_53,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_54,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53]),c_0_47]),c_0_48])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:33:02 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.35  # No SInE strategy applied
% 0.12/0.35  # Trying AutoSched0 for 299 seconds
% 0.51/0.68  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.51/0.68  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.51/0.68  #
% 0.51/0.68  # Preprocessing time       : 0.027 s
% 0.51/0.68  # Presaturation interreduction done
% 0.51/0.68  
% 0.51/0.68  # Proof found!
% 0.51/0.68  # SZS status Theorem
% 0.51/0.68  # SZS output start CNFRefutation
% 0.51/0.68  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.51/0.68  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.51/0.68  fof(t149_funct_1, conjecture, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>r1_tarski(k9_relat_1(X3,k3_xboole_0(X1,k10_relat_1(X3,X2))),k3_xboole_0(k9_relat_1(X3,X1),X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_funct_1)).
% 0.51/0.68  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.51/0.68  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.51/0.68  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.51/0.68  fof(t19_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(X1,k3_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 0.51/0.68  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.51/0.68  fof(t145_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 0.51/0.68  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.51/0.68  fof(t158_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>![X4]:(v1_relat_1(X4)=>((r1_tarski(X3,X4)&r1_tarski(X1,X2))=>r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t158_relat_1)).
% 0.51/0.68  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.51/0.68  fof(c_0_12, plain, ![X24, X25]:k1_setfam_1(k2_tarski(X24,X25))=k3_xboole_0(X24,X25), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.51/0.68  fof(c_0_13, plain, ![X19, X20]:k1_enumset1(X19,X19,X20)=k2_tarski(X19,X20), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.51/0.68  fof(c_0_14, negated_conjecture, ~(![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>r1_tarski(k9_relat_1(X3,k3_xboole_0(X1,k10_relat_1(X3,X2))),k3_xboole_0(k9_relat_1(X3,X1),X2)))), inference(assume_negation,[status(cth)],[t149_funct_1])).
% 0.51/0.68  fof(c_0_15, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.51/0.68  cnf(c_0_16, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.51/0.68  cnf(c_0_17, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.51/0.68  fof(c_0_18, plain, ![X21, X22, X23]:k2_enumset1(X21,X21,X22,X23)=k1_enumset1(X21,X22,X23), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.51/0.68  fof(c_0_19, plain, ![X17, X18]:k4_xboole_0(X17,k4_xboole_0(X17,X18))=k3_xboole_0(X17,X18), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.51/0.68  fof(c_0_20, negated_conjecture, ((v1_relat_1(esk3_0)&v1_funct_1(esk3_0))&~r1_tarski(k9_relat_1(esk3_0,k3_xboole_0(esk1_0,k10_relat_1(esk3_0,esk2_0))),k3_xboole_0(k9_relat_1(esk3_0,esk1_0),esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.51/0.68  cnf(c_0_21, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.51/0.68  cnf(c_0_22, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 0.51/0.68  cnf(c_0_23, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.51/0.68  cnf(c_0_24, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.51/0.68  fof(c_0_25, plain, ![X9, X10, X11]:(~r1_tarski(X9,X10)|~r1_tarski(X9,X11)|r1_tarski(X9,k3_xboole_0(X10,X11))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).
% 0.51/0.68  cnf(c_0_26, negated_conjecture, (~r1_tarski(k9_relat_1(esk3_0,k3_xboole_0(esk1_0,k10_relat_1(esk3_0,esk2_0))),k3_xboole_0(k9_relat_1(esk3_0,esk1_0),esk2_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.51/0.68  cnf(c_0_27, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,X2))=k1_setfam_1(k2_enumset1(X2,X2,X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_22]), c_0_22]), c_0_23]), c_0_23])).
% 0.51/0.68  cnf(c_0_28, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_setfam_1(k2_enumset1(X1,X1,X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_22]), c_0_23])).
% 0.51/0.68  cnf(c_0_29, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.51/0.68  fof(c_0_30, plain, ![X12, X13, X14]:(~r1_tarski(X12,X13)|~r1_tarski(X13,X14)|r1_tarski(X12,X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.51/0.68  fof(c_0_31, plain, ![X40, X41]:(~v1_relat_1(X41)|~v1_funct_1(X41)|r1_tarski(k9_relat_1(X41,k10_relat_1(X41,X40)),X40)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).
% 0.51/0.68  cnf(c_0_32, negated_conjecture, (~r1_tarski(k9_relat_1(esk3_0,k1_setfam_1(k2_enumset1(esk1_0,esk1_0,esk1_0,k10_relat_1(esk3_0,esk2_0)))),k1_setfam_1(k2_enumset1(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk1_0),esk2_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_22]), c_0_22]), c_0_23]), c_0_23])).
% 0.51/0.68  cnf(c_0_33, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_28]), c_0_28])).
% 0.51/0.68  cnf(c_0_34, plain, (r1_tarski(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))|~r1_tarski(X1,X3)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_22]), c_0_23])).
% 0.51/0.68  fof(c_0_35, plain, ![X7, X8]:(((r1_tarski(X7,X8)|X7!=X8)&(r1_tarski(X8,X7)|X7!=X8))&(~r1_tarski(X7,X8)|~r1_tarski(X8,X7)|X7=X8)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.51/0.68  cnf(c_0_36, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.51/0.68  cnf(c_0_37, plain, (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.51/0.68  fof(c_0_38, plain, ![X33, X34, X35, X36]:(~v1_relat_1(X35)|(~v1_relat_1(X36)|(~r1_tarski(X35,X36)|~r1_tarski(X33,X34)|r1_tarski(k9_relat_1(X35,X33),k9_relat_1(X36,X34))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t158_relat_1])])])).
% 0.51/0.68  fof(c_0_39, plain, ![X15, X16]:r1_tarski(k4_xboole_0(X15,X16),X15), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.51/0.68  cnf(c_0_40, negated_conjecture, (~r1_tarski(k9_relat_1(esk3_0,k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,k10_relat_1(esk3_0,esk2_0)))),k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,k9_relat_1(esk3_0,esk1_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_28]), c_0_28]), c_0_33])).
% 0.51/0.68  cnf(c_0_41, plain, (r1_tarski(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))|~r1_tarski(X1,X3)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_34, c_0_28])).
% 0.51/0.68  cnf(c_0_42, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.51/0.68  cnf(c_0_43, plain, (r1_tarski(X1,X2)|~v1_funct_1(X3)|~v1_relat_1(X3)|~r1_tarski(X1,k9_relat_1(X3,k10_relat_1(X3,X2)))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.51/0.68  cnf(c_0_44, plain, (r1_tarski(k9_relat_1(X1,X3),k9_relat_1(X2,X4))|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.51/0.68  cnf(c_0_45, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.51/0.68  cnf(c_0_46, negated_conjecture, (~r1_tarski(k9_relat_1(esk3_0,k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,k10_relat_1(esk3_0,esk2_0)))),k9_relat_1(esk3_0,esk1_0))|~r1_tarski(k9_relat_1(esk3_0,k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,k10_relat_1(esk3_0,esk2_0)))),esk2_0)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.51/0.68  cnf(c_0_47, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.51/0.68  cnf(c_0_48, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_42])).
% 0.51/0.68  cnf(c_0_49, plain, (r1_tarski(k9_relat_1(X1,X2),X3)|~v1_funct_1(X4)|~v1_relat_1(X4)|~v1_relat_1(X1)|~r1_tarski(X2,k10_relat_1(X4,X3))|~r1_tarski(X1,X4)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.51/0.68  cnf(c_0_50, plain, (r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_45, c_0_33])).
% 0.51/0.68  cnf(c_0_51, negated_conjecture, (~r1_tarski(k9_relat_1(esk3_0,k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,k10_relat_1(esk3_0,esk2_0)))),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_44]), c_0_47]), c_0_45]), c_0_48])])).
% 0.51/0.68  cnf(c_0_52, plain, (r1_tarski(k9_relat_1(X1,k4_xboole_0(X2,k4_xboole_0(X2,k10_relat_1(X3,X4)))),X4)|~v1_funct_1(X3)|~v1_relat_1(X3)|~v1_relat_1(X1)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.51/0.68  cnf(c_0_53, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.51/0.68  cnf(c_0_54, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53]), c_0_47]), c_0_48])]), ['proof']).
% 0.51/0.68  # SZS output end CNFRefutation
% 0.51/0.68  # Proof object total steps             : 55
% 0.51/0.68  # Proof object clause steps            : 30
% 0.51/0.68  # Proof object formula steps           : 25
% 0.51/0.68  # Proof object conjectures             : 11
% 0.51/0.68  # Proof object clause conjectures      : 8
% 0.51/0.68  # Proof object formula conjectures     : 3
% 0.51/0.68  # Proof object initial clauses used    : 14
% 0.51/0.68  # Proof object initial formulas used   : 12
% 0.51/0.68  # Proof object generating inferences   : 7
% 0.51/0.68  # Proof object simplifying inferences  : 28
% 0.51/0.68  # Training examples: 0 positive, 0 negative
% 0.51/0.68  # Parsed axioms                        : 16
% 0.51/0.68  # Removed by relevancy pruning/SinE    : 0
% 0.51/0.68  # Initial clauses                      : 20
% 0.51/0.68  # Removed in clause preprocessing      : 3
% 0.51/0.68  # Initial clauses in saturation        : 17
% 0.51/0.68  # Processed clauses                    : 2976
% 0.51/0.68  # ...of these trivial                  : 13
% 0.51/0.68  # ...subsumed                          : 2188
% 0.51/0.68  # ...remaining for further processing  : 775
% 0.51/0.68  # Other redundant clauses eliminated   : 2
% 0.51/0.68  # Clauses deleted for lack of memory   : 0
% 0.51/0.68  # Backward-subsumed                    : 69
% 0.51/0.68  # Backward-rewritten                   : 22
% 0.51/0.68  # Generated clauses                    : 15928
% 0.51/0.68  # ...of the previous two non-trivial   : 15453
% 0.51/0.68  # Contextual simplify-reflections      : 29
% 0.51/0.68  # Paramodulations                      : 15926
% 0.51/0.68  # Factorizations                       : 0
% 0.51/0.68  # Equation resolutions                 : 2
% 0.51/0.68  # Propositional unsat checks           : 0
% 0.51/0.68  #    Propositional check models        : 0
% 0.51/0.68  #    Propositional check unsatisfiable : 0
% 0.51/0.68  #    Propositional clauses             : 0
% 0.51/0.68  #    Propositional clauses after purity: 0
% 0.51/0.68  #    Propositional unsat core size     : 0
% 0.51/0.68  #    Propositional preprocessing time  : 0.000
% 0.51/0.68  #    Propositional encoding time       : 0.000
% 0.51/0.68  #    Propositional solver time         : 0.000
% 0.51/0.68  #    Success case prop preproc time    : 0.000
% 0.51/0.68  #    Success case prop encoding time   : 0.000
% 0.51/0.68  #    Success case prop solver time     : 0.000
% 0.51/0.68  # Current number of processed clauses  : 666
% 0.51/0.68  #    Positive orientable unit clauses  : 18
% 0.51/0.68  #    Positive unorientable unit clauses: 1
% 0.51/0.68  #    Negative unit clauses             : 4
% 0.51/0.68  #    Non-unit-clauses                  : 643
% 0.51/0.68  # Current number of unprocessed clauses: 12282
% 0.51/0.68  # ...number of literals in the above   : 64773
% 0.51/0.68  # Current number of archived formulas  : 0
% 0.51/0.68  # Current number of archived clauses   : 110
% 0.51/0.68  # Clause-clause subsumption calls (NU) : 244052
% 0.51/0.68  # Rec. Clause-clause subsumption calls : 33986
% 0.51/0.68  # Non-unit clause-clause subsumptions  : 2035
% 0.51/0.68  # Unit Clause-clause subsumption calls : 32
% 0.51/0.68  # Rewrite failures with RHS unbound    : 0
% 0.51/0.68  # BW rewrite match attempts            : 90
% 0.51/0.68  # BW rewrite match successes           : 22
% 0.51/0.68  # Condensation attempts                : 0
% 0.51/0.68  # Condensation successes               : 0
% 0.51/0.68  # Termbank termtop insertions          : 320020
% 0.51/0.68  
% 0.51/0.68  # -------------------------------------------------
% 0.51/0.68  # User time                : 0.320 s
% 0.51/0.68  # System time              : 0.019 s
% 0.51/0.68  # Total time               : 0.338 s
% 0.51/0.68  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------

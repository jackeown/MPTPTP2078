%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:55:30 EST 2020

% Result     : Theorem 0.91s
% Output     : CNFRefutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 137 expanded)
%              Number of clauses        :   31 (  56 expanded)
%              Number of leaves         :   14 (  38 expanded)
%              Depth                    :   12
%              Number of atoms          :  138 ( 274 expanded)
%              Number of equality atoms :   45 ( 117 expanded)
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

fof(t43_funct_1,axiom,(
    ! [X1,X2] : k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) = k6_relat_1(k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t182_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(fc4_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v2_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(t148_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => k9_relat_1(X2,k10_relat_1(X2,X1)) = k3_xboole_0(X1,k9_relat_1(X2,k1_relat_1(X2))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).

fof(t167_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t146_funct_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(t157_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( ( r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X3,X2))
          & r1_tarski(X1,k1_relat_1(X3))
          & v2_funct_1(X3) )
       => r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_funct_1)).

fof(t164_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( ( r1_tarski(X1,k1_relat_1(X2))
          & v2_funct_1(X2) )
       => k10_relat_1(X2,k9_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

fof(c_0_14,plain,(
    ! [X34,X35] : k1_setfam_1(k2_tarski(X34,X35)) = k3_xboole_0(X34,X35) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_15,plain,(
    ! [X29,X30] : k1_enumset1(X29,X29,X30) = k2_tarski(X29,X30) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_16,plain,(
    ! [X61,X62] : k5_relat_1(k6_relat_1(X62),k6_relat_1(X61)) = k6_relat_1(k3_xboole_0(X61,X62)) ),
    inference(variable_rename,[status(thm)],[t43_funct_1])).

cnf(c_0_17,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,plain,(
    ! [X31,X32,X33] : k2_enumset1(X31,X31,X32,X33) = k1_enumset1(X31,X32,X33) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_20,plain,(
    ! [X27,X28] : k2_tarski(X27,X28) = k2_tarski(X28,X27) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_21,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(k3_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_25,plain,(
    ! [X48,X49] :
      ( ~ v1_relat_1(X48)
      | ~ v1_relat_1(X49)
      | k1_relat_1(k5_relat_1(X48,X49)) = k10_relat_1(X48,k1_relat_1(X49)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).

cnf(c_0_26,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(k1_setfam_1(k2_enumset1(X2,X2,X2,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_22]),c_0_23])).

cnf(c_0_27,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k2_enumset1(X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_18]),c_0_18]),c_0_23]),c_0_23])).

fof(c_0_28,plain,(
    ! [X50] :
      ( k1_relat_1(k6_relat_1(X50)) = X50
      & k2_relat_1(k6_relat_1(X50)) = X50 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_29,plain,(
    ! [X51] :
      ( v1_relat_1(k6_relat_1(X51))
      & v2_funct_1(k6_relat_1(X51)) ) ),
    inference(variable_rename,[status(thm)],[fc4_funct_1])).

fof(c_0_30,plain,(
    ! [X56,X57] :
      ( ~ v1_relat_1(X57)
      | ~ v1_funct_1(X57)
      | k9_relat_1(X57,k10_relat_1(X57,X56)) = k3_xboole_0(X56,k9_relat_1(X57,k1_relat_1(X57))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_funct_1])])).

cnf(c_0_31,plain,
    ( k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_26])).

cnf(c_0_33,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,plain,
    ( k9_relat_1(X1,k10_relat_1(X1,X2)) = k3_xboole_0(X2,k9_relat_1(X1,k1_relat_1(X1)))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k10_relat_1(k6_relat_1(X2),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34]),c_0_34])])).

fof(c_0_37,plain,(
    ! [X41,X42] :
      ( ~ v1_relat_1(X42)
      | r1_tarski(k10_relat_1(X42,X41),k1_relat_1(X42)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).

cnf(c_0_38,plain,
    ( k9_relat_1(X1,k10_relat_1(X1,X2)) = k1_setfam_1(k2_enumset1(X2,X2,X2,k9_relat_1(X1,k1_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_22]),c_0_23])).

cnf(c_0_39,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) = k10_relat_1(k6_relat_1(X1),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_26]),c_0_36])).

fof(c_0_40,plain,(
    ! [X17,X18] :
      ( ( r1_tarski(X17,X18)
        | X17 != X18 )
      & ( r1_tarski(X18,X17)
        | X17 != X18 )
      & ( ~ r1_tarski(X17,X18)
        | ~ r1_tarski(X18,X17)
        | X17 = X18 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_41,plain,(
    ! [X52,X53] :
      ( ~ v1_relat_1(X53)
      | ~ r1_tarski(X52,k1_relat_1(X53))
      | r1_tarski(X52,k10_relat_1(X53,k9_relat_1(X53,X52))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_funct_1])])).

fof(c_0_42,plain,(
    ! [X58,X59,X60] :
      ( ~ v1_relat_1(X60)
      | ~ v1_funct_1(X60)
      | ~ r1_tarski(k9_relat_1(X60,X58),k9_relat_1(X60,X59))
      | ~ r1_tarski(X58,k1_relat_1(X60))
      | ~ v2_funct_1(X60)
      | r1_tarski(X58,X59) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t157_funct_1])])).

cnf(c_0_43,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,plain,
    ( k10_relat_1(k6_relat_1(X1),k9_relat_1(X2,k1_relat_1(X2))) = k9_relat_1(X2,k10_relat_1(X2,X1))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(rw,[status(thm)],[c_0_38,c_0_39])).

fof(c_0_45,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( ( r1_tarski(X1,k1_relat_1(X2))
            & v2_funct_1(X2) )
         => k10_relat_1(X2,k9_relat_1(X2,X1)) = X1 ) ) ),
    inference(assume_negation,[status(cth)],[t164_funct_1])).

cnf(c_0_46,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_47,plain,
    ( r1_tarski(X2,k10_relat_1(X1,k9_relat_1(X1,X2)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_48,plain,
    ( r1_tarski(X2,X3)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
    | ~ r1_tarski(X2,k1_relat_1(X1))
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_49,plain,
    ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_33]),c_0_34])])).

fof(c_0_50,negated_conjecture,
    ( v1_relat_1(esk5_0)
    & v1_funct_1(esk5_0)
    & r1_tarski(esk4_0,k1_relat_1(esk5_0))
    & v2_funct_1(esk5_0)
    & k10_relat_1(esk5_0,k9_relat_1(esk5_0,esk4_0)) != esk4_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_45])])])).

cnf(c_0_51,plain,
    ( k10_relat_1(X1,k9_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X2)),X2)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_52,plain,
    ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X2)),X2)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_43])).

cnf(c_0_53,negated_conjecture,
    ( k10_relat_1(esk5_0,k9_relat_1(esk5_0,esk4_0)) != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_54,plain,
    ( k10_relat_1(X1,k9_relat_1(X1,X2)) = X2
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_55,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( v2_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_57,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(esk4_0,k1_relat_1(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_59,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55]),c_0_56]),c_0_57]),c_0_58])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:43:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.91/1.15  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.91/1.15  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.91/1.15  #
% 0.91/1.15  # Preprocessing time       : 0.028 s
% 0.91/1.15  
% 0.91/1.15  # Proof found!
% 0.91/1.15  # SZS status Theorem
% 0.91/1.15  # SZS output start CNFRefutation
% 0.91/1.15  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.91/1.15  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.91/1.15  fof(t43_funct_1, axiom, ![X1, X2]:k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))=k6_relat_1(k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 0.91/1.15  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.91/1.15  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.91/1.15  fof(t182_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 0.91/1.15  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 0.91/1.15  fof(fc4_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v2_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 0.91/1.15  fof(t148_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>k9_relat_1(X2,k10_relat_1(X2,X1))=k3_xboole_0(X1,k9_relat_1(X2,k1_relat_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_funct_1)).
% 0.91/1.15  fof(t167_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 0.91/1.15  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.91/1.15  fof(t146_funct_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 0.91/1.15  fof(t157_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(((r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X3,X2))&r1_tarski(X1,k1_relat_1(X3)))&v2_funct_1(X3))=>r1_tarski(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t157_funct_1)).
% 0.91/1.15  fof(t164_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((r1_tarski(X1,k1_relat_1(X2))&v2_funct_1(X2))=>k10_relat_1(X2,k9_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t164_funct_1)).
% 0.91/1.15  fof(c_0_14, plain, ![X34, X35]:k1_setfam_1(k2_tarski(X34,X35))=k3_xboole_0(X34,X35), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.91/1.15  fof(c_0_15, plain, ![X29, X30]:k1_enumset1(X29,X29,X30)=k2_tarski(X29,X30), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.91/1.15  fof(c_0_16, plain, ![X61, X62]:k5_relat_1(k6_relat_1(X62),k6_relat_1(X61))=k6_relat_1(k3_xboole_0(X61,X62)), inference(variable_rename,[status(thm)],[t43_funct_1])).
% 0.91/1.15  cnf(c_0_17, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.91/1.15  cnf(c_0_18, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.91/1.15  fof(c_0_19, plain, ![X31, X32, X33]:k2_enumset1(X31,X31,X32,X33)=k1_enumset1(X31,X32,X33), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.91/1.15  fof(c_0_20, plain, ![X27, X28]:k2_tarski(X27,X28)=k2_tarski(X28,X27), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.91/1.15  cnf(c_0_21, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(k3_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.91/1.15  cnf(c_0_22, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.91/1.15  cnf(c_0_23, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.91/1.15  cnf(c_0_24, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.91/1.15  fof(c_0_25, plain, ![X48, X49]:(~v1_relat_1(X48)|(~v1_relat_1(X49)|k1_relat_1(k5_relat_1(X48,X49))=k10_relat_1(X48,k1_relat_1(X49)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).
% 0.91/1.15  cnf(c_0_26, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(k1_setfam_1(k2_enumset1(X2,X2,X2,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_22]), c_0_23])).
% 0.91/1.15  cnf(c_0_27, plain, (k2_enumset1(X1,X1,X1,X2)=k2_enumset1(X2,X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_18]), c_0_18]), c_0_23]), c_0_23])).
% 0.91/1.15  fof(c_0_28, plain, ![X50]:(k1_relat_1(k6_relat_1(X50))=X50&k2_relat_1(k6_relat_1(X50))=X50), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.91/1.15  fof(c_0_29, plain, ![X51]:(v1_relat_1(k6_relat_1(X51))&v2_funct_1(k6_relat_1(X51))), inference(variable_rename,[status(thm)],[fc4_funct_1])).
% 0.91/1.15  fof(c_0_30, plain, ![X56, X57]:(~v1_relat_1(X57)|~v1_funct_1(X57)|k9_relat_1(X57,k10_relat_1(X57,X56))=k3_xboole_0(X56,k9_relat_1(X57,k1_relat_1(X57)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_funct_1])])).
% 0.91/1.15  cnf(c_0_31, plain, (k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.91/1.15  cnf(c_0_32, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_26])).
% 0.91/1.15  cnf(c_0_33, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.91/1.15  cnf(c_0_34, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.91/1.15  cnf(c_0_35, plain, (k9_relat_1(X1,k10_relat_1(X1,X2))=k3_xboole_0(X2,k9_relat_1(X1,k1_relat_1(X1)))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.91/1.15  cnf(c_0_36, plain, (k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))=k10_relat_1(k6_relat_1(X2),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33]), c_0_34]), c_0_34])])).
% 0.91/1.15  fof(c_0_37, plain, ![X41, X42]:(~v1_relat_1(X42)|r1_tarski(k10_relat_1(X42,X41),k1_relat_1(X42))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).
% 0.91/1.15  cnf(c_0_38, plain, (k9_relat_1(X1,k10_relat_1(X1,X2))=k1_setfam_1(k2_enumset1(X2,X2,X2,k9_relat_1(X1,k1_relat_1(X1))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_22]), c_0_23])).
% 0.91/1.15  cnf(c_0_39, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,X2))=k10_relat_1(k6_relat_1(X1),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_26]), c_0_36])).
% 0.91/1.15  fof(c_0_40, plain, ![X17, X18]:(((r1_tarski(X17,X18)|X17!=X18)&(r1_tarski(X18,X17)|X17!=X18))&(~r1_tarski(X17,X18)|~r1_tarski(X18,X17)|X17=X18)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.91/1.15  fof(c_0_41, plain, ![X52, X53]:(~v1_relat_1(X53)|(~r1_tarski(X52,k1_relat_1(X53))|r1_tarski(X52,k10_relat_1(X53,k9_relat_1(X53,X52))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_funct_1])])).
% 0.91/1.15  fof(c_0_42, plain, ![X58, X59, X60]:(~v1_relat_1(X60)|~v1_funct_1(X60)|(~r1_tarski(k9_relat_1(X60,X58),k9_relat_1(X60,X59))|~r1_tarski(X58,k1_relat_1(X60))|~v2_funct_1(X60)|r1_tarski(X58,X59))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t157_funct_1])])).
% 0.91/1.15  cnf(c_0_43, plain, (r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.91/1.15  cnf(c_0_44, plain, (k10_relat_1(k6_relat_1(X1),k9_relat_1(X2,k1_relat_1(X2)))=k9_relat_1(X2,k10_relat_1(X2,X1))|~v1_funct_1(X2)|~v1_relat_1(X2)), inference(rw,[status(thm)],[c_0_38, c_0_39])).
% 0.91/1.15  fof(c_0_45, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((r1_tarski(X1,k1_relat_1(X2))&v2_funct_1(X2))=>k10_relat_1(X2,k9_relat_1(X2,X1))=X1))), inference(assume_negation,[status(cth)],[t164_funct_1])).
% 0.91/1.15  cnf(c_0_46, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.91/1.15  cnf(c_0_47, plain, (r1_tarski(X2,k10_relat_1(X1,k9_relat_1(X1,X2)))|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.91/1.15  cnf(c_0_48, plain, (r1_tarski(X2,X3)|~v1_relat_1(X1)|~v1_funct_1(X1)|~r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,X3))|~r1_tarski(X2,k1_relat_1(X1))|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.91/1.15  cnf(c_0_49, plain, (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_33]), c_0_34])])).
% 0.91/1.15  fof(c_0_50, negated_conjecture, ((v1_relat_1(esk5_0)&v1_funct_1(esk5_0))&((r1_tarski(esk4_0,k1_relat_1(esk5_0))&v2_funct_1(esk5_0))&k10_relat_1(esk5_0,k9_relat_1(esk5_0,esk4_0))!=esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_45])])])).
% 0.91/1.15  cnf(c_0_51, plain, (k10_relat_1(X1,k9_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X2)),X2)|~r1_tarski(X2,k1_relat_1(X1))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.91/1.15  cnf(c_0_52, plain, (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X2)),X2)|~v1_funct_1(X1)|~v2_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_43])).
% 0.91/1.15  cnf(c_0_53, negated_conjecture, (k10_relat_1(esk5_0,k9_relat_1(esk5_0,esk4_0))!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.91/1.15  cnf(c_0_54, plain, (k10_relat_1(X1,k9_relat_1(X1,X2))=X2|~v1_funct_1(X1)|~v2_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.91/1.15  cnf(c_0_55, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.91/1.15  cnf(c_0_56, negated_conjecture, (v2_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.91/1.15  cnf(c_0_57, negated_conjecture, (v1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.91/1.15  cnf(c_0_58, negated_conjecture, (r1_tarski(esk4_0,k1_relat_1(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.91/1.15  cnf(c_0_59, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55]), c_0_56]), c_0_57]), c_0_58])]), ['proof']).
% 0.91/1.15  # SZS output end CNFRefutation
% 0.91/1.15  # Proof object total steps             : 60
% 0.91/1.15  # Proof object clause steps            : 31
% 0.91/1.15  # Proof object formula steps           : 29
% 0.91/1.15  # Proof object conjectures             : 9
% 0.91/1.15  # Proof object clause conjectures      : 6
% 0.91/1.15  # Proof object formula conjectures     : 3
% 0.91/1.15  # Proof object initial clauses used    : 18
% 0.91/1.15  # Proof object initial formulas used   : 14
% 0.91/1.15  # Proof object generating inferences   : 8
% 0.91/1.15  # Proof object simplifying inferences  : 25
% 0.91/1.15  # Training examples: 0 positive, 0 negative
% 0.91/1.15  # Parsed axioms                        : 25
% 0.91/1.15  # Removed by relevancy pruning/SinE    : 0
% 0.91/1.15  # Initial clauses                      : 39
% 0.91/1.15  # Removed in clause preprocessing      : 3
% 0.91/1.15  # Initial clauses in saturation        : 36
% 0.91/1.15  # Processed clauses                    : 9749
% 0.91/1.15  # ...of these trivial                  : 574
% 0.91/1.15  # ...subsumed                          : 7904
% 0.91/1.15  # ...remaining for further processing  : 1271
% 0.91/1.15  # Other redundant clauses eliminated   : 2
% 0.91/1.15  # Clauses deleted for lack of memory   : 0
% 0.91/1.15  # Backward-subsumed                    : 65
% 0.91/1.15  # Backward-rewritten                   : 102
% 0.91/1.15  # Generated clauses                    : 87073
% 0.91/1.15  # ...of the previous two non-trivial   : 63615
% 0.91/1.15  # Contextual simplify-reflections      : 14
% 0.91/1.15  # Paramodulations                      : 87071
% 0.91/1.15  # Factorizations                       : 0
% 0.91/1.15  # Equation resolutions                 : 2
% 0.91/1.15  # Propositional unsat checks           : 0
% 0.91/1.15  #    Propositional check models        : 0
% 0.91/1.15  #    Propositional check unsatisfiable : 0
% 0.91/1.15  #    Propositional clauses             : 0
% 0.91/1.15  #    Propositional clauses after purity: 0
% 0.91/1.15  #    Propositional unsat core size     : 0
% 0.91/1.15  #    Propositional preprocessing time  : 0.000
% 0.91/1.15  #    Propositional encoding time       : 0.000
% 0.91/1.15  #    Propositional solver time         : 0.000
% 0.91/1.15  #    Success case prop preproc time    : 0.000
% 0.91/1.15  #    Success case prop encoding time   : 0.000
% 0.91/1.15  #    Success case prop solver time     : 0.000
% 0.91/1.15  # Current number of processed clauses  : 1102
% 0.91/1.15  #    Positive orientable unit clauses  : 261
% 0.91/1.15  #    Positive unorientable unit clauses: 3
% 0.91/1.15  #    Negative unit clauses             : 24
% 0.91/1.15  #    Non-unit-clauses                  : 814
% 0.91/1.15  # Current number of unprocessed clauses: 53406
% 0.91/1.15  # ...number of literals in the above   : 170563
% 0.91/1.15  # Current number of archived formulas  : 0
% 0.91/1.15  # Current number of archived clauses   : 170
% 0.91/1.15  # Clause-clause subsumption calls (NU) : 160043
% 0.91/1.15  # Rec. Clause-clause subsumption calls : 91430
% 0.91/1.15  # Non-unit clause-clause subsumptions  : 6340
% 0.91/1.15  # Unit Clause-clause subsumption calls : 807
% 0.91/1.15  # Rewrite failures with RHS unbound    : 0
% 0.91/1.15  # BW rewrite match attempts            : 1793
% 0.91/1.15  # BW rewrite match successes           : 101
% 0.91/1.15  # Condensation attempts                : 0
% 0.91/1.15  # Condensation successes               : 0
% 0.91/1.15  # Termbank termtop insertions          : 1265103
% 0.91/1.15  
% 0.91/1.15  # -------------------------------------------------
% 0.91/1.15  # User time                : 0.782 s
% 0.91/1.15  # System time              : 0.031 s
% 0.91/1.15  # Total time               : 0.813 s
% 0.91/1.15  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------

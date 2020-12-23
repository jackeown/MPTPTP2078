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
% DateTime   : Thu Dec  3 10:55:31 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  112 (1060 expanded)
%              Number of clauses        :   65 ( 450 expanded)
%              Number of leaves         :   23 ( 276 expanded)
%              Depth                    :   25
%              Number of atoms          :  243 (2264 expanded)
%              Number of equality atoms :   77 ( 901 expanded)
%              Maximal formula depth    :   10 (   3 average)
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

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(t138_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => k10_relat_1(X3,k6_subset_1(X1,X2)) = k6_subset_1(k10_relat_1(X3,X1),k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(t164_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( ( r1_tarski(X1,k1_relat_1(X2))
          & v2_funct_1(X2) )
       => k10_relat_1(X2,k9_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

fof(t175_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k10_relat_1(X3,k2_xboole_0(X1,X2)) = k2_xboole_0(k10_relat_1(X3,X1),k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t167_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t170_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k10_relat_1(X2,X1),k10_relat_1(X2,k2_relat_1(X2))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t170_relat_1)).

fof(t169_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(t147_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r1_tarski(X1,k2_relat_1(X2))
       => k9_relat_1(X2,k10_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

fof(t146_funct_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(t154_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( v2_funct_1(X2)
       => k9_relat_1(X2,X1) = k10_relat_1(k2_funct_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(t157_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( ( r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X3,X2))
          & r1_tarski(X1,k1_relat_1(X3))
          & v2_funct_1(X3) )
       => r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_funct_1)).

fof(t155_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( v2_funct_1(X2)
       => k10_relat_1(X2,X1) = k9_relat_1(k2_funct_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).

fof(c_0_23,plain,(
    ! [X21,X22] : k1_setfam_1(k2_tarski(X21,X22)) = k3_xboole_0(X21,X22) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_24,plain,(
    ! [X17,X18] : k1_enumset1(X17,X17,X18) = k2_tarski(X17,X18) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_25,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_26,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_27,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_28,plain,(
    ! [X15,X16] : k4_xboole_0(X15,k4_xboole_0(X15,X16)) = k3_xboole_0(X15,X16) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_29,plain,(
    ! [X14] :
      ( ~ r1_tarski(X14,k1_xboole_0)
      | X14 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

fof(c_0_30,plain,(
    ! [X11,X12] : r1_tarski(k4_xboole_0(X11,X12),X11) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_31,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_33,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k1_setfam_1(k1_enumset1(X2,X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_32]),c_0_32])).

cnf(c_0_37,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_setfam_1(k1_enumset1(X1,X1,X2)) ),
    inference(rw,[status(thm)],[c_0_33,c_0_32])).

fof(c_0_38,plain,(
    ! [X13] : k4_xboole_0(X13,k1_xboole_0) = X13 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_39,plain,(
    ! [X32,X33,X34] :
      ( ~ v1_relat_1(X34)
      | ~ v1_funct_1(X34)
      | k10_relat_1(X34,k6_subset_1(X32,X33)) = k6_subset_1(k10_relat_1(X34,X32),k10_relat_1(X34,X33)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t138_funct_1])])).

fof(c_0_40,plain,(
    ! [X19,X20] : k6_subset_1(X19,X20) = k4_xboole_0(X19,X20) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

cnf(c_0_41,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_42,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_37]),c_0_37])).

cnf(c_0_43,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_44,plain,
    ( k10_relat_1(X1,k6_subset_1(X2,X3)) = k6_subset_1(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_45,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_46,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( ( r1_tarski(X1,k1_relat_1(X2))
            & v2_funct_1(X2) )
         => k10_relat_1(X2,k9_relat_1(X2,X1)) = X1 ) ) ),
    inference(assume_negation,[status(cth)],[t164_funct_1])).

cnf(c_0_47,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])).

cnf(c_0_48,plain,
    ( k10_relat_1(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_45]),c_0_45])).

fof(c_0_49,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v1_funct_1(esk2_0)
    & r1_tarski(esk1_0,k1_relat_1(esk2_0))
    & v2_funct_1(esk2_0)
    & k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0)) != esk1_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_46])])])).

fof(c_0_50,plain,(
    ! [X28,X29,X30] :
      ( ~ v1_relat_1(X30)
      | k10_relat_1(X30,k2_xboole_0(X28,X29)) = k2_xboole_0(k10_relat_1(X30,X28),k10_relat_1(X30,X29)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t175_relat_1])])).

cnf(c_0_51,plain,
    ( k10_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_53,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_54,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | X6 != X7 )
      & ( r1_tarski(X7,X6)
        | X6 != X7 )
      & ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,X6)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_55,plain,(
    ! [X23,X24] :
      ( ~ v1_relat_1(X24)
      | r1_tarski(k10_relat_1(X24,X23),k1_relat_1(X24)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).

fof(c_0_56,plain,(
    ! [X8,X9] :
      ( ~ r1_tarski(X8,X9)
      | k2_xboole_0(X8,X9) = X9 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_57,plain,
    ( k10_relat_1(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_58,negated_conjecture,
    ( k10_relat_1(esk2_0,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53])])).

fof(c_0_59,plain,(
    ! [X10] : r1_tarski(k1_xboole_0,X10) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_60,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_61,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_62,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_63,negated_conjecture,
    ( k2_xboole_0(k1_xboole_0,k10_relat_1(esk2_0,X1)) = k10_relat_1(esk2_0,k2_xboole_0(k1_xboole_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_53])])).

cnf(c_0_64,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

fof(c_0_65,plain,(
    ! [X26,X27] :
      ( ~ v1_relat_1(X27)
      | r1_tarski(k10_relat_1(X27,X26),k10_relat_1(X27,k2_relat_1(X27))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t170_relat_1])])).

fof(c_0_66,plain,(
    ! [X25] :
      ( ~ v1_relat_1(X25)
      | k10_relat_1(X25,k2_relat_1(X25)) = k1_relat_1(X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).

fof(c_0_67,plain,(
    ! [X37,X38] :
      ( ~ v1_relat_1(X38)
      | ~ v1_funct_1(X38)
      | ~ r1_tarski(X37,k2_relat_1(X38))
      | k9_relat_1(X38,k10_relat_1(X38,X37)) = X37 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t147_funct_1])])).

cnf(c_0_68,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_69,plain,
    ( k1_relat_1(X1) = k10_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),k10_relat_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_70,negated_conjecture,
    ( k10_relat_1(esk2_0,k2_xboole_0(k1_xboole_0,X1)) = k10_relat_1(esk2_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64])])).

cnf(c_0_71,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_72,plain,
    ( k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_73,plain,
    ( k9_relat_1(X1,k10_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(X2,k2_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_74,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_68])).

cnf(c_0_75,negated_conjecture,
    ( k1_relat_1(esk2_0) = k10_relat_1(esk2_0,X1)
    | ~ r1_tarski(k1_relat_1(esk2_0),k10_relat_1(esk2_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_53])])).

cnf(c_0_76,plain,
    ( r1_tarski(k1_relat_1(X1),k10_relat_1(X1,k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

fof(c_0_77,plain,(
    ! [X35,X36] :
      ( ~ v1_relat_1(X36)
      | ~ r1_tarski(X35,k1_relat_1(X36))
      | r1_tarski(X35,k10_relat_1(X36,k9_relat_1(X36,X35))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_funct_1])])).

fof(c_0_78,plain,(
    ! [X39,X40] :
      ( ~ v1_relat_1(X40)
      | ~ v1_funct_1(X40)
      | ~ v2_funct_1(X40)
      | k9_relat_1(X40,X39) = k10_relat_1(k2_funct_1(X40),X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t154_funct_1])])).

fof(c_0_79,plain,(
    ! [X31] :
      ( ( v1_relat_1(k2_funct_1(X31))
        | ~ v1_relat_1(X31)
        | ~ v1_funct_1(X31) )
      & ( v1_funct_1(k2_funct_1(X31))
        | ~ v1_relat_1(X31)
        | ~ v1_funct_1(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

fof(c_0_80,plain,(
    ! [X43,X44,X45] :
      ( ~ v1_relat_1(X45)
      | ~ v1_funct_1(X45)
      | ~ r1_tarski(k9_relat_1(X45,X43),k9_relat_1(X45,X44))
      | ~ r1_tarski(X43,k1_relat_1(X45))
      | ~ v2_funct_1(X45)
      | r1_tarski(X43,X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t157_funct_1])])).

cnf(c_0_81,plain,
    ( k9_relat_1(X1,k10_relat_1(X1,k2_relat_1(X1))) = k2_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_82,negated_conjecture,
    ( k10_relat_1(esk2_0,k2_relat_1(esk2_0)) = k1_relat_1(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_53])])).

cnf(c_0_83,plain,
    ( r1_tarski(X2,k10_relat_1(X1,k9_relat_1(X1,X2)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_84,plain,
    ( k9_relat_1(X1,X2) = k10_relat_1(k2_funct_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_85,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_86,plain,
    ( r1_tarski(X2,X3)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
    | ~ r1_tarski(X2,k1_relat_1(X1))
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_87,negated_conjecture,
    ( k9_relat_1(esk2_0,k1_relat_1(esk2_0)) = k2_relat_1(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_52]),c_0_53])])).

cnf(c_0_88,negated_conjecture,
    ( v2_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_89,plain,
    ( k10_relat_1(X1,k9_relat_1(X1,k1_relat_1(X1))) = k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_83]),c_0_74])])).

cnf(c_0_90,plain,
    ( r1_tarski(k9_relat_1(X1,X2),k1_relat_1(k2_funct_1(X1)))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_84]),c_0_85])).

cnf(c_0_91,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk2_0),X1)
    | ~ r1_tarski(k2_relat_1(esk2_0),k9_relat_1(esk2_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_88]),c_0_52]),c_0_53]),c_0_74])])).

cnf(c_0_92,plain,
    ( k9_relat_1(X1,k9_relat_1(k2_funct_1(X1),k1_relat_1(k2_funct_1(X1)))) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_89]),c_0_85])).

cnf(c_0_93,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk2_0),k1_relat_1(k2_funct_1(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_87]),c_0_88]),c_0_52]),c_0_53])])).

fof(c_0_94,plain,(
    ! [X41,X42] :
      ( ~ v1_relat_1(X42)
      | ~ v1_funct_1(X42)
      | ~ v2_funct_1(X42)
      | k10_relat_1(X42,X41) = k9_relat_1(k2_funct_1(X42),X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t155_funct_1])])).

cnf(c_0_95,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk2_0),k9_relat_1(k2_funct_1(esk2_0),k1_relat_1(k2_funct_1(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_93]),c_0_88]),c_0_52]),c_0_53])])).

cnf(c_0_96,plain,
    ( k10_relat_1(X1,X2) = k9_relat_1(k2_funct_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_94])).

cnf(c_0_97,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk2_0),k10_relat_1(esk2_0,k1_relat_1(k2_funct_1(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_88]),c_0_52]),c_0_53])])).

cnf(c_0_98,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk2_0,X1),k1_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_70]),c_0_53])])).

cnf(c_0_99,plain,
    ( k10_relat_1(k2_funct_1(X1),k10_relat_1(X1,k1_relat_1(k2_funct_1(X1)))) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_96]),c_0_85])).

cnf(c_0_100,negated_conjecture,
    ( k10_relat_1(esk2_0,k1_relat_1(k2_funct_1(esk2_0))) = k1_relat_1(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_97]),c_0_98])])).

cnf(c_0_101,negated_conjecture,
    ( k10_relat_1(k2_funct_1(esk2_0),k1_relat_1(esk2_0)) = k1_relat_1(k2_funct_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100]),c_0_88]),c_0_52]),c_0_53])])).

cnf(c_0_102,negated_conjecture,
    ( k1_relat_1(k2_funct_1(esk2_0)) = k2_relat_1(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_101]),c_0_87]),c_0_88]),c_0_52]),c_0_53])])).

cnf(c_0_103,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk2_0,X1),k2_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_102]),c_0_88]),c_0_52]),c_0_53])])).

cnf(c_0_104,negated_conjecture,
    ( k9_relat_1(esk2_0,k10_relat_1(esk2_0,k9_relat_1(esk2_0,X1))) = k9_relat_1(esk2_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_103]),c_0_52]),c_0_53])])).

cnf(c_0_105,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk2_0,k9_relat_1(esk2_0,X1)),X2)
    | ~ r1_tarski(k9_relat_1(esk2_0,X1),k9_relat_1(esk2_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_104]),c_0_88]),c_0_52]),c_0_53]),c_0_98])])).

cnf(c_0_106,plain,
    ( k10_relat_1(X1,k9_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X2)),X2)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_83])).

cnf(c_0_107,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk2_0,k9_relat_1(esk2_0,X1)),X1) ),
    inference(spm,[status(thm)],[c_0_105,c_0_74])).

cnf(c_0_108,negated_conjecture,
    ( k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0)) != esk1_0 ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_109,negated_conjecture,
    ( k10_relat_1(esk2_0,k9_relat_1(esk2_0,X1)) = X1
    | ~ r1_tarski(X1,k1_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_107]),c_0_53])])).

cnf(c_0_110,negated_conjecture,
    ( r1_tarski(esk1_0,k1_relat_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_111,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_109]),c_0_110])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:00:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.41  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.21/0.41  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.21/0.41  #
% 0.21/0.41  # Preprocessing time       : 0.027 s
% 0.21/0.41  # Presaturation interreduction done
% 0.21/0.41  
% 0.21/0.41  # Proof found!
% 0.21/0.41  # SZS status Theorem
% 0.21/0.41  # SZS output start CNFRefutation
% 0.21/0.41  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.21/0.41  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.21/0.41  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.21/0.41  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.21/0.41  fof(t3_xboole_1, axiom, ![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 0.21/0.41  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.21/0.41  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.21/0.41  fof(t138_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>k10_relat_1(X3,k6_subset_1(X1,X2))=k6_subset_1(k10_relat_1(X3,X1),k10_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_funct_1)).
% 0.21/0.41  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 0.21/0.41  fof(t164_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((r1_tarski(X1,k1_relat_1(X2))&v2_funct_1(X2))=>k10_relat_1(X2,k9_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t164_funct_1)).
% 0.21/0.41  fof(t175_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k10_relat_1(X3,k2_xboole_0(X1,X2))=k2_xboole_0(k10_relat_1(X3,X1),k10_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_relat_1)).
% 0.21/0.41  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.21/0.41  fof(t167_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 0.21/0.41  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.21/0.41  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.21/0.41  fof(t170_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k10_relat_1(X2,X1),k10_relat_1(X2,k2_relat_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t170_relat_1)).
% 0.21/0.41  fof(t169_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 0.21/0.41  fof(t147_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(X1,k2_relat_1(X2))=>k9_relat_1(X2,k10_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 0.21/0.41  fof(t146_funct_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 0.21/0.41  fof(t154_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(v2_funct_1(X2)=>k9_relat_1(X2,X1)=k10_relat_1(k2_funct_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t154_funct_1)).
% 0.21/0.41  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 0.21/0.41  fof(t157_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(((r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X3,X2))&r1_tarski(X1,k1_relat_1(X3)))&v2_funct_1(X3))=>r1_tarski(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t157_funct_1)).
% 0.21/0.41  fof(t155_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(v2_funct_1(X2)=>k10_relat_1(X2,X1)=k9_relat_1(k2_funct_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t155_funct_1)).
% 0.21/0.41  fof(c_0_23, plain, ![X21, X22]:k1_setfam_1(k2_tarski(X21,X22))=k3_xboole_0(X21,X22), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.21/0.41  fof(c_0_24, plain, ![X17, X18]:k1_enumset1(X17,X17,X18)=k2_tarski(X17,X18), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.21/0.41  fof(c_0_25, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.21/0.41  cnf(c_0_26, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.41  cnf(c_0_27, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.21/0.41  fof(c_0_28, plain, ![X15, X16]:k4_xboole_0(X15,k4_xboole_0(X15,X16))=k3_xboole_0(X15,X16), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.21/0.41  fof(c_0_29, plain, ![X14]:(~r1_tarski(X14,k1_xboole_0)|X14=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).
% 0.21/0.41  fof(c_0_30, plain, ![X11, X12]:r1_tarski(k4_xboole_0(X11,X12),X11), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.21/0.41  cnf(c_0_31, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.41  cnf(c_0_32, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 0.21/0.41  cnf(c_0_33, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.21/0.41  cnf(c_0_34, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.21/0.41  cnf(c_0_35, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.41  cnf(c_0_36, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k1_setfam_1(k1_enumset1(X2,X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_32]), c_0_32])).
% 0.21/0.41  cnf(c_0_37, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_setfam_1(k1_enumset1(X1,X1,X2))), inference(rw,[status(thm)],[c_0_33, c_0_32])).
% 0.21/0.41  fof(c_0_38, plain, ![X13]:k4_xboole_0(X13,k1_xboole_0)=X13, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.21/0.41  fof(c_0_39, plain, ![X32, X33, X34]:(~v1_relat_1(X34)|~v1_funct_1(X34)|k10_relat_1(X34,k6_subset_1(X32,X33))=k6_subset_1(k10_relat_1(X34,X32),k10_relat_1(X34,X33))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t138_funct_1])])).
% 0.21/0.41  fof(c_0_40, plain, ![X19, X20]:k6_subset_1(X19,X20)=k4_xboole_0(X19,X20), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 0.21/0.41  cnf(c_0_41, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.21/0.41  cnf(c_0_42, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_37]), c_0_37])).
% 0.21/0.41  cnf(c_0_43, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.21/0.41  cnf(c_0_44, plain, (k10_relat_1(X1,k6_subset_1(X2,X3))=k6_subset_1(k10_relat_1(X1,X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.21/0.41  cnf(c_0_45, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.21/0.41  fof(c_0_46, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((r1_tarski(X1,k1_relat_1(X2))&v2_funct_1(X2))=>k10_relat_1(X2,k9_relat_1(X2,X1))=X1))), inference(assume_negation,[status(cth)],[t164_funct_1])).
% 0.21/0.41  cnf(c_0_47, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43])).
% 0.21/0.41  cnf(c_0_48, plain, (k10_relat_1(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_45]), c_0_45])).
% 0.21/0.41  fof(c_0_49, negated_conjecture, ((v1_relat_1(esk2_0)&v1_funct_1(esk2_0))&((r1_tarski(esk1_0,k1_relat_1(esk2_0))&v2_funct_1(esk2_0))&k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0))!=esk1_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_46])])])).
% 0.21/0.41  fof(c_0_50, plain, ![X28, X29, X30]:(~v1_relat_1(X30)|k10_relat_1(X30,k2_xboole_0(X28,X29))=k2_xboole_0(k10_relat_1(X30,X28),k10_relat_1(X30,X29))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t175_relat_1])])).
% 0.21/0.41  cnf(c_0_51, plain, (k10_relat_1(X1,k1_xboole_0)=k1_xboole_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_47])).
% 0.21/0.41  cnf(c_0_52, negated_conjecture, (v1_funct_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.21/0.41  cnf(c_0_53, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.21/0.41  fof(c_0_54, plain, ![X6, X7]:(((r1_tarski(X6,X7)|X6!=X7)&(r1_tarski(X7,X6)|X6!=X7))&(~r1_tarski(X6,X7)|~r1_tarski(X7,X6)|X6=X7)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.21/0.41  fof(c_0_55, plain, ![X23, X24]:(~v1_relat_1(X24)|r1_tarski(k10_relat_1(X24,X23),k1_relat_1(X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).
% 0.21/0.41  fof(c_0_56, plain, ![X8, X9]:(~r1_tarski(X8,X9)|k2_xboole_0(X8,X9)=X9), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.21/0.41  cnf(c_0_57, plain, (k10_relat_1(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.21/0.41  cnf(c_0_58, negated_conjecture, (k10_relat_1(esk2_0,k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53])])).
% 0.21/0.41  fof(c_0_59, plain, ![X10]:r1_tarski(k1_xboole_0,X10), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.21/0.41  cnf(c_0_60, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.21/0.41  cnf(c_0_61, plain, (r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.21/0.41  cnf(c_0_62, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.21/0.41  cnf(c_0_63, negated_conjecture, (k2_xboole_0(k1_xboole_0,k10_relat_1(esk2_0,X1))=k10_relat_1(esk2_0,k2_xboole_0(k1_xboole_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_53])])).
% 0.21/0.41  cnf(c_0_64, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.21/0.41  fof(c_0_65, plain, ![X26, X27]:(~v1_relat_1(X27)|r1_tarski(k10_relat_1(X27,X26),k10_relat_1(X27,k2_relat_1(X27)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t170_relat_1])])).
% 0.21/0.41  fof(c_0_66, plain, ![X25]:(~v1_relat_1(X25)|k10_relat_1(X25,k2_relat_1(X25))=k1_relat_1(X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).
% 0.21/0.41  fof(c_0_67, plain, ![X37, X38]:(~v1_relat_1(X38)|~v1_funct_1(X38)|(~r1_tarski(X37,k2_relat_1(X38))|k9_relat_1(X38,k10_relat_1(X38,X37))=X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t147_funct_1])])).
% 0.21/0.41  cnf(c_0_68, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.21/0.41  cnf(c_0_69, plain, (k1_relat_1(X1)=k10_relat_1(X1,X2)|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),k10_relat_1(X1,X2))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.21/0.41  cnf(c_0_70, negated_conjecture, (k10_relat_1(esk2_0,k2_xboole_0(k1_xboole_0,X1))=k10_relat_1(esk2_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_64])])).
% 0.21/0.41  cnf(c_0_71, plain, (r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,k2_relat_1(X1)))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.21/0.41  cnf(c_0_72, plain, (k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.21/0.41  cnf(c_0_73, plain, (k9_relat_1(X1,k10_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~v1_funct_1(X1)|~r1_tarski(X2,k2_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.21/0.41  cnf(c_0_74, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_68])).
% 0.21/0.41  cnf(c_0_75, negated_conjecture, (k1_relat_1(esk2_0)=k10_relat_1(esk2_0,X1)|~r1_tarski(k1_relat_1(esk2_0),k10_relat_1(esk2_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_53])])).
% 0.21/0.41  cnf(c_0_76, plain, (r1_tarski(k1_relat_1(X1),k10_relat_1(X1,k2_relat_1(X1)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.21/0.41  fof(c_0_77, plain, ![X35, X36]:(~v1_relat_1(X36)|(~r1_tarski(X35,k1_relat_1(X36))|r1_tarski(X35,k10_relat_1(X36,k9_relat_1(X36,X35))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_funct_1])])).
% 0.21/0.41  fof(c_0_78, plain, ![X39, X40]:(~v1_relat_1(X40)|~v1_funct_1(X40)|(~v2_funct_1(X40)|k9_relat_1(X40,X39)=k10_relat_1(k2_funct_1(X40),X39))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t154_funct_1])])).
% 0.21/0.41  fof(c_0_79, plain, ![X31]:((v1_relat_1(k2_funct_1(X31))|(~v1_relat_1(X31)|~v1_funct_1(X31)))&(v1_funct_1(k2_funct_1(X31))|(~v1_relat_1(X31)|~v1_funct_1(X31)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 0.21/0.41  fof(c_0_80, plain, ![X43, X44, X45]:(~v1_relat_1(X45)|~v1_funct_1(X45)|(~r1_tarski(k9_relat_1(X45,X43),k9_relat_1(X45,X44))|~r1_tarski(X43,k1_relat_1(X45))|~v2_funct_1(X45)|r1_tarski(X43,X44))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t157_funct_1])])).
% 0.21/0.41  cnf(c_0_81, plain, (k9_relat_1(X1,k10_relat_1(X1,k2_relat_1(X1)))=k2_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.21/0.41  cnf(c_0_82, negated_conjecture, (k10_relat_1(esk2_0,k2_relat_1(esk2_0))=k1_relat_1(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_53])])).
% 0.21/0.41  cnf(c_0_83, plain, (r1_tarski(X2,k10_relat_1(X1,k9_relat_1(X1,X2)))|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.21/0.41  cnf(c_0_84, plain, (k9_relat_1(X1,X2)=k10_relat_1(k2_funct_1(X1),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.21/0.41  cnf(c_0_85, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.21/0.41  cnf(c_0_86, plain, (r1_tarski(X2,X3)|~v1_relat_1(X1)|~v1_funct_1(X1)|~r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,X3))|~r1_tarski(X2,k1_relat_1(X1))|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.21/0.41  cnf(c_0_87, negated_conjecture, (k9_relat_1(esk2_0,k1_relat_1(esk2_0))=k2_relat_1(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_52]), c_0_53])])).
% 0.21/0.41  cnf(c_0_88, negated_conjecture, (v2_funct_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.21/0.41  cnf(c_0_89, plain, (k10_relat_1(X1,k9_relat_1(X1,k1_relat_1(X1)))=k1_relat_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_83]), c_0_74])])).
% 0.21/0.41  cnf(c_0_90, plain, (r1_tarski(k9_relat_1(X1,X2),k1_relat_1(k2_funct_1(X1)))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_84]), c_0_85])).
% 0.21/0.41  cnf(c_0_91, negated_conjecture, (r1_tarski(k1_relat_1(esk2_0),X1)|~r1_tarski(k2_relat_1(esk2_0),k9_relat_1(esk2_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_88]), c_0_52]), c_0_53]), c_0_74])])).
% 0.21/0.41  cnf(c_0_92, plain, (k9_relat_1(X1,k9_relat_1(k2_funct_1(X1),k1_relat_1(k2_funct_1(X1))))=k1_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_89]), c_0_85])).
% 0.21/0.41  cnf(c_0_93, negated_conjecture, (r1_tarski(k2_relat_1(esk2_0),k1_relat_1(k2_funct_1(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_87]), c_0_88]), c_0_52]), c_0_53])])).
% 0.21/0.41  fof(c_0_94, plain, ![X41, X42]:(~v1_relat_1(X42)|~v1_funct_1(X42)|(~v2_funct_1(X42)|k10_relat_1(X42,X41)=k9_relat_1(k2_funct_1(X42),X41))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t155_funct_1])])).
% 0.21/0.41  cnf(c_0_95, negated_conjecture, (r1_tarski(k1_relat_1(esk2_0),k9_relat_1(k2_funct_1(esk2_0),k1_relat_1(k2_funct_1(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_93]), c_0_88]), c_0_52]), c_0_53])])).
% 0.21/0.41  cnf(c_0_96, plain, (k10_relat_1(X1,X2)=k9_relat_1(k2_funct_1(X1),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_94])).
% 0.21/0.41  cnf(c_0_97, negated_conjecture, (r1_tarski(k1_relat_1(esk2_0),k10_relat_1(esk2_0,k1_relat_1(k2_funct_1(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_96]), c_0_88]), c_0_52]), c_0_53])])).
% 0.21/0.41  cnf(c_0_98, negated_conjecture, (r1_tarski(k10_relat_1(esk2_0,X1),k1_relat_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_70]), c_0_53])])).
% 0.21/0.41  cnf(c_0_99, plain, (k10_relat_1(k2_funct_1(X1),k10_relat_1(X1,k1_relat_1(k2_funct_1(X1))))=k1_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_96]), c_0_85])).
% 0.21/0.41  cnf(c_0_100, negated_conjecture, (k10_relat_1(esk2_0,k1_relat_1(k2_funct_1(esk2_0)))=k1_relat_1(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_97]), c_0_98])])).
% 0.21/0.41  cnf(c_0_101, negated_conjecture, (k10_relat_1(k2_funct_1(esk2_0),k1_relat_1(esk2_0))=k1_relat_1(k2_funct_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_100]), c_0_88]), c_0_52]), c_0_53])])).
% 0.21/0.41  cnf(c_0_102, negated_conjecture, (k1_relat_1(k2_funct_1(esk2_0))=k2_relat_1(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_101]), c_0_87]), c_0_88]), c_0_52]), c_0_53])])).
% 0.21/0.41  cnf(c_0_103, negated_conjecture, (r1_tarski(k9_relat_1(esk2_0,X1),k2_relat_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_102]), c_0_88]), c_0_52]), c_0_53])])).
% 0.21/0.41  cnf(c_0_104, negated_conjecture, (k9_relat_1(esk2_0,k10_relat_1(esk2_0,k9_relat_1(esk2_0,X1)))=k9_relat_1(esk2_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_103]), c_0_52]), c_0_53])])).
% 0.21/0.41  cnf(c_0_105, negated_conjecture, (r1_tarski(k10_relat_1(esk2_0,k9_relat_1(esk2_0,X1)),X2)|~r1_tarski(k9_relat_1(esk2_0,X1),k9_relat_1(esk2_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_104]), c_0_88]), c_0_52]), c_0_53]), c_0_98])])).
% 0.21/0.41  cnf(c_0_106, plain, (k10_relat_1(X1,k9_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X2)),X2)|~r1_tarski(X2,k1_relat_1(X1))), inference(spm,[status(thm)],[c_0_60, c_0_83])).
% 0.21/0.41  cnf(c_0_107, negated_conjecture, (r1_tarski(k10_relat_1(esk2_0,k9_relat_1(esk2_0,X1)),X1)), inference(spm,[status(thm)],[c_0_105, c_0_74])).
% 0.21/0.41  cnf(c_0_108, negated_conjecture, (k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0))!=esk1_0), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.21/0.41  cnf(c_0_109, negated_conjecture, (k10_relat_1(esk2_0,k9_relat_1(esk2_0,X1))=X1|~r1_tarski(X1,k1_relat_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_107]), c_0_53])])).
% 0.21/0.41  cnf(c_0_110, negated_conjecture, (r1_tarski(esk1_0,k1_relat_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.21/0.41  cnf(c_0_111, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_109]), c_0_110])]), ['proof']).
% 0.21/0.41  # SZS output end CNFRefutation
% 0.21/0.41  # Proof object total steps             : 112
% 0.21/0.41  # Proof object clause steps            : 65
% 0.21/0.41  # Proof object formula steps           : 47
% 0.21/0.41  # Proof object conjectures             : 28
% 0.21/0.41  # Proof object clause conjectures      : 25
% 0.21/0.41  # Proof object formula conjectures     : 3
% 0.21/0.41  # Proof object initial clauses used    : 28
% 0.21/0.41  # Proof object initial formulas used   : 23
% 0.21/0.41  # Proof object generating inferences   : 31
% 0.21/0.41  # Proof object simplifying inferences  : 76
% 0.21/0.41  # Training examples: 0 positive, 0 negative
% 0.21/0.41  # Parsed axioms                        : 23
% 0.21/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.41  # Initial clauses                      : 30
% 0.21/0.41  # Removed in clause preprocessing      : 3
% 0.21/0.41  # Initial clauses in saturation        : 27
% 0.21/0.41  # Processed clauses                    : 386
% 0.21/0.41  # ...of these trivial                  : 27
% 0.21/0.41  # ...subsumed                          : 157
% 0.21/0.41  # ...remaining for further processing  : 202
% 0.21/0.41  # Other redundant clauses eliminated   : 2
% 0.21/0.41  # Clauses deleted for lack of memory   : 0
% 0.21/0.41  # Backward-subsumed                    : 1
% 0.21/0.41  # Backward-rewritten                   : 29
% 0.21/0.41  # Generated clauses                    : 1503
% 0.21/0.41  # ...of the previous two non-trivial   : 1036
% 0.21/0.41  # Contextual simplify-reflections      : 21
% 0.21/0.41  # Paramodulations                      : 1501
% 0.21/0.41  # Factorizations                       : 0
% 0.21/0.41  # Equation resolutions                 : 2
% 0.21/0.41  # Propositional unsat checks           : 0
% 0.21/0.41  #    Propositional check models        : 0
% 0.21/0.41  #    Propositional check unsatisfiable : 0
% 0.21/0.41  #    Propositional clauses             : 0
% 0.21/0.41  #    Propositional clauses after purity: 0
% 0.21/0.41  #    Propositional unsat core size     : 0
% 0.21/0.41  #    Propositional preprocessing time  : 0.000
% 0.21/0.41  #    Propositional encoding time       : 0.000
% 0.21/0.41  #    Propositional solver time         : 0.000
% 0.21/0.41  #    Success case prop preproc time    : 0.000
% 0.21/0.41  #    Success case prop encoding time   : 0.000
% 0.21/0.41  #    Success case prop solver time     : 0.000
% 0.21/0.41  # Current number of processed clauses  : 144
% 0.21/0.41  #    Positive orientable unit clauses  : 50
% 0.21/0.41  #    Positive unorientable unit clauses: 1
% 0.21/0.41  #    Negative unit clauses             : 1
% 0.21/0.41  #    Non-unit-clauses                  : 92
% 0.21/0.41  # Current number of unprocessed clauses: 668
% 0.21/0.41  # ...number of literals in the above   : 2314
% 0.21/0.41  # Current number of archived formulas  : 0
% 0.21/0.41  # Current number of archived clauses   : 59
% 0.21/0.41  # Clause-clause subsumption calls (NU) : 1143
% 0.21/0.41  # Rec. Clause-clause subsumption calls : 684
% 0.21/0.41  # Non-unit clause-clause subsumptions  : 179
% 0.21/0.41  # Unit Clause-clause subsumption calls : 15
% 0.21/0.41  # Rewrite failures with RHS unbound    : 0
% 0.21/0.41  # BW rewrite match attempts            : 22
% 0.21/0.41  # BW rewrite match successes           : 11
% 0.21/0.41  # Condensation attempts                : 0
% 0.21/0.41  # Condensation successes               : 0
% 0.21/0.41  # Termbank termtop insertions          : 27707
% 0.21/0.41  
% 0.21/0.41  # -------------------------------------------------
% 0.21/0.41  # User time                : 0.052 s
% 0.21/0.41  # System time              : 0.010 s
% 0.21/0.41  # Total time               : 0.062 s
% 0.21/0.41  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------

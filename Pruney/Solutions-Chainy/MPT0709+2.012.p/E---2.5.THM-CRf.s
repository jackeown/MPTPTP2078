%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:55:32 EST 2020

% Result     : Theorem 1.51s
% Output     : CNFRefutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 184 expanded)
%              Number of clauses        :   47 (  78 expanded)
%              Number of leaves         :   17 (  46 expanded)
%              Depth                    :   17
%              Number of atoms          :  199 ( 519 expanded)
%              Number of equality atoms :   44 ( 133 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t109_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k4_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_xboole_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(t164_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( ( r1_tarski(X1,k1_relat_1(X2))
          & v2_funct_1(X2) )
       => k10_relat_1(X2,k9_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t156_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).

fof(t178_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => r1_tarski(k10_relat_1(X3,X1),k10_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).

fof(t169_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(t167_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

fof(t147_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r1_tarski(X1,k2_relat_1(X2))
       => k9_relat_1(X2,k10_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

fof(t157_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( ( r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X3,X2))
          & r1_tarski(X1,k1_relat_1(X3))
          & v2_funct_1(X3) )
       => r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_funct_1)).

fof(t146_funct_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(c_0_17,plain,(
    ! [X21,X22] : k1_setfam_1(k2_tarski(X21,X22)) = k3_xboole_0(X21,X22) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_18,plain,(
    ! [X19,X20] : k1_enumset1(X19,X19,X20) = k2_tarski(X19,X20) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_19,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_20,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_22,plain,(
    ! [X17,X18] : k4_xboole_0(X17,k4_xboole_0(X17,X18)) = k3_xboole_0(X17,X18) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_23,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_26,plain,(
    ! [X13,X14,X15] :
      ( ~ r1_tarski(X13,X14)
      | ~ r1_tarski(X14,X15)
      | r1_tarski(X13,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_27,plain,(
    ! [X10,X11,X12] :
      ( ~ r1_tarski(X10,X11)
      | r1_tarski(k4_xboole_0(X10,X12),X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t109_xboole_1])])).

cnf(c_0_28,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k1_setfam_1(k1_enumset1(X2,X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24]),c_0_24])).

cnf(c_0_29,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_setfam_1(k1_enumset1(X1,X1,X2)) ),
    inference(rw,[status(thm)],[c_0_25,c_0_24])).

fof(c_0_30,plain,(
    ! [X8,X9] :
      ( ( k4_xboole_0(X8,X9) != k1_xboole_0
        | r1_tarski(X8,X9) )
      & ( ~ r1_tarski(X8,X9)
        | k4_xboole_0(X8,X9) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_31,plain,(
    ! [X16] : k4_xboole_0(X16,k1_xboole_0) = X16 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( r1_tarski(k4_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_29]),c_0_29])).

cnf(c_0_35,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_37,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( ( r1_tarski(X1,k1_relat_1(X2))
            & v2_funct_1(X2) )
         => k10_relat_1(X2,k9_relat_1(X2,X1)) = X1 ) ) ),
    inference(assume_negation,[status(cth)],[t164_funct_1])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X3,X4))
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_39,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])).

fof(c_0_40,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v1_funct_1(esk2_0)
    & r1_tarski(esk1_0,k1_relat_1(esk2_0))
    & v2_funct_1(esk2_0)
    & k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0)) != esk1_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_37])])])).

fof(c_0_41,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | X6 != X7 )
      & ( r1_tarski(X7,X6)
        | X6 != X7 )
      & ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,X6)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_42,plain,(
    ! [X23,X24,X25] :
      ( ~ v1_relat_1(X25)
      | ~ r1_tarski(X23,X24)
      | r1_tarski(k9_relat_1(X25,X23),k9_relat_1(X25,X24)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t156_relat_1])])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X4,X2)
    | ~ r1_tarski(X3,X4) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(esk1_0,k1_relat_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_46,plain,(
    ! [X29,X30,X31] :
      ( ~ v1_relat_1(X31)
      | ~ r1_tarski(X29,X30)
      | r1_tarski(k10_relat_1(X31,X29),k10_relat_1(X31,X30)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t178_relat_1])])).

fof(c_0_47,plain,(
    ! [X28] :
      ( ~ v1_relat_1(X28)
      | k10_relat_1(X28,k2_relat_1(X28)) = k1_relat_1(X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).

cnf(c_0_48,plain,
    ( r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(esk1_0,X1)
    | ~ r1_tarski(k1_relat_1(esk2_0),X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_50,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_45])).

cnf(c_0_51,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_52,plain,
    ( k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_53,plain,
    ( r1_tarski(X1,k9_relat_1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k9_relat_1(X2,X4))
    | ~ r1_tarski(X4,X3) ),
    inference(spm,[status(thm)],[c_0_32,c_0_48])).

fof(c_0_54,plain,(
    ! [X26,X27] :
      ( ~ v1_relat_1(X27)
      | r1_tarski(k10_relat_1(X27,X26),k1_relat_1(X27)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(esk1_0,X1)
    | ~ r1_tarski(k1_relat_1(esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_56,plain,
    ( r1_tarski(k1_relat_1(X1),k10_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_57,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_58,plain,(
    ! [X34,X35] :
      ( ~ v1_relat_1(X35)
      | ~ v1_funct_1(X35)
      | ~ r1_tarski(X34,k2_relat_1(X35))
      | k9_relat_1(X35,k10_relat_1(X35,X34)) = X34 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t147_funct_1])])).

cnf(c_0_59,plain,
    ( r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X4,X3)
    | ~ r1_tarski(X2,X4) ),
    inference(spm,[status(thm)],[c_0_53,c_0_48])).

cnf(c_0_60,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(esk1_0,k10_relat_1(esk2_0,X1))
    | ~ r1_tarski(k2_relat_1(esk2_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57])])).

cnf(c_0_62,plain,
    ( k9_relat_1(X1,k10_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(X2,k2_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_63,plain,
    ( r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,k1_relat_1(X3)))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(X2,k10_relat_1(X3,X4)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(esk1_0,k10_relat_1(esk2_0,k2_relat_1(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_61,c_0_50])).

cnf(c_0_65,plain,
    ( k9_relat_1(X1,k10_relat_1(X1,k2_relat_1(X1))) = k2_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_50])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(k9_relat_1(X1,esk1_0),k9_relat_1(X1,k1_relat_1(esk2_0)))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_57])])).

cnf(c_0_67,plain,
    ( k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_65,c_0_52])).

cnf(c_0_68,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_69,plain,(
    ! [X36,X37,X38] :
      ( ~ v1_relat_1(X38)
      | ~ v1_funct_1(X38)
      | ~ r1_tarski(k9_relat_1(X38,X36),k9_relat_1(X38,X37))
      | ~ r1_tarski(X36,k1_relat_1(X38))
      | ~ v2_funct_1(X38)
      | r1_tarski(X36,X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t157_funct_1])])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk2_0,esk1_0),k2_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_57]),c_0_68])])).

fof(c_0_71,plain,(
    ! [X32,X33] :
      ( ~ v1_relat_1(X33)
      | ~ r1_tarski(X32,k1_relat_1(X33))
      | r1_tarski(X32,k10_relat_1(X33,k9_relat_1(X33,X32))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_funct_1])])).

cnf(c_0_72,plain,
    ( r1_tarski(X2,X3)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
    | ~ r1_tarski(X2,k1_relat_1(X1))
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_73,negated_conjecture,
    ( k9_relat_1(esk2_0,k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0))) = k9_relat_1(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_70]),c_0_68]),c_0_57])])).

cnf(c_0_74,negated_conjecture,
    ( v2_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_75,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_76,plain,
    ( r1_tarski(X2,k10_relat_1(X1,k9_relat_1(X1,X2)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_77,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0)),X1)
    | ~ r1_tarski(k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0)),k1_relat_1(esk2_0))
    | ~ r1_tarski(k9_relat_1(esk2_0,esk1_0),k9_relat_1(esk2_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_74]),c_0_68]),c_0_57])])).

cnf(c_0_78,plain,
    ( k10_relat_1(X1,k9_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X2)),X2)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_79,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0)),X1)
    | ~ r1_tarski(k9_relat_1(esk2_0,esk1_0),k9_relat_1(esk2_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_60]),c_0_57])])).

cnf(c_0_80,negated_conjecture,
    ( k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0)) != esk1_0 ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_81,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_57]),c_0_44]),c_0_50])]),c_0_80]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:19:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 1.51/1.72  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 1.51/1.72  # and selection function SelectComplexExceptUniqMaxHorn.
% 1.51/1.72  #
% 1.51/1.72  # Preprocessing time       : 0.024 s
% 1.51/1.72  # Presaturation interreduction done
% 1.51/1.72  
% 1.51/1.72  # Proof found!
% 1.51/1.72  # SZS status Theorem
% 1.51/1.72  # SZS output start CNFRefutation
% 1.51/1.72  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 1.51/1.72  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 1.51/1.72  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.51/1.72  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.51/1.72  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.51/1.72  fof(t109_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(k4_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_xboole_1)).
% 1.51/1.72  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.51/1.72  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 1.51/1.72  fof(t164_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((r1_tarski(X1,k1_relat_1(X2))&v2_funct_1(X2))=>k10_relat_1(X2,k9_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t164_funct_1)).
% 1.51/1.72  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.51/1.72  fof(t156_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t156_relat_1)).
% 1.51/1.72  fof(t178_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>r1_tarski(k10_relat_1(X3,X1),k10_relat_1(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t178_relat_1)).
% 1.51/1.72  fof(t169_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 1.51/1.72  fof(t167_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 1.51/1.72  fof(t147_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(X1,k2_relat_1(X2))=>k9_relat_1(X2,k10_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 1.51/1.72  fof(t157_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(((r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X3,X2))&r1_tarski(X1,k1_relat_1(X3)))&v2_funct_1(X3))=>r1_tarski(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t157_funct_1)).
% 1.51/1.72  fof(t146_funct_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 1.51/1.72  fof(c_0_17, plain, ![X21, X22]:k1_setfam_1(k2_tarski(X21,X22))=k3_xboole_0(X21,X22), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 1.51/1.72  fof(c_0_18, plain, ![X19, X20]:k1_enumset1(X19,X19,X20)=k2_tarski(X19,X20), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 1.51/1.72  fof(c_0_19, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 1.51/1.72  cnf(c_0_20, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.51/1.72  cnf(c_0_21, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.51/1.72  fof(c_0_22, plain, ![X17, X18]:k4_xboole_0(X17,k4_xboole_0(X17,X18))=k3_xboole_0(X17,X18), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 1.51/1.72  cnf(c_0_23, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.51/1.72  cnf(c_0_24, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 1.51/1.72  cnf(c_0_25, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 1.51/1.72  fof(c_0_26, plain, ![X13, X14, X15]:(~r1_tarski(X13,X14)|~r1_tarski(X14,X15)|r1_tarski(X13,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 1.51/1.72  fof(c_0_27, plain, ![X10, X11, X12]:(~r1_tarski(X10,X11)|r1_tarski(k4_xboole_0(X10,X12),X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t109_xboole_1])])).
% 1.51/1.72  cnf(c_0_28, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k1_setfam_1(k1_enumset1(X2,X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_24]), c_0_24])).
% 1.51/1.72  cnf(c_0_29, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_setfam_1(k1_enumset1(X1,X1,X2))), inference(rw,[status(thm)],[c_0_25, c_0_24])).
% 1.51/1.72  fof(c_0_30, plain, ![X8, X9]:((k4_xboole_0(X8,X9)!=k1_xboole_0|r1_tarski(X8,X9))&(~r1_tarski(X8,X9)|k4_xboole_0(X8,X9)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 1.51/1.72  fof(c_0_31, plain, ![X16]:k4_xboole_0(X16,k1_xboole_0)=X16, inference(variable_rename,[status(thm)],[t3_boole])).
% 1.51/1.72  cnf(c_0_32, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 1.51/1.72  cnf(c_0_33, plain, (r1_tarski(k4_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 1.51/1.72  cnf(c_0_34, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_29]), c_0_29])).
% 1.51/1.72  cnf(c_0_35, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 1.51/1.72  cnf(c_0_36, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_31])).
% 1.51/1.72  fof(c_0_37, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((r1_tarski(X1,k1_relat_1(X2))&v2_funct_1(X2))=>k10_relat_1(X2,k9_relat_1(X2,X1))=X1))), inference(assume_negation,[status(cth)],[t164_funct_1])).
% 1.51/1.72  cnf(c_0_38, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k4_xboole_0(X3,X4))|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 1.51/1.72  cnf(c_0_39, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=X2|~r1_tarski(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])).
% 1.51/1.72  fof(c_0_40, negated_conjecture, ((v1_relat_1(esk2_0)&v1_funct_1(esk2_0))&((r1_tarski(esk1_0,k1_relat_1(esk2_0))&v2_funct_1(esk2_0))&k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0))!=esk1_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_37])])])).
% 1.51/1.72  fof(c_0_41, plain, ![X6, X7]:(((r1_tarski(X6,X7)|X6!=X7)&(r1_tarski(X7,X6)|X6!=X7))&(~r1_tarski(X6,X7)|~r1_tarski(X7,X6)|X6=X7)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 1.51/1.72  fof(c_0_42, plain, ![X23, X24, X25]:(~v1_relat_1(X25)|(~r1_tarski(X23,X24)|r1_tarski(k9_relat_1(X25,X23),k9_relat_1(X25,X24)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t156_relat_1])])).
% 1.51/1.72  cnf(c_0_43, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,X3)|~r1_tarski(X4,X2)|~r1_tarski(X3,X4)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 1.51/1.72  cnf(c_0_44, negated_conjecture, (r1_tarski(esk1_0,k1_relat_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 1.51/1.72  cnf(c_0_45, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_41])).
% 1.51/1.72  fof(c_0_46, plain, ![X29, X30, X31]:(~v1_relat_1(X31)|(~r1_tarski(X29,X30)|r1_tarski(k10_relat_1(X31,X29),k10_relat_1(X31,X30)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t178_relat_1])])).
% 1.51/1.72  fof(c_0_47, plain, ![X28]:(~v1_relat_1(X28)|k10_relat_1(X28,k2_relat_1(X28))=k1_relat_1(X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).
% 1.51/1.72  cnf(c_0_48, plain, (r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,X3))|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 1.51/1.72  cnf(c_0_49, negated_conjecture, (r1_tarski(esk1_0,X1)|~r1_tarski(k1_relat_1(esk2_0),X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 1.51/1.72  cnf(c_0_50, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_45])).
% 1.51/1.72  cnf(c_0_51, plain, (r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 1.51/1.72  cnf(c_0_52, plain, (k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 1.51/1.72  cnf(c_0_53, plain, (r1_tarski(X1,k9_relat_1(X2,X3))|~v1_relat_1(X2)|~r1_tarski(X1,k9_relat_1(X2,X4))|~r1_tarski(X4,X3)), inference(spm,[status(thm)],[c_0_32, c_0_48])).
% 1.51/1.72  fof(c_0_54, plain, ![X26, X27]:(~v1_relat_1(X27)|r1_tarski(k10_relat_1(X27,X26),k1_relat_1(X27))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).
% 1.51/1.72  cnf(c_0_55, negated_conjecture, (r1_tarski(esk1_0,X1)|~r1_tarski(k1_relat_1(esk2_0),X1)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 1.51/1.72  cnf(c_0_56, plain, (r1_tarski(k1_relat_1(X1),k10_relat_1(X1,X2))|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 1.51/1.72  cnf(c_0_57, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 1.51/1.72  fof(c_0_58, plain, ![X34, X35]:(~v1_relat_1(X35)|~v1_funct_1(X35)|(~r1_tarski(X34,k2_relat_1(X35))|k9_relat_1(X35,k10_relat_1(X35,X34))=X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t147_funct_1])])).
% 1.51/1.72  cnf(c_0_59, plain, (r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,X3))|~v1_relat_1(X1)|~r1_tarski(X4,X3)|~r1_tarski(X2,X4)), inference(spm,[status(thm)],[c_0_53, c_0_48])).
% 1.51/1.72  cnf(c_0_60, plain, (r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 1.51/1.72  cnf(c_0_61, negated_conjecture, (r1_tarski(esk1_0,k10_relat_1(esk2_0,X1))|~r1_tarski(k2_relat_1(esk2_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57])])).
% 1.51/1.72  cnf(c_0_62, plain, (k9_relat_1(X1,k10_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~v1_funct_1(X1)|~r1_tarski(X2,k2_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 1.51/1.72  cnf(c_0_63, plain, (r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,k1_relat_1(X3)))|~v1_relat_1(X1)|~v1_relat_1(X3)|~r1_tarski(X2,k10_relat_1(X3,X4))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 1.51/1.72  cnf(c_0_64, negated_conjecture, (r1_tarski(esk1_0,k10_relat_1(esk2_0,k2_relat_1(esk2_0)))), inference(spm,[status(thm)],[c_0_61, c_0_50])).
% 1.51/1.72  cnf(c_0_65, plain, (k9_relat_1(X1,k10_relat_1(X1,k2_relat_1(X1)))=k2_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_62, c_0_50])).
% 1.51/1.72  cnf(c_0_66, negated_conjecture, (r1_tarski(k9_relat_1(X1,esk1_0),k9_relat_1(X1,k1_relat_1(esk2_0)))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_57])])).
% 1.51/1.72  cnf(c_0_67, plain, (k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_65, c_0_52])).
% 1.51/1.72  cnf(c_0_68, negated_conjecture, (v1_funct_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 1.51/1.72  fof(c_0_69, plain, ![X36, X37, X38]:(~v1_relat_1(X38)|~v1_funct_1(X38)|(~r1_tarski(k9_relat_1(X38,X36),k9_relat_1(X38,X37))|~r1_tarski(X36,k1_relat_1(X38))|~v2_funct_1(X38)|r1_tarski(X36,X37))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t157_funct_1])])).
% 1.51/1.72  cnf(c_0_70, negated_conjecture, (r1_tarski(k9_relat_1(esk2_0,esk1_0),k2_relat_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_57]), c_0_68])])).
% 1.51/1.72  fof(c_0_71, plain, ![X32, X33]:(~v1_relat_1(X33)|(~r1_tarski(X32,k1_relat_1(X33))|r1_tarski(X32,k10_relat_1(X33,k9_relat_1(X33,X32))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_funct_1])])).
% 1.51/1.72  cnf(c_0_72, plain, (r1_tarski(X2,X3)|~v1_relat_1(X1)|~v1_funct_1(X1)|~r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,X3))|~r1_tarski(X2,k1_relat_1(X1))|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 1.51/1.72  cnf(c_0_73, negated_conjecture, (k9_relat_1(esk2_0,k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0)))=k9_relat_1(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_70]), c_0_68]), c_0_57])])).
% 1.51/1.72  cnf(c_0_74, negated_conjecture, (v2_funct_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 1.51/1.72  cnf(c_0_75, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 1.51/1.72  cnf(c_0_76, plain, (r1_tarski(X2,k10_relat_1(X1,k9_relat_1(X1,X2)))|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_71])).
% 1.51/1.72  cnf(c_0_77, negated_conjecture, (r1_tarski(k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0)),X1)|~r1_tarski(k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0)),k1_relat_1(esk2_0))|~r1_tarski(k9_relat_1(esk2_0,esk1_0),k9_relat_1(esk2_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_74]), c_0_68]), c_0_57])])).
% 1.51/1.72  cnf(c_0_78, plain, (k10_relat_1(X1,k9_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X2)),X2)|~r1_tarski(X2,k1_relat_1(X1))), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 1.51/1.72  cnf(c_0_79, negated_conjecture, (r1_tarski(k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0)),X1)|~r1_tarski(k9_relat_1(esk2_0,esk1_0),k9_relat_1(esk2_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_60]), c_0_57])])).
% 1.51/1.72  cnf(c_0_80, negated_conjecture, (k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0))!=esk1_0), inference(split_conjunct,[status(thm)],[c_0_40])).
% 1.51/1.72  cnf(c_0_81, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_57]), c_0_44]), c_0_50])]), c_0_80]), ['proof']).
% 1.51/1.72  # SZS output end CNFRefutation
% 1.51/1.72  # Proof object total steps             : 82
% 1.51/1.72  # Proof object clause steps            : 47
% 1.51/1.72  # Proof object formula steps           : 35
% 1.51/1.72  # Proof object conjectures             : 18
% 1.51/1.72  # Proof object clause conjectures      : 15
% 1.51/1.72  # Proof object formula conjectures     : 3
% 1.51/1.72  # Proof object initial clauses used    : 22
% 1.51/1.72  # Proof object initial formulas used   : 17
% 1.51/1.72  # Proof object generating inferences   : 20
% 1.51/1.72  # Proof object simplifying inferences  : 29
% 1.51/1.72  # Training examples: 0 positive, 0 negative
% 1.51/1.72  # Parsed axioms                        : 17
% 1.51/1.72  # Removed by relevancy pruning/SinE    : 0
% 1.51/1.72  # Initial clauses                      : 24
% 1.51/1.72  # Removed in clause preprocessing      : 2
% 1.51/1.72  # Initial clauses in saturation        : 22
% 1.51/1.72  # Processed clauses                    : 19156
% 1.51/1.72  # ...of these trivial                  : 15
% 1.51/1.72  # ...subsumed                          : 17254
% 1.51/1.72  # ...remaining for further processing  : 1887
% 1.51/1.72  # Other redundant clauses eliminated   : 369
% 1.51/1.72  # Clauses deleted for lack of memory   : 0
% 1.51/1.72  # Backward-subsumed                    : 192
% 1.51/1.72  # Backward-rewritten                   : 10
% 1.51/1.72  # Generated clauses                    : 126513
% 1.51/1.72  # ...of the previous two non-trivial   : 119615
% 1.51/1.72  # Contextual simplify-reflections      : 33
% 1.51/1.72  # Paramodulations                      : 126144
% 1.51/1.72  # Factorizations                       : 0
% 1.51/1.72  # Equation resolutions                 : 369
% 1.51/1.72  # Propositional unsat checks           : 0
% 1.51/1.72  #    Propositional check models        : 0
% 1.51/1.72  #    Propositional check unsatisfiable : 0
% 1.51/1.72  #    Propositional clauses             : 0
% 1.51/1.72  #    Propositional clauses after purity: 0
% 1.51/1.72  #    Propositional unsat core size     : 0
% 1.51/1.72  #    Propositional preprocessing time  : 0.000
% 1.51/1.72  #    Propositional encoding time       : 0.000
% 1.51/1.72  #    Propositional solver time         : 0.000
% 1.51/1.72  #    Success case prop preproc time    : 0.000
% 1.51/1.72  #    Success case prop encoding time   : 0.000
% 1.51/1.72  #    Success case prop solver time     : 0.000
% 1.51/1.72  # Current number of processed clauses  : 1662
% 1.51/1.72  #    Positive orientable unit clauses  : 21
% 1.51/1.72  #    Positive unorientable unit clauses: 1
% 1.51/1.72  #    Negative unit clauses             : 18
% 1.51/1.72  #    Non-unit-clauses                  : 1622
% 1.51/1.72  # Current number of unprocessed clauses: 99700
% 1.51/1.72  # ...number of literals in the above   : 450677
% 1.51/1.72  # Current number of archived formulas  : 0
% 1.51/1.72  # Current number of archived clauses   : 225
% 1.51/1.72  # Clause-clause subsumption calls (NU) : 861523
% 1.51/1.72  # Rec. Clause-clause subsumption calls : 319161
% 1.51/1.72  # Non-unit clause-clause subsumptions  : 9036
% 1.51/1.72  # Unit Clause-clause subsumption calls : 1777
% 1.51/1.72  # Rewrite failures with RHS unbound    : 0
% 1.51/1.72  # BW rewrite match attempts            : 24
% 1.51/1.72  # BW rewrite match successes           : 11
% 1.51/1.72  # Condensation attempts                : 0
% 1.51/1.72  # Condensation successes               : 0
% 1.51/1.72  # Termbank termtop insertions          : 2023291
% 1.51/1.72  
% 1.51/1.72  # -------------------------------------------------
% 1.51/1.72  # User time                : 1.321 s
% 1.51/1.72  # System time              : 0.062 s
% 1.51/1.72  # Total time               : 1.384 s
% 1.51/1.72  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------

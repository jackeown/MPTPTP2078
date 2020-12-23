%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:07:33 EST 2020

% Result     : Theorem 0.47s
% Output     : CNFRefutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 757 expanded)
%              Number of clauses        :   66 ( 345 expanded)
%              Number of leaves         :   18 ( 204 expanded)
%              Depth                    :   16
%              Number of atoms          :  192 (1203 expanded)
%              Number of equality atoms :   72 ( 659 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t11_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X1,X2),X3)
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t175_funct_2,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( r1_tarski(k10_relat_1(X1,X3),X2)
         => k10_relat_1(X1,X3) = k10_relat_1(k7_relat_1(X1,X2),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t43_funct_1,axiom,(
    ! [X1,X2] : k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) = k6_relat_1(k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(t94_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k5_relat_1(k6_relat_1(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(t148_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => k9_relat_1(X2,k10_relat_1(X2,X1)) = k3_xboole_0(X1,k9_relat_1(X2,k1_relat_1(X2))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).

fof(t169_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t139_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k10_relat_1(k7_relat_1(X3,X1),X2) = k3_xboole_0(X1,k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

fof(t167_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(t163_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( ( r1_tarski(X1,k1_relat_1(X3))
          & r1_tarski(k9_relat_1(X3,X1),X2) )
       => r1_tarski(X1,k10_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

fof(t147_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r1_tarski(X1,k2_relat_1(X2))
       => k9_relat_1(X2,k10_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

fof(c_0_18,plain,(
    ! [X6,X7,X8] :
      ( ~ r1_tarski(k2_xboole_0(X6,X7),X8)
      | r1_tarski(X6,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

fof(c_0_19,plain,(
    ! [X9,X10] :
      ( ~ r1_tarski(X9,X10)
      | k2_xboole_0(X9,X10) = X10 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ! [X2,X3] :
            ( r1_tarski(k10_relat_1(X1,X3),X2)
           => k10_relat_1(X1,X3) = k10_relat_1(k7_relat_1(X1,X2),X3) ) ) ),
    inference(assume_negation,[status(cth)],[t175_funct_2])).

fof(c_0_21,plain,(
    ! [X15,X16] : k1_setfam_1(k2_tarski(X15,X16)) = k3_xboole_0(X15,X16) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_22,plain,(
    ! [X13,X14] : k1_enumset1(X13,X13,X14) = k2_tarski(X13,X14) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_25,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_funct_1(esk1_0)
    & r1_tarski(k10_relat_1(esk1_0,esk3_0),esk2_0)
    & k10_relat_1(esk1_0,esk3_0) != k10_relat_1(k7_relat_1(esk1_0,esk2_0),esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).

fof(c_0_26,plain,(
    ! [X11,X12] : r1_tarski(k3_xboole_0(X11,X12),X11) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_27,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_29,plain,(
    ! [X36,X37] : k5_relat_1(k6_relat_1(X37),k6_relat_1(X36)) = k6_relat_1(k3_xboole_0(X36,X37)) ),
    inference(variable_rename,[status(thm)],[t43_funct_1])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk1_0,esk3_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

fof(c_0_34,plain,(
    ! [X22] :
      ( k1_relat_1(k6_relat_1(X22)) = X22
      & k2_relat_1(k6_relat_1(X22)) = X22 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

cnf(c_0_35,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(k3_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(X1,esk2_0)
    | ~ r1_tarski(X1,k10_relat_1(esk1_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_37,plain,
    ( r1_tarski(k1_setfam_1(k1_enumset1(X1,X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_38,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_39,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(k1_setfam_1(k1_enumset1(X2,X2,X1))) ),
    inference(rw,[status(thm)],[c_0_35,c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(k1_setfam_1(k1_enumset1(k10_relat_1(esk1_0,esk3_0),k10_relat_1(esk1_0,esk3_0),X1)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_41,plain,
    ( k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k1_setfam_1(k1_enumset1(X2,X2,X1)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

fof(c_0_42,plain,(
    ! [X23,X24] :
      ( ~ v1_relat_1(X24)
      | k7_relat_1(X24,X23) = k5_relat_1(k6_relat_1(X23),X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).

fof(c_0_43,plain,(
    ! [X25] :
      ( v1_relat_1(k6_relat_1(X25))
      & v1_funct_1(k6_relat_1(X25)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(k10_relat_1(esk1_0,esk3_0)))),esk2_0) ),
    inference(rw,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_45,plain,
    ( k7_relat_1(X1,X2) = k5_relat_1(k6_relat_1(X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_46,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_47,plain,(
    ! [X17,X18] :
      ( ~ v1_relat_1(X18)
      | k2_relat_1(k7_relat_1(X18,X17)) = k9_relat_1(X18,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

fof(c_0_48,plain,(
    ! [X31,X32] :
      ( ~ v1_relat_1(X32)
      | ~ v1_funct_1(X32)
      | k9_relat_1(X32,k10_relat_1(X32,X31)) = k3_xboole_0(X31,k9_relat_1(X32,k1_relat_1(X32))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_funct_1])])).

fof(c_0_49,plain,(
    ! [X21] :
      ( ~ v1_relat_1(X21)
      | k10_relat_1(X21,k2_relat_1(X21)) = k1_relat_1(X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).

fof(c_0_50,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_51,plain,(
    ! [X26,X27,X28] :
      ( ~ v1_relat_1(X28)
      | k10_relat_1(k7_relat_1(X28,X26),X27) = k3_xboole_0(X26,k10_relat_1(X28,X27)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).

fof(c_0_52,plain,(
    ! [X19,X20] :
      ( ~ v1_relat_1(X20)
      | r1_tarski(k10_relat_1(X20,X19),k1_relat_1(X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).

fof(c_0_53,plain,(
    ! [X33,X34,X35] :
      ( ~ v1_relat_1(X35)
      | ~ v1_funct_1(X35)
      | ~ r1_tarski(X33,k1_relat_1(X35))
      | ~ r1_tarski(k9_relat_1(X35,X33),X34)
      | r1_tarski(X33,k10_relat_1(X35,X34)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t163_funct_1])])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(k10_relat_1(esk1_0,esk3_0)),X1)),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46])])).

cnf(c_0_55,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_56,plain,
    ( k9_relat_1(X1,k10_relat_1(X1,X2)) = k3_xboole_0(X2,k9_relat_1(X1,k1_relat_1(X1)))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_57,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_58,plain,(
    ! [X29,X30] :
      ( ~ v1_relat_1(X30)
      | ~ v1_funct_1(X30)
      | ~ r1_tarski(X29,k2_relat_1(X30))
      | k9_relat_1(X30,k10_relat_1(X30,X29)) = X29 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t147_funct_1])])).

cnf(c_0_59,plain,
    ( k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_60,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_61,plain,
    ( k10_relat_1(k7_relat_1(X1,X2),X3) = k3_xboole_0(X2,k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_62,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_63,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_64,plain,
    ( r1_tarski(X2,k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1))
    | ~ r1_tarski(k9_relat_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(k9_relat_1(k6_relat_1(k10_relat_1(esk1_0,esk3_0)),X1),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_46])])).

cnf(c_0_66,plain,
    ( v1_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_67,plain,
    ( k9_relat_1(X1,k10_relat_1(X1,X2)) = k1_setfam_1(k1_enumset1(X2,X2,k9_relat_1(X1,k1_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(rw,[status(thm)],[c_0_56,c_0_33])).

cnf(c_0_68,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k1_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_39])).

cnf(c_0_69,plain,
    ( k9_relat_1(X1,k10_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(X2,k2_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_70,plain,
    ( k10_relat_1(k6_relat_1(X1),X1) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_38]),c_0_57]),c_0_46])])).

cnf(c_0_71,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_60])).

cnf(c_0_72,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k1_setfam_1(k1_enumset1(X2,X2,X3))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_37])).

cnf(c_0_73,plain,
    ( k10_relat_1(k7_relat_1(X1,X2),X3) = k1_setfam_1(k1_enumset1(X2,X2,k10_relat_1(X1,X3)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_61,c_0_33])).

cnf(c_0_74,plain,
    ( k1_relat_1(X1) = k10_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),k10_relat_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_75,negated_conjecture,
    ( r1_tarski(X1,k10_relat_1(k6_relat_1(k10_relat_1(esk1_0,esk3_0)),esk2_0))
    | ~ r1_tarski(X1,k10_relat_1(esk1_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_66]),c_0_46]),c_0_57])])).

cnf(c_0_76,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(k9_relat_1(X1,k1_relat_1(X1))),k6_relat_1(X2))) = k9_relat_1(X1,k10_relat_1(X1,X2))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_77,plain,
    ( k9_relat_1(k6_relat_1(X1),X1) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_66]),c_0_46]),c_0_38]),c_0_71])])).

cnf(c_0_78,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k2_relat_1(k5_relat_1(k6_relat_1(X3),k6_relat_1(X2)))) ),
    inference(spm,[status(thm)],[c_0_72,c_0_41])).

cnf(c_0_79,plain,
    ( k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) ),
    inference(rw,[status(thm)],[c_0_41,c_0_68])).

cnf(c_0_80,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(k10_relat_1(X1,X2)),k6_relat_1(X3))) = k10_relat_1(k7_relat_1(X1,X3),X2)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_73,c_0_68])).

cnf(c_0_81,negated_conjecture,
    ( k10_relat_1(k6_relat_1(k10_relat_1(esk1_0,esk3_0)),esk2_0) = k10_relat_1(esk1_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_57]),c_0_46]),c_0_57]),c_0_71])])).

cnf(c_0_82,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_57]),c_0_77]),c_0_66]),c_0_46])])).

cnf(c_0_83,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k2_relat_1(k7_relat_1(k6_relat_1(X2),X3))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_45]),c_0_46])])).

cnf(c_0_84,plain,
    ( k2_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_45]),c_0_46])])).

cnf(c_0_85,negated_conjecture,
    ( k9_relat_1(k6_relat_1(k10_relat_1(esk1_0,esk3_0)),k10_relat_1(k6_relat_1(k10_relat_1(esk1_0,esk3_0)),X1)) = k10_relat_1(k7_relat_1(k6_relat_1(k10_relat_1(esk1_0,esk3_0)),X1),esk2_0) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_46])]),c_0_82])).

cnf(c_0_86,plain,
    ( v1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_39])).

cnf(c_0_87,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k9_relat_1(k6_relat_1(X2),X3)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_55]),c_0_46])])).

cnf(c_0_88,plain,
    ( k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) ),
    inference(rw,[status(thm)],[c_0_39,c_0_68])).

cnf(c_0_89,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = k9_relat_1(k6_relat_1(X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_84]),c_0_46])])).

cnf(c_0_90,negated_conjecture,
    ( k10_relat_1(k7_relat_1(k6_relat_1(k10_relat_1(esk1_0,esk3_0)),esk2_0),esk2_0) = k10_relat_1(esk1_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_81]),c_0_77])).

cnf(c_0_91,plain,
    ( v1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_45]),c_0_46])])).

cnf(c_0_92,plain,
    ( r1_tarski(k9_relat_1(k6_relat_1(X1),X2),X1) ),
    inference(spm,[status(thm)],[c_0_87,c_0_71])).

cnf(c_0_93,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k10_relat_1(k7_relat_1(k6_relat_1(X1),X2),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_70]),c_0_46])])).

cnf(c_0_94,plain,
    ( k6_relat_1(k9_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k6_relat_1(X1),X2) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_45]),c_0_46])]),c_0_89])).

cnf(c_0_95,negated_conjecture,
    ( k9_relat_1(k6_relat_1(k10_relat_1(esk1_0,esk3_0)),esk2_0) = k10_relat_1(esk1_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_90]),c_0_89]),c_0_91]),c_0_89]),c_0_92])])).

cnf(c_0_96,plain,
    ( k10_relat_1(k7_relat_1(k6_relat_1(X1),X2),X1) = k9_relat_1(k6_relat_1(X2),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_45]),c_0_89]),c_0_46])])).

cnf(c_0_97,negated_conjecture,
    ( k7_relat_1(k6_relat_1(k10_relat_1(esk1_0,esk3_0)),esk2_0) = k6_relat_1(k10_relat_1(esk1_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_98,plain,
    ( k9_relat_1(k6_relat_1(X1),k10_relat_1(X2,X3)) = k10_relat_1(k7_relat_1(X2,X1),X3)
    | ~ v1_relat_1(X2) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_45]),c_0_46])]),c_0_89])).

cnf(c_0_99,negated_conjecture,
    ( k9_relat_1(k6_relat_1(esk2_0),k10_relat_1(esk1_0,esk3_0)) = k10_relat_1(esk1_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_70])).

cnf(c_0_100,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_101,negated_conjecture,
    ( k10_relat_1(esk1_0,esk3_0) != k10_relat_1(k7_relat_1(esk1_0,esk2_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_102,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_100])]),c_0_101]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:56:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.47/0.63  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.47/0.63  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.47/0.63  #
% 0.47/0.63  # Preprocessing time       : 0.020 s
% 0.47/0.63  # Presaturation interreduction done
% 0.47/0.63  
% 0.47/0.63  # Proof found!
% 0.47/0.63  # SZS status Theorem
% 0.47/0.63  # SZS output start CNFRefutation
% 0.47/0.63  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 0.47/0.63  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.47/0.63  fof(t175_funct_2, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:(r1_tarski(k10_relat_1(X1,X3),X2)=>k10_relat_1(X1,X3)=k10_relat_1(k7_relat_1(X1,X2),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_funct_2)).
% 0.47/0.63  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.47/0.63  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.47/0.63  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.47/0.63  fof(t43_funct_1, axiom, ![X1, X2]:k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))=k6_relat_1(k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 0.47/0.63  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 0.47/0.63  fof(t94_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k5_relat_1(k6_relat_1(X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 0.47/0.63  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 0.47/0.63  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 0.47/0.63  fof(t148_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>k9_relat_1(X2,k10_relat_1(X2,X1))=k3_xboole_0(X1,k9_relat_1(X2,k1_relat_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_funct_1)).
% 0.47/0.63  fof(t169_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 0.47/0.63  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.47/0.63  fof(t139_funct_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k10_relat_1(k7_relat_1(X3,X1),X2)=k3_xboole_0(X1,k10_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 0.47/0.63  fof(t167_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 0.47/0.63  fof(t163_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((r1_tarski(X1,k1_relat_1(X3))&r1_tarski(k9_relat_1(X3,X1),X2))=>r1_tarski(X1,k10_relat_1(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t163_funct_1)).
% 0.47/0.63  fof(t147_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(X1,k2_relat_1(X2))=>k9_relat_1(X2,k10_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 0.47/0.63  fof(c_0_18, plain, ![X6, X7, X8]:(~r1_tarski(k2_xboole_0(X6,X7),X8)|r1_tarski(X6,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 0.47/0.63  fof(c_0_19, plain, ![X9, X10]:(~r1_tarski(X9,X10)|k2_xboole_0(X9,X10)=X10), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.47/0.63  fof(c_0_20, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:(r1_tarski(k10_relat_1(X1,X3),X2)=>k10_relat_1(X1,X3)=k10_relat_1(k7_relat_1(X1,X2),X3)))), inference(assume_negation,[status(cth)],[t175_funct_2])).
% 0.47/0.63  fof(c_0_21, plain, ![X15, X16]:k1_setfam_1(k2_tarski(X15,X16))=k3_xboole_0(X15,X16), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.47/0.63  fof(c_0_22, plain, ![X13, X14]:k1_enumset1(X13,X13,X14)=k2_tarski(X13,X14), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.47/0.63  cnf(c_0_23, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.47/0.63  cnf(c_0_24, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.47/0.63  fof(c_0_25, negated_conjecture, ((v1_relat_1(esk1_0)&v1_funct_1(esk1_0))&(r1_tarski(k10_relat_1(esk1_0,esk3_0),esk2_0)&k10_relat_1(esk1_0,esk3_0)!=k10_relat_1(k7_relat_1(esk1_0,esk2_0),esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).
% 0.47/0.63  fof(c_0_26, plain, ![X11, X12]:r1_tarski(k3_xboole_0(X11,X12),X11), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.47/0.63  cnf(c_0_27, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.47/0.63  cnf(c_0_28, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.47/0.63  fof(c_0_29, plain, ![X36, X37]:k5_relat_1(k6_relat_1(X37),k6_relat_1(X36))=k6_relat_1(k3_xboole_0(X36,X37)), inference(variable_rename,[status(thm)],[t43_funct_1])).
% 0.47/0.63  cnf(c_0_30, plain, (r1_tarski(X1,X2)|~r1_tarski(X3,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.47/0.63  cnf(c_0_31, negated_conjecture, (r1_tarski(k10_relat_1(esk1_0,esk3_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.47/0.63  cnf(c_0_32, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.47/0.63  cnf(c_0_33, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 0.47/0.63  fof(c_0_34, plain, ![X22]:(k1_relat_1(k6_relat_1(X22))=X22&k2_relat_1(k6_relat_1(X22))=X22), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.47/0.63  cnf(c_0_35, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(k3_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.47/0.63  cnf(c_0_36, negated_conjecture, (r1_tarski(X1,esk2_0)|~r1_tarski(X1,k10_relat_1(esk1_0,esk3_0))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.47/0.63  cnf(c_0_37, plain, (r1_tarski(k1_setfam_1(k1_enumset1(X1,X1,X2)),X1)), inference(rw,[status(thm)],[c_0_32, c_0_33])).
% 0.47/0.63  cnf(c_0_38, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.47/0.63  cnf(c_0_39, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(k1_setfam_1(k1_enumset1(X2,X2,X1)))), inference(rw,[status(thm)],[c_0_35, c_0_33])).
% 0.47/0.63  cnf(c_0_40, negated_conjecture, (r1_tarski(k1_setfam_1(k1_enumset1(k10_relat_1(esk1_0,esk3_0),k10_relat_1(esk1_0,esk3_0),X1)),esk2_0)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.47/0.63  cnf(c_0_41, plain, (k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))=k1_setfam_1(k1_enumset1(X2,X2,X1))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.47/0.63  fof(c_0_42, plain, ![X23, X24]:(~v1_relat_1(X24)|k7_relat_1(X24,X23)=k5_relat_1(k6_relat_1(X23),X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).
% 0.47/0.63  fof(c_0_43, plain, ![X25]:(v1_relat_1(k6_relat_1(X25))&v1_funct_1(k6_relat_1(X25))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 0.47/0.63  cnf(c_0_44, negated_conjecture, (r1_tarski(k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(k10_relat_1(esk1_0,esk3_0)))),esk2_0)), inference(rw,[status(thm)],[c_0_40, c_0_41])).
% 0.47/0.63  cnf(c_0_45, plain, (k7_relat_1(X1,X2)=k5_relat_1(k6_relat_1(X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.47/0.63  cnf(c_0_46, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.47/0.63  fof(c_0_47, plain, ![X17, X18]:(~v1_relat_1(X18)|k2_relat_1(k7_relat_1(X18,X17))=k9_relat_1(X18,X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.47/0.63  fof(c_0_48, plain, ![X31, X32]:(~v1_relat_1(X32)|~v1_funct_1(X32)|k9_relat_1(X32,k10_relat_1(X32,X31))=k3_xboole_0(X31,k9_relat_1(X32,k1_relat_1(X32)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_funct_1])])).
% 0.47/0.63  fof(c_0_49, plain, ![X21]:(~v1_relat_1(X21)|k10_relat_1(X21,k2_relat_1(X21))=k1_relat_1(X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).
% 0.47/0.63  fof(c_0_50, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.47/0.63  fof(c_0_51, plain, ![X26, X27, X28]:(~v1_relat_1(X28)|k10_relat_1(k7_relat_1(X28,X26),X27)=k3_xboole_0(X26,k10_relat_1(X28,X27))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).
% 0.47/0.63  fof(c_0_52, plain, ![X19, X20]:(~v1_relat_1(X20)|r1_tarski(k10_relat_1(X20,X19),k1_relat_1(X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).
% 0.47/0.63  fof(c_0_53, plain, ![X33, X34, X35]:(~v1_relat_1(X35)|~v1_funct_1(X35)|(~r1_tarski(X33,k1_relat_1(X35))|~r1_tarski(k9_relat_1(X35,X33),X34)|r1_tarski(X33,k10_relat_1(X35,X34)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t163_funct_1])])).
% 0.47/0.63  cnf(c_0_54, negated_conjecture, (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(k10_relat_1(esk1_0,esk3_0)),X1)),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46])])).
% 0.47/0.63  cnf(c_0_55, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.47/0.63  cnf(c_0_56, plain, (k9_relat_1(X1,k10_relat_1(X1,X2))=k3_xboole_0(X2,k9_relat_1(X1,k1_relat_1(X1)))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.47/0.63  cnf(c_0_57, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.47/0.63  fof(c_0_58, plain, ![X29, X30]:(~v1_relat_1(X30)|~v1_funct_1(X30)|(~r1_tarski(X29,k2_relat_1(X30))|k9_relat_1(X30,k10_relat_1(X30,X29))=X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t147_funct_1])])).
% 0.47/0.63  cnf(c_0_59, plain, (k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.47/0.63  cnf(c_0_60, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.47/0.63  cnf(c_0_61, plain, (k10_relat_1(k7_relat_1(X1,X2),X3)=k3_xboole_0(X2,k10_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.47/0.63  cnf(c_0_62, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.47/0.63  cnf(c_0_63, plain, (r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.47/0.63  cnf(c_0_64, plain, (r1_tarski(X2,k10_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~r1_tarski(X2,k1_relat_1(X1))|~r1_tarski(k9_relat_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.47/0.63  cnf(c_0_65, negated_conjecture, (r1_tarski(k9_relat_1(k6_relat_1(k10_relat_1(esk1_0,esk3_0)),X1),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_46])])).
% 0.47/0.63  cnf(c_0_66, plain, (v1_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.47/0.63  cnf(c_0_67, plain, (k9_relat_1(X1,k10_relat_1(X1,X2))=k1_setfam_1(k1_enumset1(X2,X2,k9_relat_1(X1,k1_relat_1(X1))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(rw,[status(thm)],[c_0_56, c_0_33])).
% 0.47/0.63  cnf(c_0_68, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k1_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)))), inference(spm,[status(thm)],[c_0_57, c_0_39])).
% 0.47/0.63  cnf(c_0_69, plain, (k9_relat_1(X1,k10_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~v1_funct_1(X1)|~r1_tarski(X2,k2_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.47/0.63  cnf(c_0_70, plain, (k10_relat_1(k6_relat_1(X1),X1)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_38]), c_0_57]), c_0_46])])).
% 0.47/0.63  cnf(c_0_71, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_60])).
% 0.47/0.63  cnf(c_0_72, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k1_setfam_1(k1_enumset1(X2,X2,X3)))), inference(spm,[status(thm)],[c_0_30, c_0_37])).
% 0.47/0.63  cnf(c_0_73, plain, (k10_relat_1(k7_relat_1(X1,X2),X3)=k1_setfam_1(k1_enumset1(X2,X2,k10_relat_1(X1,X3)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_61, c_0_33])).
% 0.47/0.63  cnf(c_0_74, plain, (k1_relat_1(X1)=k10_relat_1(X1,X2)|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),k10_relat_1(X1,X2))), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.47/0.63  cnf(c_0_75, negated_conjecture, (r1_tarski(X1,k10_relat_1(k6_relat_1(k10_relat_1(esk1_0,esk3_0)),esk2_0))|~r1_tarski(X1,k10_relat_1(esk1_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_66]), c_0_46]), c_0_57])])).
% 0.47/0.63  cnf(c_0_76, plain, (k1_relat_1(k5_relat_1(k6_relat_1(k9_relat_1(X1,k1_relat_1(X1))),k6_relat_1(X2)))=k9_relat_1(X1,k10_relat_1(X1,X2))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_67, c_0_68])).
% 0.47/0.63  cnf(c_0_77, plain, (k9_relat_1(k6_relat_1(X1),X1)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_66]), c_0_46]), c_0_38]), c_0_71])])).
% 0.47/0.63  cnf(c_0_78, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k2_relat_1(k5_relat_1(k6_relat_1(X3),k6_relat_1(X2))))), inference(spm,[status(thm)],[c_0_72, c_0_41])).
% 0.47/0.63  cnf(c_0_79, plain, (k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))=k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))), inference(rw,[status(thm)],[c_0_41, c_0_68])).
% 0.47/0.63  cnf(c_0_80, plain, (k1_relat_1(k5_relat_1(k6_relat_1(k10_relat_1(X1,X2)),k6_relat_1(X3)))=k10_relat_1(k7_relat_1(X1,X3),X2)|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_73, c_0_68])).
% 0.47/0.63  cnf(c_0_81, negated_conjecture, (k10_relat_1(k6_relat_1(k10_relat_1(esk1_0,esk3_0)),esk2_0)=k10_relat_1(esk1_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_57]), c_0_46]), c_0_57]), c_0_71])])).
% 0.47/0.63  cnf(c_0_82, plain, (k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))=k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_57]), c_0_77]), c_0_66]), c_0_46])])).
% 0.47/0.63  cnf(c_0_83, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k2_relat_1(k7_relat_1(k6_relat_1(X2),X3)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_45]), c_0_46])])).
% 0.47/0.63  cnf(c_0_84, plain, (k2_relat_1(k7_relat_1(k6_relat_1(X1),X2))=k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_45]), c_0_46])])).
% 0.47/0.63  cnf(c_0_85, negated_conjecture, (k9_relat_1(k6_relat_1(k10_relat_1(esk1_0,esk3_0)),k10_relat_1(k6_relat_1(k10_relat_1(esk1_0,esk3_0)),X1))=k10_relat_1(k7_relat_1(k6_relat_1(k10_relat_1(esk1_0,esk3_0)),X1),esk2_0)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_46])]), c_0_82])).
% 0.47/0.63  cnf(c_0_86, plain, (v1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))), inference(spm,[status(thm)],[c_0_46, c_0_39])).
% 0.47/0.63  cnf(c_0_87, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k9_relat_1(k6_relat_1(X2),X3))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_55]), c_0_46])])).
% 0.47/0.63  cnf(c_0_88, plain, (k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))))=k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))), inference(rw,[status(thm)],[c_0_39, c_0_68])).
% 0.47/0.63  cnf(c_0_89, plain, (k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))=k9_relat_1(k6_relat_1(X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_84]), c_0_46])])).
% 0.47/0.63  cnf(c_0_90, negated_conjecture, (k10_relat_1(k7_relat_1(k6_relat_1(k10_relat_1(esk1_0,esk3_0)),esk2_0),esk2_0)=k10_relat_1(esk1_0,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_81]), c_0_77])).
% 0.47/0.63  cnf(c_0_91, plain, (v1_relat_1(k7_relat_1(k6_relat_1(X1),X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_45]), c_0_46])])).
% 0.47/0.63  cnf(c_0_92, plain, (r1_tarski(k9_relat_1(k6_relat_1(X1),X2),X1)), inference(spm,[status(thm)],[c_0_87, c_0_71])).
% 0.47/0.63  cnf(c_0_93, plain, (k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))=k10_relat_1(k7_relat_1(k6_relat_1(X1),X2),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_70]), c_0_46])])).
% 0.47/0.63  cnf(c_0_94, plain, (k6_relat_1(k9_relat_1(k6_relat_1(X1),X2))=k7_relat_1(k6_relat_1(X1),X2)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_45]), c_0_46])]), c_0_89])).
% 0.47/0.63  cnf(c_0_95, negated_conjecture, (k9_relat_1(k6_relat_1(k10_relat_1(esk1_0,esk3_0)),esk2_0)=k10_relat_1(esk1_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_90]), c_0_89]), c_0_91]), c_0_89]), c_0_92])])).
% 0.47/0.63  cnf(c_0_96, plain, (k10_relat_1(k7_relat_1(k6_relat_1(X1),X2),X1)=k9_relat_1(k6_relat_1(X2),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_45]), c_0_89]), c_0_46])])).
% 0.47/0.63  cnf(c_0_97, negated_conjecture, (k7_relat_1(k6_relat_1(k10_relat_1(esk1_0,esk3_0)),esk2_0)=k6_relat_1(k10_relat_1(esk1_0,esk3_0))), inference(spm,[status(thm)],[c_0_94, c_0_95])).
% 0.47/0.63  cnf(c_0_98, plain, (k9_relat_1(k6_relat_1(X1),k10_relat_1(X2,X3))=k10_relat_1(k7_relat_1(X2,X1),X3)|~v1_relat_1(X2)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_45]), c_0_46])]), c_0_89])).
% 0.47/0.63  cnf(c_0_99, negated_conjecture, (k9_relat_1(k6_relat_1(esk2_0),k10_relat_1(esk1_0,esk3_0))=k10_relat_1(esk1_0,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_70])).
% 0.47/0.63  cnf(c_0_100, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.47/0.63  cnf(c_0_101, negated_conjecture, (k10_relat_1(esk1_0,esk3_0)!=k10_relat_1(k7_relat_1(esk1_0,esk2_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.47/0.63  cnf(c_0_102, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_100])]), c_0_101]), ['proof']).
% 0.47/0.63  # SZS output end CNFRefutation
% 0.47/0.63  # Proof object total steps             : 103
% 0.47/0.63  # Proof object clause steps            : 66
% 0.47/0.63  # Proof object formula steps           : 37
% 0.47/0.63  # Proof object conjectures             : 19
% 0.47/0.63  # Proof object clause conjectures      : 16
% 0.47/0.63  # Proof object formula conjectures     : 3
% 0.47/0.63  # Proof object initial clauses used    : 23
% 0.47/0.63  # Proof object initial formulas used   : 18
% 0.47/0.63  # Proof object generating inferences   : 32
% 0.47/0.63  # Proof object simplifying inferences  : 70
% 0.47/0.63  # Training examples: 0 positive, 0 negative
% 0.47/0.63  # Parsed axioms                        : 18
% 0.47/0.63  # Removed by relevancy pruning/SinE    : 0
% 0.47/0.63  # Initial clauses                      : 25
% 0.47/0.63  # Removed in clause preprocessing      : 2
% 0.47/0.63  # Initial clauses in saturation        : 23
% 0.47/0.63  # Processed clauses                    : 2665
% 0.47/0.63  # ...of these trivial                  : 18
% 0.47/0.63  # ...subsumed                          : 1997
% 0.47/0.63  # ...remaining for further processing  : 650
% 0.47/0.63  # Other redundant clauses eliminated   : 2
% 0.47/0.63  # Clauses deleted for lack of memory   : 0
% 0.47/0.63  # Backward-subsumed                    : 6
% 0.47/0.63  # Backward-rewritten                   : 38
% 0.47/0.63  # Generated clauses                    : 20022
% 0.47/0.63  # ...of the previous two non-trivial   : 18607
% 0.47/0.63  # Contextual simplify-reflections      : 3
% 0.47/0.63  # Paramodulations                      : 20020
% 0.47/0.63  # Factorizations                       : 0
% 0.47/0.63  # Equation resolutions                 : 2
% 0.47/0.63  # Propositional unsat checks           : 0
% 0.47/0.63  #    Propositional check models        : 0
% 0.47/0.63  #    Propositional check unsatisfiable : 0
% 0.47/0.63  #    Propositional clauses             : 0
% 0.47/0.63  #    Propositional clauses after purity: 0
% 0.47/0.63  #    Propositional unsat core size     : 0
% 0.47/0.63  #    Propositional preprocessing time  : 0.000
% 0.47/0.63  #    Propositional encoding time       : 0.000
% 0.47/0.63  #    Propositional solver time         : 0.000
% 0.47/0.63  #    Success case prop preproc time    : 0.000
% 0.47/0.63  #    Success case prop encoding time   : 0.000
% 0.47/0.63  #    Success case prop solver time     : 0.000
% 0.47/0.63  # Current number of processed clauses  : 582
% 0.47/0.63  #    Positive orientable unit clauses  : 112
% 0.47/0.63  #    Positive unorientable unit clauses: 1
% 0.47/0.63  #    Negative unit clauses             : 2
% 0.47/0.63  #    Non-unit-clauses                  : 467
% 0.47/0.63  # Current number of unprocessed clauses: 15778
% 0.47/0.63  # ...number of literals in the above   : 45888
% 0.47/0.63  # Current number of archived formulas  : 0
% 0.47/0.63  # Current number of archived clauses   : 68
% 0.47/0.63  # Clause-clause subsumption calls (NU) : 64706
% 0.47/0.63  # Rec. Clause-clause subsumption calls : 38097
% 0.47/0.63  # Non-unit clause-clause subsumptions  : 1790
% 0.47/0.63  # Unit Clause-clause subsumption calls : 259
% 0.47/0.63  # Rewrite failures with RHS unbound    : 0
% 0.47/0.63  # BW rewrite match attempts            : 372
% 0.47/0.63  # BW rewrite match successes           : 52
% 0.47/0.63  # Condensation attempts                : 0
% 0.47/0.63  # Condensation successes               : 0
% 0.47/0.63  # Termbank termtop insertions          : 326245
% 0.47/0.64  
% 0.47/0.64  # -------------------------------------------------
% 0.47/0.64  # User time                : 0.283 s
% 0.47/0.64  # System time              : 0.011 s
% 0.47/0.64  # Total time               : 0.295 s
% 0.47/0.64  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------

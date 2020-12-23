%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:54:51 EST 2020

% Result     : Theorem 0.68s
% Output     : CNFRefutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :  124 (9312 expanded)
%              Number of clauses        :   85 (4200 expanded)
%              Number of leaves         :   19 (2328 expanded)
%              Depth                    :   24
%              Number of atoms          :  258 (21979 expanded)
%              Number of equality atoms :   72 (4629 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    5 (   2 average)

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

fof(t10_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(X1,k2_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(t146_funct_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t8_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(t167_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

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

fof(t139_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k10_relat_1(k7_relat_1(X3,X1),X2) = k3_xboole_0(X1,k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

fof(t98_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,k1_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

fof(t90_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k1_relat_1(k7_relat_1(X2,X1)) = k3_xboole_0(k1_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(t87_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(t192_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k7_relat_1(X2,k3_xboole_0(k1_relat_1(X2),X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).

fof(t97_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X1)
       => k7_relat_1(X2,X1) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(t91_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => k1_relat_1(k7_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(c_0_19,plain,(
    ! [X9,X10,X11] :
      ( ~ r1_tarski(k2_xboole_0(X9,X10),X11)
      | r1_tarski(X9,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

fof(c_0_20,plain,(
    ! [X12,X13] :
      ( ~ r1_tarski(X12,X13)
      | k2_xboole_0(X12,X13) = X13 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_22,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_23,plain,(
    ! [X6,X7,X8] :
      ( ~ r1_tarski(X6,X7)
      | r1_tarski(X6,k2_xboole_0(X8,X7)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).

fof(c_0_24,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X1,k1_relat_1(X2))
         => r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))) ) ) ),
    inference(assume_negation,[status(cth)],[t146_funct_1])).

fof(c_0_25,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_26,plain,(
    ! [X14,X15] : r1_tarski(X14,k2_xboole_0(X14,X15)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,k2_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_29,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & r1_tarski(esk1_0,k1_relat_1(esk2_0))
    & ~ r1_tarski(esk1_0,k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).

cnf(c_0_30,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_32,plain,(
    ! [X16,X17,X18] :
      ( ~ r1_tarski(X16,X17)
      | ~ r1_tarski(X18,X17)
      | r1_tarski(k2_xboole_0(X16,X18),X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X4)
    | ~ r1_tarski(X4,X3) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(esk1_0,k1_relat_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( k2_xboole_0(X1,X2) = X1
    | ~ r1_tarski(k2_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_37,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_33])).

fof(c_0_39,plain,(
    ! [X23,X24] :
      ( ~ v1_relat_1(X24)
      | r1_tarski(k10_relat_1(X24,X23),k1_relat_1(X24)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(esk1_0,k2_xboole_0(X1,X2))
    | ~ r1_tarski(k1_relat_1(esk2_0),X2) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_41,plain,
    ( k2_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38])])).

fof(c_0_42,plain,(
    ! [X26,X27] :
      ( ~ v1_relat_1(X27)
      | r1_tarski(k10_relat_1(X27,X26),k10_relat_1(X27,k2_relat_1(X27))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t170_relat_1])])).

fof(c_0_43,plain,(
    ! [X25] :
      ( ~ v1_relat_1(X25)
      | k10_relat_1(X25,k2_relat_1(X25)) = k1_relat_1(X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).

cnf(c_0_44,plain,
    ( k2_xboole_0(X1,X2) = X3
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_30,c_0_28])).

cnf(c_0_45,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(esk1_0,X1)
    | ~ r1_tarski(k1_relat_1(esk2_0),X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_47,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_48,plain,
    ( k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_49,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3)
    | ~ r1_tarski(X3,X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_41])).

cnf(c_0_50,plain,
    ( r1_tarski(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k10_relat_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_45])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(esk1_0,X1)
    | ~ r1_tarski(k1_relat_1(esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_38])).

cnf(c_0_52,plain,
    ( r1_tarski(k1_relat_1(X1),k10_relat_1(X1,k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_53,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_54,plain,(
    ! [X39,X40,X41] :
      ( ~ v1_relat_1(X41)
      | k10_relat_1(k7_relat_1(X41,X39),X40) = k3_xboole_0(X39,k10_relat_1(X41,X40)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).

cnf(c_0_55,plain,
    ( k2_xboole_0(X1,X2) = X1
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X3,X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_31])).

cnf(c_0_56,plain,
    ( r1_tarski(k2_xboole_0(X1,X2),k1_relat_1(X3))
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(X2,k10_relat_1(X3,X4))
    | ~ r1_tarski(X1,k10_relat_1(X3,X4)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_37])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(esk1_0,k10_relat_1(esk2_0,k2_relat_1(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53])])).

cnf(c_0_58,plain,
    ( k10_relat_1(k7_relat_1(X1,X2),X3) = k3_xboole_0(X2,k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

fof(c_0_59,plain,(
    ! [X38] :
      ( ~ v1_relat_1(X38)
      | k7_relat_1(X38,k1_relat_1(X38)) = X38 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_relat_1])])).

cnf(c_0_60,plain,
    ( k2_xboole_0(X1,X2) = X1
    | ~ r1_tarski(k2_xboole_0(k2_xboole_0(X1,X2),X3),X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_31])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(k2_xboole_0(X1,esk1_0),k1_relat_1(esk2_0))
    | ~ r1_tarski(X1,k10_relat_1(esk2_0,k2_relat_1(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_53])])).

fof(c_0_62,plain,(
    ! [X32,X33] :
      ( ~ v1_relat_1(X33)
      | k1_relat_1(k7_relat_1(X33,X32)) = k3_xboole_0(k1_relat_1(X33),X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).

cnf(c_0_63,plain,
    ( k10_relat_1(k7_relat_1(X1,X2),k2_relat_1(X1)) = k3_xboole_0(X2,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_48])).

cnf(c_0_64,plain,
    ( k7_relat_1(X1,k1_relat_1(X1)) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_65,plain,
    ( X1 = X2
    | ~ r1_tarski(k2_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_22])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(k2_xboole_0(k10_relat_1(esk2_0,X1),esk1_0),k1_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_47]),c_0_53])])).

fof(c_0_67,plain,(
    ! [X30,X31] :
      ( ~ v1_relat_1(X31)
      | r1_tarski(k1_relat_1(k7_relat_1(X31,X30)),X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).

fof(c_0_68,plain,(
    ! [X28,X29] :
      ( ~ v1_relat_1(X29)
      | k7_relat_1(X29,X28) = k7_relat_1(X29,k3_xboole_0(k1_relat_1(X29),X28)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t192_relat_1])])).

cnf(c_0_69,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k3_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_70,plain,
    ( k3_xboole_0(k1_relat_1(X1),k1_relat_1(X1)) = k10_relat_1(X1,k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_71,negated_conjecture,
    ( k10_relat_1(esk2_0,X1) = k1_relat_1(esk2_0)
    | ~ r1_tarski(k1_relat_1(esk2_0),k10_relat_1(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

fof(c_0_72,plain,(
    ! [X36,X37] :
      ( ~ v1_relat_1(X37)
      | ~ r1_tarski(k1_relat_1(X37),X36)
      | k7_relat_1(X37,X36) = X37 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).

cnf(c_0_73,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_74,plain,
    ( k7_relat_1(X1,X2) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_75,plain,
    ( k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(k7_relat_1(X1,k1_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_76,negated_conjecture,
    ( k10_relat_1(esk2_0,k2_relat_1(esk2_0)) = k1_relat_1(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_52]),c_0_53])])).

fof(c_0_77,plain,(
    ! [X34,X35] :
      ( ~ v1_relat_1(X35)
      | ~ r1_tarski(X34,k1_relat_1(X35))
      | k1_relat_1(k7_relat_1(X35,X34)) = X34 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_relat_1])])).

fof(c_0_78,plain,(
    ! [X19,X20] :
      ( ~ v1_relat_1(X19)
      | v1_relat_1(k7_relat_1(X19,X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

cnf(c_0_79,plain,
    ( k7_relat_1(X1,X2) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_80,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),k3_xboole_0(k1_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_81,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk2_0,k1_relat_1(esk2_0))) = k1_relat_1(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_53])])).

cnf(c_0_82,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_83,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_84,plain,
    ( k7_relat_1(X1,X2) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),k3_xboole_0(k1_relat_1(X1),X2)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_74])).

cnf(c_0_85,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk2_0),k3_xboole_0(k1_relat_1(esk2_0),k1_relat_1(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_53])])).

cnf(c_0_86,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3)) = k3_xboole_0(X2,X3)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_82]),c_0_83])).

cnf(c_0_87,negated_conjecture,
    ( k7_relat_1(esk2_0,k1_relat_1(esk2_0)) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_53])])).

cnf(c_0_88,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(X1,k1_relat_1(k7_relat_1(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_73])).

cnf(c_0_89,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),k3_xboole_0(X2,X3)) = k7_relat_1(k7_relat_1(X1,X2),X3)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_82]),c_0_83])).

cnf(c_0_90,negated_conjecture,
    ( k3_xboole_0(k1_relat_1(esk2_0),X1) = k1_relat_1(k7_relat_1(esk2_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_53]),c_0_38])])).

cnf(c_0_91,plain,
    ( r1_tarski(k10_relat_1(k7_relat_1(X1,X2),X3),X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_45]),c_0_83])).

cnf(c_0_92,negated_conjecture,
    ( k10_relat_1(k7_relat_1(esk2_0,X1),k2_relat_1(esk2_0)) = k3_xboole_0(X1,k1_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_76]),c_0_53])])).

cnf(c_0_93,negated_conjecture,
    ( k7_relat_1(esk2_0,k1_relat_1(k7_relat_1(esk2_0,X1))) = k7_relat_1(esk2_0,X1) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_87]),c_0_53]),c_0_38])]),c_0_90])).

cnf(c_0_94,plain,
    ( r1_tarski(k3_xboole_0(X1,k1_relat_1(X2)),X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_91,c_0_63])).

cnf(c_0_95,negated_conjecture,
    ( k3_xboole_0(k1_relat_1(k7_relat_1(esk2_0,X1)),k1_relat_1(esk2_0)) = k3_xboole_0(X1,k1_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_74]),c_0_92]),c_0_90]),c_0_53])])).

cnf(c_0_96,negated_conjecture,
    ( v1_relat_1(k7_relat_1(esk2_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_93]),c_0_53])])).

cnf(c_0_97,negated_conjecture,
    ( r1_tarski(k1_relat_1(k7_relat_1(esk2_0,k1_relat_1(X1))),k1_relat_1(esk2_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_94,c_0_90])).

cnf(c_0_98,plain,
    ( k7_relat_1(X1,k1_relat_1(k7_relat_1(X1,X2))) = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_74,c_0_69])).

cnf(c_0_99,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k3_xboole_0(X2,X3)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X3)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_79]),c_0_83])).

fof(c_0_100,plain,(
    ! [X21,X22] :
      ( ~ v1_relat_1(X22)
      | k2_relat_1(k7_relat_1(X22,X21)) = k9_relat_1(X22,X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

cnf(c_0_101,negated_conjecture,
    ( k1_relat_1(k7_relat_1(k7_relat_1(esk2_0,X1),k1_relat_1(esk2_0))) = k3_xboole_0(X1,k1_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_95]),c_0_96])])).

cnf(c_0_102,negated_conjecture,
    ( r1_tarski(k1_relat_1(k7_relat_1(esk2_0,X1)),k1_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_96]),c_0_53])])).

cnf(c_0_103,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(X1,k1_relat_1(X3))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_99,c_0_82])).

cnf(c_0_104,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_100])).

cnf(c_0_105,plain,
    ( k10_relat_1(k7_relat_1(X1,k1_relat_1(X2)),X3) = k1_relat_1(k7_relat_1(X2,k10_relat_1(X1,X3)))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_69,c_0_58])).

cnf(c_0_106,negated_conjecture,
    ( k3_xboole_0(X1,k1_relat_1(esk2_0)) = k1_relat_1(k7_relat_1(esk2_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_79]),c_0_96]),c_0_102])])).

cnf(c_0_107,negated_conjecture,
    ( k3_xboole_0(esk1_0,X1) = esk1_0
    | ~ r1_tarski(esk1_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_35]),c_0_53])])).

cnf(c_0_108,plain,
    ( k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X2)) = k2_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_104,c_0_74])).

cnf(c_0_109,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X2)
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(X1,k1_relat_1(X3)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_86]),c_0_83])).

cnf(c_0_110,plain,
    ( k3_xboole_0(X1,k1_relat_1(k7_relat_1(X2,k10_relat_1(X3,X4)))) = k10_relat_1(k7_relat_1(k7_relat_1(X3,k1_relat_1(X2)),X1),X4)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_105]),c_0_83])).

cnf(c_0_111,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk2_0,k10_relat_1(esk2_0,X1))) = k10_relat_1(esk2_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_87]),c_0_53])])).

cnf(c_0_112,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk2_0,esk1_0)) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_107]),c_0_35])])).

cnf(c_0_113,negated_conjecture,
    ( k9_relat_1(esk2_0,k1_relat_1(k7_relat_1(esk2_0,X1))) = k2_relat_1(k7_relat_1(esk2_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_90]),c_0_53])])).

cnf(c_0_114,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk1_0,X1),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_35]),c_0_53])])).

cnf(c_0_115,negated_conjecture,
    ( k3_xboole_0(X1,k10_relat_1(esk2_0,X2)) = k10_relat_1(k7_relat_1(esk2_0,X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_111]),c_0_87]),c_0_53])])).

cnf(c_0_116,plain,
    ( k10_relat_1(k7_relat_1(X1,X2),k9_relat_1(X1,X2)) = k1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_104]),c_0_83])).

cnf(c_0_117,negated_conjecture,
    ( k7_relat_1(k7_relat_1(esk2_0,esk1_0),esk1_0) = k7_relat_1(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_112]),c_0_96])])).

cnf(c_0_118,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk2_0,esk1_0)) = k9_relat_1(esk2_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_113,c_0_112])).

cnf(c_0_119,negated_conjecture,
    ( r1_tarski(k10_relat_1(k7_relat_1(esk2_0,esk1_0),X1),k10_relat_1(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_114,c_0_115])).

cnf(c_0_120,plain,
    ( k10_relat_1(X1,k9_relat_1(X1,k1_relat_1(X1))) = k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_116,c_0_64])).

cnf(c_0_121,negated_conjecture,
    ( k9_relat_1(k7_relat_1(esk2_0,esk1_0),esk1_0) = k9_relat_1(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_117]),c_0_118]),c_0_96])])).

cnf(c_0_122,negated_conjecture,
    ( ~ r1_tarski(esk1_0,k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_123,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_120]),c_0_112]),c_0_112]),c_0_121]),c_0_96])]),c_0_122]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:54:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.68/0.85  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_TT_S0Y
% 0.68/0.85  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.68/0.85  #
% 0.68/0.85  # Preprocessing time       : 0.027 s
% 0.68/0.85  # Presaturation interreduction done
% 0.68/0.85  
% 0.68/0.85  # Proof found!
% 0.68/0.85  # SZS status Theorem
% 0.68/0.85  # SZS output start CNFRefutation
% 0.68/0.85  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 0.68/0.85  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.68/0.85  fof(t10_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(X1,k2_xboole_0(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 0.68/0.85  fof(t146_funct_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 0.68/0.85  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.68/0.85  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.68/0.85  fof(t8_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 0.68/0.85  fof(t167_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 0.68/0.85  fof(t170_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k10_relat_1(X2,X1),k10_relat_1(X2,k2_relat_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t170_relat_1)).
% 0.68/0.85  fof(t169_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 0.68/0.85  fof(t139_funct_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k10_relat_1(k7_relat_1(X3,X1),X2)=k3_xboole_0(X1,k10_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 0.68/0.85  fof(t98_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k7_relat_1(X1,k1_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 0.68/0.85  fof(t90_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k1_relat_1(k7_relat_1(X2,X1))=k3_xboole_0(k1_relat_1(X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 0.68/0.85  fof(t87_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 0.68/0.85  fof(t192_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k7_relat_1(X2,k3_xboole_0(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t192_relat_1)).
% 0.68/0.85  fof(t97_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X2),X1)=>k7_relat_1(X2,X1)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 0.68/0.85  fof(t91_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>k1_relat_1(k7_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 0.68/0.85  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.68/0.85  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 0.68/0.85  fof(c_0_19, plain, ![X9, X10, X11]:(~r1_tarski(k2_xboole_0(X9,X10),X11)|r1_tarski(X9,X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 0.68/0.85  fof(c_0_20, plain, ![X12, X13]:(~r1_tarski(X12,X13)|k2_xboole_0(X12,X13)=X13), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.68/0.85  cnf(c_0_21, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.68/0.85  cnf(c_0_22, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.68/0.85  fof(c_0_23, plain, ![X6, X7, X8]:(~r1_tarski(X6,X7)|r1_tarski(X6,k2_xboole_0(X8,X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).
% 0.68/0.85  fof(c_0_24, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1)))))), inference(assume_negation,[status(cth)],[t146_funct_1])).
% 0.68/0.85  fof(c_0_25, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.68/0.85  fof(c_0_26, plain, ![X14, X15]:r1_tarski(X14,k2_xboole_0(X14,X15)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.68/0.85  cnf(c_0_27, plain, (r1_tarski(X1,X2)|~r1_tarski(X3,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.68/0.85  cnf(c_0_28, plain, (r1_tarski(X1,k2_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.68/0.85  fof(c_0_29, negated_conjecture, (v1_relat_1(esk2_0)&(r1_tarski(esk1_0,k1_relat_1(esk2_0))&~r1_tarski(esk1_0,k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).
% 0.68/0.85  cnf(c_0_30, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.68/0.85  cnf(c_0_31, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.68/0.85  fof(c_0_32, plain, ![X16, X17, X18]:(~r1_tarski(X16,X17)|~r1_tarski(X18,X17)|r1_tarski(k2_xboole_0(X16,X18),X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).
% 0.68/0.85  cnf(c_0_33, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.68/0.85  cnf(c_0_34, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(X1,X4)|~r1_tarski(X4,X3)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.68/0.85  cnf(c_0_35, negated_conjecture, (r1_tarski(esk1_0,k1_relat_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.68/0.85  cnf(c_0_36, plain, (k2_xboole_0(X1,X2)=X1|~r1_tarski(k2_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.68/0.85  cnf(c_0_37, plain, (r1_tarski(k2_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.68/0.85  cnf(c_0_38, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_33])).
% 0.68/0.85  fof(c_0_39, plain, ![X23, X24]:(~v1_relat_1(X24)|r1_tarski(k10_relat_1(X24,X23),k1_relat_1(X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).
% 0.68/0.85  cnf(c_0_40, negated_conjecture, (r1_tarski(esk1_0,k2_xboole_0(X1,X2))|~r1_tarski(k1_relat_1(esk2_0),X2)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.68/0.85  cnf(c_0_41, plain, (k2_xboole_0(X1,X2)=X1|~r1_tarski(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38])])).
% 0.68/0.85  fof(c_0_42, plain, ![X26, X27]:(~v1_relat_1(X27)|r1_tarski(k10_relat_1(X27,X26),k10_relat_1(X27,k2_relat_1(X27)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t170_relat_1])])).
% 0.68/0.85  fof(c_0_43, plain, ![X25]:(~v1_relat_1(X25)|k10_relat_1(X25,k2_relat_1(X25))=k1_relat_1(X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).
% 0.68/0.85  cnf(c_0_44, plain, (k2_xboole_0(X1,X2)=X3|~r1_tarski(k2_xboole_0(X1,X2),X3)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_30, c_0_28])).
% 0.68/0.85  cnf(c_0_45, plain, (r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.68/0.85  cnf(c_0_46, negated_conjecture, (r1_tarski(esk1_0,X1)|~r1_tarski(k1_relat_1(esk2_0),X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.68/0.85  cnf(c_0_47, plain, (r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,k2_relat_1(X1)))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.68/0.85  cnf(c_0_48, plain, (k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.68/0.85  cnf(c_0_49, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)|~r1_tarski(X3,X1)), inference(spm,[status(thm)],[c_0_44, c_0_41])).
% 0.68/0.85  cnf(c_0_50, plain, (r1_tarski(X1,k1_relat_1(X2))|~v1_relat_1(X2)|~r1_tarski(X1,k10_relat_1(X2,X3))), inference(spm,[status(thm)],[c_0_27, c_0_45])).
% 0.68/0.85  cnf(c_0_51, negated_conjecture, (r1_tarski(esk1_0,X1)|~r1_tarski(k1_relat_1(esk2_0),X1)), inference(spm,[status(thm)],[c_0_46, c_0_38])).
% 0.68/0.85  cnf(c_0_52, plain, (r1_tarski(k1_relat_1(X1),k10_relat_1(X1,k2_relat_1(X1)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.68/0.85  cnf(c_0_53, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.68/0.85  fof(c_0_54, plain, ![X39, X40, X41]:(~v1_relat_1(X41)|k10_relat_1(k7_relat_1(X41,X39),X40)=k3_xboole_0(X39,k10_relat_1(X41,X40))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).
% 0.68/0.85  cnf(c_0_55, plain, (k2_xboole_0(X1,X2)=X1|~r1_tarski(k2_xboole_0(X1,X2),X3)|~r1_tarski(X3,X1)), inference(spm,[status(thm)],[c_0_49, c_0_31])).
% 0.68/0.85  cnf(c_0_56, plain, (r1_tarski(k2_xboole_0(X1,X2),k1_relat_1(X3))|~v1_relat_1(X3)|~r1_tarski(X2,k10_relat_1(X3,X4))|~r1_tarski(X1,k10_relat_1(X3,X4))), inference(spm,[status(thm)],[c_0_50, c_0_37])).
% 0.68/0.85  cnf(c_0_57, negated_conjecture, (r1_tarski(esk1_0,k10_relat_1(esk2_0,k2_relat_1(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53])])).
% 0.68/0.85  cnf(c_0_58, plain, (k10_relat_1(k7_relat_1(X1,X2),X3)=k3_xboole_0(X2,k10_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.68/0.85  fof(c_0_59, plain, ![X38]:(~v1_relat_1(X38)|k7_relat_1(X38,k1_relat_1(X38))=X38), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_relat_1])])).
% 0.68/0.85  cnf(c_0_60, plain, (k2_xboole_0(X1,X2)=X1|~r1_tarski(k2_xboole_0(k2_xboole_0(X1,X2),X3),X1)), inference(spm,[status(thm)],[c_0_55, c_0_31])).
% 0.68/0.85  cnf(c_0_61, negated_conjecture, (r1_tarski(k2_xboole_0(X1,esk1_0),k1_relat_1(esk2_0))|~r1_tarski(X1,k10_relat_1(esk2_0,k2_relat_1(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_53])])).
% 0.68/0.85  fof(c_0_62, plain, ![X32, X33]:(~v1_relat_1(X33)|k1_relat_1(k7_relat_1(X33,X32))=k3_xboole_0(k1_relat_1(X33),X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).
% 0.68/0.85  cnf(c_0_63, plain, (k10_relat_1(k7_relat_1(X1,X2),k2_relat_1(X1))=k3_xboole_0(X2,k1_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_58, c_0_48])).
% 0.68/0.85  cnf(c_0_64, plain, (k7_relat_1(X1,k1_relat_1(X1))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.68/0.85  cnf(c_0_65, plain, (X1=X2|~r1_tarski(k2_xboole_0(X1,X3),X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_60, c_0_22])).
% 0.68/0.85  cnf(c_0_66, negated_conjecture, (r1_tarski(k2_xboole_0(k10_relat_1(esk2_0,X1),esk1_0),k1_relat_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_47]), c_0_53])])).
% 0.68/0.85  fof(c_0_67, plain, ![X30, X31]:(~v1_relat_1(X31)|r1_tarski(k1_relat_1(k7_relat_1(X31,X30)),X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).
% 0.68/0.85  fof(c_0_68, plain, ![X28, X29]:(~v1_relat_1(X29)|k7_relat_1(X29,X28)=k7_relat_1(X29,k3_xboole_0(k1_relat_1(X29),X28))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t192_relat_1])])).
% 0.68/0.85  cnf(c_0_69, plain, (k1_relat_1(k7_relat_1(X1,X2))=k3_xboole_0(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.68/0.85  cnf(c_0_70, plain, (k3_xboole_0(k1_relat_1(X1),k1_relat_1(X1))=k10_relat_1(X1,k2_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.68/0.85  cnf(c_0_71, negated_conjecture, (k10_relat_1(esk2_0,X1)=k1_relat_1(esk2_0)|~r1_tarski(k1_relat_1(esk2_0),k10_relat_1(esk2_0,X1))), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.68/0.85  fof(c_0_72, plain, ![X36, X37]:(~v1_relat_1(X37)|(~r1_tarski(k1_relat_1(X37),X36)|k7_relat_1(X37,X36)=X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).
% 0.68/0.85  cnf(c_0_73, plain, (r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.68/0.85  cnf(c_0_74, plain, (k7_relat_1(X1,X2)=k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.68/0.85  cnf(c_0_75, plain, (k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(k7_relat_1(X1,k1_relat_1(X1)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.68/0.85  cnf(c_0_76, negated_conjecture, (k10_relat_1(esk2_0,k2_relat_1(esk2_0))=k1_relat_1(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_52]), c_0_53])])).
% 0.68/0.85  fof(c_0_77, plain, ![X34, X35]:(~v1_relat_1(X35)|(~r1_tarski(X34,k1_relat_1(X35))|k1_relat_1(k7_relat_1(X35,X34))=X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_relat_1])])).
% 0.68/0.85  fof(c_0_78, plain, ![X19, X20]:(~v1_relat_1(X19)|v1_relat_1(k7_relat_1(X19,X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.68/0.85  cnf(c_0_79, plain, (k7_relat_1(X1,X2)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.68/0.85  cnf(c_0_80, plain, (r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),k3_xboole_0(k1_relat_1(X1),X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.68/0.85  cnf(c_0_81, negated_conjecture, (k1_relat_1(k7_relat_1(esk2_0,k1_relat_1(esk2_0)))=k1_relat_1(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_53])])).
% 0.68/0.85  cnf(c_0_82, plain, (k1_relat_1(k7_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.68/0.85  cnf(c_0_83, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.68/0.85  cnf(c_0_84, plain, (k7_relat_1(X1,X2)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),k3_xboole_0(k1_relat_1(X1),X2))), inference(spm,[status(thm)],[c_0_79, c_0_74])).
% 0.68/0.85  cnf(c_0_85, negated_conjecture, (r1_tarski(k1_relat_1(esk2_0),k3_xboole_0(k1_relat_1(esk2_0),k1_relat_1(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_53])])).
% 0.68/0.85  cnf(c_0_86, plain, (k1_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3))=k3_xboole_0(X2,X3)|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_82]), c_0_83])).
% 0.68/0.85  cnf(c_0_87, negated_conjecture, (k7_relat_1(esk2_0,k1_relat_1(esk2_0))=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_53])])).
% 0.68/0.85  cnf(c_0_88, plain, (r1_tarski(X1,X2)|~v1_relat_1(X3)|~r1_tarski(X1,k1_relat_1(k7_relat_1(X3,X2)))), inference(spm,[status(thm)],[c_0_27, c_0_73])).
% 0.68/0.85  cnf(c_0_89, plain, (k7_relat_1(k7_relat_1(X1,X2),k3_xboole_0(X2,X3))=k7_relat_1(k7_relat_1(X1,X2),X3)|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_82]), c_0_83])).
% 0.68/0.85  cnf(c_0_90, negated_conjecture, (k3_xboole_0(k1_relat_1(esk2_0),X1)=k1_relat_1(k7_relat_1(esk2_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_53]), c_0_38])])).
% 0.68/0.85  cnf(c_0_91, plain, (r1_tarski(k10_relat_1(k7_relat_1(X1,X2),X3),X2)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_45]), c_0_83])).
% 0.68/0.85  cnf(c_0_92, negated_conjecture, (k10_relat_1(k7_relat_1(esk2_0,X1),k2_relat_1(esk2_0))=k3_xboole_0(X1,k1_relat_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_76]), c_0_53])])).
% 0.68/0.85  cnf(c_0_93, negated_conjecture, (k7_relat_1(esk2_0,k1_relat_1(k7_relat_1(esk2_0,X1)))=k7_relat_1(esk2_0,X1)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_87]), c_0_53]), c_0_38])]), c_0_90])).
% 0.68/0.85  cnf(c_0_94, plain, (r1_tarski(k3_xboole_0(X1,k1_relat_1(X2)),X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_91, c_0_63])).
% 0.68/0.85  cnf(c_0_95, negated_conjecture, (k3_xboole_0(k1_relat_1(k7_relat_1(esk2_0,X1)),k1_relat_1(esk2_0))=k3_xboole_0(X1,k1_relat_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_74]), c_0_92]), c_0_90]), c_0_53])])).
% 0.68/0.85  cnf(c_0_96, negated_conjecture, (v1_relat_1(k7_relat_1(esk2_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_93]), c_0_53])])).
% 0.68/0.85  cnf(c_0_97, negated_conjecture, (r1_tarski(k1_relat_1(k7_relat_1(esk2_0,k1_relat_1(X1))),k1_relat_1(esk2_0))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_94, c_0_90])).
% 0.68/0.85  cnf(c_0_98, plain, (k7_relat_1(X1,k1_relat_1(k7_relat_1(X1,X2)))=k7_relat_1(X1,X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_74, c_0_69])).
% 0.68/0.85  cnf(c_0_99, plain, (k1_relat_1(k7_relat_1(X1,X2))=k3_xboole_0(X2,X3)|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X3)|~r1_tarski(X2,k1_relat_1(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_79]), c_0_83])).
% 0.68/0.85  fof(c_0_100, plain, ![X21, X22]:(~v1_relat_1(X22)|k2_relat_1(k7_relat_1(X22,X21))=k9_relat_1(X22,X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.68/0.85  cnf(c_0_101, negated_conjecture, (k1_relat_1(k7_relat_1(k7_relat_1(esk2_0,X1),k1_relat_1(esk2_0)))=k3_xboole_0(X1,k1_relat_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_95]), c_0_96])])).
% 0.68/0.85  cnf(c_0_102, negated_conjecture, (r1_tarski(k1_relat_1(k7_relat_1(esk2_0,X1)),k1_relat_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_98]), c_0_96]), c_0_53])])).
% 0.68/0.85  cnf(c_0_103, plain, (k3_xboole_0(X1,X2)=X1|~v1_relat_1(X3)|~r1_tarski(X1,k1_relat_1(X3))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_99, c_0_82])).
% 0.68/0.85  cnf(c_0_104, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_100])).
% 0.68/0.85  cnf(c_0_105, plain, (k10_relat_1(k7_relat_1(X1,k1_relat_1(X2)),X3)=k1_relat_1(k7_relat_1(X2,k10_relat_1(X1,X3)))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_69, c_0_58])).
% 0.68/0.85  cnf(c_0_106, negated_conjecture, (k3_xboole_0(X1,k1_relat_1(esk2_0))=k1_relat_1(k7_relat_1(esk2_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_79]), c_0_96]), c_0_102])])).
% 0.68/0.85  cnf(c_0_107, negated_conjecture, (k3_xboole_0(esk1_0,X1)=esk1_0|~r1_tarski(esk1_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_35]), c_0_53])])).
% 0.68/0.85  cnf(c_0_108, plain, (k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X2))=k2_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_104, c_0_74])).
% 0.68/0.85  cnf(c_0_109, plain, (r1_tarski(k3_xboole_0(X1,X2),X2)|~v1_relat_1(X3)|~r1_tarski(X1,k1_relat_1(X3))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_86]), c_0_83])).
% 0.68/0.85  cnf(c_0_110, plain, (k3_xboole_0(X1,k1_relat_1(k7_relat_1(X2,k10_relat_1(X3,X4))))=k10_relat_1(k7_relat_1(k7_relat_1(X3,k1_relat_1(X2)),X1),X4)|~v1_relat_1(X2)|~v1_relat_1(X3)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_105]), c_0_83])).
% 0.68/0.85  cnf(c_0_111, negated_conjecture, (k1_relat_1(k7_relat_1(esk2_0,k10_relat_1(esk2_0,X1)))=k10_relat_1(esk2_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_87]), c_0_53])])).
% 0.68/0.85  cnf(c_0_112, negated_conjecture, (k1_relat_1(k7_relat_1(esk2_0,esk1_0))=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_107]), c_0_35])])).
% 0.68/0.85  cnf(c_0_113, negated_conjecture, (k9_relat_1(esk2_0,k1_relat_1(k7_relat_1(esk2_0,X1)))=k2_relat_1(k7_relat_1(esk2_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_90]), c_0_53])])).
% 0.68/0.85  cnf(c_0_114, negated_conjecture, (r1_tarski(k3_xboole_0(esk1_0,X1),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_35]), c_0_53])])).
% 0.68/0.85  cnf(c_0_115, negated_conjecture, (k3_xboole_0(X1,k10_relat_1(esk2_0,X2))=k10_relat_1(k7_relat_1(esk2_0,X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_111]), c_0_87]), c_0_53])])).
% 0.68/0.85  cnf(c_0_116, plain, (k10_relat_1(k7_relat_1(X1,X2),k9_relat_1(X1,X2))=k1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_104]), c_0_83])).
% 0.68/0.85  cnf(c_0_117, negated_conjecture, (k7_relat_1(k7_relat_1(esk2_0,esk1_0),esk1_0)=k7_relat_1(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_112]), c_0_96])])).
% 0.68/0.85  cnf(c_0_118, negated_conjecture, (k2_relat_1(k7_relat_1(esk2_0,esk1_0))=k9_relat_1(esk2_0,esk1_0)), inference(spm,[status(thm)],[c_0_113, c_0_112])).
% 0.68/0.85  cnf(c_0_119, negated_conjecture, (r1_tarski(k10_relat_1(k7_relat_1(esk2_0,esk1_0),X1),k10_relat_1(esk2_0,X1))), inference(spm,[status(thm)],[c_0_114, c_0_115])).
% 0.68/0.85  cnf(c_0_120, plain, (k10_relat_1(X1,k9_relat_1(X1,k1_relat_1(X1)))=k1_relat_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_116, c_0_64])).
% 0.68/0.85  cnf(c_0_121, negated_conjecture, (k9_relat_1(k7_relat_1(esk2_0,esk1_0),esk1_0)=k9_relat_1(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_117]), c_0_118]), c_0_96])])).
% 0.68/0.85  cnf(c_0_122, negated_conjecture, (~r1_tarski(esk1_0,k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.68/0.85  cnf(c_0_123, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_120]), c_0_112]), c_0_112]), c_0_121]), c_0_96])]), c_0_122]), ['proof']).
% 0.68/0.85  # SZS output end CNFRefutation
% 0.68/0.85  # Proof object total steps             : 124
% 0.68/0.85  # Proof object clause steps            : 85
% 0.68/0.85  # Proof object formula steps           : 39
% 0.68/0.85  # Proof object conjectures             : 37
% 0.68/0.85  # Proof object clause conjectures      : 34
% 0.68/0.85  # Proof object formula conjectures     : 3
% 0.68/0.85  # Proof object initial clauses used    : 22
% 0.68/0.85  # Proof object initial formulas used   : 19
% 0.68/0.85  # Proof object generating inferences   : 62
% 0.68/0.85  # Proof object simplifying inferences  : 71
% 0.68/0.85  # Training examples: 0 positive, 0 negative
% 0.68/0.85  # Parsed axioms                        : 19
% 0.68/0.85  # Removed by relevancy pruning/SinE    : 0
% 0.68/0.85  # Initial clauses                      : 23
% 0.68/0.85  # Removed in clause preprocessing      : 0
% 0.68/0.85  # Initial clauses in saturation        : 23
% 0.68/0.85  # Processed clauses                    : 4858
% 0.68/0.85  # ...of these trivial                  : 64
% 0.68/0.85  # ...subsumed                          : 3873
% 0.68/0.85  # ...remaining for further processing  : 921
% 0.68/0.85  # Other redundant clauses eliminated   : 2
% 0.68/0.85  # Clauses deleted for lack of memory   : 0
% 0.68/0.85  # Backward-subsumed                    : 106
% 0.68/0.85  # Backward-rewritten                   : 115
% 0.68/0.85  # Generated clauses                    : 36940
% 0.68/0.85  # ...of the previous two non-trivial   : 33555
% 0.68/0.85  # Contextual simplify-reflections      : 53
% 0.68/0.85  # Paramodulations                      : 36938
% 0.68/0.85  # Factorizations                       : 0
% 0.68/0.85  # Equation resolutions                 : 2
% 0.68/0.85  # Propositional unsat checks           : 0
% 0.68/0.85  #    Propositional check models        : 0
% 0.68/0.85  #    Propositional check unsatisfiable : 0
% 0.68/0.85  #    Propositional clauses             : 0
% 0.68/0.85  #    Propositional clauses after purity: 0
% 0.68/0.85  #    Propositional unsat core size     : 0
% 0.68/0.85  #    Propositional preprocessing time  : 0.000
% 0.68/0.85  #    Propositional encoding time       : 0.000
% 0.68/0.85  #    Propositional solver time         : 0.000
% 0.68/0.85  #    Success case prop preproc time    : 0.000
% 0.68/0.85  #    Success case prop encoding time   : 0.000
% 0.68/0.85  #    Success case prop solver time     : 0.000
% 0.68/0.85  # Current number of processed clauses  : 676
% 0.68/0.85  #    Positive orientable unit clauses  : 89
% 0.68/0.85  #    Positive unorientable unit clauses: 0
% 0.68/0.85  #    Negative unit clauses             : 16
% 0.68/0.85  #    Non-unit-clauses                  : 571
% 0.68/0.85  # Current number of unprocessed clauses: 28495
% 0.68/0.85  # ...number of literals in the above   : 100024
% 0.68/0.85  # Current number of archived formulas  : 0
% 0.68/0.85  # Current number of archived clauses   : 243
% 0.68/0.85  # Clause-clause subsumption calls (NU) : 73409
% 0.68/0.85  # Rec. Clause-clause subsumption calls : 49812
% 0.68/0.85  # Non-unit clause-clause subsumptions  : 2740
% 0.68/0.85  # Unit Clause-clause subsumption calls : 956
% 0.68/0.85  # Rewrite failures with RHS unbound    : 0
% 0.68/0.85  # BW rewrite match attempts            : 433
% 0.68/0.85  # BW rewrite match successes           : 43
% 0.68/0.85  # Condensation attempts                : 0
% 0.68/0.85  # Condensation successes               : 0
% 0.68/0.85  # Termbank termtop insertions          : 539646
% 0.68/0.85  
% 0.68/0.85  # -------------------------------------------------
% 0.68/0.85  # User time                : 0.479 s
% 0.68/0.85  # System time              : 0.024 s
% 0.68/0.85  # Total time               : 0.503 s
% 0.68/0.85  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------

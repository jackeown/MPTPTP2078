%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:55:10 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 583 expanded)
%              Number of clauses        :   73 ( 238 expanded)
%              Number of leaves         :   29 ( 163 expanded)
%              Depth                    :   18
%              Number of atoms          :  258 (1293 expanded)
%              Number of equality atoms :   91 ( 389 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t157_funct_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( ( r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X3,X2))
          & r1_tarski(X1,k1_relat_1(X3))
          & v2_funct_1(X3) )
       => r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_funct_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t182_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(t79_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k2_relat_1(X2),X1)
       => k5_relat_1(X2,k6_relat_1(X1)) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(t87_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t178_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => r1_tarski(k10_relat_1(X3,X1),k10_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).

fof(t94_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k5_relat_1(k6_relat_1(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t146_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(t162_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( r1_tarski(X2,X3)
         => k9_relat_1(k7_relat_1(X1,X3),X2) = k9_relat_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(t139_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k10_relat_1(k7_relat_1(X3,X1),X2) = k3_xboole_0(X1,k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(t169_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(t152_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( v2_funct_1(X2)
       => r1_tarski(k10_relat_1(X2,k9_relat_1(X2,X1)),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).

fof(c_0_29,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => ( ( r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X3,X2))
            & r1_tarski(X1,k1_relat_1(X3))
            & v2_funct_1(X3) )
         => r1_tarski(X1,X2) ) ) ),
    inference(assume_negation,[status(cth)],[t157_funct_1])).

fof(c_0_30,plain,(
    ! [X15,X16,X17] :
      ( ~ r1_tarski(X15,X16)
      | ~ r1_tarski(X16,X17)
      | r1_tarski(X15,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_31,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_funct_1(esk3_0)
    & r1_tarski(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk2_0))
    & r1_tarski(esk1_0,k1_relat_1(esk3_0))
    & v2_funct_1(esk3_0)
    & ~ r1_tarski(esk1_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_29])])])).

fof(c_0_32,plain,(
    ! [X61,X62] :
      ( ~ v1_relat_1(X61)
      | ~ v1_relat_1(X62)
      | k1_relat_1(k5_relat_1(X61,X62)) = k10_relat_1(X61,k1_relat_1(X62)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).

fof(c_0_33,plain,(
    ! [X64,X65] :
      ( ~ v1_relat_1(X65)
      | ~ r1_tarski(k2_relat_1(X65),X64)
      | k5_relat_1(X65,k6_relat_1(X64)) = X65 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_relat_1])])).

fof(c_0_34,plain,(
    ! [X63] :
      ( k1_relat_1(k6_relat_1(X63)) = X63
      & k2_relat_1(k6_relat_1(X63)) = X63 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_35,plain,(
    ! [X70] :
      ( v1_relat_1(k6_relat_1(X70))
      & v1_funct_1(k6_relat_1(X70)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(esk1_0,k1_relat_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,plain,
    ( k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,plain,
    ( k5_relat_1(X1,k6_relat_1(X2)) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_40,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_41,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(X1,k1_relat_1(esk3_0))
    | ~ r1_tarski(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

fof(c_0_43,plain,(
    ! [X66,X67] :
      ( ~ v1_relat_1(X67)
      | r1_tarski(k1_relat_1(k7_relat_1(X67,X66)),X66) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).

fof(c_0_44,plain,(
    ! [X9,X10] :
      ( ( r1_tarski(X9,X10)
        | X9 != X10 )
      & ( r1_tarski(X10,X9)
        | X9 != X10 )
      & ( ~ r1_tarski(X9,X10)
        | ~ r1_tarski(X10,X9)
        | X9 = X10 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_45,plain,(
    ! [X58,X59,X60] :
      ( ~ v1_relat_1(X60)
      | ~ r1_tarski(X58,X59)
      | r1_tarski(k10_relat_1(X60,X58),k10_relat_1(X60,X59)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t178_relat_1])])).

cnf(c_0_46,plain,
    ( k10_relat_1(X1,X2) = k1_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40]),c_0_41])])).

cnf(c_0_47,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(X1,k1_relat_1(esk3_0))
    | ~ r1_tarski(X2,esk1_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_36,c_0_42])).

cnf(c_0_49,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_50,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_51,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_52,plain,
    ( k10_relat_1(k6_relat_1(X1),X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_40]),c_0_41])])).

fof(c_0_53,plain,(
    ! [X68,X69] :
      ( ~ v1_relat_1(X69)
      | k7_relat_1(X69,X68) = k5_relat_1(k6_relat_1(X68),X69) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(X1,k1_relat_1(esk3_0))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k1_relat_1(k7_relat_1(X2,esk1_0))) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_55,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_50])).

cnf(c_0_56,plain,
    ( r1_tarski(X1,k10_relat_1(k6_relat_1(X1),X2))
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_41])])).

cnf(c_0_57,plain,
    ( k7_relat_1(X1,X2) = k5_relat_1(k6_relat_1(X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,esk1_0)),k1_relat_1(esk3_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(X1,k10_relat_1(k6_relat_1(X1),k1_relat_1(esk3_0)))
    | ~ r1_tarski(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_37])).

cnf(c_0_60,plain,
    ( k10_relat_1(k6_relat_1(X1),k1_relat_1(X2)) = k1_relat_1(k7_relat_1(X2,X1))
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_57]),c_0_41])])).

cnf(c_0_61,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_62,plain,(
    ! [X49,X50] : k1_setfam_1(k2_tarski(X49,X50)) = k3_xboole_0(X49,X50) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_63,plain,(
    ! [X22,X23] : k1_enumset1(X22,X22,X23) = k2_tarski(X22,X23) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(X1,k10_relat_1(k6_relat_1(X1),k1_relat_1(esk3_0)))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k1_relat_1(k7_relat_1(X2,esk1_0))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_58])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(X1,k1_relat_1(k7_relat_1(esk3_0,X1)))
    | ~ r1_tarski(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61])])).

cnf(c_0_66,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = k10_relat_1(k6_relat_1(X2),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_40]),c_0_41])])).

fof(c_0_67,plain,(
    ! [X13,X14] : k4_xboole_0(X13,X14) = k5_xboole_0(X13,k3_xboole_0(X13,X14)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_68,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_69,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

fof(c_0_70,plain,(
    ! [X53] :
      ( ~ v1_relat_1(X53)
      | k9_relat_1(X53,k1_relat_1(X53)) = k2_relat_1(X53) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).

fof(c_0_71,plain,(
    ! [X54,X55,X56] :
      ( ~ v1_relat_1(X54)
      | ~ r1_tarski(X55,X56)
      | k9_relat_1(k7_relat_1(X54,X56),X55) = k9_relat_1(X54,X55) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t162_relat_1])])])).

fof(c_0_72,plain,(
    ! [X51,X52] :
      ( ~ v1_relat_1(X51)
      | v1_relat_1(k7_relat_1(X51,X52)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

cnf(c_0_73,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_74,negated_conjecture,
    ( r1_tarski(esk1_0,k10_relat_1(k6_relat_1(esk1_0),k1_relat_1(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_61]),c_0_55])])).

cnf(c_0_75,plain,
    ( r1_tarski(k10_relat_1(k6_relat_1(X1),X2),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_66]),c_0_41])])).

fof(c_0_76,plain,(
    ! [X11,X12] :
      ( ( k4_xboole_0(X11,X12) != k1_xboole_0
        | r1_tarski(X11,X12) )
      & ( ~ r1_tarski(X11,X12)
        | k4_xboole_0(X11,X12) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_77,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_78,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_68,c_0_69])).

fof(c_0_79,plain,(
    ! [X24,X25,X26] : k2_enumset1(X24,X24,X25,X26) = k1_enumset1(X24,X25,X26) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_80,plain,(
    ! [X27,X28,X29,X30] : k3_enumset1(X27,X27,X28,X29,X30) = k2_enumset1(X27,X28,X29,X30) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_81,plain,(
    ! [X31,X32,X33,X34,X35] : k4_enumset1(X31,X31,X32,X33,X34,X35) = k3_enumset1(X31,X32,X33,X34,X35) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_82,plain,(
    ! [X36,X37,X38,X39,X40,X41] : k5_enumset1(X36,X36,X37,X38,X39,X40,X41) = k4_enumset1(X36,X37,X38,X39,X40,X41) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_83,plain,(
    ! [X42,X43,X44,X45,X46,X47,X48] : k6_enumset1(X42,X42,X43,X44,X45,X46,X47,X48) = k5_enumset1(X42,X43,X44,X45,X46,X47,X48) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_84,plain,(
    ! [X71,X72,X73] :
      ( ~ v1_relat_1(X73)
      | k10_relat_1(k7_relat_1(X73,X71),X72) = k3_xboole_0(X71,k10_relat_1(X73,X72)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).

cnf(c_0_85,plain,
    ( k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_86,plain,
    ( k9_relat_1(k7_relat_1(X1,X3),X2) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_87,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_88,negated_conjecture,
    ( k10_relat_1(k6_relat_1(esk1_0),k1_relat_1(esk3_0)) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_75])])).

fof(c_0_89,plain,(
    ! [X19,X20] : k4_xboole_0(X19,k4_xboole_0(X19,X20)) = k3_xboole_0(X19,X20) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_90,plain,(
    ! [X18] : k3_xboole_0(X18,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_91,plain,(
    ! [X8] : k3_xboole_0(X8,X8) = X8 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_92,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_93,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_94,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_95,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_96,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_97,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_98,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_99,plain,
    ( k10_relat_1(k7_relat_1(X1,X2),X3) = k3_xboole_0(X2,k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

fof(c_0_100,plain,(
    ! [X57] :
      ( ~ v1_relat_1(X57)
      | k10_relat_1(X57,k2_relat_1(X57)) = k1_relat_1(X57) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).

cnf(c_0_101,plain,
    ( k9_relat_1(X1,k1_relat_1(k7_relat_1(X1,X2))) = k2_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_49]),c_0_87])).

cnf(c_0_102,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk3_0,esk1_0)) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_88]),c_0_61])])).

cnf(c_0_103,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_89])).

cnf(c_0_104,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

fof(c_0_105,plain,(
    ! [X21] : k5_xboole_0(X21,k1_xboole_0) = X21 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

cnf(c_0_106,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_91])).

cnf(c_0_107,plain,
    ( r1_tarski(X1,X2)
    | k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_92,c_0_93]),c_0_94]),c_0_95]),c_0_96]),c_0_97]),c_0_98])).

cnf(c_0_108,plain,
    ( k10_relat_1(k7_relat_1(X1,X2),X3) = k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k10_relat_1(X1,X3)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_99,c_0_78]),c_0_94]),c_0_95]),c_0_96]),c_0_97]),c_0_98])).

cnf(c_0_109,plain,
    ( k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_100])).

cnf(c_0_110,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk3_0,esk1_0)) = k9_relat_1(esk3_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_102]),c_0_61])])).

cnf(c_0_111,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))))) = k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_103,c_0_78]),c_0_93]),c_0_93]),c_0_94]),c_0_94]),c_0_94]),c_0_95]),c_0_95]),c_0_95]),c_0_96]),c_0_96]),c_0_96]),c_0_97]),c_0_97]),c_0_97]),c_0_98]),c_0_98]),c_0_98])).

cnf(c_0_112,plain,
    ( k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_104,c_0_78]),c_0_94]),c_0_95]),c_0_96]),c_0_97]),c_0_98])).

cnf(c_0_113,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_105])).

cnf(c_0_114,plain,
    ( k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_106,c_0_78]),c_0_94]),c_0_95]),c_0_96]),c_0_97]),c_0_98])).

cnf(c_0_115,plain,
    ( r1_tarski(X1,k10_relat_1(X2,X3))
    | k5_xboole_0(X1,k10_relat_1(k7_relat_1(X2,X1),X3)) != k1_xboole_0
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_107,c_0_108])).

cnf(c_0_116,negated_conjecture,
    ( k10_relat_1(k7_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk1_0)) = esk1_0
    | ~ v1_relat_1(k7_relat_1(esk3_0,esk1_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_110]),c_0_102])).

cnf(c_0_117,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_112]),c_0_113]),c_0_114])).

cnf(c_0_118,plain,
    ( r1_tarski(X1,k10_relat_1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k10_relat_1(X2,X4))
    | ~ r1_tarski(X4,X3) ),
    inference(spm,[status(thm)],[c_0_36,c_0_51])).

cnf(c_0_119,negated_conjecture,
    ( r1_tarski(esk1_0,k10_relat_1(esk3_0,k9_relat_1(esk3_0,esk1_0)))
    | ~ v1_relat_1(k7_relat_1(esk3_0,esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_116]),c_0_117]),c_0_61])])).

fof(c_0_120,plain,(
    ! [X74,X75] :
      ( ~ v1_relat_1(X75)
      | ~ v1_funct_1(X75)
      | ~ v2_funct_1(X75)
      | r1_tarski(k10_relat_1(X75,k9_relat_1(X75,X74)),X74) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t152_funct_1])])).

cnf(c_0_121,negated_conjecture,
    ( r1_tarski(esk1_0,k10_relat_1(esk3_0,X1))
    | ~ v1_relat_1(k7_relat_1(esk3_0,esk1_0))
    | ~ r1_tarski(k9_relat_1(esk3_0,esk1_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_119]),c_0_61])])).

cnf(c_0_122,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_123,plain,
    ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_120])).

cnf(c_0_124,negated_conjecture,
    ( r1_tarski(esk1_0,k10_relat_1(esk3_0,X1))
    | ~ r1_tarski(k9_relat_1(esk3_0,esk1_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_87]),c_0_61])])).

cnf(c_0_125,negated_conjecture,
    ( r1_tarski(X1,k9_relat_1(esk3_0,esk2_0))
    | ~ r1_tarski(X1,k9_relat_1(esk3_0,esk1_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_122])).

cnf(c_0_126,plain,
    ( r1_tarski(X1,X2)
    | ~ v2_funct_1(X3)
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(X1,k10_relat_1(X3,k9_relat_1(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_123])).

cnf(c_0_127,negated_conjecture,
    ( r1_tarski(esk1_0,k10_relat_1(esk3_0,k9_relat_1(esk3_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_125]),c_0_55])])).

cnf(c_0_128,negated_conjecture,
    ( v2_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_129,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_130,negated_conjecture,
    ( ~ r1_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_131,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_127]),c_0_128]),c_0_129]),c_0_61])]),c_0_130]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:54:24 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.35  # Version: 2.5pre002
% 0.20/0.35  # No SInE strategy applied
% 0.20/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.45  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.45  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.45  #
% 0.20/0.45  # Preprocessing time       : 0.028 s
% 0.20/0.45  # Presaturation interreduction done
% 0.20/0.45  
% 0.20/0.45  # Proof found!
% 0.20/0.45  # SZS status Theorem
% 0.20/0.45  # SZS output start CNFRefutation
% 0.20/0.45  fof(t157_funct_1, conjecture, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(((r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X3,X2))&r1_tarski(X1,k1_relat_1(X3)))&v2_funct_1(X3))=>r1_tarski(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t157_funct_1)).
% 0.20/0.45  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.20/0.45  fof(t182_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 0.20/0.45  fof(t79_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k2_relat_1(X2),X1)=>k5_relat_1(X2,k6_relat_1(X1))=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 0.20/0.45  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 0.20/0.45  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 0.20/0.45  fof(t87_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 0.20/0.45  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.45  fof(t178_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>r1_tarski(k10_relat_1(X3,X1),k10_relat_1(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t178_relat_1)).
% 0.20/0.45  fof(t94_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k5_relat_1(k6_relat_1(X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 0.20/0.45  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.20/0.45  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.45  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.20/0.45  fof(t146_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 0.20/0.45  fof(t162_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(r1_tarski(X2,X3)=>k9_relat_1(k7_relat_1(X1,X3),X2)=k9_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_relat_1)).
% 0.20/0.45  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.20/0.45  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.20/0.45  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.45  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.20/0.45  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.20/0.45  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.20/0.45  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.20/0.45  fof(t139_funct_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k10_relat_1(k7_relat_1(X3,X1),X2)=k3_xboole_0(X1,k10_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 0.20/0.45  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.20/0.45  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 0.20/0.45  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.20/0.45  fof(t169_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 0.20/0.45  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 0.20/0.45  fof(t152_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(v2_funct_1(X2)=>r1_tarski(k10_relat_1(X2,k9_relat_1(X2,X1)),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_funct_1)).
% 0.20/0.45  fof(c_0_29, negated_conjecture, ~(![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(((r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X3,X2))&r1_tarski(X1,k1_relat_1(X3)))&v2_funct_1(X3))=>r1_tarski(X1,X2)))), inference(assume_negation,[status(cth)],[t157_funct_1])).
% 0.20/0.45  fof(c_0_30, plain, ![X15, X16, X17]:(~r1_tarski(X15,X16)|~r1_tarski(X16,X17)|r1_tarski(X15,X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.20/0.45  fof(c_0_31, negated_conjecture, ((v1_relat_1(esk3_0)&v1_funct_1(esk3_0))&(((r1_tarski(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk2_0))&r1_tarski(esk1_0,k1_relat_1(esk3_0)))&v2_funct_1(esk3_0))&~r1_tarski(esk1_0,esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_29])])])).
% 0.20/0.45  fof(c_0_32, plain, ![X61, X62]:(~v1_relat_1(X61)|(~v1_relat_1(X62)|k1_relat_1(k5_relat_1(X61,X62))=k10_relat_1(X61,k1_relat_1(X62)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).
% 0.20/0.45  fof(c_0_33, plain, ![X64, X65]:(~v1_relat_1(X65)|(~r1_tarski(k2_relat_1(X65),X64)|k5_relat_1(X65,k6_relat_1(X64))=X65)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_relat_1])])).
% 0.20/0.45  fof(c_0_34, plain, ![X63]:(k1_relat_1(k6_relat_1(X63))=X63&k2_relat_1(k6_relat_1(X63))=X63), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.20/0.45  fof(c_0_35, plain, ![X70]:(v1_relat_1(k6_relat_1(X70))&v1_funct_1(k6_relat_1(X70))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 0.20/0.45  cnf(c_0_36, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.45  cnf(c_0_37, negated_conjecture, (r1_tarski(esk1_0,k1_relat_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.45  cnf(c_0_38, plain, (k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.45  cnf(c_0_39, plain, (k5_relat_1(X1,k6_relat_1(X2))=X1|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.45  cnf(c_0_40, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.45  cnf(c_0_41, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.45  cnf(c_0_42, negated_conjecture, (r1_tarski(X1,k1_relat_1(esk3_0))|~r1_tarski(X1,esk1_0)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.20/0.45  fof(c_0_43, plain, ![X66, X67]:(~v1_relat_1(X67)|r1_tarski(k1_relat_1(k7_relat_1(X67,X66)),X66)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).
% 0.20/0.45  fof(c_0_44, plain, ![X9, X10]:(((r1_tarski(X9,X10)|X9!=X10)&(r1_tarski(X10,X9)|X9!=X10))&(~r1_tarski(X9,X10)|~r1_tarski(X10,X9)|X9=X10)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.45  fof(c_0_45, plain, ![X58, X59, X60]:(~v1_relat_1(X60)|(~r1_tarski(X58,X59)|r1_tarski(k10_relat_1(X60,X58),k10_relat_1(X60,X59)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t178_relat_1])])).
% 0.20/0.45  cnf(c_0_46, plain, (k10_relat_1(X1,X2)=k1_relat_1(X1)|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40]), c_0_41])])).
% 0.20/0.45  cnf(c_0_47, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.45  cnf(c_0_48, negated_conjecture, (r1_tarski(X1,k1_relat_1(esk3_0))|~r1_tarski(X2,esk1_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_36, c_0_42])).
% 0.20/0.45  cnf(c_0_49, plain, (r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.45  cnf(c_0_50, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.45  cnf(c_0_51, plain, (r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.20/0.45  cnf(c_0_52, plain, (k10_relat_1(k6_relat_1(X1),X2)=X1|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_40]), c_0_41])])).
% 0.20/0.45  fof(c_0_53, plain, ![X68, X69]:(~v1_relat_1(X69)|k7_relat_1(X69,X68)=k5_relat_1(k6_relat_1(X68),X69)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).
% 0.20/0.45  cnf(c_0_54, negated_conjecture, (r1_tarski(X1,k1_relat_1(esk3_0))|~v1_relat_1(X2)|~r1_tarski(X1,k1_relat_1(k7_relat_1(X2,esk1_0)))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.20/0.45  cnf(c_0_55, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_50])).
% 0.20/0.45  cnf(c_0_56, plain, (r1_tarski(X1,k10_relat_1(k6_relat_1(X1),X2))|~r1_tarski(X3,X2)|~r1_tarski(X1,X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_41])])).
% 0.20/0.45  cnf(c_0_57, plain, (k7_relat_1(X1,X2)=k5_relat_1(k6_relat_1(X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.20/0.45  cnf(c_0_58, negated_conjecture, (r1_tarski(k1_relat_1(k7_relat_1(X1,esk1_0)),k1_relat_1(esk3_0))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.20/0.45  cnf(c_0_59, negated_conjecture, (r1_tarski(X1,k10_relat_1(k6_relat_1(X1),k1_relat_1(esk3_0)))|~r1_tarski(X1,esk1_0)), inference(spm,[status(thm)],[c_0_56, c_0_37])).
% 0.20/0.45  cnf(c_0_60, plain, (k10_relat_1(k6_relat_1(X1),k1_relat_1(X2))=k1_relat_1(k7_relat_1(X2,X1))|~v1_relat_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_57]), c_0_41])])).
% 0.20/0.45  cnf(c_0_61, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.45  fof(c_0_62, plain, ![X49, X50]:k1_setfam_1(k2_tarski(X49,X50))=k3_xboole_0(X49,X50), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.20/0.45  fof(c_0_63, plain, ![X22, X23]:k1_enumset1(X22,X22,X23)=k2_tarski(X22,X23), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.45  cnf(c_0_64, negated_conjecture, (r1_tarski(X1,k10_relat_1(k6_relat_1(X1),k1_relat_1(esk3_0)))|~v1_relat_1(X2)|~r1_tarski(X1,k1_relat_1(k7_relat_1(X2,esk1_0)))), inference(spm,[status(thm)],[c_0_56, c_0_58])).
% 0.20/0.45  cnf(c_0_65, negated_conjecture, (r1_tarski(X1,k1_relat_1(k7_relat_1(esk3_0,X1)))|~r1_tarski(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61])])).
% 0.20/0.45  cnf(c_0_66, plain, (k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))=k10_relat_1(k6_relat_1(X2),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_40]), c_0_41])])).
% 0.20/0.45  fof(c_0_67, plain, ![X13, X14]:k4_xboole_0(X13,X14)=k5_xboole_0(X13,k3_xboole_0(X13,X14)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.20/0.45  cnf(c_0_68, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.20/0.45  cnf(c_0_69, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.20/0.45  fof(c_0_70, plain, ![X53]:(~v1_relat_1(X53)|k9_relat_1(X53,k1_relat_1(X53))=k2_relat_1(X53)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).
% 0.20/0.45  fof(c_0_71, plain, ![X54, X55, X56]:(~v1_relat_1(X54)|(~r1_tarski(X55,X56)|k9_relat_1(k7_relat_1(X54,X56),X55)=k9_relat_1(X54,X55))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t162_relat_1])])])).
% 0.20/0.45  fof(c_0_72, plain, ![X51, X52]:(~v1_relat_1(X51)|v1_relat_1(k7_relat_1(X51,X52))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.20/0.45  cnf(c_0_73, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.45  cnf(c_0_74, negated_conjecture, (r1_tarski(esk1_0,k10_relat_1(k6_relat_1(esk1_0),k1_relat_1(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_61]), c_0_55])])).
% 0.20/0.45  cnf(c_0_75, plain, (r1_tarski(k10_relat_1(k6_relat_1(X1),X2),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_66]), c_0_41])])).
% 0.20/0.45  fof(c_0_76, plain, ![X11, X12]:((k4_xboole_0(X11,X12)!=k1_xboole_0|r1_tarski(X11,X12))&(~r1_tarski(X11,X12)|k4_xboole_0(X11,X12)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.20/0.45  cnf(c_0_77, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.20/0.45  cnf(c_0_78, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_68, c_0_69])).
% 0.20/0.45  fof(c_0_79, plain, ![X24, X25, X26]:k2_enumset1(X24,X24,X25,X26)=k1_enumset1(X24,X25,X26), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.45  fof(c_0_80, plain, ![X27, X28, X29, X30]:k3_enumset1(X27,X27,X28,X29,X30)=k2_enumset1(X27,X28,X29,X30), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.20/0.45  fof(c_0_81, plain, ![X31, X32, X33, X34, X35]:k4_enumset1(X31,X31,X32,X33,X34,X35)=k3_enumset1(X31,X32,X33,X34,X35), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.20/0.45  fof(c_0_82, plain, ![X36, X37, X38, X39, X40, X41]:k5_enumset1(X36,X36,X37,X38,X39,X40,X41)=k4_enumset1(X36,X37,X38,X39,X40,X41), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.20/0.45  fof(c_0_83, plain, ![X42, X43, X44, X45, X46, X47, X48]:k6_enumset1(X42,X42,X43,X44,X45,X46,X47,X48)=k5_enumset1(X42,X43,X44,X45,X46,X47,X48), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.20/0.45  fof(c_0_84, plain, ![X71, X72, X73]:(~v1_relat_1(X73)|k10_relat_1(k7_relat_1(X73,X71),X72)=k3_xboole_0(X71,k10_relat_1(X73,X72))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).
% 0.20/0.45  cnf(c_0_85, plain, (k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.20/0.45  cnf(c_0_86, plain, (k9_relat_1(k7_relat_1(X1,X3),X2)=k9_relat_1(X1,X2)|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.20/0.45  cnf(c_0_87, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.20/0.45  cnf(c_0_88, negated_conjecture, (k10_relat_1(k6_relat_1(esk1_0),k1_relat_1(esk3_0))=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_75])])).
% 0.20/0.45  fof(c_0_89, plain, ![X19, X20]:k4_xboole_0(X19,k4_xboole_0(X19,X20))=k3_xboole_0(X19,X20), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.20/0.45  fof(c_0_90, plain, ![X18]:k3_xboole_0(X18,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.20/0.45  fof(c_0_91, plain, ![X8]:k3_xboole_0(X8,X8)=X8, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.20/0.45  cnf(c_0_92, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.20/0.45  cnf(c_0_93, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_77, c_0_78])).
% 0.20/0.45  cnf(c_0_94, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.20/0.45  cnf(c_0_95, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.20/0.45  cnf(c_0_96, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.20/0.45  cnf(c_0_97, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_82])).
% 0.20/0.45  cnf(c_0_98, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_83])).
% 0.20/0.45  cnf(c_0_99, plain, (k10_relat_1(k7_relat_1(X1,X2),X3)=k3_xboole_0(X2,k10_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_84])).
% 0.20/0.45  fof(c_0_100, plain, ![X57]:(~v1_relat_1(X57)|k10_relat_1(X57,k2_relat_1(X57))=k1_relat_1(X57)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).
% 0.20/0.45  cnf(c_0_101, plain, (k9_relat_1(X1,k1_relat_1(k7_relat_1(X1,X2)))=k2_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_49]), c_0_87])).
% 0.20/0.45  cnf(c_0_102, negated_conjecture, (k1_relat_1(k7_relat_1(esk3_0,esk1_0))=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_88]), c_0_61])])).
% 0.20/0.45  cnf(c_0_103, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_89])).
% 0.20/0.45  cnf(c_0_104, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_90])).
% 0.20/0.45  fof(c_0_105, plain, ![X21]:k5_xboole_0(X21,k1_xboole_0)=X21, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.20/0.45  cnf(c_0_106, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_91])).
% 0.20/0.45  cnf(c_0_107, plain, (r1_tarski(X1,X2)|k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_92, c_0_93]), c_0_94]), c_0_95]), c_0_96]), c_0_97]), c_0_98])).
% 0.20/0.45  cnf(c_0_108, plain, (k10_relat_1(k7_relat_1(X1,X2),X3)=k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k10_relat_1(X1,X3)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_99, c_0_78]), c_0_94]), c_0_95]), c_0_96]), c_0_97]), c_0_98])).
% 0.20/0.45  cnf(c_0_109, plain, (k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_100])).
% 0.20/0.45  cnf(c_0_110, negated_conjecture, (k2_relat_1(k7_relat_1(esk3_0,esk1_0))=k9_relat_1(esk3_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_102]), c_0_61])])).
% 0.20/0.45  cnf(c_0_111, plain, (k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))))=k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_103, c_0_78]), c_0_93]), c_0_93]), c_0_94]), c_0_94]), c_0_94]), c_0_95]), c_0_95]), c_0_95]), c_0_96]), c_0_96]), c_0_96]), c_0_97]), c_0_97]), c_0_97]), c_0_98]), c_0_98]), c_0_98])).
% 0.20/0.45  cnf(c_0_112, plain, (k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_104, c_0_78]), c_0_94]), c_0_95]), c_0_96]), c_0_97]), c_0_98])).
% 0.20/0.45  cnf(c_0_113, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_105])).
% 0.20/0.45  cnf(c_0_114, plain, (k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_106, c_0_78]), c_0_94]), c_0_95]), c_0_96]), c_0_97]), c_0_98])).
% 0.20/0.45  cnf(c_0_115, plain, (r1_tarski(X1,k10_relat_1(X2,X3))|k5_xboole_0(X1,k10_relat_1(k7_relat_1(X2,X1),X3))!=k1_xboole_0|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_107, c_0_108])).
% 0.20/0.45  cnf(c_0_116, negated_conjecture, (k10_relat_1(k7_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk1_0))=esk1_0|~v1_relat_1(k7_relat_1(esk3_0,esk1_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_110]), c_0_102])).
% 0.20/0.45  cnf(c_0_117, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_112]), c_0_113]), c_0_114])).
% 0.20/0.45  cnf(c_0_118, plain, (r1_tarski(X1,k10_relat_1(X2,X3))|~v1_relat_1(X2)|~r1_tarski(X1,k10_relat_1(X2,X4))|~r1_tarski(X4,X3)), inference(spm,[status(thm)],[c_0_36, c_0_51])).
% 0.20/0.45  cnf(c_0_119, negated_conjecture, (r1_tarski(esk1_0,k10_relat_1(esk3_0,k9_relat_1(esk3_0,esk1_0)))|~v1_relat_1(k7_relat_1(esk3_0,esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_116]), c_0_117]), c_0_61])])).
% 0.20/0.45  fof(c_0_120, plain, ![X74, X75]:(~v1_relat_1(X75)|~v1_funct_1(X75)|(~v2_funct_1(X75)|r1_tarski(k10_relat_1(X75,k9_relat_1(X75,X74)),X74))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t152_funct_1])])).
% 0.20/0.45  cnf(c_0_121, negated_conjecture, (r1_tarski(esk1_0,k10_relat_1(esk3_0,X1))|~v1_relat_1(k7_relat_1(esk3_0,esk1_0))|~r1_tarski(k9_relat_1(esk3_0,esk1_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118, c_0_119]), c_0_61])])).
% 0.20/0.45  cnf(c_0_122, negated_conjecture, (r1_tarski(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.45  cnf(c_0_123, plain, (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X2)),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_120])).
% 0.20/0.45  cnf(c_0_124, negated_conjecture, (r1_tarski(esk1_0,k10_relat_1(esk3_0,X1))|~r1_tarski(k9_relat_1(esk3_0,esk1_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121, c_0_87]), c_0_61])])).
% 0.20/0.45  cnf(c_0_125, negated_conjecture, (r1_tarski(X1,k9_relat_1(esk3_0,esk2_0))|~r1_tarski(X1,k9_relat_1(esk3_0,esk1_0))), inference(spm,[status(thm)],[c_0_36, c_0_122])).
% 0.20/0.45  cnf(c_0_126, plain, (r1_tarski(X1,X2)|~v2_funct_1(X3)|~v1_funct_1(X3)|~v1_relat_1(X3)|~r1_tarski(X1,k10_relat_1(X3,k9_relat_1(X3,X2)))), inference(spm,[status(thm)],[c_0_36, c_0_123])).
% 0.20/0.45  cnf(c_0_127, negated_conjecture, (r1_tarski(esk1_0,k10_relat_1(esk3_0,k9_relat_1(esk3_0,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124, c_0_125]), c_0_55])])).
% 0.20/0.45  cnf(c_0_128, negated_conjecture, (v2_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.45  cnf(c_0_129, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.45  cnf(c_0_130, negated_conjecture, (~r1_tarski(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.45  cnf(c_0_131, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126, c_0_127]), c_0_128]), c_0_129]), c_0_61])]), c_0_130]), ['proof']).
% 0.20/0.45  # SZS output end CNFRefutation
% 0.20/0.45  # Proof object total steps             : 132
% 0.20/0.45  # Proof object clause steps            : 73
% 0.20/0.45  # Proof object formula steps           : 59
% 0.20/0.45  # Proof object conjectures             : 27
% 0.20/0.45  # Proof object clause conjectures      : 24
% 0.20/0.45  # Proof object formula conjectures     : 3
% 0.20/0.45  # Proof object initial clauses used    : 36
% 0.20/0.45  # Proof object initial formulas used   : 29
% 0.20/0.45  # Proof object generating inferences   : 29
% 0.20/0.45  # Proof object simplifying inferences  : 89
% 0.20/0.45  # Training examples: 0 positive, 0 negative
% 0.20/0.45  # Parsed axioms                        : 29
% 0.20/0.45  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.45  # Initial clauses                      : 39
% 0.20/0.45  # Removed in clause preprocessing      : 8
% 0.20/0.45  # Initial clauses in saturation        : 31
% 0.20/0.45  # Processed clauses                    : 687
% 0.20/0.45  # ...of these trivial                  : 9
% 0.20/0.45  # ...subsumed                          : 346
% 0.20/0.45  # ...remaining for further processing  : 332
% 0.20/0.45  # Other redundant clauses eliminated   : 9
% 0.20/0.45  # Clauses deleted for lack of memory   : 0
% 0.20/0.45  # Backward-subsumed                    : 37
% 0.20/0.45  # Backward-rewritten                   : 21
% 0.20/0.45  # Generated clauses                    : 2930
% 0.20/0.45  # ...of the previous two non-trivial   : 2397
% 0.20/0.45  # Contextual simplify-reflections      : 8
% 0.20/0.45  # Paramodulations                      : 2921
% 0.20/0.45  # Factorizations                       : 0
% 0.20/0.45  # Equation resolutions                 : 9
% 0.20/0.45  # Propositional unsat checks           : 0
% 0.20/0.45  #    Propositional check models        : 0
% 0.20/0.45  #    Propositional check unsatisfiable : 0
% 0.20/0.45  #    Propositional clauses             : 0
% 0.20/0.45  #    Propositional clauses after purity: 0
% 0.20/0.45  #    Propositional unsat core size     : 0
% 0.20/0.45  #    Propositional preprocessing time  : 0.000
% 0.20/0.45  #    Propositional encoding time       : 0.000
% 0.20/0.45  #    Propositional solver time         : 0.000
% 0.20/0.45  #    Success case prop preproc time    : 0.000
% 0.20/0.45  #    Success case prop encoding time   : 0.000
% 0.20/0.45  #    Success case prop solver time     : 0.000
% 0.20/0.45  # Current number of processed clauses  : 242
% 0.20/0.45  #    Positive orientable unit clauses  : 40
% 0.20/0.45  #    Positive unorientable unit clauses: 1
% 0.20/0.45  #    Negative unit clauses             : 1
% 0.20/0.45  #    Non-unit-clauses                  : 200
% 0.20/0.45  # Current number of unprocessed clauses: 1698
% 0.20/0.45  # ...number of literals in the above   : 6691
% 0.20/0.45  # Current number of archived formulas  : 0
% 0.20/0.45  # Current number of archived clauses   : 96
% 0.20/0.45  # Clause-clause subsumption calls (NU) : 7217
% 0.20/0.45  # Rec. Clause-clause subsumption calls : 4933
% 0.20/0.45  # Non-unit clause-clause subsumptions  : 388
% 0.20/0.45  # Unit Clause-clause subsumption calls : 21
% 0.20/0.45  # Rewrite failures with RHS unbound    : 0
% 0.20/0.45  # BW rewrite match attempts            : 49
% 0.20/0.45  # BW rewrite match successes           : 23
% 0.20/0.45  # Condensation attempts                : 0
% 0.20/0.45  # Condensation successes               : 0
% 0.20/0.45  # Termbank termtop insertions          : 51199
% 0.20/0.45  
% 0.20/0.45  # -------------------------------------------------
% 0.20/0.45  # User time                : 0.096 s
% 0.20/0.45  # System time              : 0.009 s
% 0.20/0.45  # Total time               : 0.105 s
% 0.20/0.45  # Maximum resident set size: 1604 pages
%------------------------------------------------------------------------------

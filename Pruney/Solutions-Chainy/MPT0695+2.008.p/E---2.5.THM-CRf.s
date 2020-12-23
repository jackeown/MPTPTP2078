%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:55:01 EST 2020

% Result     : Theorem 0.56s
% Output     : CNFRefutation 0.56s
% Verified   : 
% Statistics : Number of formulae       :   99 (2130 expanded)
%              Number of clauses        :   78 ( 914 expanded)
%              Number of leaves         :   10 ( 532 expanded)
%              Depth                    :   16
%              Number of atoms          :  208 (4867 expanded)
%              Number of equality atoms :   85 (1765 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t145_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k9_relat_1(X2,X1) = k9_relat_1(X2,k3_xboole_0(k1_relat_1(X2),X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_relat_1)).

fof(t90_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k1_relat_1(k7_relat_1(X2,X1)) = k3_xboole_0(k1_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(t101_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X1),X1) = k7_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_relat_1)).

fof(t100_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k7_relat_1(k7_relat_1(X3,X1),X2) = k7_relat_1(X3,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(t150_funct_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => k9_relat_1(X3,k3_xboole_0(X1,k10_relat_1(X3,X2))) = k3_xboole_0(k9_relat_1(X3,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_funct_1)).

fof(fc8_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k7_relat_1(X1,X2))
        & v1_funct_1(k7_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).

fof(t139_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k10_relat_1(k7_relat_1(X3,X1),X2) = k3_xboole_0(X1,k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

fof(t148_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => k9_relat_1(X2,k10_relat_1(X2,X1)) = k3_xboole_0(X1,k9_relat_1(X2,k1_relat_1(X2))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).

fof(c_0_10,plain,(
    ! [X11,X12] :
      ( ~ v1_relat_1(X12)
      | k9_relat_1(X12,X11) = k9_relat_1(X12,k3_xboole_0(k1_relat_1(X12),X11)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_relat_1])])).

fof(c_0_11,plain,(
    ! [X15,X16] :
      ( ~ v1_relat_1(X16)
      | k1_relat_1(k7_relat_1(X16,X15)) = k3_xboole_0(k1_relat_1(X16),X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).

fof(c_0_12,plain,(
    ! [X9,X10] :
      ( ~ v1_relat_1(X10)
      | k7_relat_1(k7_relat_1(X10,X9),X9) = k7_relat_1(X10,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t101_relat_1])])).

fof(c_0_13,plain,(
    ! [X6,X7,X8] :
      ( ~ v1_relat_1(X8)
      | k7_relat_1(k7_relat_1(X8,X6),X7) = k7_relat_1(X8,k3_xboole_0(X6,X7)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t100_relat_1])])).

fof(c_0_14,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_15,plain,
    ( k9_relat_1(X1,X2) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k3_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X2) = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k7_relat_1(X1,k3_xboole_0(X2,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_19,plain,(
    ! [X13,X14] :
      ( ~ v1_relat_1(X14)
      | k2_relat_1(k7_relat_1(X14,X13)) = k9_relat_1(X14,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => k9_relat_1(X3,k3_xboole_0(X1,k10_relat_1(X3,X2))) = k3_xboole_0(k9_relat_1(X3,X1),X2) ) ),
    inference(assume_negation,[status(cth)],[t150_funct_1])).

cnf(c_0_21,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( k9_relat_1(X1,k1_relat_1(k7_relat_1(X1,X2))) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_23,plain,
    ( k7_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3),k3_xboole_0(X2,X3)) = k7_relat_1(k7_relat_1(X1,X2),X3)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_24,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_25,plain,(
    ! [X17,X18] :
      ( ( v1_relat_1(k7_relat_1(X17,X18))
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) )
      & ( v1_funct_1(k7_relat_1(X17,X18))
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc8_funct_1])])])).

fof(c_0_26,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_funct_1(esk3_0)
    & k9_relat_1(esk3_0,k3_xboole_0(esk1_0,k10_relat_1(esk3_0,esk2_0))) != k3_xboole_0(k9_relat_1(esk3_0,esk1_0),esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).

cnf(c_0_27,plain,
    ( k7_relat_1(X1,k3_xboole_0(X2,X3)) = k7_relat_1(k7_relat_1(X1,X3),X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_21])).

cnf(c_0_28,plain,
    ( k9_relat_1(X1,k1_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3))) = k9_relat_1(X1,k3_xboole_0(X2,X3))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_18])).

cnf(c_0_29,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),k3_xboole_0(X2,X2)) = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_17])).

cnf(c_0_30,plain,
    ( k2_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3)) = k9_relat_1(X1,k3_xboole_0(X2,X3))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_18])).

cnf(c_0_31,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( k2_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3)) = k9_relat_1(X1,k3_xboole_0(X3,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_27])).

cnf(c_0_35,plain,
    ( k9_relat_1(X1,k1_relat_1(k7_relat_1(X1,X2))) = k9_relat_1(X1,k3_xboole_0(X2,k3_xboole_0(X2,X2)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_36,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,k3_xboole_0(X2,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_17])).

cnf(c_0_37,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(k7_relat_1(X1,X2),X2)
    | ~ v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_17])).

cnf(c_0_38,plain,
    ( k7_relat_1(k7_relat_1(k7_relat_1(X1,k3_xboole_0(X2,X3)),X2),X3) = k7_relat_1(X1,k3_xboole_0(X2,X3))
    | ~ v1_relat_1(k7_relat_1(X1,k3_xboole_0(X2,X3)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_39,negated_conjecture,
    ( v1_relat_1(k7_relat_1(esk3_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])])).

cnf(c_0_40,plain,
    ( k9_relat_1(X1,k3_xboole_0(X2,X3)) = k9_relat_1(k7_relat_1(X1,X3),X2)
    | ~ v1_relat_1(k7_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_34])).

cnf(c_0_41,plain,
    ( k9_relat_1(X1,k3_xboole_0(X2,k3_xboole_0(X2,X2))) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_35])).

cnf(c_0_42,plain,
    ( k9_relat_1(X1,k3_xboole_0(X2,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_36])).

cnf(c_0_43,plain,
    ( k9_relat_1(k7_relat_1(X1,X2),X2) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_37])).

cnf(c_0_44,plain,
    ( k7_relat_1(k7_relat_1(X1,k3_xboole_0(X2,X3)),X3) = k7_relat_1(X1,k3_xboole_0(X2,X3))
    | ~ v1_relat_1(k7_relat_1(k7_relat_1(X1,k3_xboole_0(X2,X3)),X2))
    | ~ v1_relat_1(k7_relat_1(X1,k3_xboole_0(X2,X3)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_38])).

cnf(c_0_45,negated_conjecture,
    ( v1_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_18]),c_0_33])])).

cnf(c_0_46,plain,
    ( k9_relat_1(X1,k3_xboole_0(X2,X3)) = k9_relat_1(k7_relat_1(X1,X2),X3)
    | ~ v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_30])).

cnf(c_0_47,plain,
    ( k9_relat_1(k7_relat_1(X1,k3_xboole_0(X2,X2)),X2) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(k7_relat_1(X1,k3_xboole_0(X2,X2)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_48,plain,
    ( k2_relat_1(k7_relat_1(X1,k3_xboole_0(X2,X2))) = k9_relat_1(k7_relat_1(X1,k3_xboole_0(X2,X2)),X2)
    | ~ v1_relat_1(k7_relat_1(X1,k3_xboole_0(X2,X2)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_42])).

cnf(c_0_49,plain,
    ( k2_relat_1(k7_relat_1(k7_relat_1(X1,k3_xboole_0(X2,X2)),X2)) = k9_relat_1(X1,k3_xboole_0(X2,X2))
    | ~ v1_relat_1(k7_relat_1(X1,k3_xboole_0(X2,X2)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_36])).

cnf(c_0_50,negated_conjecture,
    ( k7_relat_1(k7_relat_1(esk3_0,k3_xboole_0(X1,X2)),X2) = k7_relat_1(esk3_0,k3_xboole_0(X1,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_39]),c_0_33])])).

cnf(c_0_51,plain,
    ( k9_relat_1(k7_relat_1(X1,k1_relat_1(X1)),X2) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(k7_relat_1(X1,k1_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_46])).

cnf(c_0_52,plain,
    ( k9_relat_1(k7_relat_1(X1,X2),k3_xboole_0(X3,X3)) = k9_relat_1(X1,k3_xboole_0(X3,X2))
    | ~ v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_36])).

cnf(c_0_53,plain,
    ( k2_relat_1(k7_relat_1(X1,k3_xboole_0(X2,X2))) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(k7_relat_1(X1,k3_xboole_0(X2,X2)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_54,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk3_0,k3_xboole_0(X1,X1))) = k9_relat_1(esk3_0,k3_xboole_0(X1,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_39]),c_0_33])])).

cnf(c_0_55,plain,
    ( k2_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3),X4)) = k9_relat_1(X1,k3_xboole_0(k3_xboole_0(X2,X3),X4))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_18])).

cnf(c_0_56,plain,
    ( v1_funct_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_57,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k7_relat_1(k7_relat_1(X1,X3),X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_27])).

cnf(c_0_58,plain,
    ( k2_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3),X4)) = k9_relat_1(X1,k3_xboole_0(k3_xboole_0(X3,X2),X4))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_27])).

cnf(c_0_59,plain,
    ( k2_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3),X4)) = k9_relat_1(X1,k3_xboole_0(X2,k3_xboole_0(X4,X3)))
    | ~ v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_27])).

cnf(c_0_60,plain,
    ( k9_relat_1(X1,k3_xboole_0(X2,k1_relat_1(X1))) = k9_relat_1(X1,k3_xboole_0(X2,X2))
    | ~ v1_relat_1(k7_relat_1(X1,k1_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_61,negated_conjecture,
    ( k9_relat_1(esk3_0,k3_xboole_0(X1,X1)) = k9_relat_1(esk3_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_39]),c_0_33])])).

cnf(c_0_62,plain,
    ( k9_relat_1(X1,k3_xboole_0(k3_xboole_0(X2,X3),k3_xboole_0(X2,X3))) = k2_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_23])).

cnf(c_0_63,plain,
    ( k9_relat_1(k7_relat_1(X1,X2),k3_xboole_0(X3,X3)) = k9_relat_1(X1,k3_xboole_0(X2,X3))
    | ~ v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_36])).

cnf(c_0_64,plain,
    ( v1_funct_1(k7_relat_1(k7_relat_1(X1,X2),X3))
    | ~ v1_funct_1(k7_relat_1(X1,X3))
    | ~ v1_relat_1(k7_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_65,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),k3_xboole_0(X2,k3_xboole_0(X2,X2))) = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_29])).

cnf(c_0_66,plain,
    ( k9_relat_1(X1,k3_xboole_0(k3_xboole_0(X2,X3),X4)) = k9_relat_1(X1,k3_xboole_0(X3,k3_xboole_0(X4,X2)))
    | ~ v1_relat_1(k7_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_67,negated_conjecture,
    ( k9_relat_1(esk3_0,k3_xboole_0(X1,k1_relat_1(esk3_0))) = k9_relat_1(esk3_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_39]),c_0_33])])).

cnf(c_0_68,negated_conjecture,
    ( k2_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),X2)) = k9_relat_1(esk3_0,k3_xboole_0(X1,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_61]),c_0_33])])).

cnf(c_0_69,plain,
    ( k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X2)) = k9_relat_1(X1,k3_xboole_0(X2,X2))
    | ~ v1_relat_1(k7_relat_1(X1,k1_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_63])).

cnf(c_0_70,plain,
    ( k2_relat_1(k7_relat_1(X1,k3_xboole_0(X2,X3))) = k2_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_62])).

cnf(c_0_71,plain,
    ( v1_funct_1(k7_relat_1(X1,X2))
    | ~ v1_funct_1(k7_relat_1(X1,k3_xboole_0(X2,k3_xboole_0(X2,X2))))
    | ~ v1_relat_1(k7_relat_1(X1,k3_xboole_0(X2,k3_xboole_0(X2,X2))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_72,negated_conjecture,
    ( k9_relat_1(esk3_0,k3_xboole_0(X1,k3_xboole_0(k1_relat_1(esk3_0),X2))) = k9_relat_1(esk3_0,k3_xboole_0(X2,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_39]),c_0_33])])).

cnf(c_0_73,negated_conjecture,
    ( k9_relat_1(esk3_0,k3_xboole_0(X1,X2)) = k9_relat_1(k7_relat_1(esk3_0,X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_68]),c_0_39])])).

cnf(c_0_74,negated_conjecture,
    ( k9_relat_1(esk3_0,k3_xboole_0(k1_relat_1(esk3_0),X1)) = k9_relat_1(esk3_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_61]),c_0_39]),c_0_33])])).

cnf(c_0_75,plain,
    ( k2_relat_1(k7_relat_1(X1,k3_xboole_0(X2,X3))) = k2_relat_1(k7_relat_1(k7_relat_1(X1,X3),X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_70,c_0_21])).

cnf(c_0_76,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk3_0,X1)) = k9_relat_1(esk3_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_61]),c_0_33])])).

cnf(c_0_77,plain,
    ( v1_funct_1(k7_relat_1(X1,X2))
    | ~ v1_funct_1(k7_relat_1(k7_relat_1(X1,k3_xboole_0(X2,X2)),X2))
    | ~ v1_relat_1(k7_relat_1(k7_relat_1(X1,k3_xboole_0(X2,X2)),X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_27])).

fof(c_0_78,plain,(
    ! [X19,X20,X21] :
      ( ~ v1_relat_1(X21)
      | k10_relat_1(k7_relat_1(X21,X19),X20) = k3_xboole_0(X19,k10_relat_1(X21,X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).

fof(c_0_79,plain,(
    ! [X22,X23] :
      ( ~ v1_relat_1(X23)
      | ~ v1_funct_1(X23)
      | k9_relat_1(X23,k10_relat_1(X23,X22)) = k3_xboole_0(X22,k9_relat_1(X23,k1_relat_1(X23))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_funct_1])])).

cnf(c_0_80,plain,
    ( k9_relat_1(X1,k3_xboole_0(X2,k1_relat_1(X1))) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_21])).

cnf(c_0_81,negated_conjecture,
    ( k9_relat_1(k7_relat_1(esk3_0,X1),k3_xboole_0(k1_relat_1(esk3_0),X2)) = k9_relat_1(k7_relat_1(esk3_0,X2),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_73]),c_0_73])).

cnf(c_0_82,negated_conjecture,
    ( k9_relat_1(k7_relat_1(esk3_0,X1),k1_relat_1(esk3_0)) = k9_relat_1(esk3_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_74]),c_0_39]),c_0_33])])).

cnf(c_0_83,negated_conjecture,
    ( k9_relat_1(k7_relat_1(esk3_0,X1),X2) = k9_relat_1(k7_relat_1(esk3_0,X2),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_33])]),c_0_68]),c_0_73]),c_0_73])).

cnf(c_0_84,negated_conjecture,
    ( v1_funct_1(k7_relat_1(esk3_0,X1))
    | ~ v1_funct_1(k7_relat_1(esk3_0,k3_xboole_0(X1,X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_50]),c_0_39]),c_0_33])])).

cnf(c_0_85,negated_conjecture,
    ( k7_relat_1(k7_relat_1(esk3_0,X1),k3_xboole_0(X2,X1)) = k7_relat_1(esk3_0,k3_xboole_0(X2,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_50]),c_0_33])])).

cnf(c_0_86,negated_conjecture,
    ( k9_relat_1(esk3_0,k3_xboole_0(esk1_0,k10_relat_1(esk3_0,esk2_0))) != k3_xboole_0(k9_relat_1(esk3_0,esk1_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_87,plain,
    ( k10_relat_1(k7_relat_1(X1,X2),X3) = k3_xboole_0(X2,k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_88,plain,
    ( k9_relat_1(X1,k10_relat_1(X1,X2)) = k3_xboole_0(X2,k9_relat_1(X1,k1_relat_1(X1)))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_89,negated_conjecture,
    ( k9_relat_1(k7_relat_1(esk3_0,X1),k1_relat_1(k7_relat_1(esk3_0,X1))) = k9_relat_1(esk3_0,X1) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_82]),c_0_39])]),c_0_83])).

cnf(c_0_90,negated_conjecture,
    ( v1_funct_1(k7_relat_1(esk3_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_56]),c_0_32]),c_0_33])])).

cnf(c_0_91,negated_conjecture,
    ( k7_relat_1(esk3_0,k3_xboole_0(X1,X1)) = k7_relat_1(esk3_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_85]),c_0_33])])).

cnf(c_0_92,negated_conjecture,
    ( k9_relat_1(esk3_0,k3_xboole_0(esk1_0,k10_relat_1(esk3_0,esk2_0))) != k3_xboole_0(esk2_0,k9_relat_1(esk3_0,esk1_0)) ),
    inference(rw,[status(thm)],[c_0_86,c_0_21])).

cnf(c_0_93,plain,
    ( k9_relat_1(k7_relat_1(X1,X2),k10_relat_1(X3,X4)) = k9_relat_1(X1,k10_relat_1(k7_relat_1(X3,X2),X4))
    | ~ v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X3) ),
    inference(spm,[status(thm)],[c_0_46,c_0_87])).

cnf(c_0_94,negated_conjecture,
    ( k9_relat_1(k7_relat_1(esk3_0,X1),k10_relat_1(k7_relat_1(esk3_0,X1),X2)) = k3_xboole_0(X2,k9_relat_1(esk3_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_90]),c_0_39])])).

cnf(c_0_95,negated_conjecture,
    ( k7_relat_1(k7_relat_1(esk3_0,X1),X1) = k7_relat_1(esk3_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_91]),c_0_33])])).

cnf(c_0_96,negated_conjecture,
    ( k9_relat_1(esk3_0,k10_relat_1(k7_relat_1(esk3_0,esk1_0),esk2_0)) != k3_xboole_0(esk2_0,k9_relat_1(esk3_0,esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_87]),c_0_33])])).

cnf(c_0_97,negated_conjecture,
    ( k9_relat_1(esk3_0,k10_relat_1(k7_relat_1(esk3_0,X1),X2)) = k3_xboole_0(X2,k9_relat_1(esk3_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_95]),c_0_39]),c_0_33])])).

cnf(c_0_98,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_96,c_0_97])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:31:30 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.56/0.74  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_TT_S0Y
% 0.56/0.74  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.56/0.74  #
% 0.56/0.74  # Preprocessing time       : 0.026 s
% 0.56/0.74  # Presaturation interreduction done
% 0.56/0.74  
% 0.56/0.74  # Proof found!
% 0.56/0.74  # SZS status Theorem
% 0.56/0.74  # SZS output start CNFRefutation
% 0.56/0.74  fof(t145_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k9_relat_1(X2,X1)=k9_relat_1(X2,k3_xboole_0(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_relat_1)).
% 0.56/0.74  fof(t90_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k1_relat_1(k7_relat_1(X2,X1))=k3_xboole_0(k1_relat_1(X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 0.56/0.74  fof(t101_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(k7_relat_1(X2,X1),X1)=k7_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t101_relat_1)).
% 0.56/0.74  fof(t100_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k7_relat_1(k7_relat_1(X3,X1),X2)=k7_relat_1(X3,k3_xboole_0(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 0.56/0.74  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.56/0.74  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 0.56/0.74  fof(t150_funct_1, conjecture, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>k9_relat_1(X3,k3_xboole_0(X1,k10_relat_1(X3,X2)))=k3_xboole_0(k9_relat_1(X3,X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_funct_1)).
% 0.56/0.74  fof(fc8_funct_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k7_relat_1(X1,X2))&v1_funct_1(k7_relat_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_funct_1)).
% 0.56/0.74  fof(t139_funct_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k10_relat_1(k7_relat_1(X3,X1),X2)=k3_xboole_0(X1,k10_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 0.56/0.74  fof(t148_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>k9_relat_1(X2,k10_relat_1(X2,X1))=k3_xboole_0(X1,k9_relat_1(X2,k1_relat_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_funct_1)).
% 0.56/0.74  fof(c_0_10, plain, ![X11, X12]:(~v1_relat_1(X12)|k9_relat_1(X12,X11)=k9_relat_1(X12,k3_xboole_0(k1_relat_1(X12),X11))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_relat_1])])).
% 0.56/0.74  fof(c_0_11, plain, ![X15, X16]:(~v1_relat_1(X16)|k1_relat_1(k7_relat_1(X16,X15))=k3_xboole_0(k1_relat_1(X16),X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).
% 0.56/0.74  fof(c_0_12, plain, ![X9, X10]:(~v1_relat_1(X10)|k7_relat_1(k7_relat_1(X10,X9),X9)=k7_relat_1(X10,X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t101_relat_1])])).
% 0.56/0.74  fof(c_0_13, plain, ![X6, X7, X8]:(~v1_relat_1(X8)|k7_relat_1(k7_relat_1(X8,X6),X7)=k7_relat_1(X8,k3_xboole_0(X6,X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t100_relat_1])])).
% 0.56/0.74  fof(c_0_14, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.56/0.74  cnf(c_0_15, plain, (k9_relat_1(X1,X2)=k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.56/0.74  cnf(c_0_16, plain, (k1_relat_1(k7_relat_1(X1,X2))=k3_xboole_0(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.56/0.74  cnf(c_0_17, plain, (k7_relat_1(k7_relat_1(X1,X2),X2)=k7_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.56/0.74  cnf(c_0_18, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k7_relat_1(X1,k3_xboole_0(X2,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.56/0.74  fof(c_0_19, plain, ![X13, X14]:(~v1_relat_1(X14)|k2_relat_1(k7_relat_1(X14,X13))=k9_relat_1(X14,X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.56/0.74  fof(c_0_20, negated_conjecture, ~(![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>k9_relat_1(X3,k3_xboole_0(X1,k10_relat_1(X3,X2)))=k3_xboole_0(k9_relat_1(X3,X1),X2))), inference(assume_negation,[status(cth)],[t150_funct_1])).
% 0.56/0.74  cnf(c_0_21, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.56/0.74  cnf(c_0_22, plain, (k9_relat_1(X1,k1_relat_1(k7_relat_1(X1,X2)))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.56/0.74  cnf(c_0_23, plain, (k7_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3),k3_xboole_0(X2,X3))=k7_relat_1(k7_relat_1(X1,X2),X3)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.56/0.74  cnf(c_0_24, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.56/0.74  fof(c_0_25, plain, ![X17, X18]:((v1_relat_1(k7_relat_1(X17,X18))|(~v1_relat_1(X17)|~v1_funct_1(X17)))&(v1_funct_1(k7_relat_1(X17,X18))|(~v1_relat_1(X17)|~v1_funct_1(X17)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc8_funct_1])])])).
% 0.56/0.74  fof(c_0_26, negated_conjecture, ((v1_relat_1(esk3_0)&v1_funct_1(esk3_0))&k9_relat_1(esk3_0,k3_xboole_0(esk1_0,k10_relat_1(esk3_0,esk2_0)))!=k3_xboole_0(k9_relat_1(esk3_0,esk1_0),esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).
% 0.56/0.74  cnf(c_0_27, plain, (k7_relat_1(X1,k3_xboole_0(X2,X3))=k7_relat_1(k7_relat_1(X1,X3),X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_18, c_0_21])).
% 0.56/0.74  cnf(c_0_28, plain, (k9_relat_1(X1,k1_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3)))=k9_relat_1(X1,k3_xboole_0(X2,X3))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_22, c_0_18])).
% 0.56/0.74  cnf(c_0_29, plain, (k7_relat_1(k7_relat_1(X1,X2),k3_xboole_0(X2,X2))=k7_relat_1(X1,X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_23, c_0_17])).
% 0.56/0.74  cnf(c_0_30, plain, (k2_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3))=k9_relat_1(X1,k3_xboole_0(X2,X3))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_24, c_0_18])).
% 0.56/0.74  cnf(c_0_31, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.56/0.74  cnf(c_0_32, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.56/0.74  cnf(c_0_33, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.56/0.74  cnf(c_0_34, plain, (k2_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3))=k9_relat_1(X1,k3_xboole_0(X3,X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_24, c_0_27])).
% 0.56/0.74  cnf(c_0_35, plain, (k9_relat_1(X1,k1_relat_1(k7_relat_1(X1,X2)))=k9_relat_1(X1,k3_xboole_0(X2,k3_xboole_0(X2,X2)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.56/0.74  cnf(c_0_36, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,k3_xboole_0(X2,X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_30, c_0_17])).
% 0.56/0.74  cnf(c_0_37, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(k7_relat_1(X1,X2),X2)|~v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_24, c_0_17])).
% 0.56/0.74  cnf(c_0_38, plain, (k7_relat_1(k7_relat_1(k7_relat_1(X1,k3_xboole_0(X2,X3)),X2),X3)=k7_relat_1(X1,k3_xboole_0(X2,X3))|~v1_relat_1(k7_relat_1(X1,k3_xboole_0(X2,X3)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.56/0.74  cnf(c_0_39, negated_conjecture, (v1_relat_1(k7_relat_1(esk3_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])])).
% 0.56/0.74  cnf(c_0_40, plain, (k9_relat_1(X1,k3_xboole_0(X2,X3))=k9_relat_1(k7_relat_1(X1,X3),X2)|~v1_relat_1(k7_relat_1(X1,X3))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_24, c_0_34])).
% 0.56/0.74  cnf(c_0_41, plain, (k9_relat_1(X1,k3_xboole_0(X2,k3_xboole_0(X2,X2)))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_22, c_0_35])).
% 0.56/0.74  cnf(c_0_42, plain, (k9_relat_1(X1,k3_xboole_0(X2,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_24, c_0_36])).
% 0.56/0.74  cnf(c_0_43, plain, (k9_relat_1(k7_relat_1(X1,X2),X2)=k9_relat_1(X1,X2)|~v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_24, c_0_37])).
% 0.56/0.74  cnf(c_0_44, plain, (k7_relat_1(k7_relat_1(X1,k3_xboole_0(X2,X3)),X3)=k7_relat_1(X1,k3_xboole_0(X2,X3))|~v1_relat_1(k7_relat_1(k7_relat_1(X1,k3_xboole_0(X2,X3)),X2))|~v1_relat_1(k7_relat_1(X1,k3_xboole_0(X2,X3)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_17, c_0_38])).
% 0.56/0.74  cnf(c_0_45, negated_conjecture, (v1_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_18]), c_0_33])])).
% 0.56/0.74  cnf(c_0_46, plain, (k9_relat_1(X1,k3_xboole_0(X2,X3))=k9_relat_1(k7_relat_1(X1,X2),X3)|~v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_24, c_0_30])).
% 0.56/0.74  cnf(c_0_47, plain, (k9_relat_1(k7_relat_1(X1,k3_xboole_0(X2,X2)),X2)=k9_relat_1(X1,X2)|~v1_relat_1(k7_relat_1(X1,k3_xboole_0(X2,X2)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.56/0.74  cnf(c_0_48, plain, (k2_relat_1(k7_relat_1(X1,k3_xboole_0(X2,X2)))=k9_relat_1(k7_relat_1(X1,k3_xboole_0(X2,X2)),X2)|~v1_relat_1(k7_relat_1(X1,k3_xboole_0(X2,X2)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_37, c_0_42])).
% 0.56/0.74  cnf(c_0_49, plain, (k2_relat_1(k7_relat_1(k7_relat_1(X1,k3_xboole_0(X2,X2)),X2))=k9_relat_1(X1,k3_xboole_0(X2,X2))|~v1_relat_1(k7_relat_1(X1,k3_xboole_0(X2,X2)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_43, c_0_36])).
% 0.56/0.74  cnf(c_0_50, negated_conjecture, (k7_relat_1(k7_relat_1(esk3_0,k3_xboole_0(X1,X2)),X2)=k7_relat_1(esk3_0,k3_xboole_0(X1,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_39]), c_0_33])])).
% 0.56/0.74  cnf(c_0_51, plain, (k9_relat_1(k7_relat_1(X1,k1_relat_1(X1)),X2)=k9_relat_1(X1,X2)|~v1_relat_1(k7_relat_1(X1,k1_relat_1(X1)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_15, c_0_46])).
% 0.56/0.74  cnf(c_0_52, plain, (k9_relat_1(k7_relat_1(X1,X2),k3_xboole_0(X3,X3))=k9_relat_1(X1,k3_xboole_0(X3,X2))|~v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_34, c_0_36])).
% 0.56/0.74  cnf(c_0_53, plain, (k2_relat_1(k7_relat_1(X1,k3_xboole_0(X2,X2)))=k9_relat_1(X1,X2)|~v1_relat_1(k7_relat_1(X1,k3_xboole_0(X2,X2)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.56/0.74  cnf(c_0_54, negated_conjecture, (k2_relat_1(k7_relat_1(esk3_0,k3_xboole_0(X1,X1)))=k9_relat_1(esk3_0,k3_xboole_0(X1,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_39]), c_0_33])])).
% 0.56/0.74  cnf(c_0_55, plain, (k2_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3),X4))=k9_relat_1(X1,k3_xboole_0(k3_xboole_0(X2,X3),X4))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_30, c_0_18])).
% 0.56/0.74  cnf(c_0_56, plain, (v1_funct_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.56/0.74  cnf(c_0_57, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k7_relat_1(k7_relat_1(X1,X3),X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_18, c_0_27])).
% 0.56/0.74  cnf(c_0_58, plain, (k2_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3),X4))=k9_relat_1(X1,k3_xboole_0(k3_xboole_0(X3,X2),X4))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_30, c_0_27])).
% 0.56/0.74  cnf(c_0_59, plain, (k2_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3),X4))=k9_relat_1(X1,k3_xboole_0(X2,k3_xboole_0(X4,X3)))|~v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_30, c_0_27])).
% 0.56/0.74  cnf(c_0_60, plain, (k9_relat_1(X1,k3_xboole_0(X2,k1_relat_1(X1)))=k9_relat_1(X1,k3_xboole_0(X2,X2))|~v1_relat_1(k7_relat_1(X1,k1_relat_1(X1)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.56/0.74  cnf(c_0_61, negated_conjecture, (k9_relat_1(esk3_0,k3_xboole_0(X1,X1))=k9_relat_1(esk3_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_39]), c_0_33])])).
% 0.56/0.74  cnf(c_0_62, plain, (k9_relat_1(X1,k3_xboole_0(k3_xboole_0(X2,X3),k3_xboole_0(X2,X3)))=k2_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_55, c_0_23])).
% 0.56/0.74  cnf(c_0_63, plain, (k9_relat_1(k7_relat_1(X1,X2),k3_xboole_0(X3,X3))=k9_relat_1(X1,k3_xboole_0(X2,X3))|~v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_30, c_0_36])).
% 0.56/0.74  cnf(c_0_64, plain, (v1_funct_1(k7_relat_1(k7_relat_1(X1,X2),X3))|~v1_funct_1(k7_relat_1(X1,X3))|~v1_relat_1(k7_relat_1(X1,X3))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.56/0.74  cnf(c_0_65, plain, (k7_relat_1(k7_relat_1(X1,X2),k3_xboole_0(X2,k3_xboole_0(X2,X2)))=k7_relat_1(X1,X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_23, c_0_29])).
% 0.56/0.74  cnf(c_0_66, plain, (k9_relat_1(X1,k3_xboole_0(k3_xboole_0(X2,X3),X4))=k9_relat_1(X1,k3_xboole_0(X3,k3_xboole_0(X4,X2)))|~v1_relat_1(k7_relat_1(X1,X3))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.56/0.74  cnf(c_0_67, negated_conjecture, (k9_relat_1(esk3_0,k3_xboole_0(X1,k1_relat_1(esk3_0)))=k9_relat_1(esk3_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_39]), c_0_33])])).
% 0.56/0.74  cnf(c_0_68, negated_conjecture, (k2_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),X2))=k9_relat_1(esk3_0,k3_xboole_0(X1,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_61]), c_0_33])])).
% 0.56/0.74  cnf(c_0_69, plain, (k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X2))=k9_relat_1(X1,k3_xboole_0(X2,X2))|~v1_relat_1(k7_relat_1(X1,k1_relat_1(X1)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_51, c_0_63])).
% 0.56/0.74  cnf(c_0_70, plain, (k2_relat_1(k7_relat_1(X1,k3_xboole_0(X2,X3)))=k2_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_36, c_0_62])).
% 0.56/0.74  cnf(c_0_71, plain, (v1_funct_1(k7_relat_1(X1,X2))|~v1_funct_1(k7_relat_1(X1,k3_xboole_0(X2,k3_xboole_0(X2,X2))))|~v1_relat_1(k7_relat_1(X1,k3_xboole_0(X2,k3_xboole_0(X2,X2))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.56/0.74  cnf(c_0_72, negated_conjecture, (k9_relat_1(esk3_0,k3_xboole_0(X1,k3_xboole_0(k1_relat_1(esk3_0),X2)))=k9_relat_1(esk3_0,k3_xboole_0(X2,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_39]), c_0_33])])).
% 0.56/0.74  cnf(c_0_73, negated_conjecture, (k9_relat_1(esk3_0,k3_xboole_0(X1,X2))=k9_relat_1(k7_relat_1(esk3_0,X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_68]), c_0_39])])).
% 0.56/0.74  cnf(c_0_74, negated_conjecture, (k9_relat_1(esk3_0,k3_xboole_0(k1_relat_1(esk3_0),X1))=k9_relat_1(esk3_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_61]), c_0_39]), c_0_33])])).
% 0.56/0.74  cnf(c_0_75, plain, (k2_relat_1(k7_relat_1(X1,k3_xboole_0(X2,X3)))=k2_relat_1(k7_relat_1(k7_relat_1(X1,X3),X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_70, c_0_21])).
% 0.56/0.74  cnf(c_0_76, negated_conjecture, (k2_relat_1(k7_relat_1(esk3_0,X1))=k9_relat_1(esk3_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_61]), c_0_33])])).
% 0.56/0.74  cnf(c_0_77, plain, (v1_funct_1(k7_relat_1(X1,X2))|~v1_funct_1(k7_relat_1(k7_relat_1(X1,k3_xboole_0(X2,X2)),X2))|~v1_relat_1(k7_relat_1(k7_relat_1(X1,k3_xboole_0(X2,X2)),X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_71, c_0_27])).
% 0.56/0.74  fof(c_0_78, plain, ![X19, X20, X21]:(~v1_relat_1(X21)|k10_relat_1(k7_relat_1(X21,X19),X20)=k3_xboole_0(X19,k10_relat_1(X21,X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).
% 0.56/0.74  fof(c_0_79, plain, ![X22, X23]:(~v1_relat_1(X23)|~v1_funct_1(X23)|k9_relat_1(X23,k10_relat_1(X23,X22))=k3_xboole_0(X22,k9_relat_1(X23,k1_relat_1(X23)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_funct_1])])).
% 0.56/0.74  cnf(c_0_80, plain, (k9_relat_1(X1,k3_xboole_0(X2,k1_relat_1(X1)))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_15, c_0_21])).
% 0.56/0.74  cnf(c_0_81, negated_conjecture, (k9_relat_1(k7_relat_1(esk3_0,X1),k3_xboole_0(k1_relat_1(esk3_0),X2))=k9_relat_1(k7_relat_1(esk3_0,X2),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72, c_0_73]), c_0_73])).
% 0.56/0.74  cnf(c_0_82, negated_conjecture, (k9_relat_1(k7_relat_1(esk3_0,X1),k1_relat_1(esk3_0))=k9_relat_1(esk3_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_74]), c_0_39]), c_0_33])])).
% 0.56/0.74  cnf(c_0_83, negated_conjecture, (k9_relat_1(k7_relat_1(esk3_0,X1),X2)=k9_relat_1(k7_relat_1(esk3_0,X2),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_33])]), c_0_68]), c_0_73]), c_0_73])).
% 0.56/0.74  cnf(c_0_84, negated_conjecture, (v1_funct_1(k7_relat_1(esk3_0,X1))|~v1_funct_1(k7_relat_1(esk3_0,k3_xboole_0(X1,X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_50]), c_0_39]), c_0_33])])).
% 0.56/0.74  cnf(c_0_85, negated_conjecture, (k7_relat_1(k7_relat_1(esk3_0,X1),k3_xboole_0(X2,X1))=k7_relat_1(esk3_0,k3_xboole_0(X2,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_50]), c_0_33])])).
% 0.56/0.74  cnf(c_0_86, negated_conjecture, (k9_relat_1(esk3_0,k3_xboole_0(esk1_0,k10_relat_1(esk3_0,esk2_0)))!=k3_xboole_0(k9_relat_1(esk3_0,esk1_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.56/0.74  cnf(c_0_87, plain, (k10_relat_1(k7_relat_1(X1,X2),X3)=k3_xboole_0(X2,k10_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.56/0.74  cnf(c_0_88, plain, (k9_relat_1(X1,k10_relat_1(X1,X2))=k3_xboole_0(X2,k9_relat_1(X1,k1_relat_1(X1)))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.56/0.74  cnf(c_0_89, negated_conjecture, (k9_relat_1(k7_relat_1(esk3_0,X1),k1_relat_1(k7_relat_1(esk3_0,X1)))=k9_relat_1(esk3_0,X1)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_82]), c_0_39])]), c_0_83])).
% 0.56/0.74  cnf(c_0_90, negated_conjecture, (v1_funct_1(k7_relat_1(esk3_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_56]), c_0_32]), c_0_33])])).
% 0.56/0.74  cnf(c_0_91, negated_conjecture, (k7_relat_1(esk3_0,k3_xboole_0(X1,X1))=k7_relat_1(esk3_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_85]), c_0_33])])).
% 0.56/0.74  cnf(c_0_92, negated_conjecture, (k9_relat_1(esk3_0,k3_xboole_0(esk1_0,k10_relat_1(esk3_0,esk2_0)))!=k3_xboole_0(esk2_0,k9_relat_1(esk3_0,esk1_0))), inference(rw,[status(thm)],[c_0_86, c_0_21])).
% 0.56/0.74  cnf(c_0_93, plain, (k9_relat_1(k7_relat_1(X1,X2),k10_relat_1(X3,X4))=k9_relat_1(X1,k10_relat_1(k7_relat_1(X3,X2),X4))|~v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_relat_1(X3)), inference(spm,[status(thm)],[c_0_46, c_0_87])).
% 0.56/0.74  cnf(c_0_94, negated_conjecture, (k9_relat_1(k7_relat_1(esk3_0,X1),k10_relat_1(k7_relat_1(esk3_0,X1),X2))=k3_xboole_0(X2,k9_relat_1(esk3_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_90]), c_0_39])])).
% 0.56/0.74  cnf(c_0_95, negated_conjecture, (k7_relat_1(k7_relat_1(esk3_0,X1),X1)=k7_relat_1(esk3_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_91]), c_0_33])])).
% 0.56/0.74  cnf(c_0_96, negated_conjecture, (k9_relat_1(esk3_0,k10_relat_1(k7_relat_1(esk3_0,esk1_0),esk2_0))!=k3_xboole_0(esk2_0,k9_relat_1(esk3_0,esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_87]), c_0_33])])).
% 0.56/0.74  cnf(c_0_97, negated_conjecture, (k9_relat_1(esk3_0,k10_relat_1(k7_relat_1(esk3_0,X1),X2))=k3_xboole_0(X2,k9_relat_1(esk3_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_95]), c_0_39]), c_0_33])])).
% 0.56/0.74  cnf(c_0_98, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_96, c_0_97])]), ['proof']).
% 0.56/0.74  # SZS output end CNFRefutation
% 0.56/0.74  # Proof object total steps             : 99
% 0.56/0.74  # Proof object clause steps            : 78
% 0.56/0.74  # Proof object formula steps           : 21
% 0.56/0.74  # Proof object conjectures             : 31
% 0.56/0.74  # Proof object clause conjectures      : 28
% 0.56/0.74  # Proof object formula conjectures     : 3
% 0.56/0.74  # Proof object initial clauses used    : 13
% 0.56/0.74  # Proof object initial formulas used   : 10
% 0.56/0.74  # Proof object generating inferences   : 62
% 0.56/0.74  # Proof object simplifying inferences  : 66
% 0.56/0.74  # Training examples: 0 positive, 0 negative
% 0.56/0.74  # Parsed axioms                        : 10
% 0.56/0.74  # Removed by relevancy pruning/SinE    : 0
% 0.56/0.74  # Initial clauses                      : 13
% 0.56/0.74  # Removed in clause preprocessing      : 0
% 0.56/0.74  # Initial clauses in saturation        : 13
% 0.56/0.74  # Processed clauses                    : 2032
% 0.56/0.74  # ...of these trivial                  : 415
% 0.56/0.74  # ...subsumed                          : 1192
% 0.56/0.74  # ...remaining for further processing  : 425
% 0.56/0.74  # Other redundant clauses eliminated   : 0
% 0.56/0.74  # Clauses deleted for lack of memory   : 0
% 0.56/0.74  # Backward-subsumed                    : 7
% 0.56/0.74  # Backward-rewritten                   : 66
% 0.56/0.74  # Generated clauses                    : 34315
% 0.56/0.74  # ...of the previous two non-trivial   : 29789
% 0.56/0.74  # Contextual simplify-reflections      : 1
% 0.56/0.74  # Paramodulations                      : 34315
% 0.56/0.74  # Factorizations                       : 0
% 0.56/0.74  # Equation resolutions                 : 0
% 0.56/0.74  # Propositional unsat checks           : 0
% 0.56/0.74  #    Propositional check models        : 0
% 0.56/0.74  #    Propositional check unsatisfiable : 0
% 0.56/0.74  #    Propositional clauses             : 0
% 0.56/0.74  #    Propositional clauses after purity: 0
% 0.56/0.74  #    Propositional unsat core size     : 0
% 0.56/0.74  #    Propositional preprocessing time  : 0.000
% 0.56/0.74  #    Propositional encoding time       : 0.000
% 0.56/0.74  #    Propositional solver time         : 0.000
% 0.56/0.74  #    Success case prop preproc time    : 0.000
% 0.56/0.74  #    Success case prop encoding time   : 0.000
% 0.56/0.74  #    Success case prop solver time     : 0.000
% 0.56/0.74  # Current number of processed clauses  : 339
% 0.56/0.74  #    Positive orientable unit clauses  : 74
% 0.56/0.74  #    Positive unorientable unit clauses: 9
% 0.56/0.74  #    Negative unit clauses             : 1
% 0.56/0.74  #    Non-unit-clauses                  : 255
% 0.56/0.74  # Current number of unprocessed clauses: 27528
% 0.56/0.74  # ...number of literals in the above   : 105372
% 0.56/0.74  # Current number of archived formulas  : 0
% 0.56/0.74  # Current number of archived clauses   : 86
% 0.56/0.74  # Clause-clause subsumption calls (NU) : 12515
% 0.56/0.74  # Rec. Clause-clause subsumption calls : 9331
% 0.56/0.74  # Non-unit clause-clause subsumptions  : 982
% 0.56/0.74  # Unit Clause-clause subsumption calls : 24
% 0.56/0.74  # Rewrite failures with RHS unbound    : 0
% 0.56/0.74  # BW rewrite match attempts            : 739
% 0.56/0.74  # BW rewrite match successes           : 165
% 0.56/0.74  # Condensation attempts                : 0
% 0.56/0.74  # Condensation successes               : 0
% 0.56/0.74  # Termbank termtop insertions          : 782842
% 0.56/0.74  
% 0.56/0.74  # -------------------------------------------------
% 0.56/0.74  # User time                : 0.389 s
% 0.56/0.74  # System time              : 0.019 s
% 0.56/0.74  # Total time               : 0.408 s
% 0.56/0.74  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------

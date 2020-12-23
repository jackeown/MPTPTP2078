%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:01 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 214 expanded)
%              Number of clauses        :   37 (  88 expanded)
%              Number of leaves         :   21 (  63 expanded)
%              Depth                    :    9
%              Number of atoms          :  128 ( 285 expanded)
%              Number of equality atoms :   47 ( 162 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t27_yellow_1,conjecture,(
    ! [X1] :
      ( l1_orders_2(X1)
     => k6_yellow_1(k1_xboole_0,X1) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_yellow_1)).

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

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

fof(t26_yellow_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v4_relat_1(X1,k1_xboole_0)
        & v1_funct_1(X1)
        & v1_partfun1(X1,k1_xboole_0)
        & v1_yellow_1(X1) )
     => k5_yellow_1(k1_xboole_0,X1) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_yellow_1)).

fof(fc2_funcop_1,axiom,(
    ! [X1] : v1_xboole_0(k2_funcop_1(k1_xboole_0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funcop_1)).

fof(redefinition_k7_funcop_1,axiom,(
    ! [X1,X2] : k7_funcop_1(X1,X2) = k2_funcop_1(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_funcop_1)).

fof(dt_k6_partfun1,axiom,(
    ! [X1] :
      ( v1_partfun1(k6_partfun1(X1),X1)
      & m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(fc10_yellow_1,axiom,(
    ! [X1,X2] :
      ( l1_orders_2(X2)
     => v1_yellow_1(k2_funcop_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_yellow_1)).

fof(d5_yellow_1,axiom,(
    ! [X1,X2] :
      ( l1_orders_2(X2)
     => k6_yellow_1(X1,X2) = k5_yellow_1(X1,k7_funcop_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_yellow_1)).

fof(t81_relat_1,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(l222_relat_1,axiom,(
    ! [X1,X2] :
      ( v4_relat_1(k1_xboole_0,X1)
      & v5_relat_1(k1_xboole_0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l222_relat_1)).

fof(cc1_funct_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_funct_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1] :
        ( l1_orders_2(X1)
       => k6_yellow_1(k1_xboole_0,X1) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    inference(assume_negation,[status(cth)],[t27_yellow_1])).

fof(c_0_22,negated_conjecture,
    ( l1_orders_2(esk2_0)
    & k6_yellow_1(k1_xboole_0,esk2_0) != g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).

fof(c_0_23,plain,(
    ! [X42] : k6_partfun1(X42) = k6_relat_1(X42) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

fof(c_0_24,plain,(
    ! [X9] : k2_tarski(X9,X9) = k1_tarski(X9) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_25,plain,(
    ! [X10,X11] : k1_enumset1(X10,X10,X11) = k2_tarski(X10,X11) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_26,plain,(
    ! [X12,X13,X14] : k2_enumset1(X12,X12,X13,X14) = k1_enumset1(X12,X13,X14) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_27,plain,(
    ! [X15,X16,X17,X18] : k3_enumset1(X15,X15,X16,X17,X18) = k2_enumset1(X15,X16,X17,X18) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_28,plain,(
    ! [X19,X20,X21,X22,X23] : k4_enumset1(X19,X19,X20,X21,X22,X23) = k3_enumset1(X19,X20,X21,X22,X23) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_29,plain,(
    ! [X24,X25,X26,X27,X28,X29] : k5_enumset1(X24,X24,X25,X26,X27,X28,X29) = k4_enumset1(X24,X25,X26,X27,X28,X29) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_30,plain,(
    ! [X30,X31,X32,X33,X34,X35,X36] : k6_enumset1(X30,X30,X31,X32,X33,X34,X35,X36) = k5_enumset1(X30,X31,X32,X33,X34,X35,X36) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_31,plain,(
    ! [X51] :
      ( ~ v1_relat_1(X51)
      | ~ v4_relat_1(X51,k1_xboole_0)
      | ~ v1_funct_1(X51)
      | ~ v1_partfun1(X51,k1_xboole_0)
      | ~ v1_yellow_1(X51)
      | k5_yellow_1(k1_xboole_0,X51) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_yellow_1])])).

fof(c_0_32,plain,(
    ! [X48] : v1_xboole_0(k2_funcop_1(k1_xboole_0,X48)) ),
    inference(variable_rename,[status(thm)],[fc2_funcop_1])).

fof(c_0_33,plain,(
    ! [X49,X50] : k7_funcop_1(X49,X50) = k2_funcop_1(X49,X50) ),
    inference(variable_rename,[status(thm)],[redefinition_k7_funcop_1])).

fof(c_0_34,plain,(
    ! [X41] :
      ( v1_partfun1(k6_partfun1(X41),X41)
      & m1_subset_1(k6_partfun1(X41),k1_zfmisc_1(k2_zfmisc_1(X41,X41))) ) ),
    inference(variable_rename,[status(thm)],[dt_k6_partfun1])).

cnf(c_0_35,negated_conjecture,
    ( k6_yellow_1(k1_xboole_0,esk2_0) != g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_36,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_37,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_38,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_39,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_40,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_41,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_42,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_43,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_44,plain,
    ( k5_yellow_1(k1_xboole_0,X1) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,k1_xboole_0)
    | ~ v1_funct_1(X1)
    | ~ v1_partfun1(X1,k1_xboole_0)
    | ~ v1_yellow_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_45,plain,(
    ! [X8] :
      ( ~ v1_xboole_0(X8)
      | X8 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_46,plain,
    ( v1_xboole_0(k2_funcop_1(k1_xboole_0,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_47,plain,
    ( k7_funcop_1(X1,X2) = k2_funcop_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_48,plain,
    ( v1_partfun1(k6_partfun1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_49,plain,(
    ! [X37] : v1_relat_1(k6_relat_1(X37)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

fof(c_0_50,plain,(
    ! [X46,X47] :
      ( ~ l1_orders_2(X47)
      | v1_yellow_1(k2_funcop_1(X46,X47)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc10_yellow_1])])).

cnf(c_0_51,negated_conjecture,
    ( k6_yellow_1(k1_xboole_0,esk2_0) != g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_relat_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_42]),c_0_42]),c_0_43]),c_0_43])).

cnf(c_0_52,plain,
    ( k5_yellow_1(k1_xboole_0,X1) = g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_relat_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_yellow_1(X1)
    | ~ v4_relat_1(X1,k1_xboole_0)
    | ~ v1_partfun1(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_36]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_42]),c_0_42]),c_0_43]),c_0_43])).

fof(c_0_53,plain,(
    ! [X44,X45] :
      ( ~ l1_orders_2(X45)
      | k6_yellow_1(X44,X45) = k5_yellow_1(X44,k7_funcop_1(X44,X45)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_yellow_1])])).

cnf(c_0_54,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_55,plain,
    ( v1_xboole_0(k7_funcop_1(k1_xboole_0,X1)) ),
    inference(rw,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_56,plain,
    ( v1_partfun1(k6_relat_1(X1),X1) ),
    inference(rw,[status(thm)],[c_0_48,c_0_36])).

cnf(c_0_57,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t81_relat_1])).

fof(c_0_58,plain,(
    ! [X38,X39] :
      ( v4_relat_1(k1_xboole_0,X38)
      & v5_relat_1(k1_xboole_0,X39) ) ),
    inference(variable_rename,[status(thm)],[l222_relat_1])).

cnf(c_0_59,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_60,plain,
    ( v1_yellow_1(k2_funcop_1(X2,X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_61,negated_conjecture,
    ( k5_yellow_1(k1_xboole_0,X1) != k6_yellow_1(k1_xboole_0,esk2_0)
    | ~ v1_yellow_1(X1)
    | ~ v1_partfun1(X1,k1_xboole_0)
    | ~ v1_funct_1(X1)
    | ~ v4_relat_1(X1,k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_62,plain,
    ( k6_yellow_1(X2,X1) = k5_yellow_1(X2,k7_funcop_1(X2,X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_63,plain,
    ( k7_funcop_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_64,plain,
    ( v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_65,plain,
    ( v4_relat_1(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_66,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_57])).

cnf(c_0_67,plain,
    ( v1_yellow_1(k7_funcop_1(X2,X1))
    | ~ l1_orders_2(X1) ),
    inference(rw,[status(thm)],[c_0_60,c_0_47])).

cnf(c_0_68,negated_conjecture,
    ( k6_yellow_1(k1_xboole_0,X1) != k6_yellow_1(k1_xboole_0,esk2_0)
    | ~ v1_yellow_1(k1_xboole_0)
    | ~ l1_orders_2(X1)
    | ~ v1_funct_1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63]),c_0_63]),c_0_64]),c_0_63]),c_0_63]),c_0_65]),c_0_63]),c_0_66])])).

cnf(c_0_69,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_70,plain,
    ( v1_yellow_1(k1_xboole_0)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_67,c_0_63])).

cnf(c_0_71,negated_conjecture,
    ( ~ v1_yellow_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_68]),c_0_69])])).

cnf(c_0_72,negated_conjecture,
    ( v1_yellow_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_70,c_0_69])).

fof(c_0_73,plain,(
    ! [X40] :
      ( ~ v1_xboole_0(X40)
      | v1_funct_1(X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_1])])).

cnf(c_0_74,negated_conjecture,
    ( ~ v1_funct_1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_72])])).

cnf(c_0_75,plain,
    ( v1_funct_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_76,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_77,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_76])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:21:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.14/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.027 s
% 0.14/0.38  # Presaturation interreduction done
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(t27_yellow_1, conjecture, ![X1]:(l1_orders_2(X1)=>k6_yellow_1(k1_xboole_0,X1)=g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_yellow_1)).
% 0.14/0.38  fof(redefinition_k6_partfun1, axiom, ![X1]:k6_partfun1(X1)=k6_relat_1(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 0.14/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.14/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.14/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.14/0.38  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.14/0.38  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.14/0.38  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.14/0.38  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.14/0.38  fof(t26_yellow_1, axiom, ![X1]:(((((v1_relat_1(X1)&v4_relat_1(X1,k1_xboole_0))&v1_funct_1(X1))&v1_partfun1(X1,k1_xboole_0))&v1_yellow_1(X1))=>k5_yellow_1(k1_xboole_0,X1)=g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_yellow_1)).
% 0.14/0.38  fof(fc2_funcop_1, axiom, ![X1]:v1_xboole_0(k2_funcop_1(k1_xboole_0,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_funcop_1)).
% 0.14/0.38  fof(redefinition_k7_funcop_1, axiom, ![X1, X2]:k7_funcop_1(X1,X2)=k2_funcop_1(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_funcop_1)).
% 0.14/0.38  fof(dt_k6_partfun1, axiom, ![X1]:(v1_partfun1(k6_partfun1(X1),X1)&m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 0.14/0.38  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.14/0.38  fof(dt_k6_relat_1, axiom, ![X1]:v1_relat_1(k6_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 0.14/0.38  fof(fc10_yellow_1, axiom, ![X1, X2]:(l1_orders_2(X2)=>v1_yellow_1(k2_funcop_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_yellow_1)).
% 0.14/0.38  fof(d5_yellow_1, axiom, ![X1, X2]:(l1_orders_2(X2)=>k6_yellow_1(X1,X2)=k5_yellow_1(X1,k7_funcop_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_yellow_1)).
% 0.14/0.38  fof(t81_relat_1, axiom, k6_relat_1(k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 0.14/0.38  fof(l222_relat_1, axiom, ![X1, X2]:(v4_relat_1(k1_xboole_0,X1)&v5_relat_1(k1_xboole_0,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l222_relat_1)).
% 0.14/0.38  fof(cc1_funct_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_funct_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_1)).
% 0.14/0.38  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.14/0.38  fof(c_0_21, negated_conjecture, ~(![X1]:(l1_orders_2(X1)=>k6_yellow_1(k1_xboole_0,X1)=g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))))), inference(assume_negation,[status(cth)],[t27_yellow_1])).
% 0.14/0.38  fof(c_0_22, negated_conjecture, (l1_orders_2(esk2_0)&k6_yellow_1(k1_xboole_0,esk2_0)!=g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).
% 0.14/0.38  fof(c_0_23, plain, ![X42]:k6_partfun1(X42)=k6_relat_1(X42), inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).
% 0.14/0.38  fof(c_0_24, plain, ![X9]:k2_tarski(X9,X9)=k1_tarski(X9), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.14/0.38  fof(c_0_25, plain, ![X10, X11]:k1_enumset1(X10,X10,X11)=k2_tarski(X10,X11), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.14/0.38  fof(c_0_26, plain, ![X12, X13, X14]:k2_enumset1(X12,X12,X13,X14)=k1_enumset1(X12,X13,X14), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.14/0.38  fof(c_0_27, plain, ![X15, X16, X17, X18]:k3_enumset1(X15,X15,X16,X17,X18)=k2_enumset1(X15,X16,X17,X18), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.14/0.38  fof(c_0_28, plain, ![X19, X20, X21, X22, X23]:k4_enumset1(X19,X19,X20,X21,X22,X23)=k3_enumset1(X19,X20,X21,X22,X23), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.14/0.38  fof(c_0_29, plain, ![X24, X25, X26, X27, X28, X29]:k5_enumset1(X24,X24,X25,X26,X27,X28,X29)=k4_enumset1(X24,X25,X26,X27,X28,X29), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.14/0.38  fof(c_0_30, plain, ![X30, X31, X32, X33, X34, X35, X36]:k6_enumset1(X30,X30,X31,X32,X33,X34,X35,X36)=k5_enumset1(X30,X31,X32,X33,X34,X35,X36), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.14/0.38  fof(c_0_31, plain, ![X51]:(~v1_relat_1(X51)|~v4_relat_1(X51,k1_xboole_0)|~v1_funct_1(X51)|~v1_partfun1(X51,k1_xboole_0)|~v1_yellow_1(X51)|k5_yellow_1(k1_xboole_0,X51)=g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_yellow_1])])).
% 0.14/0.38  fof(c_0_32, plain, ![X48]:v1_xboole_0(k2_funcop_1(k1_xboole_0,X48)), inference(variable_rename,[status(thm)],[fc2_funcop_1])).
% 0.14/0.38  fof(c_0_33, plain, ![X49, X50]:k7_funcop_1(X49,X50)=k2_funcop_1(X49,X50), inference(variable_rename,[status(thm)],[redefinition_k7_funcop_1])).
% 0.14/0.38  fof(c_0_34, plain, ![X41]:(v1_partfun1(k6_partfun1(X41),X41)&m1_subset_1(k6_partfun1(X41),k1_zfmisc_1(k2_zfmisc_1(X41,X41)))), inference(variable_rename,[status(thm)],[dt_k6_partfun1])).
% 0.14/0.38  cnf(c_0_35, negated_conjecture, (k6_yellow_1(k1_xboole_0,esk2_0)!=g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.38  cnf(c_0_36, plain, (k6_partfun1(X1)=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.14/0.38  cnf(c_0_37, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.14/0.38  cnf(c_0_38, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.14/0.38  cnf(c_0_39, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.14/0.38  cnf(c_0_40, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.14/0.38  cnf(c_0_41, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.14/0.38  cnf(c_0_42, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.14/0.38  cnf(c_0_43, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.14/0.38  cnf(c_0_44, plain, (k5_yellow_1(k1_xboole_0,X1)=g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))|~v1_relat_1(X1)|~v4_relat_1(X1,k1_xboole_0)|~v1_funct_1(X1)|~v1_partfun1(X1,k1_xboole_0)|~v1_yellow_1(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.14/0.38  fof(c_0_45, plain, ![X8]:(~v1_xboole_0(X8)|X8=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.14/0.38  cnf(c_0_46, plain, (v1_xboole_0(k2_funcop_1(k1_xboole_0,X1))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.14/0.38  cnf(c_0_47, plain, (k7_funcop_1(X1,X2)=k2_funcop_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.14/0.38  cnf(c_0_48, plain, (v1_partfun1(k6_partfun1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.14/0.38  fof(c_0_49, plain, ![X37]:v1_relat_1(k6_relat_1(X37)), inference(variable_rename,[status(thm)],[dt_k6_relat_1])).
% 0.14/0.38  fof(c_0_50, plain, ![X46, X47]:(~l1_orders_2(X47)|v1_yellow_1(k2_funcop_1(X46,X47))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc10_yellow_1])])).
% 0.14/0.38  cnf(c_0_51, negated_conjecture, (k6_yellow_1(k1_xboole_0,esk2_0)!=g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_relat_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_36]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_42]), c_0_42]), c_0_43]), c_0_43])).
% 0.14/0.38  cnf(c_0_52, plain, (k5_yellow_1(k1_xboole_0,X1)=g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_relat_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_yellow_1(X1)|~v4_relat_1(X1,k1_xboole_0)|~v1_partfun1(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_36]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_42]), c_0_42]), c_0_43]), c_0_43])).
% 0.14/0.38  fof(c_0_53, plain, ![X44, X45]:(~l1_orders_2(X45)|k6_yellow_1(X44,X45)=k5_yellow_1(X44,k7_funcop_1(X44,X45))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_yellow_1])])).
% 0.14/0.38  cnf(c_0_54, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.14/0.38  cnf(c_0_55, plain, (v1_xboole_0(k7_funcop_1(k1_xboole_0,X1))), inference(rw,[status(thm)],[c_0_46, c_0_47])).
% 0.14/0.38  cnf(c_0_56, plain, (v1_partfun1(k6_relat_1(X1),X1)), inference(rw,[status(thm)],[c_0_48, c_0_36])).
% 0.14/0.38  cnf(c_0_57, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t81_relat_1])).
% 0.14/0.38  fof(c_0_58, plain, ![X38, X39]:(v4_relat_1(k1_xboole_0,X38)&v5_relat_1(k1_xboole_0,X39)), inference(variable_rename,[status(thm)],[l222_relat_1])).
% 0.14/0.38  cnf(c_0_59, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.14/0.38  cnf(c_0_60, plain, (v1_yellow_1(k2_funcop_1(X2,X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.14/0.38  cnf(c_0_61, negated_conjecture, (k5_yellow_1(k1_xboole_0,X1)!=k6_yellow_1(k1_xboole_0,esk2_0)|~v1_yellow_1(X1)|~v1_partfun1(X1,k1_xboole_0)|~v1_funct_1(X1)|~v4_relat_1(X1,k1_xboole_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.14/0.38  cnf(c_0_62, plain, (k6_yellow_1(X2,X1)=k5_yellow_1(X2,k7_funcop_1(X2,X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.14/0.38  cnf(c_0_63, plain, (k7_funcop_1(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.14/0.38  cnf(c_0_64, plain, (v1_partfun1(k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.14/0.38  cnf(c_0_65, plain, (v4_relat_1(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.14/0.38  cnf(c_0_66, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_59, c_0_57])).
% 0.14/0.38  cnf(c_0_67, plain, (v1_yellow_1(k7_funcop_1(X2,X1))|~l1_orders_2(X1)), inference(rw,[status(thm)],[c_0_60, c_0_47])).
% 0.14/0.38  cnf(c_0_68, negated_conjecture, (k6_yellow_1(k1_xboole_0,X1)!=k6_yellow_1(k1_xboole_0,esk2_0)|~v1_yellow_1(k1_xboole_0)|~l1_orders_2(X1)|~v1_funct_1(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63]), c_0_63]), c_0_64]), c_0_63]), c_0_63]), c_0_65]), c_0_63]), c_0_66])])).
% 0.14/0.38  cnf(c_0_69, negated_conjecture, (l1_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.38  cnf(c_0_70, plain, (v1_yellow_1(k1_xboole_0)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_67, c_0_63])).
% 0.14/0.38  cnf(c_0_71, negated_conjecture, (~v1_yellow_1(k1_xboole_0)|~v1_funct_1(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_68]), c_0_69])])).
% 0.14/0.38  cnf(c_0_72, negated_conjecture, (v1_yellow_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_70, c_0_69])).
% 0.14/0.38  fof(c_0_73, plain, ![X40]:(~v1_xboole_0(X40)|v1_funct_1(X40)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_1])])).
% 0.14/0.38  cnf(c_0_74, negated_conjecture, (~v1_funct_1(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_72])])).
% 0.14/0.38  cnf(c_0_75, plain, (v1_funct_1(X1)|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.14/0.38  cnf(c_0_76, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.14/0.38  cnf(c_0_77, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_76])]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 78
% 0.14/0.38  # Proof object clause steps            : 37
% 0.14/0.38  # Proof object formula steps           : 41
% 0.14/0.38  # Proof object conjectures             : 12
% 0.14/0.38  # Proof object clause conjectures      : 9
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 22
% 0.14/0.38  # Proof object initial formulas used   : 21
% 0.14/0.38  # Proof object generating inferences   : 9
% 0.14/0.38  # Proof object simplifying inferences  : 48
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 22
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 29
% 0.14/0.38  # Removed in clause preprocessing      : 9
% 0.14/0.38  # Initial clauses in saturation        : 20
% 0.14/0.38  # Processed clauses                    : 49
% 0.14/0.38  # ...of these trivial                  : 0
% 0.14/0.38  # ...subsumed                          : 0
% 0.14/0.38  # ...remaining for further processing  : 49
% 0.14/0.38  # Other redundant clauses eliminated   : 0
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 1
% 0.14/0.38  # Backward-rewritten                   : 3
% 0.14/0.38  # Generated clauses                    : 15
% 0.14/0.38  # ...of the previous two non-trivial   : 15
% 0.14/0.38  # Contextual simplify-reflections      : 0
% 0.14/0.38  # Paramodulations                      : 14
% 0.14/0.38  # Factorizations                       : 0
% 0.14/0.38  # Equation resolutions                 : 1
% 0.14/0.38  # Propositional unsat checks           : 0
% 0.14/0.38  #    Propositional check models        : 0
% 0.14/0.38  #    Propositional check unsatisfiable : 0
% 0.14/0.38  #    Propositional clauses             : 0
% 0.14/0.38  #    Propositional clauses after purity: 0
% 0.14/0.38  #    Propositional unsat core size     : 0
% 0.14/0.38  #    Propositional preprocessing time  : 0.000
% 0.14/0.38  #    Propositional encoding time       : 0.000
% 0.14/0.38  #    Propositional solver time         : 0.000
% 0.14/0.38  #    Success case prop preproc time    : 0.000
% 0.14/0.38  #    Success case prop encoding time   : 0.000
% 0.14/0.38  #    Success case prop solver time     : 0.000
% 0.14/0.38  # Current number of processed clauses  : 25
% 0.14/0.38  #    Positive orientable unit clauses  : 16
% 0.14/0.38  #    Positive unorientable unit clauses: 0
% 0.14/0.38  #    Negative unit clauses             : 3
% 0.14/0.38  #    Non-unit-clauses                  : 6
% 0.14/0.38  # Current number of unprocessed clauses: 6
% 0.14/0.38  # ...number of literals in the above   : 25
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 33
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 25
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 1
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 1
% 0.14/0.38  # Unit Clause-clause subsumption calls : 2
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 2
% 0.14/0.38  # BW rewrite match successes           : 2
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 1744
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.032 s
% 0.14/0.38  # System time              : 0.001 s
% 0.14/0.38  # Total time               : 0.033 s
% 0.14/0.38  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------

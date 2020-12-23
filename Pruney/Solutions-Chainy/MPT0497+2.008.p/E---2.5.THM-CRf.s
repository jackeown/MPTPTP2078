%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:49:34 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 278 expanded)
%              Number of clauses        :   43 ( 113 expanded)
%              Number of leaves         :   19 (  79 expanded)
%              Depth                    :   10
%              Number of atoms          :  131 ( 440 expanded)
%              Number of equality atoms :   69 ( 280 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t90_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k1_relat_1(k7_relat_1(X2,X1)) = k3_xboole_0(k1_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(t85_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_xboole_0(X1,k4_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t95_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k7_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

fof(t67_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_xboole_0(k2_relat_1(X1),k1_relat_1(X2))
           => k5_relat_1(X1,X2) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_relat_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t94_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k5_relat_1(k6_relat_1(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(c_0_19,plain,(
    ! [X38,X39] : k1_setfam_1(k2_tarski(X38,X39)) = k3_xboole_0(X38,X39) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_20,plain,(
    ! [X18,X19] : k1_enumset1(X18,X18,X19) = k2_tarski(X18,X19) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_21,plain,(
    ! [X11,X12] : k4_xboole_0(X11,X12) = k5_xboole_0(X11,k3_xboole_0(X11,X12)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_22,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_24,plain,(
    ! [X44,X45] :
      ( ~ v1_relat_1(X45)
      | k1_relat_1(k7_relat_1(X45,X44)) = k3_xboole_0(k1_relat_1(X45),X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).

fof(c_0_25,plain,(
    ! [X20,X21,X22] : k2_enumset1(X20,X20,X21,X22) = k1_enumset1(X20,X21,X22) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_26,plain,(
    ! [X23,X24,X25,X26] : k3_enumset1(X23,X23,X24,X25,X26) = k2_enumset1(X23,X24,X25,X26) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_27,plain,(
    ! [X27,X28,X29,X30,X31] : k4_enumset1(X27,X27,X28,X29,X30,X31) = k3_enumset1(X27,X28,X29,X30,X31) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_28,plain,(
    ! [X32,X33,X34,X35,X36,X37] : k5_enumset1(X32,X32,X33,X34,X35,X36,X37) = k4_enumset1(X32,X33,X34,X35,X36,X37) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_29,plain,(
    ! [X15,X16,X17] :
      ( ~ r1_tarski(X15,X16)
      | r1_xboole_0(X15,k4_xboole_0(X17,X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_xboole_1])])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_32,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k3_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_37,plain,(
    ! [X40] : v1_relat_1(k6_relat_1(X40)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

fof(c_0_38,plain,(
    ! [X43] :
      ( k1_relat_1(k6_relat_1(X43)) = X43
      & k2_relat_1(k6_relat_1(X43)) = X43 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

cnf(c_0_39,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_40,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_41,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k1_setfam_1(k5_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_31]),c_0_33]),c_0_34]),c_0_35]),c_0_36])).

cnf(c_0_42,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_43,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

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

fof(c_0_45,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( k7_relat_1(X2,X1) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(X2),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t95_relat_1])).

cnf(c_0_46,plain,
    ( r1_xboole_0(X1,k5_xboole_0(X3,k1_setfam_1(k5_enumset1(X3,X3,X3,X3,X3,X3,X2))))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_40]),c_0_33]),c_0_34]),c_0_35]),c_0_36])).

cnf(c_0_47,plain,
    ( k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_43])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_49,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & ( k7_relat_1(esk2_0,esk1_0) != k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(esk2_0),esk1_0) )
    & ( k7_relat_1(esk2_0,esk1_0) = k1_xboole_0
      | r1_xboole_0(k1_relat_1(esk2_0),esk1_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_45])])])).

fof(c_0_50,plain,(
    ! [X41,X42] :
      ( ~ v1_relat_1(X41)
      | ~ v1_relat_1(X42)
      | ~ r1_xboole_0(k2_relat_1(X41),k1_relat_1(X42))
      | k5_relat_1(X41,X42) = k1_xboole_0 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_relat_1])])])).

fof(c_0_51,plain,(
    ! [X7,X8] :
      ( ~ r1_xboole_0(X7,X8)
      | r1_xboole_0(X8,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

fof(c_0_52,plain,(
    ! [X46,X47] :
      ( ~ v1_relat_1(X47)
      | k7_relat_1(X47,X46) = k5_relat_1(k6_relat_1(X46),X47) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).

fof(c_0_53,plain,(
    ! [X14] : k4_xboole_0(X14,k1_xboole_0) = X14 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_54,plain,(
    ! [X13] : k3_xboole_0(X13,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

cnf(c_0_55,plain,
    ( r1_xboole_0(X1,k5_xboole_0(X2,k1_relat_1(k7_relat_1(k6_relat_1(X2),X3))))
    | ~ r1_tarski(X1,X3) ),
    inference(rw,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_56,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_48])).

cnf(c_0_57,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(X1)),X2)) = k1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_41,c_0_47])).

cnf(c_0_58,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_59,plain,
    ( k5_relat_1(X1,X2) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_xboole_0(k2_relat_1(X1),k1_relat_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_60,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_61,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_62,negated_conjecture,
    ( k7_relat_1(esk2_0,esk1_0) = k1_xboole_0
    | r1_xboole_0(k1_relat_1(esk2_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_63,plain,
    ( k7_relat_1(X1,X2) = k5_relat_1(k6_relat_1(X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_64,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_65,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_66,plain,
    ( r1_xboole_0(X1,k5_xboole_0(X2,k1_relat_1(k7_relat_1(k6_relat_1(X2),X1)))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_67,negated_conjecture,
    ( k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(esk2_0)),X1)) = k1_relat_1(k7_relat_1(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_68,plain,
    ( k5_relat_1(k6_relat_1(X1),X2) = k1_xboole_0
    | ~ v1_relat_1(X2)
    | ~ r1_xboole_0(X1,k1_relat_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_42])])).

cnf(c_0_69,negated_conjecture,
    ( k7_relat_1(esk2_0,esk1_0) = k1_xboole_0
    | r1_xboole_0(esk1_0,k1_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_70,negated_conjecture,
    ( k5_relat_1(k6_relat_1(X1),esk2_0) = k7_relat_1(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_58])).

cnf(c_0_71,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,k1_xboole_0))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_40]),c_0_33]),c_0_34]),c_0_35]),c_0_36])).

cnf(c_0_72,plain,
    ( k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_31]),c_0_33]),c_0_34]),c_0_35]),c_0_36])).

cnf(c_0_73,negated_conjecture,
    ( r1_xboole_0(X1,k5_xboole_0(k1_relat_1(esk2_0),k1_relat_1(k7_relat_1(esk2_0,X1)))) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_74,negated_conjecture,
    ( k7_relat_1(esk2_0,esk1_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70]),c_0_58])])).

cnf(c_0_75,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_76,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_77,negated_conjecture,
    ( k7_relat_1(esk2_0,esk1_0) != k1_xboole_0
    | ~ r1_xboole_0(k1_relat_1(esk2_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_78,negated_conjecture,
    ( r1_xboole_0(esk1_0,k1_relat_1(esk2_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_75]),c_0_76])).

cnf(c_0_79,negated_conjecture,
    ( ~ r1_xboole_0(k1_relat_1(esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_77,c_0_74])])).

cnf(c_0_80,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_78]),c_0_79]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:50:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S03EI
% 0.14/0.40  # and selection function SelectLComplex.
% 0.14/0.40  #
% 0.14/0.40  # Preprocessing time       : 0.041 s
% 0.14/0.40  # Presaturation interreduction done
% 0.14/0.40  
% 0.14/0.40  # Proof found!
% 0.14/0.40  # SZS status Theorem
% 0.14/0.40  # SZS output start CNFRefutation
% 0.14/0.40  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.14/0.40  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.14/0.40  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.14/0.40  fof(t90_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k1_relat_1(k7_relat_1(X2,X1))=k3_xboole_0(k1_relat_1(X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 0.14/0.40  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.14/0.40  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.14/0.40  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.14/0.40  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.14/0.40  fof(t85_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_xboole_0(X1,k4_xboole_0(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 0.14/0.40  fof(dt_k6_relat_1, axiom, ![X1]:v1_relat_1(k6_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 0.14/0.40  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 0.14/0.40  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.14/0.40  fof(t95_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(k7_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 0.14/0.40  fof(t67_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_xboole_0(k2_relat_1(X1),k1_relat_1(X2))=>k5_relat_1(X1,X2)=k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_relat_1)).
% 0.14/0.40  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.14/0.40  fof(t94_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k5_relat_1(k6_relat_1(X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 0.14/0.40  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 0.14/0.40  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 0.14/0.40  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 0.14/0.40  fof(c_0_19, plain, ![X38, X39]:k1_setfam_1(k2_tarski(X38,X39))=k3_xboole_0(X38,X39), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.14/0.40  fof(c_0_20, plain, ![X18, X19]:k1_enumset1(X18,X18,X19)=k2_tarski(X18,X19), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.14/0.40  fof(c_0_21, plain, ![X11, X12]:k4_xboole_0(X11,X12)=k5_xboole_0(X11,k3_xboole_0(X11,X12)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.14/0.40  cnf(c_0_22, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.14/0.40  cnf(c_0_23, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.40  fof(c_0_24, plain, ![X44, X45]:(~v1_relat_1(X45)|k1_relat_1(k7_relat_1(X45,X44))=k3_xboole_0(k1_relat_1(X45),X44)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).
% 0.14/0.40  fof(c_0_25, plain, ![X20, X21, X22]:k2_enumset1(X20,X20,X21,X22)=k1_enumset1(X20,X21,X22), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.14/0.40  fof(c_0_26, plain, ![X23, X24, X25, X26]:k3_enumset1(X23,X23,X24,X25,X26)=k2_enumset1(X23,X24,X25,X26), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.14/0.40  fof(c_0_27, plain, ![X27, X28, X29, X30, X31]:k4_enumset1(X27,X27,X28,X29,X30,X31)=k3_enumset1(X27,X28,X29,X30,X31), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.14/0.40  fof(c_0_28, plain, ![X32, X33, X34, X35, X36, X37]:k5_enumset1(X32,X32,X33,X34,X35,X36,X37)=k4_enumset1(X32,X33,X34,X35,X36,X37), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.14/0.40  fof(c_0_29, plain, ![X15, X16, X17]:(~r1_tarski(X15,X16)|r1_xboole_0(X15,k4_xboole_0(X17,X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_xboole_1])])).
% 0.14/0.40  cnf(c_0_30, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.40  cnf(c_0_31, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 0.14/0.40  cnf(c_0_32, plain, (k1_relat_1(k7_relat_1(X1,X2))=k3_xboole_0(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.14/0.40  cnf(c_0_33, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.14/0.40  cnf(c_0_34, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.14/0.40  cnf(c_0_35, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.14/0.40  cnf(c_0_36, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.14/0.40  fof(c_0_37, plain, ![X40]:v1_relat_1(k6_relat_1(X40)), inference(variable_rename,[status(thm)],[dt_k6_relat_1])).
% 0.14/0.40  fof(c_0_38, plain, ![X43]:(k1_relat_1(k6_relat_1(X43))=X43&k2_relat_1(k6_relat_1(X43))=X43), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.14/0.40  cnf(c_0_39, plain, (r1_xboole_0(X1,k4_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.14/0.40  cnf(c_0_40, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_30, c_0_31])).
% 0.14/0.40  cnf(c_0_41, plain, (k1_relat_1(k7_relat_1(X1,X2))=k1_setfam_1(k5_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_31]), c_0_33]), c_0_34]), c_0_35]), c_0_36])).
% 0.14/0.40  cnf(c_0_42, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.14/0.40  cnf(c_0_43, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.14/0.40  fof(c_0_44, plain, ![X9, X10]:(((r1_tarski(X9,X10)|X9!=X10)&(r1_tarski(X10,X9)|X9!=X10))&(~r1_tarski(X9,X10)|~r1_tarski(X10,X9)|X9=X10)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.14/0.40  fof(c_0_45, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(k7_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k1_relat_1(X2),X1)))), inference(assume_negation,[status(cth)],[t95_relat_1])).
% 0.14/0.40  cnf(c_0_46, plain, (r1_xboole_0(X1,k5_xboole_0(X3,k1_setfam_1(k5_enumset1(X3,X3,X3,X3,X3,X3,X2))))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_40]), c_0_33]), c_0_34]), c_0_35]), c_0_36])).
% 0.14/0.40  cnf(c_0_47, plain, (k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2))=k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_43])).
% 0.14/0.40  cnf(c_0_48, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.14/0.40  fof(c_0_49, negated_conjecture, (v1_relat_1(esk2_0)&((k7_relat_1(esk2_0,esk1_0)!=k1_xboole_0|~r1_xboole_0(k1_relat_1(esk2_0),esk1_0))&(k7_relat_1(esk2_0,esk1_0)=k1_xboole_0|r1_xboole_0(k1_relat_1(esk2_0),esk1_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_45])])])).
% 0.14/0.40  fof(c_0_50, plain, ![X41, X42]:(~v1_relat_1(X41)|(~v1_relat_1(X42)|(~r1_xboole_0(k2_relat_1(X41),k1_relat_1(X42))|k5_relat_1(X41,X42)=k1_xboole_0))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_relat_1])])])).
% 0.14/0.40  fof(c_0_51, plain, ![X7, X8]:(~r1_xboole_0(X7,X8)|r1_xboole_0(X8,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.14/0.40  fof(c_0_52, plain, ![X46, X47]:(~v1_relat_1(X47)|k7_relat_1(X47,X46)=k5_relat_1(k6_relat_1(X46),X47)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).
% 0.14/0.40  fof(c_0_53, plain, ![X14]:k4_xboole_0(X14,k1_xboole_0)=X14, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.14/0.40  fof(c_0_54, plain, ![X13]:k3_xboole_0(X13,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.14/0.40  cnf(c_0_55, plain, (r1_xboole_0(X1,k5_xboole_0(X2,k1_relat_1(k7_relat_1(k6_relat_1(X2),X3))))|~r1_tarski(X1,X3)), inference(rw,[status(thm)],[c_0_46, c_0_47])).
% 0.14/0.40  cnf(c_0_56, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_48])).
% 0.14/0.40  cnf(c_0_57, plain, (k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(X1)),X2))=k1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_41, c_0_47])).
% 0.14/0.40  cnf(c_0_58, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.14/0.40  cnf(c_0_59, plain, (k5_relat_1(X1,X2)=k1_xboole_0|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_xboole_0(k2_relat_1(X1),k1_relat_1(X2))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.14/0.40  cnf(c_0_60, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.14/0.40  cnf(c_0_61, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.14/0.40  cnf(c_0_62, negated_conjecture, (k7_relat_1(esk2_0,esk1_0)=k1_xboole_0|r1_xboole_0(k1_relat_1(esk2_0),esk1_0)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.14/0.40  cnf(c_0_63, plain, (k7_relat_1(X1,X2)=k5_relat_1(k6_relat_1(X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.14/0.40  cnf(c_0_64, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.14/0.40  cnf(c_0_65, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.14/0.40  cnf(c_0_66, plain, (r1_xboole_0(X1,k5_xboole_0(X2,k1_relat_1(k7_relat_1(k6_relat_1(X2),X1))))), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.14/0.40  cnf(c_0_67, negated_conjecture, (k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(esk2_0)),X1))=k1_relat_1(k7_relat_1(esk2_0,X1))), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.14/0.40  cnf(c_0_68, plain, (k5_relat_1(k6_relat_1(X1),X2)=k1_xboole_0|~v1_relat_1(X2)|~r1_xboole_0(X1,k1_relat_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_42])])).
% 0.14/0.40  cnf(c_0_69, negated_conjecture, (k7_relat_1(esk2_0,esk1_0)=k1_xboole_0|r1_xboole_0(esk1_0,k1_relat_1(esk2_0))), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.14/0.40  cnf(c_0_70, negated_conjecture, (k5_relat_1(k6_relat_1(X1),esk2_0)=k7_relat_1(esk2_0,X1)), inference(spm,[status(thm)],[c_0_63, c_0_58])).
% 0.14/0.40  cnf(c_0_71, plain, (k5_xboole_0(X1,k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,k1_xboole_0)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_40]), c_0_33]), c_0_34]), c_0_35]), c_0_36])).
% 0.14/0.40  cnf(c_0_72, plain, (k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_31]), c_0_33]), c_0_34]), c_0_35]), c_0_36])).
% 0.14/0.40  cnf(c_0_73, negated_conjecture, (r1_xboole_0(X1,k5_xboole_0(k1_relat_1(esk2_0),k1_relat_1(k7_relat_1(esk2_0,X1))))), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.14/0.40  cnf(c_0_74, negated_conjecture, (k7_relat_1(esk2_0,esk1_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_70]), c_0_58])])).
% 0.14/0.40  cnf(c_0_75, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.14/0.40  cnf(c_0_76, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_71, c_0_72])).
% 0.14/0.40  cnf(c_0_77, negated_conjecture, (k7_relat_1(esk2_0,esk1_0)!=k1_xboole_0|~r1_xboole_0(k1_relat_1(esk2_0),esk1_0)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.14/0.40  cnf(c_0_78, negated_conjecture, (r1_xboole_0(esk1_0,k1_relat_1(esk2_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_75]), c_0_76])).
% 0.14/0.40  cnf(c_0_79, negated_conjecture, (~r1_xboole_0(k1_relat_1(esk2_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_77, c_0_74])])).
% 0.14/0.40  cnf(c_0_80, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_78]), c_0_79]), ['proof']).
% 0.14/0.40  # SZS output end CNFRefutation
% 0.14/0.40  # Proof object total steps             : 81
% 0.14/0.40  # Proof object clause steps            : 43
% 0.14/0.40  # Proof object formula steps           : 38
% 0.14/0.40  # Proof object conjectures             : 14
% 0.14/0.40  # Proof object clause conjectures      : 11
% 0.14/0.40  # Proof object formula conjectures     : 3
% 0.14/0.40  # Proof object initial clauses used    : 22
% 0.14/0.40  # Proof object initial formulas used   : 19
% 0.14/0.40  # Proof object generating inferences   : 10
% 0.14/0.40  # Proof object simplifying inferences  : 42
% 0.14/0.40  # Training examples: 0 positive, 0 negative
% 0.14/0.40  # Parsed axioms                        : 19
% 0.14/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.40  # Initial clauses                      : 25
% 0.14/0.40  # Removed in clause preprocessing      : 7
% 0.14/0.40  # Initial clauses in saturation        : 18
% 0.14/0.40  # Processed clauses                    : 80
% 0.14/0.40  # ...of these trivial                  : 2
% 0.14/0.40  # ...subsumed                          : 4
% 0.14/0.40  # ...remaining for further processing  : 74
% 0.14/0.40  # Other redundant clauses eliminated   : 2
% 0.14/0.40  # Clauses deleted for lack of memory   : 0
% 0.14/0.40  # Backward-subsumed                    : 0
% 0.14/0.40  # Backward-rewritten                   : 17
% 0.14/0.40  # Generated clauses                    : 57
% 0.14/0.40  # ...of the previous two non-trivial   : 57
% 0.14/0.40  # Contextual simplify-reflections      : 0
% 0.14/0.40  # Paramodulations                      : 55
% 0.14/0.40  # Factorizations                       : 0
% 0.14/0.40  # Equation resolutions                 : 2
% 0.14/0.40  # Propositional unsat checks           : 0
% 0.14/0.40  #    Propositional check models        : 0
% 0.14/0.40  #    Propositional check unsatisfiable : 0
% 0.14/0.40  #    Propositional clauses             : 0
% 0.14/0.40  #    Propositional clauses after purity: 0
% 0.14/0.40  #    Propositional unsat core size     : 0
% 0.14/0.40  #    Propositional preprocessing time  : 0.000
% 0.14/0.40  #    Propositional encoding time       : 0.000
% 0.14/0.40  #    Propositional solver time         : 0.000
% 0.14/0.40  #    Success case prop preproc time    : 0.000
% 0.14/0.40  #    Success case prop encoding time   : 0.000
% 0.14/0.40  #    Success case prop solver time     : 0.000
% 0.14/0.40  # Current number of processed clauses  : 38
% 0.14/0.40  #    Positive orientable unit clauses  : 22
% 0.14/0.40  #    Positive unorientable unit clauses: 0
% 0.14/0.40  #    Negative unit clauses             : 1
% 0.14/0.40  #    Non-unit-clauses                  : 15
% 0.14/0.40  # Current number of unprocessed clauses: 12
% 0.14/0.40  # ...number of literals in the above   : 24
% 0.14/0.40  # Current number of archived formulas  : 0
% 0.14/0.40  # Current number of archived clauses   : 41
% 0.14/0.40  # Clause-clause subsumption calls (NU) : 69
% 0.14/0.40  # Rec. Clause-clause subsumption calls : 56
% 0.14/0.40  # Non-unit clause-clause subsumptions  : 4
% 0.14/0.40  # Unit Clause-clause subsumption calls : 4
% 0.14/0.40  # Rewrite failures with RHS unbound    : 0
% 0.14/0.40  # BW rewrite match attempts            : 16
% 0.14/0.40  # BW rewrite match successes           : 11
% 0.14/0.40  # Condensation attempts                : 0
% 0.14/0.40  # Condensation successes               : 0
% 0.14/0.40  # Termbank termtop insertions          : 2243
% 0.14/0.40  
% 0.14/0.40  # -------------------------------------------------
% 0.14/0.40  # User time                : 0.046 s
% 0.14/0.40  # System time              : 0.006 s
% 0.14/0.40  # Total time               : 0.052 s
% 0.14/0.40  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------

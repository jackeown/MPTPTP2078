%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:54:32 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   93 (3122 expanded)
%              Number of clauses        :   64 (1319 expanded)
%              Number of leaves         :   14 ( 899 expanded)
%              Depth                    :   13
%              Number of atoms          :  180 (4034 expanded)
%              Number of equality atoms :   90 (3163 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t182_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(t43_funct_1,axiom,(
    ! [X1,X2] : k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) = k6_relat_1(k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

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

fof(t181_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => k10_relat_1(k5_relat_1(X2,X3),X1) = k10_relat_1(X2,k10_relat_1(X3,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t181_relat_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t139_funct_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k10_relat_1(k7_relat_1(X3,X1),X2) = k3_xboole_0(X1,k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

fof(t94_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k5_relat_1(k6_relat_1(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(c_0_14,plain,(
    ! [X36,X37] : k1_setfam_1(k2_tarski(X36,X37)) = k3_xboole_0(X36,X37) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_15,plain,(
    ! [X16,X17] : k1_enumset1(X16,X16,X17) = k2_tarski(X16,X17) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_16,plain,(
    ! [X41,X42] :
      ( ~ v1_relat_1(X41)
      | ~ v1_relat_1(X42)
      | k1_relat_1(k5_relat_1(X41,X42)) = k10_relat_1(X41,k1_relat_1(X42)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).

fof(c_0_17,plain,(
    ! [X46] :
      ( v1_relat_1(k6_relat_1(X46))
      & v1_funct_1(k6_relat_1(X46)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

fof(c_0_18,plain,(
    ! [X43] :
      ( k1_relat_1(k6_relat_1(X43)) = X43
      & k2_relat_1(k6_relat_1(X43)) = X43 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_19,plain,(
    ! [X47,X48] : k5_relat_1(k6_relat_1(X48),k6_relat_1(X47)) = k6_relat_1(k3_xboole_0(X47,X48)) ),
    inference(variable_rename,[status(thm)],[t43_funct_1])).

cnf(c_0_20,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_22,plain,(
    ! [X18,X19,X20] : k2_enumset1(X18,X18,X19,X20) = k1_enumset1(X18,X19,X20) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_23,plain,(
    ! [X21,X22,X23,X24] : k3_enumset1(X21,X21,X22,X23,X24) = k2_enumset1(X21,X22,X23,X24) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_24,plain,(
    ! [X25,X26,X27,X28,X29] : k4_enumset1(X25,X25,X26,X27,X28,X29) = k3_enumset1(X25,X26,X27,X28,X29) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_25,plain,(
    ! [X30,X31,X32,X33,X34,X35] : k5_enumset1(X30,X30,X31,X32,X33,X34,X35) = k4_enumset1(X30,X31,X32,X33,X34,X35) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_26,plain,(
    ! [X38,X39,X40] :
      ( ~ v1_relat_1(X39)
      | ~ v1_relat_1(X40)
      | k10_relat_1(k5_relat_1(X39,X40),X38) = k10_relat_1(X39,k10_relat_1(X40,X38)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t181_relat_1])])])).

cnf(c_0_27,plain,
    ( k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_28,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_29,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_30,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(k3_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_31,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_32,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,plain,
    ( k10_relat_1(k5_relat_1(X1,X2),X3) = k10_relat_1(X1,k10_relat_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,plain,
    ( k10_relat_1(X1,X2) = k1_relat_1(k5_relat_1(X1,k6_relat_1(X2)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])).

cnf(c_0_38,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(k1_setfam_1(k5_enumset1(X2,X2,X2,X2,X2,X2,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_35])).

fof(c_0_39,plain,(
    ! [X7,X8,X9,X10,X11,X12,X13,X14] :
      ( ( r2_hidden(X10,X7)
        | ~ r2_hidden(X10,X9)
        | X9 != k3_xboole_0(X7,X8) )
      & ( r2_hidden(X10,X8)
        | ~ r2_hidden(X10,X9)
        | X9 != k3_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X11,X7)
        | ~ r2_hidden(X11,X8)
        | r2_hidden(X11,X9)
        | X9 != k3_xboole_0(X7,X8) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X12)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X13)
        | X14 = k3_xboole_0(X12,X13) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X12)
        | r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k3_xboole_0(X12,X13) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X13)
        | r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k3_xboole_0(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_40,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => k10_relat_1(k7_relat_1(X3,X1),X2) = k3_xboole_0(X1,k10_relat_1(X3,X2)) ) ),
    inference(assume_negation,[status(cth)],[t139_funct_1])).

cnf(c_0_41,plain,
    ( k10_relat_1(k5_relat_1(X1,k6_relat_1(X2)),X3) = k10_relat_1(X1,k10_relat_1(k6_relat_1(X2),X3))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_28])).

cnf(c_0_42,plain,
    ( k10_relat_1(k6_relat_1(X1),X2) = k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_28])).

cnf(c_0_43,plain,
    ( v1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_38])).

cnf(c_0_44,plain,
    ( k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)) = k1_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_38])).

cnf(c_0_45,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_47,negated_conjecture,
    ( v1_relat_1(esk4_0)
    & k10_relat_1(k7_relat_1(esk4_0,esk2_0),esk3_0) != k3_xboole_0(esk2_0,k10_relat_1(esk4_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_40])])])).

fof(c_0_48,plain,(
    ! [X44,X45] :
      ( ~ v1_relat_1(X45)
      | k7_relat_1(X45,X44) = k5_relat_1(k6_relat_1(X44),X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).

cnf(c_0_49,plain,
    ( k10_relat_1(k5_relat_1(X1,k6_relat_1(X2)),X3) = k10_relat_1(X1,k1_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X3))))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_50,plain,
    ( k10_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),X3) = k1_relat_1(k5_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),k6_relat_1(X3))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_43])).

cnf(c_0_51,plain,
    ( k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) ),
    inference(rw,[status(thm)],[c_0_38,c_0_44])).

cnf(c_0_52,plain,
    ( X3 = k3_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_53,plain,
    ( X3 = k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_35])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,X2)
    | X3 != k1_setfam_1(k5_enumset1(X2,X2,X2,X2,X2,X2,X4))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_35])).

cnf(c_0_55,negated_conjecture,
    ( k10_relat_1(k7_relat_1(esk4_0,esk2_0),esk3_0) != k3_xboole_0(esk2_0,k10_relat_1(esk4_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_56,plain,
    ( k7_relat_1(X1,X2) = k5_relat_1(k6_relat_1(X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_57,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_58,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_59,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_60,plain,
    ( k1_relat_1(k5_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),k6_relat_1(X3))) = k1_relat_1(k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(X2),k6_relat_1(X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_28]),c_0_42]),c_0_50]),c_0_51])).

cnf(c_0_61,plain,
    ( X3 = k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2))
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_35])).

cnf(c_0_62,plain,
    ( X1 = k1_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X3)))
    | r2_hidden(esk1_3(X3,X2,X1),X3)
    | r2_hidden(esk1_3(X3,X2,X1),X1) ),
    inference(rw,[status(thm)],[c_0_53,c_0_44])).

cnf(c_0_63,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_setfam_1(k5_enumset1(X2,X2,X2,X2,X2,X2,X3))) ),
    inference(er,[status(thm)],[c_0_54])).

cnf(c_0_64,negated_conjecture,
    ( k10_relat_1(k7_relat_1(esk4_0,esk2_0),esk3_0) != k1_setfam_1(k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,k10_relat_1(esk4_0,esk3_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_35])).

cnf(c_0_65,negated_conjecture,
    ( k7_relat_1(esk4_0,X1) = k5_relat_1(k6_relat_1(X1),esk4_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_66,plain,
    ( X3 = k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_35])).

cnf(c_0_67,plain,
    ( r2_hidden(X1,X2)
    | X3 != k1_setfam_1(k5_enumset1(X4,X4,X4,X4,X4,X4,X2))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_35])).

cnf(c_0_68,plain,
    ( k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(X2),k6_relat_1(X3))))) = k5_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),k6_relat_1(X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_51]),c_0_60])).

cnf(c_0_69,plain,
    ( X1 = k1_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X3)))
    | ~ r2_hidden(esk1_3(X3,X2,X1),X1)
    | ~ r2_hidden(esk1_3(X3,X2,X1),X2)
    | ~ r2_hidden(esk1_3(X3,X2,X1),X3) ),
    inference(rw,[status(thm)],[c_0_61,c_0_44])).

cnf(c_0_70,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = X2
    | r2_hidden(esk1_3(X2,X1,X2),X2) ),
    inference(ef,[status(thm)],[c_0_62])).

cnf(c_0_71,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_relat_1(k5_relat_1(k6_relat_1(X3),k6_relat_1(X2)))) ),
    inference(rw,[status(thm)],[c_0_63,c_0_44])).

cnf(c_0_72,negated_conjecture,
    ( k10_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk4_0),esk3_0) != k1_setfam_1(k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,k10_relat_1(esk4_0,esk3_0))) ),
    inference(rw,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_73,negated_conjecture,
    ( k10_relat_1(esk4_0,X1) = k1_relat_1(k5_relat_1(esk4_0,k6_relat_1(X1))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_57])).

cnf(c_0_74,plain,
    ( X1 = k1_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X3)))
    | r2_hidden(esk1_3(X3,X2,X1),X2)
    | r2_hidden(esk1_3(X3,X2,X1),X1) ),
    inference(rw,[status(thm)],[c_0_66,c_0_44])).

cnf(c_0_75,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_setfam_1(k5_enumset1(X3,X3,X3,X3,X3,X3,X2))) ),
    inference(er,[status(thm)],[c_0_67])).

cnf(c_0_76,plain,
    ( k5_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),k6_relat_1(X3)) = k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(X2),k6_relat_1(X3))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_51]),c_0_68])).

cnf(c_0_77,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = X2
    | ~ r2_hidden(esk1_3(X2,X1,X2),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_70])).

cnf(c_0_78,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(X2),k6_relat_1(X3)))) = k1_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X3)))
    | r2_hidden(esk1_3(k1_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X3))),X1,k1_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X3)))),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_70]),c_0_51])).

cnf(c_0_79,negated_conjecture,
    ( k10_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk4_0),esk3_0) != k1_setfam_1(k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,k1_relat_1(k5_relat_1(esk4_0,k6_relat_1(esk3_0))))) ),
    inference(rw,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_80,negated_conjecture,
    ( k10_relat_1(k5_relat_1(X1,esk4_0),X2) = k10_relat_1(X1,k1_relat_1(k5_relat_1(esk4_0,k6_relat_1(X2))))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_57]),c_0_73])).

cnf(c_0_81,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = X1
    | r2_hidden(esk1_3(X2,X1,X1),X1) ),
    inference(ef,[status(thm)],[c_0_74])).

cnf(c_0_82,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X3)))) ),
    inference(rw,[status(thm)],[c_0_75,c_0_44])).

cnf(c_0_83,plain,
    ( k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(X2),k6_relat_1(X3))))) = k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(X2),k6_relat_1(X3))) ),
    inference(rw,[status(thm)],[c_0_68,c_0_76])).

cnf(c_0_84,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)))) = k1_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_51])])).

cnf(c_0_85,negated_conjecture,
    ( k10_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk4_0),esk3_0) != k1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(k5_relat_1(esk4_0,k6_relat_1(esk3_0)))),k6_relat_1(esk2_0))) ),
    inference(rw,[status(thm)],[c_0_79,c_0_44])).

cnf(c_0_86,negated_conjecture,
    ( k10_relat_1(k5_relat_1(k6_relat_1(X1),esk4_0),X2) = k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(k1_relat_1(k5_relat_1(esk4_0,k6_relat_1(X2)))))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_28]),c_0_42])).

cnf(c_0_87,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = X1
    | ~ r2_hidden(esk1_3(X2,X1,X1),X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_81]),c_0_81])).

cnf(c_0_88,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(X2),k6_relat_1(X3)))) = k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))
    | r2_hidden(esk1_3(X3,k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))),k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_81]),c_0_51]),c_0_76])).

cnf(c_0_89,plain,
    ( k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_51])).

cnf(c_0_90,negated_conjecture,
    ( k1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(k5_relat_1(esk4_0,k6_relat_1(esk3_0)))),k6_relat_1(esk2_0))) != k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(k1_relat_1(k5_relat_1(esk4_0,k6_relat_1(esk3_0)))))) ),
    inference(rw,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_91,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k1_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_51]),c_0_76]),c_0_89]),c_0_89])])).

cnf(c_0_92,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_90,c_0_91])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:04:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.47  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0YI
% 0.19/0.47  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.47  #
% 0.19/0.47  # Preprocessing time       : 0.027 s
% 0.19/0.47  # Presaturation interreduction done
% 0.19/0.47  
% 0.19/0.47  # Proof found!
% 0.19/0.47  # SZS status Theorem
% 0.19/0.47  # SZS output start CNFRefutation
% 0.19/0.47  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.19/0.47  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.47  fof(t182_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 0.19/0.47  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 0.19/0.47  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 0.19/0.47  fof(t43_funct_1, axiom, ![X1, X2]:k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))=k6_relat_1(k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 0.19/0.47  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.47  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.19/0.47  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.19/0.47  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.19/0.47  fof(t181_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>k10_relat_1(k5_relat_1(X2,X3),X1)=k10_relat_1(X2,k10_relat_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t181_relat_1)).
% 0.19/0.47  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.19/0.47  fof(t139_funct_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>k10_relat_1(k7_relat_1(X3,X1),X2)=k3_xboole_0(X1,k10_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 0.19/0.47  fof(t94_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k5_relat_1(k6_relat_1(X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 0.19/0.47  fof(c_0_14, plain, ![X36, X37]:k1_setfam_1(k2_tarski(X36,X37))=k3_xboole_0(X36,X37), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.19/0.47  fof(c_0_15, plain, ![X16, X17]:k1_enumset1(X16,X16,X17)=k2_tarski(X16,X17), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.47  fof(c_0_16, plain, ![X41, X42]:(~v1_relat_1(X41)|(~v1_relat_1(X42)|k1_relat_1(k5_relat_1(X41,X42))=k10_relat_1(X41,k1_relat_1(X42)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).
% 0.19/0.47  fof(c_0_17, plain, ![X46]:(v1_relat_1(k6_relat_1(X46))&v1_funct_1(k6_relat_1(X46))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 0.19/0.47  fof(c_0_18, plain, ![X43]:(k1_relat_1(k6_relat_1(X43))=X43&k2_relat_1(k6_relat_1(X43))=X43), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.19/0.47  fof(c_0_19, plain, ![X47, X48]:k5_relat_1(k6_relat_1(X48),k6_relat_1(X47))=k6_relat_1(k3_xboole_0(X47,X48)), inference(variable_rename,[status(thm)],[t43_funct_1])).
% 0.19/0.47  cnf(c_0_20, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.47  cnf(c_0_21, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.47  fof(c_0_22, plain, ![X18, X19, X20]:k2_enumset1(X18,X18,X19,X20)=k1_enumset1(X18,X19,X20), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.47  fof(c_0_23, plain, ![X21, X22, X23, X24]:k3_enumset1(X21,X21,X22,X23,X24)=k2_enumset1(X21,X22,X23,X24), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.19/0.47  fof(c_0_24, plain, ![X25, X26, X27, X28, X29]:k4_enumset1(X25,X25,X26,X27,X28,X29)=k3_enumset1(X25,X26,X27,X28,X29), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.19/0.47  fof(c_0_25, plain, ![X30, X31, X32, X33, X34, X35]:k5_enumset1(X30,X30,X31,X32,X33,X34,X35)=k4_enumset1(X30,X31,X32,X33,X34,X35), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.19/0.47  fof(c_0_26, plain, ![X38, X39, X40]:(~v1_relat_1(X39)|(~v1_relat_1(X40)|k10_relat_1(k5_relat_1(X39,X40),X38)=k10_relat_1(X39,k10_relat_1(X40,X38)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t181_relat_1])])])).
% 0.19/0.47  cnf(c_0_27, plain, (k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.47  cnf(c_0_28, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.47  cnf(c_0_29, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.47  cnf(c_0_30, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(k3_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.47  cnf(c_0_31, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.47  cnf(c_0_32, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.47  cnf(c_0_33, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.47  cnf(c_0_34, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.47  cnf(c_0_35, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.47  cnf(c_0_36, plain, (k10_relat_1(k5_relat_1(X1,X2),X3)=k10_relat_1(X1,k10_relat_1(X2,X3))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.47  cnf(c_0_37, plain, (k10_relat_1(X1,X2)=k1_relat_1(k5_relat_1(X1,k6_relat_1(X2)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29])).
% 0.19/0.47  cnf(c_0_38, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(k1_setfam_1(k5_enumset1(X2,X2,X2,X2,X2,X2,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_31]), c_0_32]), c_0_33]), c_0_34]), c_0_35])).
% 0.19/0.47  fof(c_0_39, plain, ![X7, X8, X9, X10, X11, X12, X13, X14]:((((r2_hidden(X10,X7)|~r2_hidden(X10,X9)|X9!=k3_xboole_0(X7,X8))&(r2_hidden(X10,X8)|~r2_hidden(X10,X9)|X9!=k3_xboole_0(X7,X8)))&(~r2_hidden(X11,X7)|~r2_hidden(X11,X8)|r2_hidden(X11,X9)|X9!=k3_xboole_0(X7,X8)))&((~r2_hidden(esk1_3(X12,X13,X14),X14)|(~r2_hidden(esk1_3(X12,X13,X14),X12)|~r2_hidden(esk1_3(X12,X13,X14),X13))|X14=k3_xboole_0(X12,X13))&((r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k3_xboole_0(X12,X13))&(r2_hidden(esk1_3(X12,X13,X14),X13)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k3_xboole_0(X12,X13))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.19/0.47  fof(c_0_40, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>k10_relat_1(k7_relat_1(X3,X1),X2)=k3_xboole_0(X1,k10_relat_1(X3,X2)))), inference(assume_negation,[status(cth)],[t139_funct_1])).
% 0.19/0.47  cnf(c_0_41, plain, (k10_relat_1(k5_relat_1(X1,k6_relat_1(X2)),X3)=k10_relat_1(X1,k10_relat_1(k6_relat_1(X2),X3))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_36, c_0_28])).
% 0.19/0.47  cnf(c_0_42, plain, (k10_relat_1(k6_relat_1(X1),X2)=k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))), inference(spm,[status(thm)],[c_0_37, c_0_28])).
% 0.19/0.47  cnf(c_0_43, plain, (v1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))), inference(spm,[status(thm)],[c_0_28, c_0_38])).
% 0.19/0.47  cnf(c_0_44, plain, (k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2))=k1_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)))), inference(spm,[status(thm)],[c_0_29, c_0_38])).
% 0.19/0.47  cnf(c_0_45, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.47  cnf(c_0_46, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.47  fof(c_0_47, negated_conjecture, (v1_relat_1(esk4_0)&k10_relat_1(k7_relat_1(esk4_0,esk2_0),esk3_0)!=k3_xboole_0(esk2_0,k10_relat_1(esk4_0,esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_40])])])).
% 0.19/0.47  fof(c_0_48, plain, ![X44, X45]:(~v1_relat_1(X45)|k7_relat_1(X45,X44)=k5_relat_1(k6_relat_1(X44),X45)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).
% 0.19/0.47  cnf(c_0_49, plain, (k10_relat_1(k5_relat_1(X1,k6_relat_1(X2)),X3)=k10_relat_1(X1,k1_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X3))))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_41, c_0_42])).
% 0.19/0.47  cnf(c_0_50, plain, (k10_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),X3)=k1_relat_1(k5_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),k6_relat_1(X3)))), inference(spm,[status(thm)],[c_0_37, c_0_43])).
% 0.19/0.47  cnf(c_0_51, plain, (k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))))=k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))), inference(rw,[status(thm)],[c_0_38, c_0_44])).
% 0.19/0.47  cnf(c_0_52, plain, (X3=k3_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.47  cnf(c_0_53, plain, (X3=k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_31]), c_0_32]), c_0_33]), c_0_34]), c_0_35])).
% 0.19/0.47  cnf(c_0_54, plain, (r2_hidden(X1,X2)|X3!=k1_setfam_1(k5_enumset1(X2,X2,X2,X2,X2,X2,X4))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_31]), c_0_32]), c_0_33]), c_0_34]), c_0_35])).
% 0.19/0.47  cnf(c_0_55, negated_conjecture, (k10_relat_1(k7_relat_1(esk4_0,esk2_0),esk3_0)!=k3_xboole_0(esk2_0,k10_relat_1(esk4_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.47  cnf(c_0_56, plain, (k7_relat_1(X1,X2)=k5_relat_1(k6_relat_1(X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.47  cnf(c_0_57, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.47  cnf(c_0_58, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.47  cnf(c_0_59, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.47  cnf(c_0_60, plain, (k1_relat_1(k5_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),k6_relat_1(X3)))=k1_relat_1(k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(X2),k6_relat_1(X3))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_28]), c_0_42]), c_0_50]), c_0_51])).
% 0.19/0.47  cnf(c_0_61, plain, (X3=k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2))|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X2)|~r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_31]), c_0_32]), c_0_33]), c_0_34]), c_0_35])).
% 0.19/0.47  cnf(c_0_62, plain, (X1=k1_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X3)))|r2_hidden(esk1_3(X3,X2,X1),X3)|r2_hidden(esk1_3(X3,X2,X1),X1)), inference(rw,[status(thm)],[c_0_53, c_0_44])).
% 0.19/0.47  cnf(c_0_63, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_setfam_1(k5_enumset1(X2,X2,X2,X2,X2,X2,X3)))), inference(er,[status(thm)],[c_0_54])).
% 0.19/0.47  cnf(c_0_64, negated_conjecture, (k10_relat_1(k7_relat_1(esk4_0,esk2_0),esk3_0)!=k1_setfam_1(k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,k10_relat_1(esk4_0,esk3_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_31]), c_0_32]), c_0_33]), c_0_34]), c_0_35])).
% 0.19/0.47  cnf(c_0_65, negated_conjecture, (k7_relat_1(esk4_0,X1)=k5_relat_1(k6_relat_1(X1),esk4_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.19/0.47  cnf(c_0_66, plain, (X3=k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_31]), c_0_32]), c_0_33]), c_0_34]), c_0_35])).
% 0.19/0.47  cnf(c_0_67, plain, (r2_hidden(X1,X2)|X3!=k1_setfam_1(k5_enumset1(X4,X4,X4,X4,X4,X4,X2))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_31]), c_0_32]), c_0_33]), c_0_34]), c_0_35])).
% 0.19/0.47  cnf(c_0_68, plain, (k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(X2),k6_relat_1(X3)))))=k5_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),k6_relat_1(X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_51]), c_0_60])).
% 0.19/0.47  cnf(c_0_69, plain, (X1=k1_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X3)))|~r2_hidden(esk1_3(X3,X2,X1),X1)|~r2_hidden(esk1_3(X3,X2,X1),X2)|~r2_hidden(esk1_3(X3,X2,X1),X3)), inference(rw,[status(thm)],[c_0_61, c_0_44])).
% 0.19/0.47  cnf(c_0_70, plain, (k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))=X2|r2_hidden(esk1_3(X2,X1,X2),X2)), inference(ef,[status(thm)],[c_0_62])).
% 0.19/0.47  cnf(c_0_71, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_relat_1(k5_relat_1(k6_relat_1(X3),k6_relat_1(X2))))), inference(rw,[status(thm)],[c_0_63, c_0_44])).
% 0.19/0.47  cnf(c_0_72, negated_conjecture, (k10_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk4_0),esk3_0)!=k1_setfam_1(k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,k10_relat_1(esk4_0,esk3_0)))), inference(rw,[status(thm)],[c_0_64, c_0_65])).
% 0.19/0.47  cnf(c_0_73, negated_conjecture, (k10_relat_1(esk4_0,X1)=k1_relat_1(k5_relat_1(esk4_0,k6_relat_1(X1)))), inference(spm,[status(thm)],[c_0_37, c_0_57])).
% 0.19/0.47  cnf(c_0_74, plain, (X1=k1_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X3)))|r2_hidden(esk1_3(X3,X2,X1),X2)|r2_hidden(esk1_3(X3,X2,X1),X1)), inference(rw,[status(thm)],[c_0_66, c_0_44])).
% 0.19/0.47  cnf(c_0_75, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_setfam_1(k5_enumset1(X3,X3,X3,X3,X3,X3,X2)))), inference(er,[status(thm)],[c_0_67])).
% 0.19/0.47  cnf(c_0_76, plain, (k5_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),k6_relat_1(X3))=k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(X2),k6_relat_1(X3)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_51]), c_0_68])).
% 0.19/0.47  cnf(c_0_77, plain, (k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))=X2|~r2_hidden(esk1_3(X2,X1,X2),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_70])).
% 0.19/0.47  cnf(c_0_78, plain, (k1_relat_1(k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(X2),k6_relat_1(X3))))=k1_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X3)))|r2_hidden(esk1_3(k1_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X3))),X1,k1_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X3)))),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_70]), c_0_51])).
% 0.19/0.47  cnf(c_0_79, negated_conjecture, (k10_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk4_0),esk3_0)!=k1_setfam_1(k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,k1_relat_1(k5_relat_1(esk4_0,k6_relat_1(esk3_0)))))), inference(rw,[status(thm)],[c_0_72, c_0_73])).
% 0.19/0.47  cnf(c_0_80, negated_conjecture, (k10_relat_1(k5_relat_1(X1,esk4_0),X2)=k10_relat_1(X1,k1_relat_1(k5_relat_1(esk4_0,k6_relat_1(X2))))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_57]), c_0_73])).
% 0.19/0.47  cnf(c_0_81, plain, (k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))=X1|r2_hidden(esk1_3(X2,X1,X1),X1)), inference(ef,[status(thm)],[c_0_74])).
% 0.19/0.47  cnf(c_0_82, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X3))))), inference(rw,[status(thm)],[c_0_75, c_0_44])).
% 0.19/0.47  cnf(c_0_83, plain, (k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(X2),k6_relat_1(X3)))))=k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(X2),k6_relat_1(X3)))), inference(rw,[status(thm)],[c_0_68, c_0_76])).
% 0.19/0.47  cnf(c_0_84, plain, (k1_relat_1(k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))))=k1_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_51])])).
% 0.19/0.47  cnf(c_0_85, negated_conjecture, (k10_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk4_0),esk3_0)!=k1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(k5_relat_1(esk4_0,k6_relat_1(esk3_0)))),k6_relat_1(esk2_0)))), inference(rw,[status(thm)],[c_0_79, c_0_44])).
% 0.19/0.47  cnf(c_0_86, negated_conjecture, (k10_relat_1(k5_relat_1(k6_relat_1(X1),esk4_0),X2)=k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(k1_relat_1(k5_relat_1(esk4_0,k6_relat_1(X2))))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_28]), c_0_42])).
% 0.19/0.47  cnf(c_0_87, plain, (k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))=X1|~r2_hidden(esk1_3(X2,X1,X1),X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_81]), c_0_81])).
% 0.19/0.47  cnf(c_0_88, plain, (k1_relat_1(k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(X2),k6_relat_1(X3))))=k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))|r2_hidden(esk1_3(X3,k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))),k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_81]), c_0_51]), c_0_76])).
% 0.19/0.47  cnf(c_0_89, plain, (k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)))=k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_51])).
% 0.19/0.47  cnf(c_0_90, negated_conjecture, (k1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(k5_relat_1(esk4_0,k6_relat_1(esk3_0)))),k6_relat_1(esk2_0)))!=k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(k1_relat_1(k5_relat_1(esk4_0,k6_relat_1(esk3_0))))))), inference(rw,[status(thm)],[c_0_85, c_0_86])).
% 0.19/0.47  cnf(c_0_91, plain, (k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))=k1_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_51]), c_0_76]), c_0_89]), c_0_89])])).
% 0.19/0.47  cnf(c_0_92, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_90, c_0_91])]), ['proof']).
% 0.19/0.47  # SZS output end CNFRefutation
% 0.19/0.47  # Proof object total steps             : 93
% 0.19/0.47  # Proof object clause steps            : 64
% 0.19/0.47  # Proof object formula steps           : 29
% 0.19/0.47  # Proof object conjectures             : 15
% 0.19/0.47  # Proof object clause conjectures      : 12
% 0.19/0.47  # Proof object formula conjectures     : 3
% 0.19/0.47  # Proof object initial clauses used    : 19
% 0.19/0.47  # Proof object initial formulas used   : 14
% 0.19/0.47  # Proof object generating inferences   : 22
% 0.19/0.47  # Proof object simplifying inferences  : 73
% 0.19/0.47  # Training examples: 0 positive, 0 negative
% 0.19/0.47  # Parsed axioms                        : 14
% 0.19/0.47  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.47  # Initial clauses                      : 22
% 0.19/0.47  # Removed in clause preprocessing      : 6
% 0.19/0.47  # Initial clauses in saturation        : 16
% 0.19/0.47  # Processed clauses                    : 679
% 0.19/0.47  # ...of these trivial                  : 99
% 0.19/0.47  # ...subsumed                          : 312
% 0.19/0.47  # ...remaining for further processing  : 268
% 0.19/0.47  # Other redundant clauses eliminated   : 3
% 0.19/0.47  # Clauses deleted for lack of memory   : 0
% 0.19/0.47  # Backward-subsumed                    : 0
% 0.19/0.47  # Backward-rewritten                   : 66
% 0.19/0.47  # Generated clauses                    : 6169
% 0.19/0.47  # ...of the previous two non-trivial   : 5473
% 0.19/0.47  # Contextual simplify-reflections      : 4
% 0.19/0.47  # Paramodulations                      : 6124
% 0.19/0.47  # Factorizations                       : 42
% 0.19/0.47  # Equation resolutions                 : 3
% 0.19/0.47  # Propositional unsat checks           : 0
% 0.19/0.47  #    Propositional check models        : 0
% 0.19/0.47  #    Propositional check unsatisfiable : 0
% 0.19/0.47  #    Propositional clauses             : 0
% 0.19/0.47  #    Propositional clauses after purity: 0
% 0.19/0.47  #    Propositional unsat core size     : 0
% 0.19/0.47  #    Propositional preprocessing time  : 0.000
% 0.19/0.47  #    Propositional encoding time       : 0.000
% 0.19/0.47  #    Propositional solver time         : 0.000
% 0.19/0.47  #    Success case prop preproc time    : 0.000
% 0.19/0.47  #    Success case prop encoding time   : 0.000
% 0.19/0.47  #    Success case prop solver time     : 0.000
% 0.19/0.47  # Current number of processed clauses  : 183
% 0.19/0.47  #    Positive orientable unit clauses  : 73
% 0.19/0.47  #    Positive unorientable unit clauses: 5
% 0.19/0.47  #    Negative unit clauses             : 0
% 0.19/0.47  #    Non-unit-clauses                  : 105
% 0.19/0.47  # Current number of unprocessed clauses: 4709
% 0.19/0.47  # ...number of literals in the above   : 9969
% 0.19/0.47  # Current number of archived formulas  : 0
% 0.19/0.47  # Current number of archived clauses   : 88
% 0.19/0.47  # Clause-clause subsumption calls (NU) : 6418
% 0.19/0.47  # Rec. Clause-clause subsumption calls : 4433
% 0.19/0.47  # Non-unit clause-clause subsumptions  : 306
% 0.19/0.47  # Unit Clause-clause subsumption calls : 227
% 0.19/0.47  # Rewrite failures with RHS unbound    : 0
% 0.19/0.47  # BW rewrite match attempts            : 428
% 0.19/0.47  # BW rewrite match successes           : 80
% 0.19/0.47  # Condensation attempts                : 0
% 0.19/0.47  # Condensation successes               : 0
% 0.19/0.47  # Termbank termtop insertions          : 180294
% 0.19/0.47  
% 0.19/0.47  # -------------------------------------------------
% 0.19/0.47  # User time                : 0.123 s
% 0.19/0.47  # System time              : 0.006 s
% 0.19/0.47  # Total time               : 0.130 s
% 0.19/0.47  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------

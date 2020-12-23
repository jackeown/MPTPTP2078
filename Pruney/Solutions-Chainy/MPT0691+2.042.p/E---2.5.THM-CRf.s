%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:54:47 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 153 expanded)
%              Number of clauses        :   47 (  65 expanded)
%              Number of leaves         :   21 (  39 expanded)
%              Depth                    :   10
%              Number of atoms          :  139 ( 262 expanded)
%              Number of equality atoms :   71 (  93 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t95_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(t146_funct_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(dt_k4_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k4_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(t182_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(t123_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X1,X2) = k5_relat_1(X2,k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

fof(t54_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k4_relat_1(k5_relat_1(X1,X2)) = k5_relat_1(k4_relat_1(X2),k4_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

fof(t94_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k5_relat_1(k6_relat_1(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(dt_k8_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => v1_relat_1(k8_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(t163_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k3_xboole_0(k1_relat_1(X2),X1),k9_relat_1(k4_relat_1(X2),k9_relat_1(X2,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_relat_1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(t72_relat_1,axiom,(
    ! [X1] : k4_relat_1(k6_relat_1(X1)) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).

fof(t37_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k2_relat_1(X1) = k1_relat_1(k4_relat_1(X1))
        & k1_relat_1(X1) = k2_relat_1(k4_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(c_0_21,plain,(
    ! [X17,X18] : k2_xboole_0(X17,X18) = k5_xboole_0(X17,k4_xboole_0(X18,X17)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_22,plain,(
    ! [X6,X7] : k4_xboole_0(X6,X7) = k5_xboole_0(X6,k3_xboole_0(X6,X7)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_23,plain,(
    ! [X15,X16] : k3_xboole_0(X15,X16) = k5_xboole_0(k5_xboole_0(X15,X16),k2_xboole_0(X15,X16)) ),
    inference(variable_rename,[status(thm)],[t95_xboole_1])).

cnf(c_0_24,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_26,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X1,k1_relat_1(X2))
         => r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))) ) ) ),
    inference(assume_negation,[status(cth)],[t146_funct_1])).

cnf(c_0_27,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

fof(c_0_29,plain,(
    ! [X11,X12,X13] : k5_xboole_0(k5_xboole_0(X11,X12),X13) = k5_xboole_0(X11,k5_xboole_0(X12,X13)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

fof(c_0_30,plain,(
    ! [X8,X9] :
      ( ~ r1_tarski(X8,X9)
      | k3_xboole_0(X8,X9) = X8 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_31,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & r1_tarski(esk1_0,k1_relat_1(esk2_0))
    & ~ r1_tarski(esk1_0,k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])).

fof(c_0_32,plain,(
    ! [X10] : k5_xboole_0(X10,k1_xboole_0) = X10 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_33,plain,(
    ! [X4,X5] : k5_xboole_0(X4,X5) = k5_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

fof(c_0_34,plain,(
    ! [X14] : k5_xboole_0(X14,X14) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

cnf(c_0_35,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_36,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(esk1_0,k1_relat_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_39,plain,(
    ! [X19] :
      ( ~ v1_relat_1(X19)
      | v1_relat_1(k4_relat_1(X19)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relat_1])])).

fof(c_0_40,plain,(
    ! [X30,X31] :
      ( ~ v1_relat_1(X30)
      | ~ v1_relat_1(X31)
      | k1_relat_1(k5_relat_1(X30,X31)) = k10_relat_1(X30,k1_relat_1(X31)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).

fof(c_0_41,plain,(
    ! [X20] : v1_relat_1(k6_relat_1(X20)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

fof(c_0_42,plain,(
    ! [X35] :
      ( k1_relat_1(k6_relat_1(X35)) = X35
      & k2_relat_1(k6_relat_1(X35)) = X35 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_43,plain,(
    ! [X24,X25] :
      ( ~ v1_relat_1(X25)
      | k8_relat_1(X24,X25) = k5_relat_1(X25,k6_relat_1(X24)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_relat_1])])).

cnf(c_0_44,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_45,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_46,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_47,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_48,negated_conjecture,
    ( k3_xboole_0(esk1_0,k1_relat_1(esk2_0)) = esk1_0 ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

fof(c_0_49,plain,(
    ! [X33,X34] :
      ( ~ v1_relat_1(X33)
      | ~ v1_relat_1(X34)
      | k4_relat_1(k5_relat_1(X33,X34)) = k5_relat_1(k4_relat_1(X34),k4_relat_1(X33)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_relat_1])])])).

fof(c_0_50,plain,(
    ! [X37,X38] :
      ( ~ v1_relat_1(X38)
      | k7_relat_1(X38,X37) = k5_relat_1(k6_relat_1(X37),X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).

cnf(c_0_51,plain,
    ( v1_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_52,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_53,plain,(
    ! [X21,X22] :
      ( ~ v1_relat_1(X22)
      | v1_relat_1(k8_relat_1(X21,X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relat_1])])).

cnf(c_0_54,plain,
    ( k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_55,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_56,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_57,plain,
    ( k8_relat_1(X2,X1) = k5_relat_1(X1,k6_relat_1(X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_58,plain,(
    ! [X28,X29] :
      ( ~ v1_relat_1(X29)
      | r1_tarski(k3_xboole_0(k1_relat_1(X29),X28),k9_relat_1(k4_relat_1(X29),k9_relat_1(X29,X28))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t163_relat_1])])).

cnf(c_0_59,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_60,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_46,c_0_36])).

cnf(c_0_61,negated_conjecture,
    ( k5_xboole_0(k1_relat_1(esk2_0),k5_xboole_0(esk1_0,k1_relat_1(esk2_0))) = k3_xboole_0(k1_relat_1(esk2_0),esk1_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_46]),c_0_44])).

fof(c_0_62,plain,(
    ! [X26,X27] :
      ( ~ v1_relat_1(X27)
      | k2_relat_1(k7_relat_1(X27,X26)) = k9_relat_1(X27,X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

cnf(c_0_63,plain,
    ( k4_relat_1(k5_relat_1(X1,X2)) = k5_relat_1(k4_relat_1(X2),k4_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_64,plain,(
    ! [X36] : k4_relat_1(k6_relat_1(X36)) = k6_relat_1(X36) ),
    inference(variable_rename,[status(thm)],[t72_relat_1])).

cnf(c_0_65,plain,
    ( k7_relat_1(X1,X2) = k5_relat_1(k6_relat_1(X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_66,negated_conjecture,
    ( v1_relat_1(k4_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

fof(c_0_67,plain,(
    ! [X32] :
      ( ( k2_relat_1(X32) = k1_relat_1(k4_relat_1(X32))
        | ~ v1_relat_1(X32) )
      & ( k1_relat_1(X32) = k2_relat_1(k4_relat_1(X32))
        | ~ v1_relat_1(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_relat_1])])])).

cnf(c_0_68,plain,
    ( v1_relat_1(k8_relat_1(X2,X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_69,plain,
    ( k1_relat_1(k5_relat_1(X1,k6_relat_1(X2))) = k10_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56])).

cnf(c_0_70,negated_conjecture,
    ( k5_relat_1(esk2_0,k6_relat_1(X1)) = k8_relat_1(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_52])).

cnf(c_0_71,plain,
    ( r1_tarski(k3_xboole_0(k1_relat_1(X1),X2),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_72,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_46]),c_0_59])).

cnf(c_0_73,negated_conjecture,
    ( k5_xboole_0(esk1_0,k3_xboole_0(k1_relat_1(esk2_0),esk1_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_74,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_75,negated_conjecture,
    ( k5_relat_1(k4_relat_1(X1),k4_relat_1(esk2_0)) = k4_relat_1(k5_relat_1(esk2_0,X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_52])).

cnf(c_0_76,plain,
    ( k4_relat_1(k6_relat_1(X1)) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_77,negated_conjecture,
    ( k5_relat_1(k6_relat_1(X1),k4_relat_1(esk2_0)) = k7_relat_1(k4_relat_1(esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_78,plain,
    ( k1_relat_1(X1) = k2_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_79,negated_conjecture,
    ( v1_relat_1(k8_relat_1(X1,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_52])).

cnf(c_0_80,negated_conjecture,
    ( k1_relat_1(k8_relat_1(X1,esk2_0)) = k10_relat_1(esk2_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_52]),c_0_70])).

cnf(c_0_81,negated_conjecture,
    ( r1_tarski(k3_xboole_0(k1_relat_1(esk2_0),X1),k9_relat_1(k4_relat_1(esk2_0),k9_relat_1(esk2_0,X1))) ),
    inference(spm,[status(thm)],[c_0_71,c_0_52])).

cnf(c_0_82,negated_conjecture,
    ( k3_xboole_0(k1_relat_1(esk2_0),esk1_0) = esk1_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_44])).

cnf(c_0_83,negated_conjecture,
    ( k2_relat_1(k7_relat_1(k4_relat_1(esk2_0),X1)) = k9_relat_1(k4_relat_1(esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_74,c_0_66])).

cnf(c_0_84,negated_conjecture,
    ( k7_relat_1(k4_relat_1(esk2_0),X1) = k4_relat_1(k8_relat_1(X1,esk2_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_55]),c_0_76]),c_0_70]),c_0_77])).

cnf(c_0_85,negated_conjecture,
    ( k2_relat_1(k4_relat_1(k8_relat_1(X1,esk2_0))) = k10_relat_1(esk2_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_80])).

cnf(c_0_86,negated_conjecture,
    ( r1_tarski(esk1_0,k9_relat_1(k4_relat_1(esk2_0),k9_relat_1(esk2_0,esk1_0))) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_87,negated_conjecture,
    ( k9_relat_1(k4_relat_1(esk2_0),X1) = k10_relat_1(esk2_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_83,c_0_84]),c_0_85])).

cnf(c_0_88,negated_conjecture,
    ( ~ r1_tarski(esk1_0,k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_89,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_87]),c_0_88]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n016.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:05:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S05EA
% 0.19/0.38  # and selection function SelectDivPreferIntoLits.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.027 s
% 0.19/0.38  # Presaturation interreduction done
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.19/0.38  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.19/0.38  fof(t95_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 0.19/0.38  fof(t146_funct_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 0.19/0.38  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.19/0.38  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.19/0.38  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 0.19/0.38  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 0.19/0.38  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.19/0.38  fof(dt_k4_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>v1_relat_1(k4_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 0.19/0.38  fof(t182_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 0.19/0.38  fof(dt_k6_relat_1, axiom, ![X1]:v1_relat_1(k6_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 0.19/0.38  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 0.19/0.38  fof(t123_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k8_relat_1(X1,X2)=k5_relat_1(X2,k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 0.19/0.38  fof(t54_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k4_relat_1(k5_relat_1(X1,X2))=k5_relat_1(k4_relat_1(X2),k4_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_relat_1)).
% 0.19/0.38  fof(t94_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k5_relat_1(k6_relat_1(X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 0.19/0.38  fof(dt_k8_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>v1_relat_1(k8_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 0.19/0.38  fof(t163_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k3_xboole_0(k1_relat_1(X2),X1),k9_relat_1(k4_relat_1(X2),k9_relat_1(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t163_relat_1)).
% 0.19/0.38  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 0.19/0.38  fof(t72_relat_1, axiom, ![X1]:k4_relat_1(k6_relat_1(X1))=k6_relat_1(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_relat_1)).
% 0.19/0.38  fof(t37_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k4_relat_1(X1))&k1_relat_1(X1)=k2_relat_1(k4_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_relat_1)).
% 0.19/0.38  fof(c_0_21, plain, ![X17, X18]:k2_xboole_0(X17,X18)=k5_xboole_0(X17,k4_xboole_0(X18,X17)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.19/0.38  fof(c_0_22, plain, ![X6, X7]:k4_xboole_0(X6,X7)=k5_xboole_0(X6,k3_xboole_0(X6,X7)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.19/0.38  fof(c_0_23, plain, ![X15, X16]:k3_xboole_0(X15,X16)=k5_xboole_0(k5_xboole_0(X15,X16),k2_xboole_0(X15,X16)), inference(variable_rename,[status(thm)],[t95_xboole_1])).
% 0.19/0.38  cnf(c_0_24, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.38  cnf(c_0_25, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.38  fof(c_0_26, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1)))))), inference(assume_negation,[status(cth)],[t146_funct_1])).
% 0.19/0.38  cnf(c_0_27, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.38  cnf(c_0_28, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 0.19/0.38  fof(c_0_29, plain, ![X11, X12, X13]:k5_xboole_0(k5_xboole_0(X11,X12),X13)=k5_xboole_0(X11,k5_xboole_0(X12,X13)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.19/0.38  fof(c_0_30, plain, ![X8, X9]:(~r1_tarski(X8,X9)|k3_xboole_0(X8,X9)=X8), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.19/0.38  fof(c_0_31, negated_conjecture, (v1_relat_1(esk2_0)&(r1_tarski(esk1_0,k1_relat_1(esk2_0))&~r1_tarski(esk1_0,k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])).
% 0.19/0.38  fof(c_0_32, plain, ![X10]:k5_xboole_0(X10,k1_xboole_0)=X10, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.19/0.38  fof(c_0_33, plain, ![X4, X5]:k5_xboole_0(X4,X5)=k5_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 0.19/0.38  fof(c_0_34, plain, ![X14]:k5_xboole_0(X14,X14)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.19/0.38  cnf(c_0_35, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 0.19/0.38  cnf(c_0_36, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.38  cnf(c_0_37, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.38  cnf(c_0_38, negated_conjecture, (r1_tarski(esk1_0,k1_relat_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.38  fof(c_0_39, plain, ![X19]:(~v1_relat_1(X19)|v1_relat_1(k4_relat_1(X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relat_1])])).
% 0.19/0.38  fof(c_0_40, plain, ![X30, X31]:(~v1_relat_1(X30)|(~v1_relat_1(X31)|k1_relat_1(k5_relat_1(X30,X31))=k10_relat_1(X30,k1_relat_1(X31)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).
% 0.19/0.38  fof(c_0_41, plain, ![X20]:v1_relat_1(k6_relat_1(X20)), inference(variable_rename,[status(thm)],[dt_k6_relat_1])).
% 0.19/0.38  fof(c_0_42, plain, ![X35]:(k1_relat_1(k6_relat_1(X35))=X35&k2_relat_1(k6_relat_1(X35))=X35), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.19/0.38  fof(c_0_43, plain, ![X24, X25]:(~v1_relat_1(X25)|k8_relat_1(X24,X25)=k5_relat_1(X25,k6_relat_1(X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_relat_1])])).
% 0.19/0.38  cnf(c_0_44, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.38  cnf(c_0_45, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.38  cnf(c_0_46, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.38  cnf(c_0_47, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_35, c_0_36])).
% 0.19/0.38  cnf(c_0_48, negated_conjecture, (k3_xboole_0(esk1_0,k1_relat_1(esk2_0))=esk1_0), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.19/0.38  fof(c_0_49, plain, ![X33, X34]:(~v1_relat_1(X33)|(~v1_relat_1(X34)|k4_relat_1(k5_relat_1(X33,X34))=k5_relat_1(k4_relat_1(X34),k4_relat_1(X33)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_relat_1])])])).
% 0.19/0.38  fof(c_0_50, plain, ![X37, X38]:(~v1_relat_1(X38)|k7_relat_1(X38,X37)=k5_relat_1(k6_relat_1(X37),X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).
% 0.19/0.38  cnf(c_0_51, plain, (v1_relat_1(k4_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.38  cnf(c_0_52, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.38  fof(c_0_53, plain, ![X21, X22]:(~v1_relat_1(X22)|v1_relat_1(k8_relat_1(X21,X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relat_1])])).
% 0.19/0.38  cnf(c_0_54, plain, (k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.38  cnf(c_0_55, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.38  cnf(c_0_56, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.38  cnf(c_0_57, plain, (k8_relat_1(X2,X1)=k5_relat_1(X1,k6_relat_1(X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.38  fof(c_0_58, plain, ![X28, X29]:(~v1_relat_1(X29)|r1_tarski(k3_xboole_0(k1_relat_1(X29),X28),k9_relat_1(k4_relat_1(X29),k9_relat_1(X29,X28)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t163_relat_1])])).
% 0.19/0.38  cnf(c_0_59, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.19/0.38  cnf(c_0_60, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_46, c_0_36])).
% 0.19/0.38  cnf(c_0_61, negated_conjecture, (k5_xboole_0(k1_relat_1(esk2_0),k5_xboole_0(esk1_0,k1_relat_1(esk2_0)))=k3_xboole_0(k1_relat_1(esk2_0),esk1_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_46]), c_0_44])).
% 0.19/0.38  fof(c_0_62, plain, ![X26, X27]:(~v1_relat_1(X27)|k2_relat_1(k7_relat_1(X27,X26))=k9_relat_1(X27,X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.19/0.38  cnf(c_0_63, plain, (k4_relat_1(k5_relat_1(X1,X2))=k5_relat_1(k4_relat_1(X2),k4_relat_1(X1))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.19/0.38  fof(c_0_64, plain, ![X36]:k4_relat_1(k6_relat_1(X36))=k6_relat_1(X36), inference(variable_rename,[status(thm)],[t72_relat_1])).
% 0.19/0.38  cnf(c_0_65, plain, (k7_relat_1(X1,X2)=k5_relat_1(k6_relat_1(X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.19/0.38  cnf(c_0_66, negated_conjecture, (v1_relat_1(k4_relat_1(esk2_0))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.19/0.38  fof(c_0_67, plain, ![X32]:((k2_relat_1(X32)=k1_relat_1(k4_relat_1(X32))|~v1_relat_1(X32))&(k1_relat_1(X32)=k2_relat_1(k4_relat_1(X32))|~v1_relat_1(X32))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_relat_1])])])).
% 0.19/0.38  cnf(c_0_68, plain, (v1_relat_1(k8_relat_1(X2,X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.19/0.38  cnf(c_0_69, plain, (k1_relat_1(k5_relat_1(X1,k6_relat_1(X2)))=k10_relat_1(X1,X2)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56])).
% 0.19/0.38  cnf(c_0_70, negated_conjecture, (k5_relat_1(esk2_0,k6_relat_1(X1))=k8_relat_1(X1,esk2_0)), inference(spm,[status(thm)],[c_0_57, c_0_52])).
% 0.19/0.38  cnf(c_0_71, plain, (r1_tarski(k3_xboole_0(k1_relat_1(X1),X2),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X2)))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.19/0.38  cnf(c_0_72, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_46]), c_0_59])).
% 0.19/0.38  cnf(c_0_73, negated_conjecture, (k5_xboole_0(esk1_0,k3_xboole_0(k1_relat_1(esk2_0),esk1_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.19/0.38  cnf(c_0_74, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.19/0.38  cnf(c_0_75, negated_conjecture, (k5_relat_1(k4_relat_1(X1),k4_relat_1(esk2_0))=k4_relat_1(k5_relat_1(esk2_0,X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_63, c_0_52])).
% 0.19/0.38  cnf(c_0_76, plain, (k4_relat_1(k6_relat_1(X1))=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.19/0.38  cnf(c_0_77, negated_conjecture, (k5_relat_1(k6_relat_1(X1),k4_relat_1(esk2_0))=k7_relat_1(k4_relat_1(esk2_0),X1)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.19/0.38  cnf(c_0_78, plain, (k1_relat_1(X1)=k2_relat_1(k4_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.19/0.38  cnf(c_0_79, negated_conjecture, (v1_relat_1(k8_relat_1(X1,esk2_0))), inference(spm,[status(thm)],[c_0_68, c_0_52])).
% 0.19/0.38  cnf(c_0_80, negated_conjecture, (k1_relat_1(k8_relat_1(X1,esk2_0))=k10_relat_1(esk2_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_52]), c_0_70])).
% 0.19/0.38  cnf(c_0_81, negated_conjecture, (r1_tarski(k3_xboole_0(k1_relat_1(esk2_0),X1),k9_relat_1(k4_relat_1(esk2_0),k9_relat_1(esk2_0,X1)))), inference(spm,[status(thm)],[c_0_71, c_0_52])).
% 0.19/0.38  cnf(c_0_82, negated_conjecture, (k3_xboole_0(k1_relat_1(esk2_0),esk1_0)=esk1_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_44])).
% 0.19/0.38  cnf(c_0_83, negated_conjecture, (k2_relat_1(k7_relat_1(k4_relat_1(esk2_0),X1))=k9_relat_1(k4_relat_1(esk2_0),X1)), inference(spm,[status(thm)],[c_0_74, c_0_66])).
% 0.19/0.38  cnf(c_0_84, negated_conjecture, (k7_relat_1(k4_relat_1(esk2_0),X1)=k4_relat_1(k8_relat_1(X1,esk2_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_55]), c_0_76]), c_0_70]), c_0_77])).
% 0.19/0.38  cnf(c_0_85, negated_conjecture, (k2_relat_1(k4_relat_1(k8_relat_1(X1,esk2_0)))=k10_relat_1(esk2_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_80])).
% 0.19/0.38  cnf(c_0_86, negated_conjecture, (r1_tarski(esk1_0,k9_relat_1(k4_relat_1(esk2_0),k9_relat_1(esk2_0,esk1_0)))), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 0.19/0.38  cnf(c_0_87, negated_conjecture, (k9_relat_1(k4_relat_1(esk2_0),X1)=k10_relat_1(esk2_0,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_83, c_0_84]), c_0_85])).
% 0.19/0.38  cnf(c_0_88, negated_conjecture, (~r1_tarski(esk1_0,k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.38  cnf(c_0_89, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_86, c_0_87]), c_0_88]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 90
% 0.19/0.38  # Proof object clause steps            : 47
% 0.19/0.38  # Proof object formula steps           : 43
% 0.19/0.38  # Proof object conjectures             : 23
% 0.19/0.38  # Proof object clause conjectures      : 20
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 23
% 0.19/0.38  # Proof object initial formulas used   : 21
% 0.19/0.38  # Proof object generating inferences   : 19
% 0.19/0.38  # Proof object simplifying inferences  : 17
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 22
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 26
% 0.19/0.38  # Removed in clause preprocessing      : 2
% 0.19/0.38  # Initial clauses in saturation        : 24
% 0.19/0.38  # Processed clauses                    : 167
% 0.19/0.38  # ...of these trivial                  : 12
% 0.19/0.38  # ...subsumed                          : 23
% 0.19/0.38  # ...remaining for further processing  : 132
% 0.19/0.38  # Other redundant clauses eliminated   : 0
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 0
% 0.19/0.38  # Backward-rewritten                   : 21
% 0.19/0.38  # Generated clauses                    : 708
% 0.19/0.38  # ...of the previous two non-trivial   : 618
% 0.19/0.38  # Contextual simplify-reflections      : 0
% 0.19/0.38  # Paramodulations                      : 708
% 0.19/0.38  # Factorizations                       : 0
% 0.19/0.38  # Equation resolutions                 : 0
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 87
% 0.19/0.38  #    Positive orientable unit clauses  : 62
% 0.19/0.38  #    Positive unorientable unit clauses: 4
% 0.19/0.38  #    Negative unit clauses             : 1
% 0.19/0.38  #    Non-unit-clauses                  : 20
% 0.19/0.38  # Current number of unprocessed clauses: 479
% 0.19/0.38  # ...number of literals in the above   : 509
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 47
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 45
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 41
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.19/0.38  # Unit Clause-clause subsumption calls : 39
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 115
% 0.19/0.38  # BW rewrite match successes           : 70
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 10643
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.046 s
% 0.19/0.38  # System time              : 0.002 s
% 0.19/0.38  # Total time               : 0.048 s
% 0.19/0.38  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------

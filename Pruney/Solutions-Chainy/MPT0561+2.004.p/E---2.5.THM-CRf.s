%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:51:09 EST 2020

% Result     : Theorem 0.47s
% Output     : CNFRefutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 352 expanded)
%              Number of clauses        :   53 ( 148 expanded)
%              Number of leaves         :   16 (  89 expanded)
%              Depth                    :   14
%              Number of atoms          :  164 ( 632 expanded)
%              Number of equality atoms :   56 ( 162 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t163_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k3_xboole_0(k1_relat_1(X2),X1),k9_relat_1(k4_relat_1(X2),k9_relat_1(X2,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_relat_1)).

fof(t80_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(X1,k6_relat_1(k2_relat_1(X1))) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

fof(dt_k4_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k4_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(t37_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k2_relat_1(X1) = k1_relat_1(k4_relat_1(X1))
        & k1_relat_1(X1) = k2_relat_1(k4_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

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

fof(t72_relat_1,axiom,(
    ! [X1] : k4_relat_1(k6_relat_1(X1)) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(involutiveness_k4_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k4_relat_1(k4_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t90_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k1_relat_1(k7_relat_1(X2,X1)) = k3_xboole_0(k1_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(t25_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
              & r1_tarski(k2_relat_1(X1),k2_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(t92_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => r1_tarski(k5_relat_1(k7_relat_1(X2,X1),X3),k5_relat_1(X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_relat_1)).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => r1_tarski(k3_xboole_0(k1_relat_1(X2),X1),k9_relat_1(k4_relat_1(X2),k9_relat_1(X2,X1))) ) ),
    inference(assume_negation,[status(cth)],[t163_relat_1])).

fof(c_0_17,plain,(
    ! [X21] :
      ( ~ v1_relat_1(X21)
      | k5_relat_1(X21,k6_relat_1(k2_relat_1(X21))) = X21 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_relat_1])])).

fof(c_0_18,plain,(
    ! [X8] :
      ( ~ v1_relat_1(X8)
      | v1_relat_1(k4_relat_1(X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relat_1])])).

fof(c_0_19,plain,(
    ! [X17] :
      ( ( k2_relat_1(X17) = k1_relat_1(k4_relat_1(X17))
        | ~ v1_relat_1(X17) )
      & ( k1_relat_1(X17) = k2_relat_1(k4_relat_1(X17))
        | ~ v1_relat_1(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_relat_1])])])).

fof(c_0_20,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & ~ r1_tarski(k3_xboole_0(k1_relat_1(esk2_0),esk1_0),k9_relat_1(k4_relat_1(esk2_0),k9_relat_1(esk2_0,esk1_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

fof(c_0_21,plain,(
    ! [X18,X19] :
      ( ~ v1_relat_1(X18)
      | ~ v1_relat_1(X19)
      | k4_relat_1(k5_relat_1(X18,X19)) = k5_relat_1(k4_relat_1(X19),k4_relat_1(X18)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_relat_1])])])).

fof(c_0_22,plain,(
    ! [X27,X28] :
      ( ~ v1_relat_1(X28)
      | k7_relat_1(X28,X27) = k5_relat_1(k6_relat_1(X27),X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).

cnf(c_0_23,plain,
    ( k5_relat_1(X1,k6_relat_1(k2_relat_1(X1))) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( v1_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( k1_relat_1(X1) = k2_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( k4_relat_1(k5_relat_1(X1,X2)) = k5_relat_1(k4_relat_1(X2),k4_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_28,plain,(
    ! [X20] : k4_relat_1(k6_relat_1(X20)) = k6_relat_1(X20) ),
    inference(variable_rename,[status(thm)],[t72_relat_1])).

cnf(c_0_29,plain,
    ( k7_relat_1(X1,X2) = k5_relat_1(k6_relat_1(X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_30,plain,(
    ! [X9] : v1_relat_1(k6_relat_1(X9)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

cnf(c_0_31,plain,
    ( k5_relat_1(k4_relat_1(X1),k6_relat_1(k2_relat_1(k4_relat_1(X1)))) = k4_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( k2_relat_1(k4_relat_1(esk2_0)) = k1_relat_1(esk2_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( k5_relat_1(k4_relat_1(esk2_0),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,esk2_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_26])).

cnf(c_0_34,plain,
    ( k4_relat_1(k6_relat_1(X1)) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( k5_relat_1(k6_relat_1(X1),esk2_0) = k7_relat_1(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_26])).

cnf(c_0_36,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( k5_relat_1(k4_relat_1(esk2_0),k6_relat_1(k1_relat_1(esk2_0))) = k4_relat_1(esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_26]),c_0_32])).

cnf(c_0_38,negated_conjecture,
    ( k5_relat_1(k4_relat_1(esk2_0),k6_relat_1(X1)) = k4_relat_1(k7_relat_1(esk2_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_36])])).

cnf(c_0_39,negated_conjecture,
    ( k4_relat_1(k7_relat_1(esk2_0,k1_relat_1(esk2_0))) = k4_relat_1(esk2_0) ),
    inference(rw,[status(thm)],[c_0_37,c_0_38])).

fof(c_0_40,plain,(
    ! [X10,X11] :
      ( ~ v1_relat_1(X10)
      | v1_relat_1(k7_relat_1(X10,X11)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

fof(c_0_41,plain,(
    ! [X12] :
      ( ~ v1_relat_1(X12)
      | k4_relat_1(k4_relat_1(X12)) = X12 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k4_relat_1])])).

fof(c_0_42,plain,(
    ! [X13,X14] :
      ( ~ v1_relat_1(X14)
      | k2_relat_1(k7_relat_1(X14,X13)) = k9_relat_1(X14,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

cnf(c_0_43,negated_conjecture,
    ( v1_relat_1(k4_relat_1(esk2_0))
    | ~ v1_relat_1(k7_relat_1(esk2_0,k1_relat_1(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_24,c_0_39])).

cnf(c_0_44,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_45,plain,
    ( k4_relat_1(k4_relat_1(X1)) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_46,plain,
    ( k2_relat_1(X1) = k1_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_47,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_48,plain,(
    ! [X6,X7] : k4_xboole_0(X6,k4_xboole_0(X6,X7)) = k3_xboole_0(X6,X7) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_49,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_50,plain,(
    ! [X22,X23] :
      ( ~ v1_relat_1(X23)
      | k1_relat_1(k7_relat_1(X23,X22)) = k3_xboole_0(k1_relat_1(X23),X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).

fof(c_0_51,plain,(
    ! [X15,X16] :
      ( ( r1_tarski(k1_relat_1(X15),k1_relat_1(X16))
        | ~ r1_tarski(X15,X16)
        | ~ v1_relat_1(X16)
        | ~ v1_relat_1(X15) )
      & ( r1_tarski(k2_relat_1(X15),k2_relat_1(X16))
        | ~ r1_tarski(X15,X16)
        | ~ v1_relat_1(X16)
        | ~ v1_relat_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).

fof(c_0_52,plain,(
    ! [X24,X25,X26] :
      ( ~ v1_relat_1(X25)
      | ~ v1_relat_1(X26)
      | r1_tarski(k5_relat_1(k7_relat_1(X25,X24),X26),k5_relat_1(X25,X26)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t92_relat_1])])])).

cnf(c_0_53,negated_conjecture,
    ( v1_relat_1(k4_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_26])])).

cnf(c_0_54,negated_conjecture,
    ( k4_relat_1(k4_relat_1(esk2_0)) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_45,c_0_26])).

cnf(c_0_55,plain,
    ( k1_relat_1(k4_relat_1(k7_relat_1(X1,X2))) = k2_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_44])).

cnf(c_0_56,plain,
    ( k2_relat_1(k7_relat_1(k4_relat_1(X1),X2)) = k9_relat_1(k4_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_24])).

cnf(c_0_57,plain,
    ( k5_relat_1(k6_relat_1(X1),k4_relat_1(X2)) = k7_relat_1(k4_relat_1(X2),X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_29,c_0_24])).

cnf(c_0_58,negated_conjecture,
    ( ~ r1_tarski(k3_xboole_0(k1_relat_1(esk2_0),esk1_0),k9_relat_1(k4_relat_1(esk2_0),k9_relat_1(esk2_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_59,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_60,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_61,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k3_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_62,plain,
    ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_63,plain,
    ( r1_tarski(k5_relat_1(k7_relat_1(X1,X3),X2),k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_64,negated_conjecture,
    ( k4_relat_1(k5_relat_1(X1,k4_relat_1(esk2_0))) = k5_relat_1(esk2_0,k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_53]),c_0_54])).

cnf(c_0_65,plain,
    ( k1_relat_1(k4_relat_1(k7_relat_1(k4_relat_1(X1),X2))) = k2_relat_1(k7_relat_1(k4_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_24])).

cnf(c_0_66,negated_conjecture,
    ( k2_relat_1(k7_relat_1(k4_relat_1(esk2_0),X1)) = k9_relat_1(k4_relat_1(esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_26])).

cnf(c_0_67,negated_conjecture,
    ( k5_relat_1(k6_relat_1(X1),k4_relat_1(esk2_0)) = k7_relat_1(k4_relat_1(esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_26])).

cnf(c_0_68,negated_conjecture,
    ( ~ r1_tarski(k4_xboole_0(k1_relat_1(esk2_0),k4_xboole_0(k1_relat_1(esk2_0),esk1_0)),k9_relat_1(k4_relat_1(esk2_0),k9_relat_1(esk2_0,esk1_0))) ),
    inference(rw,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_69,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_59]),c_0_59])).

cnf(c_0_70,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_61,c_0_59])).

cnf(c_0_71,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(k7_relat_1(X1,X2),X3)),k1_relat_1(k5_relat_1(X1,X3)))
    | ~ v1_relat_1(k5_relat_1(k7_relat_1(X1,X2),X3))
    | ~ v1_relat_1(k5_relat_1(X1,X3))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_72,plain,
    ( k5_relat_1(k7_relat_1(X1,X2),k6_relat_1(k2_relat_1(k7_relat_1(X1,X2)))) = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_44])).

cnf(c_0_73,negated_conjecture,
    ( v1_relat_1(k5_relat_1(esk2_0,k4_relat_1(X1)))
    | ~ v1_relat_1(k5_relat_1(X1,k4_relat_1(esk2_0)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_64])).

cnf(c_0_74,negated_conjecture,
    ( k1_relat_1(k4_relat_1(k7_relat_1(k4_relat_1(esk2_0),X1))) = k9_relat_1(k4_relat_1(esk2_0),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_26]),c_0_66])).

cnf(c_0_75,negated_conjecture,
    ( k4_relat_1(k7_relat_1(k4_relat_1(esk2_0),X1)) = k5_relat_1(esk2_0,k6_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_67]),c_0_34]),c_0_36])])).

cnf(c_0_76,negated_conjecture,
    ( ~ r1_tarski(k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,k1_relat_1(esk2_0))),k9_relat_1(k4_relat_1(esk2_0),k9_relat_1(esk2_0,esk1_0))) ),
    inference(rw,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_77,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k1_relat_1(X2))) = k1_relat_1(k7_relat_1(X2,X1))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_78,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),k1_relat_1(k5_relat_1(X1,k6_relat_1(k2_relat_1(k7_relat_1(X1,X2))))))
    | ~ v1_relat_1(k5_relat_1(X1,k6_relat_1(k2_relat_1(k7_relat_1(X1,X2)))))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_36])]),c_0_44])).

cnf(c_0_79,negated_conjecture,
    ( v1_relat_1(k5_relat_1(esk2_0,k6_relat_1(X1)))
    | ~ v1_relat_1(k7_relat_1(k4_relat_1(esk2_0),X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_67]),c_0_34]),c_0_36])])).

cnf(c_0_80,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk2_0,X1)) = k9_relat_1(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_26])).

cnf(c_0_81,negated_conjecture,
    ( k1_relat_1(k5_relat_1(esk2_0,k6_relat_1(X1))) = k9_relat_1(k4_relat_1(esk2_0),X1) ),
    inference(rw,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_82,negated_conjecture,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(esk2_0,esk1_0)),k9_relat_1(k4_relat_1(esk2_0),k9_relat_1(esk2_0,esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_26])])).

cnf(c_0_83,negated_conjecture,
    ( r1_tarski(k1_relat_1(k7_relat_1(esk2_0,X1)),k9_relat_1(k4_relat_1(esk2_0),k9_relat_1(esk2_0,X1)))
    | ~ v1_relat_1(k7_relat_1(k4_relat_1(esk2_0),k9_relat_1(esk2_0,X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_80]),c_0_81]),c_0_26]),c_0_80])])).

cnf(c_0_84,negated_conjecture,
    ( ~ v1_relat_1(k7_relat_1(k4_relat_1(esk2_0),k9_relat_1(esk2_0,esk1_0))) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_85,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_44]),c_0_53])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:38:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.47/0.69  # AutoSched0-Mode selected heuristic G_E___208_C12_11_nc_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.47/0.69  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.47/0.69  #
% 0.47/0.69  # Preprocessing time       : 0.027 s
% 0.47/0.69  # Presaturation interreduction done
% 0.47/0.69  
% 0.47/0.69  # Proof found!
% 0.47/0.69  # SZS status Theorem
% 0.47/0.69  # SZS output start CNFRefutation
% 0.47/0.69  fof(t163_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k3_xboole_0(k1_relat_1(X2),X1),k9_relat_1(k4_relat_1(X2),k9_relat_1(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t163_relat_1)).
% 0.47/0.69  fof(t80_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k5_relat_1(X1,k6_relat_1(k2_relat_1(X1)))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 0.47/0.69  fof(dt_k4_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>v1_relat_1(k4_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 0.47/0.69  fof(t37_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k4_relat_1(X1))&k1_relat_1(X1)=k2_relat_1(k4_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_relat_1)).
% 0.47/0.69  fof(t54_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k4_relat_1(k5_relat_1(X1,X2))=k5_relat_1(k4_relat_1(X2),k4_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_relat_1)).
% 0.47/0.69  fof(t94_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k5_relat_1(k6_relat_1(X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 0.47/0.69  fof(t72_relat_1, axiom, ![X1]:k4_relat_1(k6_relat_1(X1))=k6_relat_1(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_relat_1)).
% 0.47/0.69  fof(dt_k6_relat_1, axiom, ![X1]:v1_relat_1(k6_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 0.47/0.69  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.47/0.69  fof(involutiveness_k4_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k4_relat_1(k4_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k4_relat_1)).
% 0.47/0.69  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 0.47/0.69  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.47/0.69  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.47/0.69  fof(t90_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k1_relat_1(k7_relat_1(X2,X1))=k3_xboole_0(k1_relat_1(X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 0.47/0.69  fof(t25_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>(r1_tarski(k1_relat_1(X1),k1_relat_1(X2))&r1_tarski(k2_relat_1(X1),k2_relat_1(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 0.47/0.69  fof(t92_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>r1_tarski(k5_relat_1(k7_relat_1(X2,X1),X3),k5_relat_1(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_relat_1)).
% 0.47/0.69  fof(c_0_16, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k3_xboole_0(k1_relat_1(X2),X1),k9_relat_1(k4_relat_1(X2),k9_relat_1(X2,X1))))), inference(assume_negation,[status(cth)],[t163_relat_1])).
% 0.47/0.69  fof(c_0_17, plain, ![X21]:(~v1_relat_1(X21)|k5_relat_1(X21,k6_relat_1(k2_relat_1(X21)))=X21), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_relat_1])])).
% 0.47/0.69  fof(c_0_18, plain, ![X8]:(~v1_relat_1(X8)|v1_relat_1(k4_relat_1(X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relat_1])])).
% 0.47/0.69  fof(c_0_19, plain, ![X17]:((k2_relat_1(X17)=k1_relat_1(k4_relat_1(X17))|~v1_relat_1(X17))&(k1_relat_1(X17)=k2_relat_1(k4_relat_1(X17))|~v1_relat_1(X17))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_relat_1])])])).
% 0.47/0.69  fof(c_0_20, negated_conjecture, (v1_relat_1(esk2_0)&~r1_tarski(k3_xboole_0(k1_relat_1(esk2_0),esk1_0),k9_relat_1(k4_relat_1(esk2_0),k9_relat_1(esk2_0,esk1_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 0.47/0.69  fof(c_0_21, plain, ![X18, X19]:(~v1_relat_1(X18)|(~v1_relat_1(X19)|k4_relat_1(k5_relat_1(X18,X19))=k5_relat_1(k4_relat_1(X19),k4_relat_1(X18)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_relat_1])])])).
% 0.47/0.69  fof(c_0_22, plain, ![X27, X28]:(~v1_relat_1(X28)|k7_relat_1(X28,X27)=k5_relat_1(k6_relat_1(X27),X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).
% 0.47/0.69  cnf(c_0_23, plain, (k5_relat_1(X1,k6_relat_1(k2_relat_1(X1)))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.47/0.69  cnf(c_0_24, plain, (v1_relat_1(k4_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.47/0.69  cnf(c_0_25, plain, (k1_relat_1(X1)=k2_relat_1(k4_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.47/0.69  cnf(c_0_26, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.47/0.69  cnf(c_0_27, plain, (k4_relat_1(k5_relat_1(X1,X2))=k5_relat_1(k4_relat_1(X2),k4_relat_1(X1))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.47/0.69  fof(c_0_28, plain, ![X20]:k4_relat_1(k6_relat_1(X20))=k6_relat_1(X20), inference(variable_rename,[status(thm)],[t72_relat_1])).
% 0.47/0.69  cnf(c_0_29, plain, (k7_relat_1(X1,X2)=k5_relat_1(k6_relat_1(X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.47/0.69  fof(c_0_30, plain, ![X9]:v1_relat_1(k6_relat_1(X9)), inference(variable_rename,[status(thm)],[dt_k6_relat_1])).
% 0.47/0.69  cnf(c_0_31, plain, (k5_relat_1(k4_relat_1(X1),k6_relat_1(k2_relat_1(k4_relat_1(X1))))=k4_relat_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.47/0.69  cnf(c_0_32, negated_conjecture, (k2_relat_1(k4_relat_1(esk2_0))=k1_relat_1(esk2_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.47/0.69  cnf(c_0_33, negated_conjecture, (k5_relat_1(k4_relat_1(esk2_0),k4_relat_1(X1))=k4_relat_1(k5_relat_1(X1,esk2_0))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_27, c_0_26])).
% 0.47/0.69  cnf(c_0_34, plain, (k4_relat_1(k6_relat_1(X1))=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.47/0.69  cnf(c_0_35, negated_conjecture, (k5_relat_1(k6_relat_1(X1),esk2_0)=k7_relat_1(esk2_0,X1)), inference(spm,[status(thm)],[c_0_29, c_0_26])).
% 0.47/0.69  cnf(c_0_36, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.47/0.69  cnf(c_0_37, negated_conjecture, (k5_relat_1(k4_relat_1(esk2_0),k6_relat_1(k1_relat_1(esk2_0)))=k4_relat_1(esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_26]), c_0_32])).
% 0.47/0.69  cnf(c_0_38, negated_conjecture, (k5_relat_1(k4_relat_1(esk2_0),k6_relat_1(X1))=k4_relat_1(k7_relat_1(esk2_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35]), c_0_36])])).
% 0.47/0.69  cnf(c_0_39, negated_conjecture, (k4_relat_1(k7_relat_1(esk2_0,k1_relat_1(esk2_0)))=k4_relat_1(esk2_0)), inference(rw,[status(thm)],[c_0_37, c_0_38])).
% 0.47/0.69  fof(c_0_40, plain, ![X10, X11]:(~v1_relat_1(X10)|v1_relat_1(k7_relat_1(X10,X11))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.47/0.69  fof(c_0_41, plain, ![X12]:(~v1_relat_1(X12)|k4_relat_1(k4_relat_1(X12))=X12), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k4_relat_1])])).
% 0.47/0.69  fof(c_0_42, plain, ![X13, X14]:(~v1_relat_1(X14)|k2_relat_1(k7_relat_1(X14,X13))=k9_relat_1(X14,X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.47/0.69  cnf(c_0_43, negated_conjecture, (v1_relat_1(k4_relat_1(esk2_0))|~v1_relat_1(k7_relat_1(esk2_0,k1_relat_1(esk2_0)))), inference(spm,[status(thm)],[c_0_24, c_0_39])).
% 0.47/0.69  cnf(c_0_44, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.47/0.69  cnf(c_0_45, plain, (k4_relat_1(k4_relat_1(X1))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.47/0.69  cnf(c_0_46, plain, (k2_relat_1(X1)=k1_relat_1(k4_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.47/0.69  cnf(c_0_47, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.47/0.69  fof(c_0_48, plain, ![X6, X7]:k4_xboole_0(X6,k4_xboole_0(X6,X7))=k3_xboole_0(X6,X7), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.47/0.69  fof(c_0_49, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.47/0.69  fof(c_0_50, plain, ![X22, X23]:(~v1_relat_1(X23)|k1_relat_1(k7_relat_1(X23,X22))=k3_xboole_0(k1_relat_1(X23),X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).
% 0.47/0.69  fof(c_0_51, plain, ![X15, X16]:((r1_tarski(k1_relat_1(X15),k1_relat_1(X16))|~r1_tarski(X15,X16)|~v1_relat_1(X16)|~v1_relat_1(X15))&(r1_tarski(k2_relat_1(X15),k2_relat_1(X16))|~r1_tarski(X15,X16)|~v1_relat_1(X16)|~v1_relat_1(X15))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).
% 0.47/0.69  fof(c_0_52, plain, ![X24, X25, X26]:(~v1_relat_1(X25)|(~v1_relat_1(X26)|r1_tarski(k5_relat_1(k7_relat_1(X25,X24),X26),k5_relat_1(X25,X26)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t92_relat_1])])])).
% 0.47/0.69  cnf(c_0_53, negated_conjecture, (v1_relat_1(k4_relat_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_26])])).
% 0.47/0.69  cnf(c_0_54, negated_conjecture, (k4_relat_1(k4_relat_1(esk2_0))=esk2_0), inference(spm,[status(thm)],[c_0_45, c_0_26])).
% 0.47/0.69  cnf(c_0_55, plain, (k1_relat_1(k4_relat_1(k7_relat_1(X1,X2)))=k2_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_46, c_0_44])).
% 0.47/0.69  cnf(c_0_56, plain, (k2_relat_1(k7_relat_1(k4_relat_1(X1),X2))=k9_relat_1(k4_relat_1(X1),X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_47, c_0_24])).
% 0.47/0.69  cnf(c_0_57, plain, (k5_relat_1(k6_relat_1(X1),k4_relat_1(X2))=k7_relat_1(k4_relat_1(X2),X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_29, c_0_24])).
% 0.47/0.69  cnf(c_0_58, negated_conjecture, (~r1_tarski(k3_xboole_0(k1_relat_1(esk2_0),esk1_0),k9_relat_1(k4_relat_1(esk2_0),k9_relat_1(esk2_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.47/0.69  cnf(c_0_59, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.47/0.69  cnf(c_0_60, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.47/0.69  cnf(c_0_61, plain, (k1_relat_1(k7_relat_1(X1,X2))=k3_xboole_0(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.47/0.69  cnf(c_0_62, plain, (r1_tarski(k1_relat_1(X1),k1_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.47/0.69  cnf(c_0_63, plain, (r1_tarski(k5_relat_1(k7_relat_1(X1,X3),X2),k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.47/0.69  cnf(c_0_64, negated_conjecture, (k4_relat_1(k5_relat_1(X1,k4_relat_1(esk2_0)))=k5_relat_1(esk2_0,k4_relat_1(X1))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_53]), c_0_54])).
% 0.47/0.69  cnf(c_0_65, plain, (k1_relat_1(k4_relat_1(k7_relat_1(k4_relat_1(X1),X2)))=k2_relat_1(k7_relat_1(k4_relat_1(X1),X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_55, c_0_24])).
% 0.47/0.69  cnf(c_0_66, negated_conjecture, (k2_relat_1(k7_relat_1(k4_relat_1(esk2_0),X1))=k9_relat_1(k4_relat_1(esk2_0),X1)), inference(spm,[status(thm)],[c_0_56, c_0_26])).
% 0.47/0.69  cnf(c_0_67, negated_conjecture, (k5_relat_1(k6_relat_1(X1),k4_relat_1(esk2_0))=k7_relat_1(k4_relat_1(esk2_0),X1)), inference(spm,[status(thm)],[c_0_57, c_0_26])).
% 0.47/0.69  cnf(c_0_68, negated_conjecture, (~r1_tarski(k4_xboole_0(k1_relat_1(esk2_0),k4_xboole_0(k1_relat_1(esk2_0),esk1_0)),k9_relat_1(k4_relat_1(esk2_0),k9_relat_1(esk2_0,esk1_0)))), inference(rw,[status(thm)],[c_0_58, c_0_59])).
% 0.47/0.69  cnf(c_0_69, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_59]), c_0_59])).
% 0.47/0.69  cnf(c_0_70, plain, (k1_relat_1(k7_relat_1(X1,X2))=k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_61, c_0_59])).
% 0.47/0.69  cnf(c_0_71, plain, (r1_tarski(k1_relat_1(k5_relat_1(k7_relat_1(X1,X2),X3)),k1_relat_1(k5_relat_1(X1,X3)))|~v1_relat_1(k5_relat_1(k7_relat_1(X1,X2),X3))|~v1_relat_1(k5_relat_1(X1,X3))|~v1_relat_1(X3)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.47/0.69  cnf(c_0_72, plain, (k5_relat_1(k7_relat_1(X1,X2),k6_relat_1(k2_relat_1(k7_relat_1(X1,X2))))=k7_relat_1(X1,X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_23, c_0_44])).
% 0.47/0.69  cnf(c_0_73, negated_conjecture, (v1_relat_1(k5_relat_1(esk2_0,k4_relat_1(X1)))|~v1_relat_1(k5_relat_1(X1,k4_relat_1(esk2_0)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_24, c_0_64])).
% 0.47/0.69  cnf(c_0_74, negated_conjecture, (k1_relat_1(k4_relat_1(k7_relat_1(k4_relat_1(esk2_0),X1)))=k9_relat_1(k4_relat_1(esk2_0),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_26]), c_0_66])).
% 0.47/0.69  cnf(c_0_75, negated_conjecture, (k4_relat_1(k7_relat_1(k4_relat_1(esk2_0),X1))=k5_relat_1(esk2_0,k6_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_67]), c_0_34]), c_0_36])])).
% 0.47/0.69  cnf(c_0_76, negated_conjecture, (~r1_tarski(k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,k1_relat_1(esk2_0))),k9_relat_1(k4_relat_1(esk2_0),k9_relat_1(esk2_0,esk1_0)))), inference(rw,[status(thm)],[c_0_68, c_0_69])).
% 0.47/0.69  cnf(c_0_77, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k1_relat_1(X2)))=k1_relat_1(k7_relat_1(X2,X1))|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.47/0.69  cnf(c_0_78, plain, (r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),k1_relat_1(k5_relat_1(X1,k6_relat_1(k2_relat_1(k7_relat_1(X1,X2))))))|~v1_relat_1(k5_relat_1(X1,k6_relat_1(k2_relat_1(k7_relat_1(X1,X2)))))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_36])]), c_0_44])).
% 0.47/0.69  cnf(c_0_79, negated_conjecture, (v1_relat_1(k5_relat_1(esk2_0,k6_relat_1(X1)))|~v1_relat_1(k7_relat_1(k4_relat_1(esk2_0),X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_67]), c_0_34]), c_0_36])])).
% 0.47/0.69  cnf(c_0_80, negated_conjecture, (k2_relat_1(k7_relat_1(esk2_0,X1))=k9_relat_1(esk2_0,X1)), inference(spm,[status(thm)],[c_0_47, c_0_26])).
% 0.47/0.69  cnf(c_0_81, negated_conjecture, (k1_relat_1(k5_relat_1(esk2_0,k6_relat_1(X1)))=k9_relat_1(k4_relat_1(esk2_0),X1)), inference(rw,[status(thm)],[c_0_74, c_0_75])).
% 0.47/0.69  cnf(c_0_82, negated_conjecture, (~r1_tarski(k1_relat_1(k7_relat_1(esk2_0,esk1_0)),k9_relat_1(k4_relat_1(esk2_0),k9_relat_1(esk2_0,esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_26])])).
% 0.47/0.69  cnf(c_0_83, negated_conjecture, (r1_tarski(k1_relat_1(k7_relat_1(esk2_0,X1)),k9_relat_1(k4_relat_1(esk2_0),k9_relat_1(esk2_0,X1)))|~v1_relat_1(k7_relat_1(k4_relat_1(esk2_0),k9_relat_1(esk2_0,X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_80]), c_0_81]), c_0_26]), c_0_80])])).
% 0.47/0.69  cnf(c_0_84, negated_conjecture, (~v1_relat_1(k7_relat_1(k4_relat_1(esk2_0),k9_relat_1(esk2_0,esk1_0)))), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 0.47/0.69  cnf(c_0_85, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_44]), c_0_53])]), ['proof']).
% 0.47/0.69  # SZS output end CNFRefutation
% 0.47/0.69  # Proof object total steps             : 86
% 0.47/0.69  # Proof object clause steps            : 53
% 0.47/0.69  # Proof object formula steps           : 33
% 0.47/0.69  # Proof object conjectures             : 29
% 0.47/0.69  # Proof object clause conjectures      : 26
% 0.47/0.69  # Proof object formula conjectures     : 3
% 0.47/0.69  # Proof object initial clauses used    : 18
% 0.47/0.69  # Proof object initial formulas used   : 16
% 0.47/0.69  # Proof object generating inferences   : 29
% 0.47/0.69  # Proof object simplifying inferences  : 33
% 0.47/0.69  # Training examples: 0 positive, 0 negative
% 0.47/0.69  # Parsed axioms                        : 16
% 0.47/0.69  # Removed by relevancy pruning/SinE    : 0
% 0.47/0.69  # Initial clauses                      : 19
% 0.47/0.69  # Removed in clause preprocessing      : 1
% 0.47/0.69  # Initial clauses in saturation        : 18
% 0.47/0.69  # Processed clauses                    : 1708
% 0.47/0.69  # ...of these trivial                  : 238
% 0.47/0.69  # ...subsumed                          : 655
% 0.47/0.69  # ...remaining for further processing  : 815
% 0.47/0.69  # Other redundant clauses eliminated   : 0
% 0.47/0.69  # Clauses deleted for lack of memory   : 0
% 0.47/0.69  # Backward-subsumed                    : 2
% 0.47/0.69  # Backward-rewritten                   : 59
% 0.47/0.69  # Generated clauses                    : 18447
% 0.47/0.69  # ...of the previous two non-trivial   : 15973
% 0.47/0.69  # Contextual simplify-reflections      : 5
% 0.47/0.69  # Paramodulations                      : 18447
% 0.47/0.69  # Factorizations                       : 0
% 0.47/0.69  # Equation resolutions                 : 0
% 0.47/0.69  # Propositional unsat checks           : 0
% 0.47/0.69  #    Propositional check models        : 0
% 0.47/0.69  #    Propositional check unsatisfiable : 0
% 0.47/0.69  #    Propositional clauses             : 0
% 0.47/0.69  #    Propositional clauses after purity: 0
% 0.47/0.69  #    Propositional unsat core size     : 0
% 0.47/0.69  #    Propositional preprocessing time  : 0.000
% 0.47/0.69  #    Propositional encoding time       : 0.000
% 0.47/0.69  #    Propositional solver time         : 0.000
% 0.47/0.69  #    Success case prop preproc time    : 0.000
% 0.47/0.69  #    Success case prop encoding time   : 0.000
% 0.47/0.69  #    Success case prop solver time     : 0.000
% 0.47/0.69  # Current number of processed clauses  : 736
% 0.47/0.69  #    Positive orientable unit clauses  : 156
% 0.47/0.69  #    Positive unorientable unit clauses: 2
% 0.47/0.69  #    Negative unit clauses             : 2
% 0.47/0.69  #    Non-unit-clauses                  : 576
% 0.47/0.69  # Current number of unprocessed clauses: 14214
% 0.47/0.69  # ...number of literals in the above   : 52387
% 0.47/0.69  # Current number of archived formulas  : 0
% 0.47/0.69  # Current number of archived clauses   : 80
% 0.47/0.69  # Clause-clause subsumption calls (NU) : 27181
% 0.47/0.69  # Rec. Clause-clause subsumption calls : 24311
% 0.47/0.69  # Non-unit clause-clause subsumptions  : 658
% 0.47/0.69  # Unit Clause-clause subsumption calls : 511
% 0.47/0.69  # Rewrite failures with RHS unbound    : 0
% 0.47/0.69  # BW rewrite match attempts            : 399
% 0.47/0.69  # BW rewrite match successes           : 50
% 0.47/0.69  # Condensation attempts                : 0
% 0.47/0.69  # Condensation successes               : 0
% 0.47/0.69  # Termbank termtop insertions          : 675787
% 0.47/0.69  
% 0.47/0.69  # -------------------------------------------------
% 0.47/0.69  # User time                : 0.339 s
% 0.47/0.69  # System time              : 0.011 s
% 0.47/0.69  # Total time               : 0.351 s
% 0.47/0.69  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------

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
% DateTime   : Thu Dec  3 10:54:51 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 109 expanded)
%              Number of clauses        :   33 (  44 expanded)
%              Number of leaves         :   15 (  27 expanded)
%              Depth                    :    8
%              Number of atoms          :  121 ( 231 expanded)
%              Number of equality atoms :   44 (  44 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t146_funct_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(dt_k4_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k4_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(t90_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k1_relat_1(k7_relat_1(X2,X1)) = k3_xboole_0(k1_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(dt_k8_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => v1_relat_1(k8_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(t123_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X1,X2) = k5_relat_1(X2,k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

fof(t54_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k4_relat_1(k5_relat_1(X1,X2)) = k5_relat_1(k4_relat_1(X2),k4_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).

fof(fc4_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v2_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(t72_relat_1,axiom,(
    ! [X1] : k4_relat_1(k6_relat_1(X1)) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_relat_1)).

fof(t94_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k5_relat_1(k6_relat_1(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(t182_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(t163_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k3_xboole_0(k1_relat_1(X2),X1),k9_relat_1(k4_relat_1(X2),k9_relat_1(X2,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_relat_1)).

fof(t91_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => k1_relat_1(k7_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(t37_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k2_relat_1(X1) = k1_relat_1(k4_relat_1(X1))
        & k1_relat_1(X1) = k2_relat_1(k4_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X1,k1_relat_1(X2))
         => r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))) ) ) ),
    inference(assume_negation,[status(cth)],[t146_funct_1])).

fof(c_0_16,plain,(
    ! [X3] :
      ( ~ v1_relat_1(X3)
      | v1_relat_1(k4_relat_1(X3)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relat_1])])).

fof(c_0_17,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & r1_tarski(esk1_0,k1_relat_1(esk2_0))
    & ~ r1_tarski(esk1_0,k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

fof(c_0_18,plain,(
    ! [X19,X20] :
      ( ~ v1_relat_1(X20)
      | k1_relat_1(k7_relat_1(X20,X19)) = k3_xboole_0(k1_relat_1(X20),X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).

fof(c_0_19,plain,(
    ! [X4,X5] :
      ( ~ v1_relat_1(X5)
      | v1_relat_1(k8_relat_1(X4,X5)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relat_1])])).

fof(c_0_20,plain,(
    ! [X6,X7] :
      ( ~ v1_relat_1(X7)
      | k8_relat_1(X6,X7) = k5_relat_1(X7,k6_relat_1(X6)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_relat_1])])).

fof(c_0_21,plain,(
    ! [X15,X16] :
      ( ~ v1_relat_1(X15)
      | ~ v1_relat_1(X16)
      | k4_relat_1(k5_relat_1(X15,X16)) = k5_relat_1(k4_relat_1(X16),k4_relat_1(X15)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_relat_1])])])).

fof(c_0_22,plain,(
    ! [X25] :
      ( v1_relat_1(k6_relat_1(X25))
      & v2_funct_1(k6_relat_1(X25)) ) ),
    inference(variable_rename,[status(thm)],[fc4_funct_1])).

fof(c_0_23,plain,(
    ! [X18] : k4_relat_1(k6_relat_1(X18)) = k6_relat_1(X18) ),
    inference(variable_rename,[status(thm)],[t72_relat_1])).

fof(c_0_24,plain,(
    ! [X23,X24] :
      ( ~ v1_relat_1(X24)
      | k7_relat_1(X24,X23) = k5_relat_1(k6_relat_1(X23),X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).

cnf(c_0_25,plain,
    ( v1_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_27,plain,(
    ! [X12,X13] :
      ( ~ v1_relat_1(X12)
      | ~ v1_relat_1(X13)
      | k1_relat_1(k5_relat_1(X12,X13)) = k10_relat_1(X12,k1_relat_1(X13)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).

fof(c_0_28,plain,(
    ! [X17] :
      ( k1_relat_1(k6_relat_1(X17)) = X17
      & k2_relat_1(k6_relat_1(X17)) = X17 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_29,plain,(
    ! [X10,X11] :
      ( ~ v1_relat_1(X11)
      | r1_tarski(k3_xboole_0(k1_relat_1(X11),X10),k9_relat_1(k4_relat_1(X11),k9_relat_1(X11,X10))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t163_relat_1])])).

cnf(c_0_30,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k3_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_31,plain,(
    ! [X21,X22] :
      ( ~ v1_relat_1(X22)
      | ~ r1_tarski(X21,k1_relat_1(X22))
      | k1_relat_1(k7_relat_1(X22,X21)) = X21 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_relat_1])])).

cnf(c_0_32,plain,
    ( v1_relat_1(k8_relat_1(X2,X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_33,plain,
    ( k8_relat_1(X2,X1) = k5_relat_1(X1,k6_relat_1(X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_34,plain,
    ( k4_relat_1(k5_relat_1(X1,X2)) = k5_relat_1(k4_relat_1(X2),k4_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_35,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_36,plain,
    ( k4_relat_1(k6_relat_1(X1)) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_37,plain,
    ( k7_relat_1(X1,X2) = k5_relat_1(k6_relat_1(X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_38,negated_conjecture,
    ( v1_relat_1(k4_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_39,plain,(
    ! [X8,X9] :
      ( ~ v1_relat_1(X9)
      | k2_relat_1(k7_relat_1(X9,X8)) = k9_relat_1(X9,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

cnf(c_0_40,plain,
    ( k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_41,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_42,plain,
    ( r1_tarski(k3_xboole_0(k1_relat_1(X1),X2),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_43,negated_conjecture,
    ( k3_xboole_0(k1_relat_1(esk2_0),X1) = k1_relat_1(k7_relat_1(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_26])).

cnf(c_0_44,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(esk1_0,k1_relat_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_46,plain,(
    ! [X14] :
      ( ( k2_relat_1(X14) = k1_relat_1(k4_relat_1(X14))
        | ~ v1_relat_1(X14) )
      & ( k1_relat_1(X14) = k2_relat_1(k4_relat_1(X14))
        | ~ v1_relat_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_relat_1])])])).

cnf(c_0_47,negated_conjecture,
    ( v1_relat_1(k8_relat_1(X1,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_26])).

cnf(c_0_48,negated_conjecture,
    ( k8_relat_1(X1,esk2_0) = k5_relat_1(esk2_0,k6_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_26])).

cnf(c_0_49,plain,
    ( k5_relat_1(k6_relat_1(X1),k4_relat_1(X2)) = k4_relat_1(k5_relat_1(X2,k6_relat_1(X1)))
    | ~ v1_relat_1(X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])).

cnf(c_0_50,negated_conjecture,
    ( k5_relat_1(k6_relat_1(X1),k4_relat_1(esk2_0)) = k7_relat_1(k4_relat_1(esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_51,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_52,plain,
    ( k1_relat_1(k5_relat_1(X1,k6_relat_1(X2))) = k10_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_35]),c_0_41])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(k1_relat_1(k7_relat_1(esk2_0,X1)),k9_relat_1(k4_relat_1(esk2_0),k9_relat_1(esk2_0,X1))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_26]),c_0_43])).

cnf(c_0_54,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk2_0,esk1_0)) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_26])])).

cnf(c_0_55,plain,
    ( k1_relat_1(X1) = k2_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_56,negated_conjecture,
    ( v1_relat_1(k5_relat_1(esk2_0,k6_relat_1(X1))) ),
    inference(rw,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_57,negated_conjecture,
    ( k4_relat_1(k5_relat_1(esk2_0,k6_relat_1(X1))) = k7_relat_1(k4_relat_1(esk2_0),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_26]),c_0_50])).

cnf(c_0_58,negated_conjecture,
    ( k2_relat_1(k7_relat_1(k4_relat_1(esk2_0),X1)) = k9_relat_1(k4_relat_1(esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_38])).

cnf(c_0_59,negated_conjecture,
    ( k1_relat_1(k5_relat_1(esk2_0,k6_relat_1(X1))) = k10_relat_1(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_26])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(esk1_0,k9_relat_1(k4_relat_1(esk2_0),k9_relat_1(esk2_0,esk1_0))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_61,negated_conjecture,
    ( k9_relat_1(k4_relat_1(esk2_0),X1) = k10_relat_1(esk2_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57]),c_0_58]),c_0_59])).

cnf(c_0_62,negated_conjecture,
    ( ~ r1_tarski(esk1_0,k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_63,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_61]),c_0_62]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:39:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.40  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_PS_S0i
% 0.21/0.40  # and selection function SelectDiffNegLit.
% 0.21/0.40  #
% 0.21/0.40  # Preprocessing time       : 0.026 s
% 0.21/0.40  # Presaturation interreduction done
% 0.21/0.40  
% 0.21/0.40  # Proof found!
% 0.21/0.40  # SZS status Theorem
% 0.21/0.40  # SZS output start CNFRefutation
% 0.21/0.40  fof(t146_funct_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 0.21/0.40  fof(dt_k4_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>v1_relat_1(k4_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 0.21/0.40  fof(t90_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k1_relat_1(k7_relat_1(X2,X1))=k3_xboole_0(k1_relat_1(X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 0.21/0.40  fof(dt_k8_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>v1_relat_1(k8_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 0.21/0.40  fof(t123_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k8_relat_1(X1,X2)=k5_relat_1(X2,k6_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 0.21/0.40  fof(t54_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k4_relat_1(k5_relat_1(X1,X2))=k5_relat_1(k4_relat_1(X2),k4_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_relat_1)).
% 0.21/0.40  fof(fc4_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v2_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 0.21/0.40  fof(t72_relat_1, axiom, ![X1]:k4_relat_1(k6_relat_1(X1))=k6_relat_1(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_relat_1)).
% 0.21/0.40  fof(t94_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k5_relat_1(k6_relat_1(X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 0.21/0.40  fof(t182_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 0.21/0.40  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 0.21/0.40  fof(t163_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k3_xboole_0(k1_relat_1(X2),X1),k9_relat_1(k4_relat_1(X2),k9_relat_1(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t163_relat_1)).
% 0.21/0.40  fof(t91_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>k1_relat_1(k7_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 0.21/0.40  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 0.21/0.40  fof(t37_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k4_relat_1(X1))&k1_relat_1(X1)=k2_relat_1(k4_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 0.21/0.40  fof(c_0_15, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1)))))), inference(assume_negation,[status(cth)],[t146_funct_1])).
% 0.21/0.40  fof(c_0_16, plain, ![X3]:(~v1_relat_1(X3)|v1_relat_1(k4_relat_1(X3))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relat_1])])).
% 0.21/0.40  fof(c_0_17, negated_conjecture, (v1_relat_1(esk2_0)&(r1_tarski(esk1_0,k1_relat_1(esk2_0))&~r1_tarski(esk1_0,k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.21/0.40  fof(c_0_18, plain, ![X19, X20]:(~v1_relat_1(X20)|k1_relat_1(k7_relat_1(X20,X19))=k3_xboole_0(k1_relat_1(X20),X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).
% 0.21/0.40  fof(c_0_19, plain, ![X4, X5]:(~v1_relat_1(X5)|v1_relat_1(k8_relat_1(X4,X5))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relat_1])])).
% 0.21/0.40  fof(c_0_20, plain, ![X6, X7]:(~v1_relat_1(X7)|k8_relat_1(X6,X7)=k5_relat_1(X7,k6_relat_1(X6))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_relat_1])])).
% 0.21/0.40  fof(c_0_21, plain, ![X15, X16]:(~v1_relat_1(X15)|(~v1_relat_1(X16)|k4_relat_1(k5_relat_1(X15,X16))=k5_relat_1(k4_relat_1(X16),k4_relat_1(X15)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_relat_1])])])).
% 0.21/0.40  fof(c_0_22, plain, ![X25]:(v1_relat_1(k6_relat_1(X25))&v2_funct_1(k6_relat_1(X25))), inference(variable_rename,[status(thm)],[fc4_funct_1])).
% 0.21/0.40  fof(c_0_23, plain, ![X18]:k4_relat_1(k6_relat_1(X18))=k6_relat_1(X18), inference(variable_rename,[status(thm)],[t72_relat_1])).
% 0.21/0.40  fof(c_0_24, plain, ![X23, X24]:(~v1_relat_1(X24)|k7_relat_1(X24,X23)=k5_relat_1(k6_relat_1(X23),X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).
% 0.21/0.40  cnf(c_0_25, plain, (v1_relat_1(k4_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.40  cnf(c_0_26, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.40  fof(c_0_27, plain, ![X12, X13]:(~v1_relat_1(X12)|(~v1_relat_1(X13)|k1_relat_1(k5_relat_1(X12,X13))=k10_relat_1(X12,k1_relat_1(X13)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).
% 0.21/0.40  fof(c_0_28, plain, ![X17]:(k1_relat_1(k6_relat_1(X17))=X17&k2_relat_1(k6_relat_1(X17))=X17), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.21/0.40  fof(c_0_29, plain, ![X10, X11]:(~v1_relat_1(X11)|r1_tarski(k3_xboole_0(k1_relat_1(X11),X10),k9_relat_1(k4_relat_1(X11),k9_relat_1(X11,X10)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t163_relat_1])])).
% 0.21/0.40  cnf(c_0_30, plain, (k1_relat_1(k7_relat_1(X1,X2))=k3_xboole_0(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.40  fof(c_0_31, plain, ![X21, X22]:(~v1_relat_1(X22)|(~r1_tarski(X21,k1_relat_1(X22))|k1_relat_1(k7_relat_1(X22,X21))=X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_relat_1])])).
% 0.21/0.40  cnf(c_0_32, plain, (v1_relat_1(k8_relat_1(X2,X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.40  cnf(c_0_33, plain, (k8_relat_1(X2,X1)=k5_relat_1(X1,k6_relat_1(X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.40  cnf(c_0_34, plain, (k4_relat_1(k5_relat_1(X1,X2))=k5_relat_1(k4_relat_1(X2),k4_relat_1(X1))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.40  cnf(c_0_35, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.40  cnf(c_0_36, plain, (k4_relat_1(k6_relat_1(X1))=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.40  cnf(c_0_37, plain, (k7_relat_1(X1,X2)=k5_relat_1(k6_relat_1(X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.21/0.40  cnf(c_0_38, negated_conjecture, (v1_relat_1(k4_relat_1(esk2_0))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.21/0.40  fof(c_0_39, plain, ![X8, X9]:(~v1_relat_1(X9)|k2_relat_1(k7_relat_1(X9,X8))=k9_relat_1(X9,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.21/0.40  cnf(c_0_40, plain, (k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.40  cnf(c_0_41, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.21/0.40  cnf(c_0_42, plain, (r1_tarski(k3_xboole_0(k1_relat_1(X1),X2),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X2)))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.21/0.40  cnf(c_0_43, negated_conjecture, (k3_xboole_0(k1_relat_1(esk2_0),X1)=k1_relat_1(k7_relat_1(esk2_0,X1))), inference(spm,[status(thm)],[c_0_30, c_0_26])).
% 0.21/0.40  cnf(c_0_44, plain, (k1_relat_1(k7_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.21/0.40  cnf(c_0_45, negated_conjecture, (r1_tarski(esk1_0,k1_relat_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.40  fof(c_0_46, plain, ![X14]:((k2_relat_1(X14)=k1_relat_1(k4_relat_1(X14))|~v1_relat_1(X14))&(k1_relat_1(X14)=k2_relat_1(k4_relat_1(X14))|~v1_relat_1(X14))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_relat_1])])])).
% 0.21/0.40  cnf(c_0_47, negated_conjecture, (v1_relat_1(k8_relat_1(X1,esk2_0))), inference(spm,[status(thm)],[c_0_32, c_0_26])).
% 0.21/0.40  cnf(c_0_48, negated_conjecture, (k8_relat_1(X1,esk2_0)=k5_relat_1(esk2_0,k6_relat_1(X1))), inference(spm,[status(thm)],[c_0_33, c_0_26])).
% 0.21/0.40  cnf(c_0_49, plain, (k5_relat_1(k6_relat_1(X1),k4_relat_1(X2))=k4_relat_1(k5_relat_1(X2,k6_relat_1(X1)))|~v1_relat_1(X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])).
% 0.21/0.40  cnf(c_0_50, negated_conjecture, (k5_relat_1(k6_relat_1(X1),k4_relat_1(esk2_0))=k7_relat_1(k4_relat_1(esk2_0),X1)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.21/0.40  cnf(c_0_51, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.21/0.40  cnf(c_0_52, plain, (k1_relat_1(k5_relat_1(X1,k6_relat_1(X2)))=k10_relat_1(X1,X2)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_35]), c_0_41])).
% 0.21/0.40  cnf(c_0_53, negated_conjecture, (r1_tarski(k1_relat_1(k7_relat_1(esk2_0,X1)),k9_relat_1(k4_relat_1(esk2_0),k9_relat_1(esk2_0,X1)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_26]), c_0_43])).
% 0.21/0.40  cnf(c_0_54, negated_conjecture, (k1_relat_1(k7_relat_1(esk2_0,esk1_0))=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_26])])).
% 0.21/0.40  cnf(c_0_55, plain, (k1_relat_1(X1)=k2_relat_1(k4_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.21/0.40  cnf(c_0_56, negated_conjecture, (v1_relat_1(k5_relat_1(esk2_0,k6_relat_1(X1)))), inference(rw,[status(thm)],[c_0_47, c_0_48])).
% 0.21/0.40  cnf(c_0_57, negated_conjecture, (k4_relat_1(k5_relat_1(esk2_0,k6_relat_1(X1)))=k7_relat_1(k4_relat_1(esk2_0),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_26]), c_0_50])).
% 0.21/0.40  cnf(c_0_58, negated_conjecture, (k2_relat_1(k7_relat_1(k4_relat_1(esk2_0),X1))=k9_relat_1(k4_relat_1(esk2_0),X1)), inference(spm,[status(thm)],[c_0_51, c_0_38])).
% 0.21/0.40  cnf(c_0_59, negated_conjecture, (k1_relat_1(k5_relat_1(esk2_0,k6_relat_1(X1)))=k10_relat_1(esk2_0,X1)), inference(spm,[status(thm)],[c_0_52, c_0_26])).
% 0.21/0.40  cnf(c_0_60, negated_conjecture, (r1_tarski(esk1_0,k9_relat_1(k4_relat_1(esk2_0),k9_relat_1(esk2_0,esk1_0)))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.21/0.40  cnf(c_0_61, negated_conjecture, (k9_relat_1(k4_relat_1(esk2_0),X1)=k10_relat_1(esk2_0,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57]), c_0_58]), c_0_59])).
% 0.21/0.40  cnf(c_0_62, negated_conjecture, (~r1_tarski(esk1_0,k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.40  cnf(c_0_63, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_61]), c_0_62]), ['proof']).
% 0.21/0.40  # SZS output end CNFRefutation
% 0.21/0.40  # Proof object total steps             : 64
% 0.21/0.40  # Proof object clause steps            : 33
% 0.21/0.40  # Proof object formula steps           : 31
% 0.21/0.40  # Proof object conjectures             : 20
% 0.21/0.40  # Proof object clause conjectures      : 17
% 0.21/0.40  # Proof object formula conjectures     : 3
% 0.21/0.40  # Proof object initial clauses used    : 17
% 0.21/0.40  # Proof object initial formulas used   : 15
% 0.21/0.40  # Proof object generating inferences   : 14
% 0.21/0.40  # Proof object simplifying inferences  : 12
% 0.21/0.40  # Training examples: 0 positive, 0 negative
% 0.21/0.40  # Parsed axioms                        : 15
% 0.21/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.40  # Initial clauses                      : 20
% 0.21/0.40  # Removed in clause preprocessing      : 0
% 0.21/0.40  # Initial clauses in saturation        : 20
% 0.21/0.40  # Processed clauses                    : 208
% 0.21/0.40  # ...of these trivial                  : 8
% 0.21/0.40  # ...subsumed                          : 0
% 0.21/0.40  # ...remaining for further processing  : 200
% 0.21/0.40  # Other redundant clauses eliminated   : 0
% 0.21/0.40  # Clauses deleted for lack of memory   : 0
% 0.21/0.40  # Backward-subsumed                    : 0
% 0.21/0.40  # Backward-rewritten                   : 36
% 0.21/0.40  # Generated clauses                    : 1393
% 0.21/0.40  # ...of the previous two non-trivial   : 1420
% 0.21/0.40  # Contextual simplify-reflections      : 0
% 0.21/0.40  # Paramodulations                      : 1393
% 0.21/0.40  # Factorizations                       : 0
% 0.21/0.40  # Equation resolutions                 : 0
% 0.21/0.40  # Propositional unsat checks           : 0
% 0.21/0.40  #    Propositional check models        : 0
% 0.21/0.40  #    Propositional check unsatisfiable : 0
% 0.21/0.40  #    Propositional clauses             : 0
% 0.21/0.40  #    Propositional clauses after purity: 0
% 0.21/0.40  #    Propositional unsat core size     : 0
% 0.21/0.40  #    Propositional preprocessing time  : 0.000
% 0.21/0.40  #    Propositional encoding time       : 0.000
% 0.21/0.40  #    Propositional solver time         : 0.000
% 0.21/0.40  #    Success case prop preproc time    : 0.000
% 0.21/0.40  #    Success case prop encoding time   : 0.000
% 0.21/0.40  #    Success case prop solver time     : 0.000
% 0.21/0.40  # Current number of processed clauses  : 144
% 0.21/0.40  #    Positive orientable unit clauses  : 108
% 0.21/0.40  #    Positive unorientable unit clauses: 0
% 0.21/0.40  #    Negative unit clauses             : 1
% 0.21/0.40  #    Non-unit-clauses                  : 35
% 0.21/0.40  # Current number of unprocessed clauses: 1190
% 0.21/0.40  # ...number of literals in the above   : 1309
% 0.21/0.40  # Current number of archived formulas  : 0
% 0.21/0.40  # Current number of archived clauses   : 56
% 0.21/0.40  # Clause-clause subsumption calls (NU) : 48
% 0.21/0.40  # Rec. Clause-clause subsumption calls : 48
% 0.21/0.40  # Non-unit clause-clause subsumptions  : 0
% 0.21/0.40  # Unit Clause-clause subsumption calls : 41
% 0.21/0.40  # Rewrite failures with RHS unbound    : 0
% 0.21/0.40  # BW rewrite match attempts            : 216
% 0.21/0.40  # BW rewrite match successes           : 23
% 0.21/0.40  # Condensation attempts                : 0
% 0.21/0.40  # Condensation successes               : 0
% 0.21/0.40  # Termbank termtop insertions          : 26732
% 0.21/0.40  
% 0.21/0.40  # -------------------------------------------------
% 0.21/0.40  # User time                : 0.050 s
% 0.21/0.40  # System time              : 0.003 s
% 0.21/0.40  # Total time               : 0.053 s
% 0.21/0.40  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------

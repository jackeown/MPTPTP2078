%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:47:49 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 170 expanded)
%              Number of clauses        :   39 (  70 expanded)
%              Number of leaves         :   14 (  42 expanded)
%              Depth                    :   12
%              Number of atoms          :  132 ( 436 expanded)
%              Number of equality atoms :   51 ( 107 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t59_setfam_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
         => ( r1_tarski(X2,X3)
           => r1_tarski(k8_setfam_1(X1,X3),k8_setfam_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_setfam_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(d10_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( ( X2 != k1_xboole_0
         => k8_setfam_1(X1,X2) = k6_setfam_1(X1,X2) )
        & ( X2 = k1_xboole_0
         => k8_setfam_1(X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).

fof(dt_k8_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => m1_subset_1(k8_setfam_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_setfam_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(redefinition_k6_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k6_setfam_1(X1,X2) = k1_setfam_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

fof(t49_zfmisc_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(l22_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => k2_xboole_0(k1_tarski(X1),X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_zfmisc_1)).

fof(cc1_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(t7_setfam_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => ( X1 = k1_xboole_0
        | r1_tarski(k1_setfam_1(X2),k1_setfam_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
           => ( r1_tarski(X2,X3)
             => r1_tarski(k8_setfam_1(X1,X3),k8_setfam_1(X1,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t59_setfam_1])).

fof(c_0_15,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))
    & m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))
    & r1_tarski(esk3_0,esk4_0)
    & ~ r1_tarski(k8_setfam_1(esk2_0,esk4_0),k8_setfam_1(esk2_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_16,plain,(
    ! [X27,X28] :
      ( ( ~ m1_subset_1(X27,k1_zfmisc_1(X28))
        | r1_tarski(X27,X28) )
      & ( ~ r1_tarski(X27,X28)
        | m1_subset_1(X27,k1_zfmisc_1(X28)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_17,negated_conjecture,
    ( ~ r1_tarski(k8_setfam_1(esk2_0,esk4_0),k8_setfam_1(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_19,plain,(
    ! [X19,X20] :
      ( ( X20 = k1_xboole_0
        | k8_setfam_1(X19,X20) = k6_setfam_1(X19,X20)
        | ~ m1_subset_1(X20,k1_zfmisc_1(k1_zfmisc_1(X19))) )
      & ( X20 != k1_xboole_0
        | k8_setfam_1(X19,X20) = X19
        | ~ m1_subset_1(X20,k1_zfmisc_1(k1_zfmisc_1(X19))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_setfam_1])])])).

cnf(c_0_20,negated_conjecture,
    ( ~ m1_subset_1(k8_setfam_1(esk2_0,esk4_0),k1_zfmisc_1(k8_setfam_1(esk2_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_21,plain,
    ( k8_setfam_1(X2,X1) = X2
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_23,plain,(
    ! [X21,X22] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(k1_zfmisc_1(X21)))
      | m1_subset_1(k8_setfam_1(X21,X22),k1_zfmisc_1(X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_setfam_1])])).

fof(c_0_24,plain,(
    ! [X9,X10] : k4_xboole_0(X9,X10) = k5_xboole_0(X9,k3_xboole_0(X9,X10)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_25,plain,(
    ! [X25,X26] : k1_setfam_1(k2_tarski(X25,X26)) = k3_xboole_0(X25,X26) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

cnf(c_0_26,negated_conjecture,
    ( esk3_0 != k1_xboole_0
    | ~ m1_subset_1(k8_setfam_1(esk2_0,esk4_0),k1_zfmisc_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])])).

cnf(c_0_27,plain,
    ( m1_subset_1(k8_setfam_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_29,plain,(
    ! [X11,X12] : k2_xboole_0(X11,X12) = k5_xboole_0(X11,k4_xboole_0(X12,X11)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_32,plain,(
    ! [X23,X24] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(k1_zfmisc_1(X23)))
      | k6_setfam_1(X23,X24) = k1_setfam_1(X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k6_setfam_1])])).

cnf(c_0_33,plain,
    ( X1 = k1_xboole_0
    | k8_setfam_1(X2,X1) = k6_setfam_1(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_34,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])])).

fof(c_0_35,plain,(
    ! [X15,X16] : k2_xboole_0(k1_tarski(X15),X16) != k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t49_zfmisc_1])).

cnf(c_0_36,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_30,c_0_31])).

fof(c_0_38,plain,(
    ! [X13,X14] :
      ( ~ r2_hidden(X13,X14)
      | k2_xboole_0(k1_tarski(X13),X14) = X14 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l22_zfmisc_1])])).

fof(c_0_39,plain,(
    ! [X17,X18] :
      ( ~ v1_xboole_0(X17)
      | ~ m1_subset_1(X18,k1_zfmisc_1(X17))
      | v1_xboole_0(X18) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

cnf(c_0_40,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_42,plain,(
    ! [X29,X30] :
      ( ~ r1_tarski(X29,X30)
      | X29 = k1_xboole_0
      | r1_tarski(k1_setfam_1(X30),k1_setfam_1(X29)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_setfam_1])])).

cnf(c_0_43,plain,
    ( k6_setfam_1(X2,X1) = k1_setfam_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_44,negated_conjecture,
    ( k6_setfam_1(esk2_0,esk3_0) = k8_setfam_1(esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_22]),c_0_34])).

cnf(c_0_45,plain,
    ( k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_46,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))) ),
    inference(rw,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_47,plain,
    ( k2_xboole_0(k1_tarski(X1),X2) = X2
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_48,plain,(
    ! [X8] :
      ( ~ v1_xboole_0(X8)
      | X8 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_49,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_51,plain,
    ( X1 = k1_xboole_0
    | r1_tarski(k1_setfam_1(X2),k1_setfam_1(X1))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_52,negated_conjecture,
    ( k1_setfam_1(esk3_0) = k8_setfam_1(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_22])])).

cnf(c_0_53,negated_conjecture,
    ( k6_setfam_1(esk2_0,esk4_0) = k8_setfam_1(esk2_0,esk4_0)
    | esk4_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_33,c_0_28])).

cnf(c_0_54,plain,
    ( k5_xboole_0(k1_tarski(X1),k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,k1_tarski(X1))))) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_55,plain,
    ( k5_xboole_0(k1_tarski(X1),k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,k1_tarski(X1))))) = X2
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_47,c_0_46])).

cnf(c_0_56,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_57,negated_conjecture,
    ( v1_xboole_0(esk3_0)
    | ~ v1_xboole_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(k1_setfam_1(esk4_0),k8_setfam_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_41]),c_0_52]),c_0_34])).

cnf(c_0_59,negated_conjecture,
    ( k1_setfam_1(esk4_0) = k8_setfam_1(esk2_0,esk4_0)
    | esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_53]),c_0_28])])).

cnf(c_0_60,plain,
    ( X1 != k1_xboole_0
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

fof(c_0_61,plain,(
    ! [X4,X5,X6] :
      ( ( ~ v1_xboole_0(X4)
        | ~ r2_hidden(X5,X4) )
      & ( r2_hidden(esk1_1(X6),X6)
        | v1_xboole_0(X6) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_62,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | ~ v1_xboole_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_63,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_17])).

cnf(c_0_64,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(er,[status(thm)],[c_0_60])).

cnf(c_0_65,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_66,negated_conjecture,
    ( ~ v1_xboole_0(k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_63]),c_0_34])).

cnf(c_0_67,plain,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_66]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:20:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___107_C41_F1_PI_AE_Q4_CS_SP_PS_S2U
% 0.13/0.38  # and selection function SelectNewComplexAHPExceptRRHorn.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.027 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t59_setfam_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(r1_tarski(X2,X3)=>r1_tarski(k8_setfam_1(X1,X3),k8_setfam_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_setfam_1)).
% 0.13/0.38  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.13/0.38  fof(d10_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>((X2!=k1_xboole_0=>k8_setfam_1(X1,X2)=k6_setfam_1(X1,X2))&(X2=k1_xboole_0=>k8_setfam_1(X1,X2)=X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_setfam_1)).
% 0.13/0.38  fof(dt_k8_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>m1_subset_1(k8_setfam_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_setfam_1)).
% 0.13/0.38  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.13/0.38  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.13/0.38  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.13/0.38  fof(redefinition_k6_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>k6_setfam_1(X1,X2)=k1_setfam_1(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 0.13/0.38  fof(t49_zfmisc_1, axiom, ![X1, X2]:k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 0.13/0.38  fof(l22_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>k2_xboole_0(k1_tarski(X1),X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 0.13/0.38  fof(cc1_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_xboole_0(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 0.13/0.38  fof(t7_setfam_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>(X1=k1_xboole_0|r1_tarski(k1_setfam_1(X2),k1_setfam_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_setfam_1)).
% 0.13/0.38  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.13/0.38  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.13/0.38  fof(c_0_14, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(r1_tarski(X2,X3)=>r1_tarski(k8_setfam_1(X1,X3),k8_setfam_1(X1,X2)))))), inference(assume_negation,[status(cth)],[t59_setfam_1])).
% 0.13/0.38  fof(c_0_15, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))&(m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))&(r1_tarski(esk3_0,esk4_0)&~r1_tarski(k8_setfam_1(esk2_0,esk4_0),k8_setfam_1(esk2_0,esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.13/0.38  fof(c_0_16, plain, ![X27, X28]:((~m1_subset_1(X27,k1_zfmisc_1(X28))|r1_tarski(X27,X28))&(~r1_tarski(X27,X28)|m1_subset_1(X27,k1_zfmisc_1(X28)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.13/0.38  cnf(c_0_17, negated_conjecture, (~r1_tarski(k8_setfam_1(esk2_0,esk4_0),k8_setfam_1(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_18, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  fof(c_0_19, plain, ![X19, X20]:((X20=k1_xboole_0|k8_setfam_1(X19,X20)=k6_setfam_1(X19,X20)|~m1_subset_1(X20,k1_zfmisc_1(k1_zfmisc_1(X19))))&(X20!=k1_xboole_0|k8_setfam_1(X19,X20)=X19|~m1_subset_1(X20,k1_zfmisc_1(k1_zfmisc_1(X19))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_setfam_1])])])).
% 0.13/0.38  cnf(c_0_20, negated_conjecture, (~m1_subset_1(k8_setfam_1(esk2_0,esk4_0),k1_zfmisc_1(k8_setfam_1(esk2_0,esk3_0)))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.13/0.38  cnf(c_0_21, plain, (k8_setfam_1(X2,X1)=X2|X1!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  fof(c_0_23, plain, ![X21, X22]:(~m1_subset_1(X22,k1_zfmisc_1(k1_zfmisc_1(X21)))|m1_subset_1(k8_setfam_1(X21,X22),k1_zfmisc_1(X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_setfam_1])])).
% 0.13/0.38  fof(c_0_24, plain, ![X9, X10]:k4_xboole_0(X9,X10)=k5_xboole_0(X9,k3_xboole_0(X9,X10)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.13/0.38  fof(c_0_25, plain, ![X25, X26]:k1_setfam_1(k2_tarski(X25,X26))=k3_xboole_0(X25,X26), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.13/0.38  cnf(c_0_26, negated_conjecture, (esk3_0!=k1_xboole_0|~m1_subset_1(k8_setfam_1(esk2_0,esk4_0),k1_zfmisc_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])])).
% 0.13/0.38  cnf(c_0_27, plain, (m1_subset_1(k8_setfam_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.38  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  fof(c_0_29, plain, ![X11, X12]:k2_xboole_0(X11,X12)=k5_xboole_0(X11,k4_xboole_0(X12,X11)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.13/0.38  cnf(c_0_30, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.38  cnf(c_0_31, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.38  fof(c_0_32, plain, ![X23, X24]:(~m1_subset_1(X24,k1_zfmisc_1(k1_zfmisc_1(X23)))|k6_setfam_1(X23,X24)=k1_setfam_1(X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k6_setfam_1])])).
% 0.13/0.38  cnf(c_0_33, plain, (X1=k1_xboole_0|k8_setfam_1(X2,X1)=k6_setfam_1(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_34, negated_conjecture, (esk3_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])])).
% 0.13/0.38  fof(c_0_35, plain, ![X15, X16]:k2_xboole_0(k1_tarski(X15),X16)!=k1_xboole_0, inference(variable_rename,[status(thm)],[t49_zfmisc_1])).
% 0.13/0.38  cnf(c_0_36, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.38  cnf(c_0_37, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_30, c_0_31])).
% 0.13/0.38  fof(c_0_38, plain, ![X13, X14]:(~r2_hidden(X13,X14)|k2_xboole_0(k1_tarski(X13),X14)=X14), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l22_zfmisc_1])])).
% 0.13/0.38  fof(c_0_39, plain, ![X17, X18]:(~v1_xboole_0(X17)|(~m1_subset_1(X18,k1_zfmisc_1(X17))|v1_xboole_0(X18))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).
% 0.13/0.38  cnf(c_0_40, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_41, negated_conjecture, (r1_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  fof(c_0_42, plain, ![X29, X30]:(~r1_tarski(X29,X30)|(X29=k1_xboole_0|r1_tarski(k1_setfam_1(X30),k1_setfam_1(X29)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_setfam_1])])).
% 0.13/0.38  cnf(c_0_43, plain, (k6_setfam_1(X2,X1)=k1_setfam_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.38  cnf(c_0_44, negated_conjecture, (k6_setfam_1(esk2_0,esk3_0)=k8_setfam_1(esk2_0,esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_22]), c_0_34])).
% 0.13/0.38  cnf(c_0_45, plain, (k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.38  cnf(c_0_46, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1))))), inference(rw,[status(thm)],[c_0_36, c_0_37])).
% 0.13/0.38  cnf(c_0_47, plain, (k2_xboole_0(k1_tarski(X1),X2)=X2|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.13/0.38  fof(c_0_48, plain, ![X8]:(~v1_xboole_0(X8)|X8=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.13/0.38  cnf(c_0_49, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.13/0.38  cnf(c_0_50, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.13/0.38  cnf(c_0_51, plain, (X1=k1_xboole_0|r1_tarski(k1_setfam_1(X2),k1_setfam_1(X1))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.13/0.38  cnf(c_0_52, negated_conjecture, (k1_setfam_1(esk3_0)=k8_setfam_1(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_22])])).
% 0.13/0.38  cnf(c_0_53, negated_conjecture, (k6_setfam_1(esk2_0,esk4_0)=k8_setfam_1(esk2_0,esk4_0)|esk4_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_33, c_0_28])).
% 0.13/0.38  cnf(c_0_54, plain, (k5_xboole_0(k1_tarski(X1),k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,k1_tarski(X1)))))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_45, c_0_46])).
% 0.13/0.38  cnf(c_0_55, plain, (k5_xboole_0(k1_tarski(X1),k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,k1_tarski(X1)))))=X2|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_47, c_0_46])).
% 0.13/0.38  cnf(c_0_56, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.13/0.38  cnf(c_0_57, negated_conjecture, (v1_xboole_0(esk3_0)|~v1_xboole_0(esk4_0)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.13/0.38  cnf(c_0_58, negated_conjecture, (r1_tarski(k1_setfam_1(esk4_0),k8_setfam_1(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_41]), c_0_52]), c_0_34])).
% 0.13/0.38  cnf(c_0_59, negated_conjecture, (k1_setfam_1(esk4_0)=k8_setfam_1(esk2_0,esk4_0)|esk4_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_53]), c_0_28])])).
% 0.13/0.38  cnf(c_0_60, plain, (X1!=k1_xboole_0|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.13/0.38  fof(c_0_61, plain, ![X4, X5, X6]:((~v1_xboole_0(X4)|~r2_hidden(X5,X4))&(r2_hidden(esk1_1(X6),X6)|v1_xboole_0(X6))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.13/0.38  cnf(c_0_62, negated_conjecture, (esk3_0=k1_xboole_0|~v1_xboole_0(esk4_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.13/0.38  cnf(c_0_63, negated_conjecture, (esk4_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_17])).
% 0.13/0.38  cnf(c_0_64, plain, (~r2_hidden(X1,k1_xboole_0)), inference(er,[status(thm)],[c_0_60])).
% 0.13/0.38  cnf(c_0_65, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.13/0.38  cnf(c_0_66, negated_conjecture, (~v1_xboole_0(k1_xboole_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_63]), c_0_34])).
% 0.13/0.38  cnf(c_0_67, plain, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_66]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 68
% 0.13/0.38  # Proof object clause steps            : 39
% 0.13/0.38  # Proof object formula steps           : 29
% 0.13/0.38  # Proof object conjectures             : 20
% 0.13/0.38  # Proof object clause conjectures      : 17
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 19
% 0.13/0.38  # Proof object initial formulas used   : 14
% 0.13/0.38  # Proof object generating inferences   : 15
% 0.13/0.38  # Proof object simplifying inferences  : 19
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 14
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 20
% 0.13/0.38  # Removed in clause preprocessing      : 3
% 0.13/0.38  # Initial clauses in saturation        : 17
% 0.13/0.38  # Processed clauses                    : 92
% 0.13/0.38  # ...of these trivial                  : 2
% 0.13/0.38  # ...subsumed                          : 19
% 0.13/0.38  # ...remaining for further processing  : 71
% 0.13/0.38  # Other redundant clauses eliminated   : 0
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 17
% 0.13/0.38  # Generated clauses                    : 62
% 0.13/0.38  # ...of the previous two non-trivial   : 71
% 0.13/0.38  # Contextual simplify-reflections      : 0
% 0.13/0.38  # Paramodulations                      : 60
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 2
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 37
% 0.13/0.38  #    Positive orientable unit clauses  : 10
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 9
% 0.13/0.38  #    Non-unit-clauses                  : 18
% 0.13/0.38  # Current number of unprocessed clauses: 10
% 0.13/0.38  # ...number of literals in the above   : 24
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 37
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 97
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 86
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 2
% 0.13/0.38  # Unit Clause-clause subsumption calls : 46
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 2
% 0.13/0.38  # BW rewrite match successes           : 1
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 2036
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.031 s
% 0.13/0.38  # System time              : 0.003 s
% 0.13/0.38  # Total time               : 0.034 s
% 0.13/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------

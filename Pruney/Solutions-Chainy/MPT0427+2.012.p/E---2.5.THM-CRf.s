%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:47:50 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 264 expanded)
%              Number of clauses        :   41 ( 110 expanded)
%              Number of leaves         :   13 (  66 expanded)
%              Depth                    :   11
%              Number of atoms          :  129 ( 683 expanded)
%              Number of equality atoms :   41 ( 168 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

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

fof(redefinition_k6_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k6_setfam_1(X1,X2) = k1_setfam_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

fof(dt_k8_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => m1_subset_1(k8_setfam_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_setfam_1)).

fof(d10_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( ( X2 != k1_xboole_0
         => k8_setfam_1(X1,X2) = k6_setfam_1(X1,X2) )
        & ( X2 = k1_xboole_0
         => k8_setfam_1(X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).

fof(t7_setfam_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => ( X1 = k1_xboole_0
        | r1_tarski(k1_setfam_1(X2),k1_setfam_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(cc1_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(t69_xboole_1,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ~ ( r1_tarski(X2,X1)
          & r1_xboole_0(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
           => ( r1_tarski(X2,X3)
             => r1_tarski(k8_setfam_1(X1,X3),k8_setfam_1(X1,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t59_setfam_1])).

fof(c_0_14,plain,(
    ! [X20,X21] :
      ( ~ m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(X20)))
      | k6_setfam_1(X20,X21) = k1_setfam_1(X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k6_setfam_1])])).

fof(c_0_15,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0)))
    & m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0)))
    & r1_tarski(esk2_0,esk3_0)
    & ~ r1_tarski(k8_setfam_1(esk1_0,esk3_0),k8_setfam_1(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

fof(c_0_16,plain,(
    ! [X18,X19] :
      ( ~ m1_subset_1(X19,k1_zfmisc_1(k1_zfmisc_1(X18)))
      | m1_subset_1(k8_setfam_1(X18,X19),k1_zfmisc_1(X18)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_setfam_1])])).

fof(c_0_17,plain,(
    ! [X16,X17] :
      ( ( X17 = k1_xboole_0
        | k8_setfam_1(X16,X17) = k6_setfam_1(X16,X17)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(X16))) )
      & ( X17 != k1_xboole_0
        | k8_setfam_1(X16,X17) = X16
        | ~ m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(X16))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_setfam_1])])])).

cnf(c_0_18,plain,
    ( k6_setfam_1(X2,X1) = k1_setfam_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_20,plain,(
    ! [X27,X28] :
      ( ~ r1_tarski(X27,X28)
      | X27 = k1_xboole_0
      | r1_tarski(k1_setfam_1(X28),k1_setfam_1(X27)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_setfam_1])])).

fof(c_0_21,plain,(
    ! [X13] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X13)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_22,plain,(
    ! [X22,X23] :
      ( ( ~ m1_subset_1(X22,k1_zfmisc_1(X23))
        | r1_tarski(X22,X23) )
      & ( ~ r1_tarski(X22,X23)
        | m1_subset_1(X22,k1_zfmisc_1(X23)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_23,plain,
    ( m1_subset_1(k8_setfam_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( X1 = k1_xboole_0
    | k8_setfam_1(X2,X1) = k6_setfam_1(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( k6_setfam_1(esk1_0,esk3_0) = k1_setfam_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_27,plain,
    ( X1 = k1_xboole_0
    | r1_tarski(k1_setfam_1(X2),k1_setfam_1(X1))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_29,plain,
    ( k8_setfam_1(X2,X1) = X2
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_30,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(k8_setfam_1(esk1_0,esk3_0),k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_19])).

fof(c_0_33,plain,(
    ! [X5,X6] : k4_xboole_0(X5,k2_xboole_0(X5,X6)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

fof(c_0_34,plain,(
    ! [X11,X12] : k2_xboole_0(X11,X12) = k5_xboole_0(X11,k4_xboole_0(X12,X11)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

cnf(c_0_35,negated_conjecture,
    ( ~ r1_tarski(k8_setfam_1(esk1_0,esk3_0),k8_setfam_1(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_36,negated_conjecture,
    ( k8_setfam_1(esk1_0,esk3_0) = k1_setfam_1(esk3_0)
    | esk3_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_19]),c_0_25])).

cnf(c_0_37,negated_conjecture,
    ( k6_setfam_1(esk1_0,esk2_0) = k1_setfam_1(esk2_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_26])).

cnf(c_0_38,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | r1_tarski(k1_setfam_1(esk3_0),k1_setfam_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_39,plain,
    ( k8_setfam_1(X1,k1_xboole_0) = X1 ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(k8_setfam_1(esk1_0,esk3_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

fof(c_0_41,plain,(
    ! [X9,X10] : r1_xboole_0(k4_xboole_0(X9,X10),X10) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

cnf(c_0_42,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_43,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_44,plain,(
    ! [X14,X15] :
      ( ~ v1_xboole_0(X14)
      | ~ m1_subset_1(X15,k1_zfmisc_1(X14))
      | v1_xboole_0(X15) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

cnf(c_0_45,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_46,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | ~ r1_tarski(k1_setfam_1(esk3_0),k8_setfam_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_47,negated_conjecture,
    ( k8_setfam_1(esk1_0,esk2_0) = k1_setfam_1(esk2_0)
    | esk2_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_26]),c_0_37])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(k1_setfam_1(esk3_0),k1_setfam_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_38]),c_0_39]),c_0_40])])).

fof(c_0_49,plain,(
    ! [X7,X8] :
      ( v1_xboole_0(X8)
      | ~ r1_tarski(X8,X7)
      | ~ r1_xboole_0(X8,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).

cnf(c_0_50,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_51,plain,
    ( k4_xboole_0(X1,k5_xboole_0(X1,k4_xboole_0(X2,X1))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_52,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_28])).

cnf(c_0_54,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])])).

cnf(c_0_55,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_56,plain,
    ( r1_xboole_0(k1_xboole_0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_57,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_30])).

fof(c_0_58,plain,(
    ! [X4] :
      ( ~ v1_xboole_0(X4)
      | X4 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_59,negated_conjecture,
    ( v1_xboole_0(esk2_0)
    | ~ v1_xboole_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_60,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_54]),c_0_39]),c_0_40])])).

cnf(c_0_61,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57])])).

cnf(c_0_62,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_63,negated_conjecture,
    ( v1_xboole_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_60]),c_0_61])])).

cnf(c_0_64,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_30]),c_0_39])).

cnf(c_0_65,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_66,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_64])).

cnf(c_0_67,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_60]),c_0_39]),c_0_65]),c_0_39]),c_0_66])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:30:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___107_B00_00_F1_PI_AE_Q4_CS_SP_PS_S064A
% 0.13/0.38  # and selection function SelectComplexG.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.027 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t59_setfam_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(r1_tarski(X2,X3)=>r1_tarski(k8_setfam_1(X1,X3),k8_setfam_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_setfam_1)).
% 0.13/0.38  fof(redefinition_k6_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>k6_setfam_1(X1,X2)=k1_setfam_1(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 0.13/0.38  fof(dt_k8_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>m1_subset_1(k8_setfam_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_setfam_1)).
% 0.13/0.38  fof(d10_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>((X2!=k1_xboole_0=>k8_setfam_1(X1,X2)=k6_setfam_1(X1,X2))&(X2=k1_xboole_0=>k8_setfam_1(X1,X2)=X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_setfam_1)).
% 0.13/0.38  fof(t7_setfam_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>(X1=k1_xboole_0|r1_tarski(k1_setfam_1(X2),k1_setfam_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_setfam_1)).
% 0.13/0.38  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.13/0.38  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.13/0.38  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 0.13/0.38  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.13/0.38  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.13/0.38  fof(cc1_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_xboole_0(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 0.13/0.38  fof(t69_xboole_1, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>~((r1_tarski(X2,X1)&r1_xboole_0(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 0.13/0.38  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.13/0.38  fof(c_0_13, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(r1_tarski(X2,X3)=>r1_tarski(k8_setfam_1(X1,X3),k8_setfam_1(X1,X2)))))), inference(assume_negation,[status(cth)],[t59_setfam_1])).
% 0.13/0.38  fof(c_0_14, plain, ![X20, X21]:(~m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(X20)))|k6_setfam_1(X20,X21)=k1_setfam_1(X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k6_setfam_1])])).
% 0.13/0.38  fof(c_0_15, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0)))&(m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0)))&(r1_tarski(esk2_0,esk3_0)&~r1_tarski(k8_setfam_1(esk1_0,esk3_0),k8_setfam_1(esk1_0,esk2_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.13/0.38  fof(c_0_16, plain, ![X18, X19]:(~m1_subset_1(X19,k1_zfmisc_1(k1_zfmisc_1(X18)))|m1_subset_1(k8_setfam_1(X18,X19),k1_zfmisc_1(X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_setfam_1])])).
% 0.13/0.38  fof(c_0_17, plain, ![X16, X17]:((X17=k1_xboole_0|k8_setfam_1(X16,X17)=k6_setfam_1(X16,X17)|~m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(X16))))&(X17!=k1_xboole_0|k8_setfam_1(X16,X17)=X16|~m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(X16))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_setfam_1])])])).
% 0.13/0.38  cnf(c_0_18, plain, (k6_setfam_1(X2,X1)=k1_setfam_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  fof(c_0_20, plain, ![X27, X28]:(~r1_tarski(X27,X28)|(X27=k1_xboole_0|r1_tarski(k1_setfam_1(X28),k1_setfam_1(X27)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_setfam_1])])).
% 0.13/0.38  fof(c_0_21, plain, ![X13]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X13)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.13/0.38  fof(c_0_22, plain, ![X22, X23]:((~m1_subset_1(X22,k1_zfmisc_1(X23))|r1_tarski(X22,X23))&(~r1_tarski(X22,X23)|m1_subset_1(X22,k1_zfmisc_1(X23)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.13/0.38  cnf(c_0_23, plain, (m1_subset_1(k8_setfam_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_24, plain, (X1=k1_xboole_0|k8_setfam_1(X2,X1)=k6_setfam_1(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.38  cnf(c_0_25, negated_conjecture, (k6_setfam_1(esk1_0,esk3_0)=k1_setfam_1(esk3_0)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.13/0.38  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_27, plain, (X1=k1_xboole_0|r1_tarski(k1_setfam_1(X2),k1_setfam_1(X1))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  cnf(c_0_28, negated_conjecture, (r1_tarski(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_29, plain, (k8_setfam_1(X2,X1)=X2|X1!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.38  cnf(c_0_30, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.38  cnf(c_0_31, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.38  cnf(c_0_32, negated_conjecture, (m1_subset_1(k8_setfam_1(esk1_0,esk3_0),k1_zfmisc_1(esk1_0))), inference(spm,[status(thm)],[c_0_23, c_0_19])).
% 0.13/0.38  fof(c_0_33, plain, ![X5, X6]:k4_xboole_0(X5,k2_xboole_0(X5,X6))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 0.13/0.38  fof(c_0_34, plain, ![X11, X12]:k2_xboole_0(X11,X12)=k5_xboole_0(X11,k4_xboole_0(X12,X11)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.13/0.38  cnf(c_0_35, negated_conjecture, (~r1_tarski(k8_setfam_1(esk1_0,esk3_0),k8_setfam_1(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_36, negated_conjecture, (k8_setfam_1(esk1_0,esk3_0)=k1_setfam_1(esk3_0)|esk3_0=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_19]), c_0_25])).
% 0.13/0.38  cnf(c_0_37, negated_conjecture, (k6_setfam_1(esk1_0,esk2_0)=k1_setfam_1(esk2_0)), inference(spm,[status(thm)],[c_0_18, c_0_26])).
% 0.13/0.38  cnf(c_0_38, negated_conjecture, (esk2_0=k1_xboole_0|r1_tarski(k1_setfam_1(esk3_0),k1_setfam_1(esk2_0))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.13/0.38  cnf(c_0_39, plain, (k8_setfam_1(X1,k1_xboole_0)=X1), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.13/0.38  cnf(c_0_40, negated_conjecture, (r1_tarski(k8_setfam_1(esk1_0,esk3_0),esk1_0)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.13/0.38  fof(c_0_41, plain, ![X9, X10]:r1_xboole_0(k4_xboole_0(X9,X10),X10), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.13/0.38  cnf(c_0_42, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.13/0.38  cnf(c_0_43, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.38  fof(c_0_44, plain, ![X14, X15]:(~v1_xboole_0(X14)|(~m1_subset_1(X15,k1_zfmisc_1(X14))|v1_xboole_0(X15))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).
% 0.13/0.38  cnf(c_0_45, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.38  cnf(c_0_46, negated_conjecture, (esk3_0=k1_xboole_0|~r1_tarski(k1_setfam_1(esk3_0),k8_setfam_1(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.13/0.38  cnf(c_0_47, negated_conjecture, (k8_setfam_1(esk1_0,esk2_0)=k1_setfam_1(esk2_0)|esk2_0=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_26]), c_0_37])).
% 0.13/0.38  cnf(c_0_48, negated_conjecture, (r1_tarski(k1_setfam_1(esk3_0),k1_setfam_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_38]), c_0_39]), c_0_40])])).
% 0.13/0.38  fof(c_0_49, plain, ![X7, X8]:(v1_xboole_0(X8)|(~r1_tarski(X8,X7)|~r1_xboole_0(X8,X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).
% 0.13/0.38  cnf(c_0_50, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.13/0.38  cnf(c_0_51, plain, (k4_xboole_0(X1,k5_xboole_0(X1,k4_xboole_0(X2,X1)))=k1_xboole_0), inference(rw,[status(thm)],[c_0_42, c_0_43])).
% 0.13/0.38  cnf(c_0_52, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.13/0.38  cnf(c_0_53, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(esk3_0))), inference(spm,[status(thm)],[c_0_45, c_0_28])).
% 0.13/0.38  cnf(c_0_54, negated_conjecture, (esk2_0=k1_xboole_0|esk3_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48])])).
% 0.13/0.38  cnf(c_0_55, plain, (v1_xboole_0(X1)|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.13/0.38  cnf(c_0_56, plain, (r1_xboole_0(k1_xboole_0,k5_xboole_0(X1,k4_xboole_0(X2,X1)))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.13/0.38  cnf(c_0_57, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_31, c_0_30])).
% 0.13/0.38  fof(c_0_58, plain, ![X4]:(~v1_xboole_0(X4)|X4=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.13/0.38  cnf(c_0_59, negated_conjecture, (v1_xboole_0(esk2_0)|~v1_xboole_0(esk3_0)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.13/0.38  cnf(c_0_60, negated_conjecture, (esk3_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_54]), c_0_39]), c_0_40])])).
% 0.13/0.38  cnf(c_0_61, plain, (v1_xboole_0(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57])])).
% 0.13/0.38  cnf(c_0_62, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.13/0.38  cnf(c_0_63, negated_conjecture, (v1_xboole_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_60]), c_0_61])])).
% 0.13/0.38  cnf(c_0_64, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_30]), c_0_39])).
% 0.13/0.38  cnf(c_0_65, negated_conjecture, (esk2_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.13/0.38  cnf(c_0_66, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_31, c_0_64])).
% 0.13/0.38  cnf(c_0_67, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_60]), c_0_39]), c_0_65]), c_0_39]), c_0_66])]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 68
% 0.13/0.38  # Proof object clause steps            : 41
% 0.13/0.38  # Proof object formula steps           : 27
% 0.13/0.38  # Proof object conjectures             : 23
% 0.13/0.38  # Proof object clause conjectures      : 20
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 18
% 0.13/0.38  # Proof object initial formulas used   : 13
% 0.13/0.38  # Proof object generating inferences   : 20
% 0.13/0.38  # Proof object simplifying inferences  : 23
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 14
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 19
% 0.13/0.38  # Removed in clause preprocessing      : 1
% 0.13/0.38  # Initial clauses in saturation        : 18
% 0.13/0.38  # Processed clauses                    : 100
% 0.13/0.38  # ...of these trivial                  : 3
% 0.13/0.38  # ...subsumed                          : 2
% 0.13/0.38  # ...remaining for further processing  : 94
% 0.13/0.38  # Other redundant clauses eliminated   : 0
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 46
% 0.13/0.38  # Generated clauses                    : 193
% 0.13/0.38  # ...of the previous two non-trivial   : 160
% 0.13/0.38  # Contextual simplify-reflections      : 0
% 0.13/0.38  # Paramodulations                      : 193
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 0
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
% 0.13/0.38  # Current number of processed clauses  : 30
% 0.13/0.38  #    Positive orientable unit clauses  : 15
% 0.13/0.38  #    Positive unorientable unit clauses: 1
% 0.13/0.38  #    Negative unit clauses             : 0
% 0.13/0.38  #    Non-unit-clauses                  : 14
% 0.13/0.38  # Current number of unprocessed clauses: 85
% 0.13/0.38  # ...number of literals in the above   : 172
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 65
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 176
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 167
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 2
% 0.13/0.38  # Unit Clause-clause subsumption calls : 52
% 0.13/0.38  # Rewrite failures with RHS unbound    : 2
% 0.13/0.38  # BW rewrite match attempts            : 27
% 0.13/0.38  # BW rewrite match successes           : 8
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 3193
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.033 s
% 0.13/0.38  # System time              : 0.002 s
% 0.13/0.38  # Total time               : 0.035 s
% 0.13/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------

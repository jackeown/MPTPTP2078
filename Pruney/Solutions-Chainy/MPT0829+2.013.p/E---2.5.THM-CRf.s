%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:57:33 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 478 expanded)
%              Number of clauses        :   42 ( 210 expanded)
%              Number of leaves         :   17 ( 130 expanded)
%              Depth                    :   14
%              Number of atoms          :  154 ( 665 expanded)
%              Number of equality atoms :   49 ( 458 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t43_funct_1,axiom,(
    ! [X1,X2] : k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) = k6_relat_1(k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t94_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k5_relat_1(k6_relat_1(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(t32_relset_1,conjecture,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( r1_tarski(k6_relat_1(X2),X3)
       => ( r1_tarski(X2,k1_relset_1(X1,X2,X3))
          & X2 = k2_relset_1(X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_relset_1)).

fof(t97_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X1)
       => k7_relat_1(X2,X1) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(t30_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( r1_tarski(k6_relat_1(X3),X4)
       => ( r1_tarski(X3,k1_relset_1(X1,X2,X4))
          & r1_tarski(X3,k2_relset_1(X1,X2,X4)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relset_1)).

fof(t25_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
              & r1_tarski(k2_relat_1(X1),k2_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(c_0_17,plain,(
    ! [X12,X13] : k1_setfam_1(k2_tarski(X12,X13)) = k3_xboole_0(X12,X13) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_18,plain,(
    ! [X7,X8] : k1_enumset1(X7,X7,X8) = k2_tarski(X7,X8) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_19,plain,(
    ! [X28,X29] : k5_relat_1(k6_relat_1(X29),k6_relat_1(X28)) = k6_relat_1(k3_xboole_0(X28,X29)) ),
    inference(variable_rename,[status(thm)],[t43_funct_1])).

cnf(c_0_20,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_22,plain,(
    ! [X9,X10,X11] : k2_enumset1(X9,X9,X10,X11) = k1_enumset1(X9,X10,X11) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_23,plain,(
    ! [X23] :
      ( k1_relat_1(k6_relat_1(X23)) = X23
      & k2_relat_1(k6_relat_1(X23)) = X23 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

cnf(c_0_24,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(k3_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_26,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_27,plain,(
    ! [X5,X6] : k2_tarski(X5,X6) = k2_tarski(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_28,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(k1_setfam_1(k2_enumset1(X2,X2,X2,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25]),c_0_26])).

cnf(c_0_30,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_31,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) = k2_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_32,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k2_enumset1(X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_21]),c_0_21]),c_0_26]),c_0_26])).

fof(c_0_33,plain,(
    ! [X24,X25] :
      ( ~ v1_relat_1(X25)
      | k7_relat_1(X25,X24) = k5_relat_1(k6_relat_1(X24),X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).

cnf(c_0_34,plain,
    ( k6_relat_1(k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) ),
    inference(rw,[status(thm)],[c_0_29,c_0_31])).

cnf(c_0_35,plain,
    ( k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k2_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_31])).

fof(c_0_36,plain,(
    ! [X18] : v1_relat_1(k6_relat_1(X18)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

cnf(c_0_37,plain,
    ( k7_relat_1(X1,X2) = k5_relat_1(k6_relat_1(X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_38,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_34])).

cnf(c_0_39,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_40,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
       => ( r1_tarski(k6_relat_1(X2),X3)
         => ( r1_tarski(X2,k1_relset_1(X1,X2,X3))
            & X2 = k2_relset_1(X1,X2,X3) ) ) ) ),
    inference(assume_negation,[status(cth)],[t32_relset_1])).

fof(c_0_41,plain,(
    ! [X26,X27] :
      ( ~ v1_relat_1(X27)
      | ~ r1_tarski(k1_relat_1(X27),X26)
      | k7_relat_1(X27,X26) = X27 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).

cnf(c_0_42,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])])).

fof(c_0_43,plain,(
    ! [X30,X31,X32] :
      ( ( v4_relat_1(X32,X30)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) )
      & ( v5_relat_1(X32,X31)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_44,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    & r1_tarski(k6_relat_1(esk2_0),esk3_0)
    & ( ~ r1_tarski(esk2_0,k1_relset_1(esk1_0,esk2_0,esk3_0))
      | esk2_0 != k2_relset_1(esk1_0,esk2_0,esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_40])])])).

fof(c_0_45,plain,(
    ! [X14,X15] :
      ( ~ v1_relat_1(X14)
      | ~ m1_subset_1(X15,k1_zfmisc_1(X14))
      | v1_relat_1(X15) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_46,plain,(
    ! [X19,X20] : v1_relat_1(k2_zfmisc_1(X19,X20)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_47,plain,(
    ! [X33,X34,X35] :
      ( ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
      | k2_relset_1(X33,X34,X35) = k2_relat_1(X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_48,plain,
    ( k7_relat_1(X1,X2) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_49,plain,
    ( k7_relat_1(k6_relat_1(X1),X2) = k7_relat_1(k6_relat_1(X2),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_42]),c_0_42])).

cnf(c_0_50,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_51,plain,(
    ! [X16,X17] :
      ( ( ~ v5_relat_1(X17,X16)
        | r1_tarski(k2_relat_1(X17),X16)
        | ~ v1_relat_1(X17) )
      & ( ~ r1_tarski(k2_relat_1(X17),X16)
        | v5_relat_1(X17,X16)
        | ~ v1_relat_1(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

cnf(c_0_52,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_54,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_55,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_56,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

fof(c_0_57,plain,(
    ! [X36,X37,X38,X39] :
      ( ( r1_tarski(X38,k1_relset_1(X36,X37,X39))
        | ~ r1_tarski(k6_relat_1(X38),X39)
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X36,X37))) )
      & ( r1_tarski(X38,k2_relset_1(X36,X37,X39))
        | ~ r1_tarski(k6_relat_1(X38),X39)
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X36,X37))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_relset_1])])])).

cnf(c_0_58,plain,
    ( k7_relat_1(k6_relat_1(X1),X2) = k6_relat_1(X2)
    | ~ r1_tarski(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50]),c_0_39])])).

cnf(c_0_59,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_60,negated_conjecture,
    ( v5_relat_1(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_61,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_53]),c_0_55])])).

cnf(c_0_62,negated_conjecture,
    ( ~ r1_tarski(esk2_0,k1_relset_1(esk1_0,esk2_0,esk3_0))
    | esk2_0 != k2_relset_1(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_63,negated_conjecture,
    ( k2_relset_1(esk1_0,esk2_0,esk3_0) = k2_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_53])).

cnf(c_0_64,plain,
    ( r1_tarski(X1,k1_relset_1(X2,X3,X4))
    | ~ r1_tarski(k6_relat_1(X1),X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_65,plain,
    ( k6_relat_1(X1) = k6_relat_1(X2)
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_58]),c_0_50]),c_0_39])])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61])])).

cnf(c_0_67,negated_conjecture,
    ( k2_relat_1(esk3_0) != esk2_0
    | ~ r1_tarski(esk2_0,k1_relset_1(esk1_0,esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_68,negated_conjecture,
    ( r1_tarski(X1,k1_relset_1(esk1_0,esk2_0,esk3_0))
    | ~ r1_tarski(k6_relat_1(X1),esk3_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_53])).

cnf(c_0_69,negated_conjecture,
    ( r1_tarski(k6_relat_1(esk2_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_70,plain,(
    ! [X21,X22] :
      ( ( r1_tarski(k1_relat_1(X21),k1_relat_1(X22))
        | ~ r1_tarski(X21,X22)
        | ~ v1_relat_1(X22)
        | ~ v1_relat_1(X21) )
      & ( r1_tarski(k2_relat_1(X21),k2_relat_1(X22))
        | ~ r1_tarski(X21,X22)
        | ~ v1_relat_1(X22)
        | ~ v1_relat_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).

cnf(c_0_71,negated_conjecture,
    ( k6_relat_1(k2_relat_1(esk3_0)) = k6_relat_1(esk2_0)
    | ~ r1_tarski(esk2_0,k2_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_72,negated_conjecture,
    ( k2_relat_1(esk3_0) != esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_69])])).

cnf(c_0_73,plain,
    ( r1_tarski(k2_relat_1(X1),k2_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_74,negated_conjecture,
    ( ~ r1_tarski(esk2_0,k2_relat_1(esk3_0)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_71]),c_0_28]),c_0_72])).

cnf(c_0_75,plain,
    ( r1_tarski(X1,k2_relat_1(X2))
    | ~ r1_tarski(k6_relat_1(X1),X2)
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_28]),c_0_39])])).

cnf(c_0_76,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_69]),c_0_61])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:42:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.029 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.13/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.38  fof(t43_funct_1, axiom, ![X1, X2]:k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))=k6_relat_1(k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 0.13/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.13/0.38  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 0.13/0.38  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.13/0.38  fof(t94_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k5_relat_1(k6_relat_1(X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 0.13/0.38  fof(dt_k6_relat_1, axiom, ![X1]:v1_relat_1(k6_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 0.13/0.38  fof(t32_relset_1, conjecture, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(r1_tarski(k6_relat_1(X2),X3)=>(r1_tarski(X2,k1_relset_1(X1,X2,X3))&X2=k2_relset_1(X1,X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_relset_1)).
% 0.13/0.38  fof(t97_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X2),X1)=>k7_relat_1(X2,X1)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 0.13/0.38  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.13/0.38  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.13/0.38  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.13/0.38  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.13/0.38  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 0.13/0.38  fof(t30_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(r1_tarski(k6_relat_1(X3),X4)=>(r1_tarski(X3,k1_relset_1(X1,X2,X4))&r1_tarski(X3,k2_relset_1(X1,X2,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_relset_1)).
% 0.13/0.38  fof(t25_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>(r1_tarski(k1_relat_1(X1),k1_relat_1(X2))&r1_tarski(k2_relat_1(X1),k2_relat_1(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 0.13/0.38  fof(c_0_17, plain, ![X12, X13]:k1_setfam_1(k2_tarski(X12,X13))=k3_xboole_0(X12,X13), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.13/0.38  fof(c_0_18, plain, ![X7, X8]:k1_enumset1(X7,X7,X8)=k2_tarski(X7,X8), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.38  fof(c_0_19, plain, ![X28, X29]:k5_relat_1(k6_relat_1(X29),k6_relat_1(X28))=k6_relat_1(k3_xboole_0(X28,X29)), inference(variable_rename,[status(thm)],[t43_funct_1])).
% 0.13/0.38  cnf(c_0_20, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.38  cnf(c_0_21, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.38  fof(c_0_22, plain, ![X9, X10, X11]:k2_enumset1(X9,X9,X10,X11)=k1_enumset1(X9,X10,X11), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.13/0.38  fof(c_0_23, plain, ![X23]:(k1_relat_1(k6_relat_1(X23))=X23&k2_relat_1(k6_relat_1(X23))=X23), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.13/0.38  cnf(c_0_24, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(k3_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_25, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 0.13/0.38  cnf(c_0_26, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.38  fof(c_0_27, plain, ![X5, X6]:k2_tarski(X5,X6)=k2_tarski(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.13/0.38  cnf(c_0_28, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.38  cnf(c_0_29, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(k1_setfam_1(k2_enumset1(X2,X2,X2,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_25]), c_0_26])).
% 0.13/0.38  cnf(c_0_30, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.38  cnf(c_0_31, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,X2))=k2_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.13/0.38  cnf(c_0_32, plain, (k2_enumset1(X1,X1,X1,X2)=k2_enumset1(X2,X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_21]), c_0_21]), c_0_26]), c_0_26])).
% 0.13/0.38  fof(c_0_33, plain, ![X24, X25]:(~v1_relat_1(X25)|k7_relat_1(X25,X24)=k5_relat_1(k6_relat_1(X24),X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).
% 0.13/0.38  cnf(c_0_34, plain, (k6_relat_1(k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))))=k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))), inference(rw,[status(thm)],[c_0_29, c_0_31])).
% 0.13/0.38  cnf(c_0_35, plain, (k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))=k2_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_31])).
% 0.13/0.38  fof(c_0_36, plain, ![X18]:v1_relat_1(k6_relat_1(X18)), inference(variable_rename,[status(thm)],[dt_k6_relat_1])).
% 0.13/0.38  cnf(c_0_37, plain, (k7_relat_1(X1,X2)=k5_relat_1(k6_relat_1(X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.13/0.38  cnf(c_0_38, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_34])).
% 0.13/0.38  cnf(c_0_39, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.13/0.38  fof(c_0_40, negated_conjecture, ~(![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(r1_tarski(k6_relat_1(X2),X3)=>(r1_tarski(X2,k1_relset_1(X1,X2,X3))&X2=k2_relset_1(X1,X2,X3))))), inference(assume_negation,[status(cth)],[t32_relset_1])).
% 0.13/0.38  fof(c_0_41, plain, ![X26, X27]:(~v1_relat_1(X27)|(~r1_tarski(k1_relat_1(X27),X26)|k7_relat_1(X27,X26)=X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).
% 0.13/0.38  cnf(c_0_42, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k7_relat_1(k6_relat_1(X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])])).
% 0.13/0.38  fof(c_0_43, plain, ![X30, X31, X32]:((v4_relat_1(X32,X30)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))))&(v5_relat_1(X32,X31)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.13/0.38  fof(c_0_44, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))&(r1_tarski(k6_relat_1(esk2_0),esk3_0)&(~r1_tarski(esk2_0,k1_relset_1(esk1_0,esk2_0,esk3_0))|esk2_0!=k2_relset_1(esk1_0,esk2_0,esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_40])])])).
% 0.13/0.38  fof(c_0_45, plain, ![X14, X15]:(~v1_relat_1(X14)|(~m1_subset_1(X15,k1_zfmisc_1(X14))|v1_relat_1(X15))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.13/0.38  fof(c_0_46, plain, ![X19, X20]:v1_relat_1(k2_zfmisc_1(X19,X20)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.13/0.38  fof(c_0_47, plain, ![X33, X34, X35]:(~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))|k2_relset_1(X33,X34,X35)=k2_relat_1(X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.13/0.38  cnf(c_0_48, plain, (k7_relat_1(X1,X2)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.13/0.38  cnf(c_0_49, plain, (k7_relat_1(k6_relat_1(X1),X2)=k7_relat_1(k6_relat_1(X2),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_42]), c_0_42])).
% 0.13/0.38  cnf(c_0_50, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.38  fof(c_0_51, plain, ![X16, X17]:((~v5_relat_1(X17,X16)|r1_tarski(k2_relat_1(X17),X16)|~v1_relat_1(X17))&(~r1_tarski(k2_relat_1(X17),X16)|v5_relat_1(X17,X16)|~v1_relat_1(X17))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.13/0.38  cnf(c_0_52, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.13/0.38  cnf(c_0_53, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.13/0.38  cnf(c_0_54, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.13/0.38  cnf(c_0_55, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.13/0.38  cnf(c_0_56, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.13/0.38  fof(c_0_57, plain, ![X36, X37, X38, X39]:((r1_tarski(X38,k1_relset_1(X36,X37,X39))|~r1_tarski(k6_relat_1(X38),X39)|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X36,X37))))&(r1_tarski(X38,k2_relset_1(X36,X37,X39))|~r1_tarski(k6_relat_1(X38),X39)|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X36,X37))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_relset_1])])])).
% 0.13/0.38  cnf(c_0_58, plain, (k7_relat_1(k6_relat_1(X1),X2)=k6_relat_1(X2)|~r1_tarski(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50]), c_0_39])])).
% 0.13/0.38  cnf(c_0_59, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.13/0.38  cnf(c_0_60, negated_conjecture, (v5_relat_1(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.13/0.38  cnf(c_0_61, negated_conjecture, (v1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_53]), c_0_55])])).
% 0.13/0.38  cnf(c_0_62, negated_conjecture, (~r1_tarski(esk2_0,k1_relset_1(esk1_0,esk2_0,esk3_0))|esk2_0!=k2_relset_1(esk1_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.13/0.38  cnf(c_0_63, negated_conjecture, (k2_relset_1(esk1_0,esk2_0,esk3_0)=k2_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_56, c_0_53])).
% 0.13/0.38  cnf(c_0_64, plain, (r1_tarski(X1,k1_relset_1(X2,X3,X4))|~r1_tarski(k6_relat_1(X1),X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.13/0.38  cnf(c_0_65, plain, (k6_relat_1(X1)=k6_relat_1(X2)|~r1_tarski(X2,X1)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_58]), c_0_50]), c_0_39])])).
% 0.13/0.38  cnf(c_0_66, negated_conjecture, (r1_tarski(k2_relat_1(esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61])])).
% 0.13/0.38  cnf(c_0_67, negated_conjecture, (k2_relat_1(esk3_0)!=esk2_0|~r1_tarski(esk2_0,k1_relset_1(esk1_0,esk2_0,esk3_0))), inference(rw,[status(thm)],[c_0_62, c_0_63])).
% 0.13/0.38  cnf(c_0_68, negated_conjecture, (r1_tarski(X1,k1_relset_1(esk1_0,esk2_0,esk3_0))|~r1_tarski(k6_relat_1(X1),esk3_0)), inference(spm,[status(thm)],[c_0_64, c_0_53])).
% 0.13/0.38  cnf(c_0_69, negated_conjecture, (r1_tarski(k6_relat_1(esk2_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.13/0.38  fof(c_0_70, plain, ![X21, X22]:((r1_tarski(k1_relat_1(X21),k1_relat_1(X22))|~r1_tarski(X21,X22)|~v1_relat_1(X22)|~v1_relat_1(X21))&(r1_tarski(k2_relat_1(X21),k2_relat_1(X22))|~r1_tarski(X21,X22)|~v1_relat_1(X22)|~v1_relat_1(X21))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).
% 0.13/0.38  cnf(c_0_71, negated_conjecture, (k6_relat_1(k2_relat_1(esk3_0))=k6_relat_1(esk2_0)|~r1_tarski(esk2_0,k2_relat_1(esk3_0))), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.13/0.38  cnf(c_0_72, negated_conjecture, (k2_relat_1(esk3_0)!=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_69])])).
% 0.13/0.38  cnf(c_0_73, plain, (r1_tarski(k2_relat_1(X1),k2_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.13/0.38  cnf(c_0_74, negated_conjecture, (~r1_tarski(esk2_0,k2_relat_1(esk3_0))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_71]), c_0_28]), c_0_72])).
% 0.13/0.38  cnf(c_0_75, plain, (r1_tarski(X1,k2_relat_1(X2))|~r1_tarski(k6_relat_1(X1),X2)|~v1_relat_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_28]), c_0_39])])).
% 0.13/0.38  cnf(c_0_76, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_69]), c_0_61])]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 77
% 0.13/0.38  # Proof object clause steps            : 42
% 0.13/0.38  # Proof object formula steps           : 35
% 0.13/0.38  # Proof object conjectures             : 16
% 0.13/0.38  # Proof object clause conjectures      : 13
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 20
% 0.13/0.38  # Proof object initial formulas used   : 17
% 0.13/0.38  # Proof object generating inferences   : 16
% 0.13/0.38  # Proof object simplifying inferences  : 34
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 17
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 24
% 0.13/0.38  # Removed in clause preprocessing      : 3
% 0.13/0.38  # Initial clauses in saturation        : 21
% 0.13/0.38  # Processed clauses                    : 82
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 4
% 0.13/0.38  # ...remaining for further processing  : 78
% 0.13/0.38  # Other redundant clauses eliminated   : 0
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 1
% 0.13/0.38  # Backward-rewritten                   : 9
% 0.13/0.38  # Generated clauses                    : 218
% 0.13/0.38  # ...of the previous two non-trivial   : 156
% 0.13/0.38  # Contextual simplify-reflections      : 0
% 0.13/0.38  # Paramodulations                      : 218
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
% 0.13/0.38  # Current number of processed clauses  : 47
% 0.13/0.38  #    Positive orientable unit clauses  : 18
% 0.13/0.38  #    Positive unorientable unit clauses: 2
% 0.13/0.38  #    Negative unit clauses             : 2
% 0.13/0.38  #    Non-unit-clauses                  : 25
% 0.13/0.38  # Current number of unprocessed clauses: 106
% 0.13/0.38  # ...number of literals in the above   : 180
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 34
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 104
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 88
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 4
% 0.13/0.38  # Unit Clause-clause subsumption calls : 23
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 23
% 0.13/0.38  # BW rewrite match successes           : 23
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 3955
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.034 s
% 0.13/0.38  # System time              : 0.004 s
% 0.13/0.38  # Total time               : 0.038 s
% 0.13/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------

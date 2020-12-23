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
% DateTime   : Thu Dec  3 10:57:12 EST 2020

% Result     : Theorem 0.48s
% Output     : CNFRefutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 157 expanded)
%              Number of clauses        :   40 (  72 expanded)
%              Number of leaves         :   14 (  39 expanded)
%              Depth                    :   15
%              Number of atoms          :  147 ( 285 expanded)
%              Number of equality atoms :   15 (  45 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t19_relset_1,conjecture,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => r1_tarski(k3_relat_1(X3),k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_relset_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t10_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(X1,k2_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t209_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => X2 = k7_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(t8_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t87_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(d6_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(dt_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k2_relset_1(X1,X2,X3),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
       => r1_tarski(k3_relat_1(X3),k2_xboole_0(X1,X2)) ) ),
    inference(assume_negation,[status(cth)],[t19_relset_1])).

fof(c_0_15,plain,(
    ! [X27,X28,X29] :
      ( ( v4_relat_1(X29,X27)
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))) )
      & ( v5_relat_1(X29,X28)
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_16,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    & ~ r1_tarski(k3_relat_1(esk3_0),k2_xboole_0(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_17,plain,(
    ! [X24,X25,X26] :
      ( ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))
      | v1_relat_1(X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_18,plain,(
    ! [X4,X5,X6] :
      ( ~ r1_tarski(X4,X5)
      | r1_tarski(X4,k2_xboole_0(X6,X5)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).

fof(c_0_19,plain,(
    ! [X15,X16] : k3_tarski(k2_tarski(X15,X16)) = k2_xboole_0(X15,X16) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_20,plain,(
    ! [X20,X21] :
      ( ~ v1_relat_1(X21)
      | ~ v4_relat_1(X21,X20)
      | X21 = k7_relat_1(X21,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).

cnf(c_0_21,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_24,plain,(
    ! [X12,X13,X14] :
      ( ~ r1_tarski(X12,X13)
      | ~ r1_tarski(X14,X13)
      | r1_tarski(k2_xboole_0(X12,X14),X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).

fof(c_0_25,plain,(
    ! [X7,X8,X9] :
      ( ~ r1_tarski(X7,X8)
      | ~ r1_tarski(X8,X9)
      | r1_tarski(X7,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,k2_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_28,plain,(
    ! [X22,X23] :
      ( ~ v1_relat_1(X23)
      | r1_tarski(k1_relat_1(k7_relat_1(X23,X22)),X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).

cnf(c_0_29,plain,
    ( X1 = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,negated_conjecture,
    ( v4_relat_1(esk3_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_31,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_22])).

cnf(c_0_32,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X3,X2)))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_35,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,negated_conjecture,
    ( k7_relat_1(esk3_0,esk1_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])])).

cnf(c_0_37,plain,
    ( r1_tarski(k3_tarski(k2_tarski(X1,X3)),X2)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_32,c_0_27])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))
    | ~ r1_tarski(X1,X4)
    | ~ r1_tarski(X4,X3) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk3_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_31])])).

fof(c_0_40,plain,(
    ! [X10,X11] : r1_tarski(X10,k2_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k3_tarski(k2_tarski(X3,X4)))
    | ~ r1_tarski(X4,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_37])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk3_0),k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_tarski(esk1_0,X2) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk3_0),X1)
    | ~ r1_tarski(esk1_0,X2)
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X3,X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_43,c_0_27])).

fof(c_0_46,plain,(
    ! [X19] :
      ( ~ v1_relat_1(X19)
      | k3_relat_1(X19) = k2_xboole_0(k1_relat_1(X19),k2_relat_1(X19)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk3_0),X1)
    | ~ r1_tarski(k3_tarski(k2_tarski(esk1_0,X2)),X1)
    | ~ r1_tarski(X3,X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_48,plain,
    ( k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk3_0),X1)
    | ~ r1_tarski(esk1_0,X1)
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X3,X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_37])).

fof(c_0_50,plain,(
    ! [X33,X34,X35] :
      ( ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
      | k2_relset_1(X33,X34,X35) = k2_relat_1(X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_51,plain,
    ( k3_relat_1(X1) = k3_tarski(k2_tarski(k1_relat_1(X1),k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_48,c_0_27])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk3_0),k3_tarski(k2_tarski(esk1_0,X1)))
    | ~ r1_tarski(X2,k3_tarski(k2_tarski(esk1_0,X1)))
    | ~ r1_tarski(X3,k3_tarski(k2_tarski(esk1_0,X1))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_45])).

fof(c_0_53,plain,(
    ! [X30,X31,X32] :
      ( ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
      | m1_subset_1(k2_relset_1(X30,X31,X32),k1_zfmisc_1(X31)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_relset_1])])).

cnf(c_0_54,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_55,plain,
    ( r1_tarski(k3_relat_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_51])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk3_0),k3_tarski(k2_tarski(esk1_0,X1)))
    | ~ r1_tarski(X2,k3_tarski(k2_tarski(esk1_0,X1))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_45])).

fof(c_0_57,plain,(
    ! [X17,X18] :
      ( ( ~ m1_subset_1(X17,k1_zfmisc_1(X18))
        | r1_tarski(X17,X18) )
      & ( ~ r1_tarski(X17,X18)
        | m1_subset_1(X17,k1_zfmisc_1(X18)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_58,plain,
    ( m1_subset_1(k2_relset_1(X2,X3,X1),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_59,negated_conjecture,
    ( k2_relset_1(esk1_0,esk2_0,esk3_0) = k2_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_22])).

cnf(c_0_60,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(esk3_0),k2_xboole_0(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_61,plain,
    ( r1_tarski(k3_relat_1(X1),k3_tarski(k2_tarski(X2,X3)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),k3_tarski(k2_tarski(X2,X3)))
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(spm,[status(thm)],[c_0_55,c_0_34])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk3_0),k3_tarski(k2_tarski(esk1_0,X1))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_45])).

cnf(c_0_63,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(k2_relat_1(esk3_0),k1_zfmisc_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_22])])).

cnf(c_0_65,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(esk3_0),k3_tarski(k2_tarski(esk1_0,esk2_0))) ),
    inference(rw,[status(thm)],[c_0_60,c_0_27])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(k3_relat_1(esk3_0),k3_tarski(k2_tarski(esk1_0,X1)))
    | ~ r1_tarski(k2_relat_1(esk3_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_31])])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk3_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_68,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:55:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.48/0.65  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.48/0.65  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.48/0.65  #
% 0.48/0.65  # Preprocessing time       : 0.027 s
% 0.48/0.65  # Presaturation interreduction done
% 0.48/0.65  
% 0.48/0.65  # Proof found!
% 0.48/0.65  # SZS status Theorem
% 0.48/0.65  # SZS output start CNFRefutation
% 0.48/0.65  fof(t19_relset_1, conjecture, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>r1_tarski(k3_relat_1(X3),k2_xboole_0(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_relset_1)).
% 0.48/0.65  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.48/0.65  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.48/0.65  fof(t10_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(X1,k2_xboole_0(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 0.48/0.65  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.48/0.65  fof(t209_relat_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>X2=k7_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 0.48/0.65  fof(t8_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 0.48/0.65  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.48/0.65  fof(t87_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 0.48/0.65  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.48/0.65  fof(d6_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 0.48/0.65  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.48/0.65  fof(dt_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k2_relset_1(X1,X2,X3),k1_zfmisc_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 0.48/0.65  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.48/0.65  fof(c_0_14, negated_conjecture, ~(![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>r1_tarski(k3_relat_1(X3),k2_xboole_0(X1,X2)))), inference(assume_negation,[status(cth)],[t19_relset_1])).
% 0.48/0.65  fof(c_0_15, plain, ![X27, X28, X29]:((v4_relat_1(X29,X27)|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))))&(v5_relat_1(X29,X28)|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.48/0.65  fof(c_0_16, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))&~r1_tarski(k3_relat_1(esk3_0),k2_xboole_0(esk1_0,esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.48/0.65  fof(c_0_17, plain, ![X24, X25, X26]:(~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))|v1_relat_1(X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.48/0.65  fof(c_0_18, plain, ![X4, X5, X6]:(~r1_tarski(X4,X5)|r1_tarski(X4,k2_xboole_0(X6,X5))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).
% 0.48/0.65  fof(c_0_19, plain, ![X15, X16]:k3_tarski(k2_tarski(X15,X16))=k2_xboole_0(X15,X16), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.48/0.65  fof(c_0_20, plain, ![X20, X21]:(~v1_relat_1(X21)|~v4_relat_1(X21,X20)|X21=k7_relat_1(X21,X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).
% 0.48/0.65  cnf(c_0_21, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.48/0.65  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.48/0.65  cnf(c_0_23, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.48/0.65  fof(c_0_24, plain, ![X12, X13, X14]:(~r1_tarski(X12,X13)|~r1_tarski(X14,X13)|r1_tarski(k2_xboole_0(X12,X14),X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).
% 0.48/0.65  fof(c_0_25, plain, ![X7, X8, X9]:(~r1_tarski(X7,X8)|~r1_tarski(X8,X9)|r1_tarski(X7,X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.48/0.65  cnf(c_0_26, plain, (r1_tarski(X1,k2_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.48/0.65  cnf(c_0_27, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.48/0.65  fof(c_0_28, plain, ![X22, X23]:(~v1_relat_1(X23)|r1_tarski(k1_relat_1(k7_relat_1(X23,X22)),X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).
% 0.48/0.65  cnf(c_0_29, plain, (X1=k7_relat_1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.48/0.65  cnf(c_0_30, negated_conjecture, (v4_relat_1(esk3_0,esk1_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.48/0.65  cnf(c_0_31, negated_conjecture, (v1_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_23, c_0_22])).
% 0.48/0.65  cnf(c_0_32, plain, (r1_tarski(k2_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.48/0.65  cnf(c_0_33, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.48/0.65  cnf(c_0_34, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X3,X2)))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 0.48/0.65  cnf(c_0_35, plain, (r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.48/0.65  cnf(c_0_36, negated_conjecture, (k7_relat_1(esk3_0,esk1_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])])).
% 0.48/0.65  cnf(c_0_37, plain, (r1_tarski(k3_tarski(k2_tarski(X1,X3)),X2)|~r1_tarski(X3,X2)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_32, c_0_27])).
% 0.48/0.65  cnf(c_0_38, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))|~r1_tarski(X1,X4)|~r1_tarski(X4,X3)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.48/0.65  cnf(c_0_39, negated_conjecture, (r1_tarski(k1_relat_1(esk3_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_31])])).
% 0.48/0.65  fof(c_0_40, plain, ![X10, X11]:r1_tarski(X10,k2_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.48/0.65  cnf(c_0_41, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k3_tarski(k2_tarski(X3,X4)))|~r1_tarski(X4,X2)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_33, c_0_37])).
% 0.48/0.65  cnf(c_0_42, negated_conjecture, (r1_tarski(k1_relat_1(esk3_0),k3_tarski(k2_tarski(X1,X2)))|~r1_tarski(esk1_0,X2)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.48/0.65  cnf(c_0_43, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.48/0.65  cnf(c_0_44, negated_conjecture, (r1_tarski(k1_relat_1(esk3_0),X1)|~r1_tarski(esk1_0,X2)|~r1_tarski(X2,X1)|~r1_tarski(X3,X1)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.48/0.65  cnf(c_0_45, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_43, c_0_27])).
% 0.48/0.65  fof(c_0_46, plain, ![X19]:(~v1_relat_1(X19)|k3_relat_1(X19)=k2_xboole_0(k1_relat_1(X19),k2_relat_1(X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).
% 0.48/0.65  cnf(c_0_47, negated_conjecture, (r1_tarski(k1_relat_1(esk3_0),X1)|~r1_tarski(k3_tarski(k2_tarski(esk1_0,X2)),X1)|~r1_tarski(X3,X1)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.48/0.65  cnf(c_0_48, plain, (k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.48/0.65  cnf(c_0_49, negated_conjecture, (r1_tarski(k1_relat_1(esk3_0),X1)|~r1_tarski(esk1_0,X1)|~r1_tarski(X2,X1)|~r1_tarski(X3,X1)), inference(spm,[status(thm)],[c_0_47, c_0_37])).
% 0.48/0.65  fof(c_0_50, plain, ![X33, X34, X35]:(~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))|k2_relset_1(X33,X34,X35)=k2_relat_1(X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.48/0.65  cnf(c_0_51, plain, (k3_relat_1(X1)=k3_tarski(k2_tarski(k1_relat_1(X1),k2_relat_1(X1)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_48, c_0_27])).
% 0.48/0.65  cnf(c_0_52, negated_conjecture, (r1_tarski(k1_relat_1(esk3_0),k3_tarski(k2_tarski(esk1_0,X1)))|~r1_tarski(X2,k3_tarski(k2_tarski(esk1_0,X1)))|~r1_tarski(X3,k3_tarski(k2_tarski(esk1_0,X1)))), inference(spm,[status(thm)],[c_0_49, c_0_45])).
% 0.48/0.65  fof(c_0_53, plain, ![X30, X31, X32]:(~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))|m1_subset_1(k2_relset_1(X30,X31,X32),k1_zfmisc_1(X31))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_relset_1])])).
% 0.48/0.65  cnf(c_0_54, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.48/0.65  cnf(c_0_55, plain, (r1_tarski(k3_relat_1(X1),X2)|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)|~r1_tarski(k1_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_37, c_0_51])).
% 0.48/0.65  cnf(c_0_56, negated_conjecture, (r1_tarski(k1_relat_1(esk3_0),k3_tarski(k2_tarski(esk1_0,X1)))|~r1_tarski(X2,k3_tarski(k2_tarski(esk1_0,X1)))), inference(spm,[status(thm)],[c_0_52, c_0_45])).
% 0.48/0.65  fof(c_0_57, plain, ![X17, X18]:((~m1_subset_1(X17,k1_zfmisc_1(X18))|r1_tarski(X17,X18))&(~r1_tarski(X17,X18)|m1_subset_1(X17,k1_zfmisc_1(X18)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.48/0.65  cnf(c_0_58, plain, (m1_subset_1(k2_relset_1(X2,X3,X1),k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.48/0.65  cnf(c_0_59, negated_conjecture, (k2_relset_1(esk1_0,esk2_0,esk3_0)=k2_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_54, c_0_22])).
% 0.48/0.65  cnf(c_0_60, negated_conjecture, (~r1_tarski(k3_relat_1(esk3_0),k2_xboole_0(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.48/0.65  cnf(c_0_61, plain, (r1_tarski(k3_relat_1(X1),k3_tarski(k2_tarski(X2,X3)))|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),k3_tarski(k2_tarski(X2,X3)))|~r1_tarski(k2_relat_1(X1),X3)), inference(spm,[status(thm)],[c_0_55, c_0_34])).
% 0.48/0.65  cnf(c_0_62, negated_conjecture, (r1_tarski(k1_relat_1(esk3_0),k3_tarski(k2_tarski(esk1_0,X1)))), inference(spm,[status(thm)],[c_0_56, c_0_45])).
% 0.48/0.65  cnf(c_0_63, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.48/0.65  cnf(c_0_64, negated_conjecture, (m1_subset_1(k2_relat_1(esk3_0),k1_zfmisc_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_22])])).
% 0.48/0.65  cnf(c_0_65, negated_conjecture, (~r1_tarski(k3_relat_1(esk3_0),k3_tarski(k2_tarski(esk1_0,esk2_0)))), inference(rw,[status(thm)],[c_0_60, c_0_27])).
% 0.48/0.65  cnf(c_0_66, negated_conjecture, (r1_tarski(k3_relat_1(esk3_0),k3_tarski(k2_tarski(esk1_0,X1)))|~r1_tarski(k2_relat_1(esk3_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_31])])).
% 0.48/0.65  cnf(c_0_67, negated_conjecture, (r1_tarski(k2_relat_1(esk3_0),esk2_0)), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.48/0.65  cnf(c_0_68, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67])]), ['proof']).
% 0.48/0.65  # SZS output end CNFRefutation
% 0.48/0.65  # Proof object total steps             : 69
% 0.48/0.65  # Proof object clause steps            : 40
% 0.48/0.65  # Proof object formula steps           : 29
% 0.48/0.65  # Proof object conjectures             : 22
% 0.48/0.65  # Proof object clause conjectures      : 19
% 0.48/0.65  # Proof object formula conjectures     : 3
% 0.48/0.65  # Proof object initial clauses used    : 15
% 0.48/0.65  # Proof object initial formulas used   : 14
% 0.48/0.65  # Proof object generating inferences   : 20
% 0.48/0.65  # Proof object simplifying inferences  : 15
% 0.48/0.65  # Training examples: 0 positive, 0 negative
% 0.48/0.65  # Parsed axioms                        : 14
% 0.48/0.65  # Removed by relevancy pruning/SinE    : 0
% 0.48/0.65  # Initial clauses                      : 17
% 0.48/0.65  # Removed in clause preprocessing      : 1
% 0.48/0.65  # Initial clauses in saturation        : 16
% 0.48/0.65  # Processed clauses                    : 1415
% 0.48/0.65  # ...of these trivial                  : 0
% 0.48/0.65  # ...subsumed                          : 443
% 0.48/0.65  # ...remaining for further processing  : 972
% 0.48/0.65  # Other redundant clauses eliminated   : 0
% 0.48/0.65  # Clauses deleted for lack of memory   : 0
% 0.48/0.65  # Backward-subsumed                    : 76
% 0.48/0.65  # Backward-rewritten                   : 9
% 0.48/0.65  # Generated clauses                    : 5838
% 0.48/0.65  # ...of the previous two non-trivial   : 5734
% 0.48/0.65  # Contextual simplify-reflections      : 66
% 0.48/0.65  # Paramodulations                      : 5838
% 0.48/0.65  # Factorizations                       : 0
% 0.48/0.65  # Equation resolutions                 : 0
% 0.48/0.65  # Propositional unsat checks           : 0
% 0.48/0.65  #    Propositional check models        : 0
% 0.48/0.65  #    Propositional check unsatisfiable : 0
% 0.48/0.65  #    Propositional clauses             : 0
% 0.48/0.65  #    Propositional clauses after purity: 0
% 0.48/0.65  #    Propositional unsat core size     : 0
% 0.48/0.65  #    Propositional preprocessing time  : 0.000
% 0.48/0.65  #    Propositional encoding time       : 0.000
% 0.48/0.65  #    Propositional solver time         : 0.000
% 0.48/0.65  #    Success case prop preproc time    : 0.000
% 0.48/0.65  #    Success case prop encoding time   : 0.000
% 0.48/0.65  #    Success case prop solver time     : 0.000
% 0.48/0.65  # Current number of processed clauses  : 871
% 0.48/0.65  #    Positive orientable unit clauses  : 21
% 0.48/0.65  #    Positive unorientable unit clauses: 0
% 0.48/0.65  #    Negative unit clauses             : 16
% 0.48/0.65  #    Non-unit-clauses                  : 834
% 0.48/0.65  # Current number of unprocessed clauses: 4181
% 0.48/0.65  # ...number of literals in the above   : 18045
% 0.48/0.65  # Current number of archived formulas  : 0
% 0.48/0.65  # Current number of archived clauses   : 102
% 0.48/0.65  # Clause-clause subsumption calls (NU) : 258478
% 0.48/0.65  # Rec. Clause-clause subsumption calls : 56965
% 0.48/0.65  # Non-unit clause-clause subsumptions  : 547
% 0.48/0.65  # Unit Clause-clause subsumption calls : 5651
% 0.48/0.65  # Rewrite failures with RHS unbound    : 0
% 0.48/0.65  # BW rewrite match attempts            : 112
% 0.48/0.65  # BW rewrite match successes           : 7
% 0.48/0.65  # Condensation attempts                : 0
% 0.48/0.65  # Condensation successes               : 0
% 0.48/0.65  # Termbank termtop insertions          : 142330
% 0.48/0.65  
% 0.48/0.65  # -------------------------------------------------
% 0.48/0.65  # User time                : 0.307 s
% 0.48/0.65  # System time              : 0.011 s
% 0.48/0.65  # Total time               : 0.318 s
% 0.48/0.65  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------

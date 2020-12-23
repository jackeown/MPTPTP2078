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
% DateTime   : Thu Dec  3 10:57:18 EST 2020

% Result     : Theorem 0.57s
% Output     : CNFRefutation 0.57s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 148 expanded)
%              Number of clauses        :   40 (  68 expanded)
%              Number of leaves         :   14 (  37 expanded)
%              Depth                    :   15
%              Number of atoms          :  141 ( 266 expanded)
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

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t10_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(X1,k2_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(dt_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k1_relset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

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

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

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

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(dt_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k2_relset_1(X1,X2,X3),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
       => r1_tarski(k3_relat_1(X3),k2_xboole_0(X1,X2)) ) ),
    inference(assume_negation,[status(cth)],[t19_relset_1])).

fof(c_0_15,plain,(
    ! [X30,X31,X32] :
      ( ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
      | k1_relset_1(X30,X31,X32) = k1_relat_1(X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_16,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    & ~ r1_tarski(k3_relat_1(esk3_0),k2_xboole_0(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_17,plain,(
    ! [X4,X5,X6] :
      ( ~ r1_tarski(X4,X5)
      | r1_tarski(X4,k2_xboole_0(X6,X5)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).

fof(c_0_18,plain,(
    ! [X15,X16] : k3_tarski(k2_tarski(X15,X16)) = k2_xboole_0(X15,X16) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_19,plain,(
    ! [X24,X25,X26] :
      ( ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))
      | m1_subset_1(k1_relset_1(X24,X25,X26),k1_zfmisc_1(X24)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_relset_1])])).

cnf(c_0_20,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_22,plain,(
    ! [X12,X13,X14] :
      ( ~ r1_tarski(X12,X13)
      | ~ r1_tarski(X14,X13)
      | r1_tarski(k2_xboole_0(X12,X14),X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).

fof(c_0_23,plain,(
    ! [X7,X8,X9] :
      ( ~ r1_tarski(X7,X8)
      | ~ r1_tarski(X8,X9)
      | r1_tarski(X7,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,k2_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_26,plain,(
    ! [X17,X18] :
      ( ( ~ m1_subset_1(X17,k1_zfmisc_1(X18))
        | r1_tarski(X17,X18) )
      & ( ~ r1_tarski(X17,X18)
        | m1_subset_1(X17,k1_zfmisc_1(X18)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_27,plain,
    ( m1_subset_1(k1_relset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,negated_conjecture,
    ( k1_relset_1(esk1_0,esk2_0,esk3_0) = k1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_29,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X3,X2)))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(k1_relat_1(esk3_0),k1_zfmisc_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_21])])).

cnf(c_0_34,plain,
    ( r1_tarski(k3_tarski(k2_tarski(X1,X3)),X2)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_29,c_0_25])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))
    | ~ r1_tarski(X1,X4)
    | ~ r1_tarski(X4,X3) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk3_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

fof(c_0_37,plain,(
    ! [X10,X11] : r1_tarski(X10,k2_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k3_tarski(k2_tarski(X3,X4)))
    | ~ r1_tarski(X4,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_30,c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk3_0),k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_tarski(esk1_0,X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk3_0),X1)
    | ~ r1_tarski(esk1_0,X2)
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X3,X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_40,c_0_25])).

fof(c_0_43,plain,(
    ! [X21] :
      ( ~ v1_relat_1(X21)
      | k3_relat_1(X21) = k2_xboole_0(k1_relat_1(X21),k2_relat_1(X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk3_0),X1)
    | ~ r1_tarski(k3_tarski(k2_tarski(esk1_0,X2)),X1)
    | ~ r1_tarski(X3,X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_45,plain,
    ( k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk3_0),X1)
    | ~ r1_tarski(esk1_0,X1)
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X3,X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_34])).

fof(c_0_47,plain,(
    ! [X33,X34,X35] :
      ( ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
      | k2_relset_1(X33,X34,X35) = k2_relat_1(X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_48,plain,
    ( k3_relat_1(X1) = k3_tarski(k2_tarski(k1_relat_1(X1),k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_45,c_0_25])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk3_0),k3_tarski(k2_tarski(esk1_0,X1)))
    | ~ r1_tarski(X2,k3_tarski(k2_tarski(esk1_0,X1)))
    | ~ r1_tarski(X3,k3_tarski(k2_tarski(esk1_0,X1))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_42])).

fof(c_0_50,plain,(
    ! [X19,X20] :
      ( ~ v1_relat_1(X19)
      | ~ m1_subset_1(X20,k1_zfmisc_1(X19))
      | v1_relat_1(X20) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_51,plain,(
    ! [X22,X23] : v1_relat_1(k2_zfmisc_1(X22,X23)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_52,plain,(
    ! [X27,X28,X29] :
      ( ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))
      | m1_subset_1(k2_relset_1(X27,X28,X29),k1_zfmisc_1(X28)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_relset_1])])).

cnf(c_0_53,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_54,plain,
    ( r1_tarski(k3_relat_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_34,c_0_48])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk3_0),k3_tarski(k2_tarski(esk1_0,X1)))
    | ~ r1_tarski(X2,k3_tarski(k2_tarski(esk1_0,X1))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_42])).

cnf(c_0_56,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_57,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_58,plain,
    ( m1_subset_1(k2_relset_1(X2,X3,X1),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_59,negated_conjecture,
    ( k2_relset_1(esk1_0,esk2_0,esk3_0) = k2_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_21])).

cnf(c_0_60,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(esk3_0),k2_xboole_0(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_61,plain,
    ( r1_tarski(k3_relat_1(X1),k3_tarski(k2_tarski(X2,X3)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),k3_tarski(k2_tarski(X2,X3)))
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(spm,[status(thm)],[c_0_54,c_0_31])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk3_0),k3_tarski(k2_tarski(esk1_0,X1))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_42])).

cnf(c_0_63,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_21]),c_0_57])])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(k2_relat_1(esk3_0),k1_zfmisc_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_21])])).

cnf(c_0_65,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(esk3_0),k3_tarski(k2_tarski(esk1_0,esk2_0))) ),
    inference(rw,[status(thm)],[c_0_60,c_0_25])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(k3_relat_1(esk3_0),k3_tarski(k2_tarski(esk1_0,X1)))
    | ~ r1_tarski(k2_relat_1(esk3_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63])])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk3_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_64])).

cnf(c_0_68,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:41:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.57/0.74  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.57/0.74  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.57/0.74  #
% 0.57/0.74  # Preprocessing time       : 0.027 s
% 0.57/0.74  # Presaturation interreduction done
% 0.57/0.74  
% 0.57/0.74  # Proof found!
% 0.57/0.74  # SZS status Theorem
% 0.57/0.74  # SZS output start CNFRefutation
% 0.57/0.74  fof(t19_relset_1, conjecture, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>r1_tarski(k3_relat_1(X3),k2_xboole_0(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_relset_1)).
% 0.57/0.74  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.57/0.74  fof(t10_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(X1,k2_xboole_0(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 0.57/0.74  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.57/0.74  fof(dt_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k1_relset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 0.57/0.74  fof(t8_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 0.57/0.74  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.57/0.74  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.57/0.74  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.57/0.74  fof(d6_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 0.57/0.74  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.57/0.74  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.57/0.74  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.57/0.74  fof(dt_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k2_relset_1(X1,X2,X3),k1_zfmisc_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 0.57/0.74  fof(c_0_14, negated_conjecture, ~(![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>r1_tarski(k3_relat_1(X3),k2_xboole_0(X1,X2)))), inference(assume_negation,[status(cth)],[t19_relset_1])).
% 0.57/0.74  fof(c_0_15, plain, ![X30, X31, X32]:(~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))|k1_relset_1(X30,X31,X32)=k1_relat_1(X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.57/0.74  fof(c_0_16, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))&~r1_tarski(k3_relat_1(esk3_0),k2_xboole_0(esk1_0,esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.57/0.74  fof(c_0_17, plain, ![X4, X5, X6]:(~r1_tarski(X4,X5)|r1_tarski(X4,k2_xboole_0(X6,X5))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).
% 0.57/0.74  fof(c_0_18, plain, ![X15, X16]:k3_tarski(k2_tarski(X15,X16))=k2_xboole_0(X15,X16), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.57/0.74  fof(c_0_19, plain, ![X24, X25, X26]:(~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))|m1_subset_1(k1_relset_1(X24,X25,X26),k1_zfmisc_1(X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_relset_1])])).
% 0.57/0.74  cnf(c_0_20, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.57/0.74  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.57/0.74  fof(c_0_22, plain, ![X12, X13, X14]:(~r1_tarski(X12,X13)|~r1_tarski(X14,X13)|r1_tarski(k2_xboole_0(X12,X14),X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).
% 0.57/0.74  fof(c_0_23, plain, ![X7, X8, X9]:(~r1_tarski(X7,X8)|~r1_tarski(X8,X9)|r1_tarski(X7,X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.57/0.74  cnf(c_0_24, plain, (r1_tarski(X1,k2_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.57/0.74  cnf(c_0_25, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.57/0.74  fof(c_0_26, plain, ![X17, X18]:((~m1_subset_1(X17,k1_zfmisc_1(X18))|r1_tarski(X17,X18))&(~r1_tarski(X17,X18)|m1_subset_1(X17,k1_zfmisc_1(X18)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.57/0.74  cnf(c_0_27, plain, (m1_subset_1(k1_relset_1(X2,X3,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.57/0.74  cnf(c_0_28, negated_conjecture, (k1_relset_1(esk1_0,esk2_0,esk3_0)=k1_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.57/0.74  cnf(c_0_29, plain, (r1_tarski(k2_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.57/0.74  cnf(c_0_30, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.57/0.74  cnf(c_0_31, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X3,X2)))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 0.57/0.74  cnf(c_0_32, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.57/0.74  cnf(c_0_33, negated_conjecture, (m1_subset_1(k1_relat_1(esk3_0),k1_zfmisc_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_21])])).
% 0.57/0.74  cnf(c_0_34, plain, (r1_tarski(k3_tarski(k2_tarski(X1,X3)),X2)|~r1_tarski(X3,X2)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_29, c_0_25])).
% 0.57/0.74  cnf(c_0_35, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))|~r1_tarski(X1,X4)|~r1_tarski(X4,X3)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.57/0.74  cnf(c_0_36, negated_conjecture, (r1_tarski(k1_relat_1(esk3_0),esk1_0)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.57/0.74  fof(c_0_37, plain, ![X10, X11]:r1_tarski(X10,k2_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.57/0.74  cnf(c_0_38, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k3_tarski(k2_tarski(X3,X4)))|~r1_tarski(X4,X2)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_30, c_0_34])).
% 0.57/0.74  cnf(c_0_39, negated_conjecture, (r1_tarski(k1_relat_1(esk3_0),k3_tarski(k2_tarski(X1,X2)))|~r1_tarski(esk1_0,X2)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.57/0.74  cnf(c_0_40, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.57/0.74  cnf(c_0_41, negated_conjecture, (r1_tarski(k1_relat_1(esk3_0),X1)|~r1_tarski(esk1_0,X2)|~r1_tarski(X2,X1)|~r1_tarski(X3,X1)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.57/0.74  cnf(c_0_42, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_40, c_0_25])).
% 0.57/0.74  fof(c_0_43, plain, ![X21]:(~v1_relat_1(X21)|k3_relat_1(X21)=k2_xboole_0(k1_relat_1(X21),k2_relat_1(X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).
% 0.57/0.74  cnf(c_0_44, negated_conjecture, (r1_tarski(k1_relat_1(esk3_0),X1)|~r1_tarski(k3_tarski(k2_tarski(esk1_0,X2)),X1)|~r1_tarski(X3,X1)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.57/0.74  cnf(c_0_45, plain, (k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.57/0.74  cnf(c_0_46, negated_conjecture, (r1_tarski(k1_relat_1(esk3_0),X1)|~r1_tarski(esk1_0,X1)|~r1_tarski(X2,X1)|~r1_tarski(X3,X1)), inference(spm,[status(thm)],[c_0_44, c_0_34])).
% 0.57/0.74  fof(c_0_47, plain, ![X33, X34, X35]:(~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))|k2_relset_1(X33,X34,X35)=k2_relat_1(X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.57/0.74  cnf(c_0_48, plain, (k3_relat_1(X1)=k3_tarski(k2_tarski(k1_relat_1(X1),k2_relat_1(X1)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_45, c_0_25])).
% 0.57/0.74  cnf(c_0_49, negated_conjecture, (r1_tarski(k1_relat_1(esk3_0),k3_tarski(k2_tarski(esk1_0,X1)))|~r1_tarski(X2,k3_tarski(k2_tarski(esk1_0,X1)))|~r1_tarski(X3,k3_tarski(k2_tarski(esk1_0,X1)))), inference(spm,[status(thm)],[c_0_46, c_0_42])).
% 0.57/0.74  fof(c_0_50, plain, ![X19, X20]:(~v1_relat_1(X19)|(~m1_subset_1(X20,k1_zfmisc_1(X19))|v1_relat_1(X20))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.57/0.74  fof(c_0_51, plain, ![X22, X23]:v1_relat_1(k2_zfmisc_1(X22,X23)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.57/0.74  fof(c_0_52, plain, ![X27, X28, X29]:(~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))|m1_subset_1(k2_relset_1(X27,X28,X29),k1_zfmisc_1(X28))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_relset_1])])).
% 0.57/0.74  cnf(c_0_53, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.57/0.74  cnf(c_0_54, plain, (r1_tarski(k3_relat_1(X1),X2)|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)|~r1_tarski(k1_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_34, c_0_48])).
% 0.57/0.74  cnf(c_0_55, negated_conjecture, (r1_tarski(k1_relat_1(esk3_0),k3_tarski(k2_tarski(esk1_0,X1)))|~r1_tarski(X2,k3_tarski(k2_tarski(esk1_0,X1)))), inference(spm,[status(thm)],[c_0_49, c_0_42])).
% 0.57/0.74  cnf(c_0_56, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.57/0.74  cnf(c_0_57, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.57/0.74  cnf(c_0_58, plain, (m1_subset_1(k2_relset_1(X2,X3,X1),k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.57/0.74  cnf(c_0_59, negated_conjecture, (k2_relset_1(esk1_0,esk2_0,esk3_0)=k2_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_53, c_0_21])).
% 0.57/0.74  cnf(c_0_60, negated_conjecture, (~r1_tarski(k3_relat_1(esk3_0),k2_xboole_0(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.57/0.74  cnf(c_0_61, plain, (r1_tarski(k3_relat_1(X1),k3_tarski(k2_tarski(X2,X3)))|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),k3_tarski(k2_tarski(X2,X3)))|~r1_tarski(k2_relat_1(X1),X3)), inference(spm,[status(thm)],[c_0_54, c_0_31])).
% 0.57/0.74  cnf(c_0_62, negated_conjecture, (r1_tarski(k1_relat_1(esk3_0),k3_tarski(k2_tarski(esk1_0,X1)))), inference(spm,[status(thm)],[c_0_55, c_0_42])).
% 0.57/0.74  cnf(c_0_63, negated_conjecture, (v1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_21]), c_0_57])])).
% 0.57/0.74  cnf(c_0_64, negated_conjecture, (m1_subset_1(k2_relat_1(esk3_0),k1_zfmisc_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_21])])).
% 0.57/0.74  cnf(c_0_65, negated_conjecture, (~r1_tarski(k3_relat_1(esk3_0),k3_tarski(k2_tarski(esk1_0,esk2_0)))), inference(rw,[status(thm)],[c_0_60, c_0_25])).
% 0.57/0.74  cnf(c_0_66, negated_conjecture, (r1_tarski(k3_relat_1(esk3_0),k3_tarski(k2_tarski(esk1_0,X1)))|~r1_tarski(k2_relat_1(esk3_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63])])).
% 0.57/0.74  cnf(c_0_67, negated_conjecture, (r1_tarski(k2_relat_1(esk3_0),esk2_0)), inference(spm,[status(thm)],[c_0_32, c_0_64])).
% 0.57/0.74  cnf(c_0_68, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67])]), ['proof']).
% 0.57/0.74  # SZS output end CNFRefutation
% 0.57/0.74  # Proof object total steps             : 69
% 0.57/0.74  # Proof object clause steps            : 40
% 0.57/0.74  # Proof object formula steps           : 29
% 0.57/0.74  # Proof object conjectures             : 22
% 0.57/0.74  # Proof object clause conjectures      : 19
% 0.57/0.74  # Proof object formula conjectures     : 3
% 0.57/0.74  # Proof object initial clauses used    : 15
% 0.57/0.74  # Proof object initial formulas used   : 14
% 0.57/0.74  # Proof object generating inferences   : 20
% 0.57/0.74  # Proof object simplifying inferences  : 15
% 0.57/0.74  # Training examples: 0 positive, 0 negative
% 0.57/0.74  # Parsed axioms                        : 14
% 0.57/0.74  # Removed by relevancy pruning/SinE    : 0
% 0.57/0.74  # Initial clauses                      : 16
% 0.57/0.74  # Removed in clause preprocessing      : 1
% 0.57/0.74  # Initial clauses in saturation        : 15
% 0.57/0.74  # Processed clauses                    : 2592
% 0.57/0.74  # ...of these trivial                  : 0
% 0.57/0.74  # ...subsumed                          : 1245
% 0.57/0.74  # ...remaining for further processing  : 1347
% 0.57/0.74  # Other redundant clauses eliminated   : 0
% 0.57/0.74  # Clauses deleted for lack of memory   : 0
% 0.57/0.74  # Backward-subsumed                    : 84
% 0.57/0.74  # Backward-rewritten                   : 10
% 0.57/0.74  # Generated clauses                    : 12631
% 0.57/0.74  # ...of the previous two non-trivial   : 12464
% 0.57/0.74  # Contextual simplify-reflections      : 24
% 0.57/0.74  # Paramodulations                      : 12631
% 0.57/0.74  # Factorizations                       : 0
% 0.57/0.74  # Equation resolutions                 : 0
% 0.57/0.74  # Propositional unsat checks           : 0
% 0.57/0.74  #    Propositional check models        : 0
% 0.57/0.74  #    Propositional check unsatisfiable : 0
% 0.57/0.74  #    Propositional clauses             : 0
% 0.57/0.74  #    Propositional clauses after purity: 0
% 0.57/0.74  #    Propositional unsat core size     : 0
% 0.57/0.74  #    Propositional preprocessing time  : 0.000
% 0.57/0.74  #    Propositional encoding time       : 0.000
% 0.57/0.74  #    Propositional solver time         : 0.000
% 0.57/0.74  #    Success case prop preproc time    : 0.000
% 0.57/0.74  #    Success case prop encoding time   : 0.000
% 0.57/0.74  #    Success case prop solver time     : 0.000
% 0.57/0.74  # Current number of processed clauses  : 1238
% 0.57/0.74  #    Positive orientable unit clauses  : 21
% 0.57/0.74  #    Positive unorientable unit clauses: 0
% 0.57/0.74  #    Negative unit clauses             : 13
% 0.57/0.74  #    Non-unit-clauses                  : 1204
% 0.57/0.74  # Current number of unprocessed clauses: 9764
% 0.57/0.74  # ...number of literals in the above   : 42693
% 0.57/0.74  # Current number of archived formulas  : 0
% 0.57/0.74  # Current number of archived clauses   : 110
% 0.57/0.74  # Clause-clause subsumption calls (NU) : 449165
% 0.57/0.74  # Rec. Clause-clause subsumption calls : 107733
% 0.57/0.74  # Non-unit clause-clause subsumptions  : 1262
% 0.57/0.74  # Unit Clause-clause subsumption calls : 5728
% 0.57/0.74  # Rewrite failures with RHS unbound    : 0
% 0.57/0.74  # BW rewrite match attempts            : 104
% 0.57/0.74  # BW rewrite match successes           : 7
% 0.57/0.74  # Condensation attempts                : 0
% 0.57/0.74  # Condensation successes               : 0
% 0.57/0.74  # Termbank termtop insertions          : 259424
% 0.57/0.75  
% 0.57/0.75  # -------------------------------------------------
% 0.57/0.75  # User time                : 0.398 s
% 0.57/0.75  # System time              : 0.011 s
% 0.57/0.75  # Total time               : 0.409 s
% 0.57/0.75  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------

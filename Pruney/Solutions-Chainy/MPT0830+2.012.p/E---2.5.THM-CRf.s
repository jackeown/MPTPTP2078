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
% DateTime   : Thu Dec  3 10:57:37 EST 2020

% Result     : Theorem 0.60s
% Output     : CNFRefutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 177 expanded)
%              Number of clauses        :   37 (  77 expanded)
%              Number of leaves         :   12 (  43 expanded)
%              Depth                    :   15
%              Number of atoms          :  143 ( 415 expanded)
%              Number of equality atoms :    8 (  12 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    9 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t33_relset_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
     => m1_subset_1(k5_relset_1(X1,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_relset_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(dt_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k2_relset_1(X1,X2,X3),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(fc23_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v4_relat_1(X3,X2) )
     => ( v1_relat_1(k7_relat_1(X3,X1))
        & v4_relat_1(k7_relat_1(X3,X1),X1)
        & v4_relat_1(k7_relat_1(X3,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc23_relat_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t99_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k2_relat_1(k7_relat_1(X2,X1)),k2_relat_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_relat_1)).

fof(t11_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( r1_tarski(k1_relat_1(X3),X1)
          & r1_tarski(k2_relat_1(X3),X2) )
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(redefinition_k5_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k5_relset_1(X1,X2,X3,X4) = k7_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
       => m1_subset_1(k5_relset_1(X1,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(assume_negation,[status(cth)],[t33_relset_1])).

fof(c_0_13,plain,(
    ! [X26,X27,X28] :
      ( ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
      | k2_relset_1(X26,X27,X28) = k2_relat_1(X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_14,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))
    & ~ m1_subset_1(k5_relset_1(esk1_0,esk3_0,esk4_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

fof(c_0_15,plain,(
    ! [X23,X24,X25] :
      ( ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))
      | m1_subset_1(k2_relset_1(X23,X24,X25),k1_zfmisc_1(X24)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_relset_1])])).

cnf(c_0_16,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,plain,(
    ! [X10,X11] :
      ( ( ~ v4_relat_1(X11,X10)
        | r1_tarski(k1_relat_1(X11),X10)
        | ~ v1_relat_1(X11) )
      & ( ~ r1_tarski(k1_relat_1(X11),X10)
        | v4_relat_1(X11,X10)
        | ~ v1_relat_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

fof(c_0_19,plain,(
    ! [X12,X13,X14] :
      ( ( v1_relat_1(k7_relat_1(X14,X12))
        | ~ v1_relat_1(X14)
        | ~ v4_relat_1(X14,X13) )
      & ( v4_relat_1(k7_relat_1(X14,X12),X12)
        | ~ v1_relat_1(X14)
        | ~ v4_relat_1(X14,X13) )
      & ( v4_relat_1(k7_relat_1(X14,X12),X13)
        | ~ v1_relat_1(X14)
        | ~ v4_relat_1(X14,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc23_relat_1])])])).

fof(c_0_20,plain,(
    ! [X20,X21,X22] :
      ( ( v4_relat_1(X22,X20)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) )
      & ( v5_relat_1(X22,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_21,plain,(
    ! [X17,X18,X19] :
      ( ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))
      | v1_relat_1(X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_22,plain,(
    ! [X8,X9] :
      ( ( ~ m1_subset_1(X8,k1_zfmisc_1(X9))
        | r1_tarski(X8,X9) )
      & ( ~ r1_tarski(X8,X9)
        | m1_subset_1(X8,k1_zfmisc_1(X9)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_23,plain,
    ( m1_subset_1(k2_relset_1(X2,X3,X1),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( k2_relset_1(esk1_0,esk3_0,esk4_0) = k2_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_25,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( v4_relat_1(k7_relat_1(X1,X2),X3)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_30,plain,(
    ! [X5,X6,X7] :
      ( ~ r1_tarski(X5,X6)
      | ~ r1_tarski(X6,X7)
      | r1_tarski(X5,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(k2_relat_1(esk4_0),k1_zfmisc_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_17])])).

fof(c_0_33,plain,(
    ! [X15,X16] :
      ( ~ v1_relat_1(X16)
      | r1_tarski(k2_relat_1(k7_relat_1(X16,X15)),k2_relat_1(X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t99_relat_1])])).

fof(c_0_34,plain,(
    ! [X33,X34,X35] :
      ( ~ v1_relat_1(X35)
      | ~ r1_tarski(k1_relat_1(X35),X33)
      | ~ r1_tarski(k2_relat_1(X35),X34)
      | m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).

cnf(c_0_35,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X3)
    | ~ v4_relat_1(X1,X3)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])).

cnf(c_0_36,negated_conjecture,
    ( v4_relat_1(esk4_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_17])).

cnf(c_0_37,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_17])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_40,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(X1,X2)),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(k1_relat_1(k7_relat_1(esk4_0,X1)),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(X1,esk3_0)
    | ~ r1_tarski(X1,k2_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(k2_relat_1(k7_relat_1(esk4_0,X1)),k2_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_37])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(k7_relat_1(esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(esk1_0,X2)))
    | ~ v1_relat_1(k7_relat_1(esk4_0,X1))
    | ~ r1_tarski(k2_relat_1(k7_relat_1(esk4_0,X1)),X2) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(k2_relat_1(k7_relat_1(esk4_0,X1)),esk3_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(k7_relat_1(esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))
    | ~ v1_relat_1(k7_relat_1(esk4_0,X1)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_48,plain,
    ( v4_relat_1(k7_relat_1(X1,X2),X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(k7_relat_1(esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))
    | ~ v4_relat_1(esk4_0,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_27]),c_0_37])])).

fof(c_0_50,plain,(
    ! [X29,X30,X31,X32] :
      ( ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))
      | k5_relset_1(X29,X30,X31,X32) = k7_relat_1(X31,X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_relset_1])])).

cnf(c_0_51,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)
    | ~ v4_relat_1(X1,X3)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_48]),c_0_27])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(k7_relat_1(esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_36])).

cnf(c_0_53,plain,
    ( k5_relset_1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(k1_relat_1(k7_relat_1(esk4_0,X1)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_36]),c_0_37])])).

cnf(c_0_55,negated_conjecture,
    ( v1_relat_1(k7_relat_1(esk4_0,X1)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_52])).

cnf(c_0_56,negated_conjecture,
    ( ~ m1_subset_1(k5_relset_1(esk1_0,esk3_0,esk4_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_57,negated_conjecture,
    ( k5_relset_1(esk1_0,esk3_0,esk4_0,X1) = k7_relat_1(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_17])).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(k7_relat_1(esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relat_1(k7_relat_1(esk4_0,X1)),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_54]),c_0_55])])).

cnf(c_0_59,negated_conjecture,
    ( ~ m1_subset_1(k7_relat_1(esk4_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(rw,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_60,negated_conjecture,
    ( m1_subset_1(k7_relat_1(esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(X1,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_58,c_0_46])).

cnf(c_0_61,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_60])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:07:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.60/0.78  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S087N
% 0.60/0.78  # and selection function SelectCQArNpEqFirstUnlessPDom.
% 0.60/0.78  #
% 0.60/0.78  # Preprocessing time       : 0.027 s
% 0.60/0.78  # Presaturation interreduction done
% 0.60/0.78  
% 0.60/0.78  # Proof found!
% 0.60/0.78  # SZS status Theorem
% 0.60/0.78  # SZS output start CNFRefutation
% 0.60/0.78  fof(t33_relset_1, conjecture, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))=>m1_subset_1(k5_relset_1(X1,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_relset_1)).
% 0.60/0.78  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.60/0.78  fof(dt_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k2_relset_1(X1,X2,X3),k1_zfmisc_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 0.60/0.78  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 0.60/0.78  fof(fc23_relat_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v4_relat_1(X3,X2))=>((v1_relat_1(k7_relat_1(X3,X1))&v4_relat_1(k7_relat_1(X3,X1),X1))&v4_relat_1(k7_relat_1(X3,X1),X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc23_relat_1)).
% 0.60/0.78  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.60/0.78  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.60/0.78  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.60/0.78  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.60/0.78  fof(t99_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k2_relat_1(k7_relat_1(X2,X1)),k2_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_relat_1)).
% 0.60/0.78  fof(t11_relset_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>((r1_tarski(k1_relat_1(X3),X1)&r1_tarski(k2_relat_1(X3),X2))=>m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 0.60/0.78  fof(redefinition_k5_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k5_relset_1(X1,X2,X3,X4)=k7_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 0.60/0.78  fof(c_0_12, negated_conjecture, ~(![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))=>m1_subset_1(k5_relset_1(X1,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X3))))), inference(assume_negation,[status(cth)],[t33_relset_1])).
% 0.60/0.78  fof(c_0_13, plain, ![X26, X27, X28]:(~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))|k2_relset_1(X26,X27,X28)=k2_relat_1(X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.60/0.79  fof(c_0_14, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))&~m1_subset_1(k5_relset_1(esk1_0,esk3_0,esk4_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.60/0.79  fof(c_0_15, plain, ![X23, X24, X25]:(~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))|m1_subset_1(k2_relset_1(X23,X24,X25),k1_zfmisc_1(X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_relset_1])])).
% 0.60/0.79  cnf(c_0_16, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.60/0.79  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.60/0.79  fof(c_0_18, plain, ![X10, X11]:((~v4_relat_1(X11,X10)|r1_tarski(k1_relat_1(X11),X10)|~v1_relat_1(X11))&(~r1_tarski(k1_relat_1(X11),X10)|v4_relat_1(X11,X10)|~v1_relat_1(X11))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.60/0.79  fof(c_0_19, plain, ![X12, X13, X14]:(((v1_relat_1(k7_relat_1(X14,X12))|(~v1_relat_1(X14)|~v4_relat_1(X14,X13)))&(v4_relat_1(k7_relat_1(X14,X12),X12)|(~v1_relat_1(X14)|~v4_relat_1(X14,X13))))&(v4_relat_1(k7_relat_1(X14,X12),X13)|(~v1_relat_1(X14)|~v4_relat_1(X14,X13)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc23_relat_1])])])).
% 0.60/0.79  fof(c_0_20, plain, ![X20, X21, X22]:((v4_relat_1(X22,X20)|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))))&(v5_relat_1(X22,X21)|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.60/0.79  fof(c_0_21, plain, ![X17, X18, X19]:(~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))|v1_relat_1(X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.60/0.79  fof(c_0_22, plain, ![X8, X9]:((~m1_subset_1(X8,k1_zfmisc_1(X9))|r1_tarski(X8,X9))&(~r1_tarski(X8,X9)|m1_subset_1(X8,k1_zfmisc_1(X9)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.60/0.79  cnf(c_0_23, plain, (m1_subset_1(k2_relset_1(X2,X3,X1),k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.60/0.79  cnf(c_0_24, negated_conjecture, (k2_relset_1(esk1_0,esk3_0,esk4_0)=k2_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.60/0.79  cnf(c_0_25, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.60/0.79  cnf(c_0_26, plain, (v4_relat_1(k7_relat_1(X1,X2),X3)|~v1_relat_1(X1)|~v4_relat_1(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.60/0.79  cnf(c_0_27, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)|~v4_relat_1(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.60/0.79  cnf(c_0_28, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.60/0.79  cnf(c_0_29, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.60/0.79  fof(c_0_30, plain, ![X5, X6, X7]:(~r1_tarski(X5,X6)|~r1_tarski(X6,X7)|r1_tarski(X5,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.60/0.79  cnf(c_0_31, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.60/0.79  cnf(c_0_32, negated_conjecture, (m1_subset_1(k2_relat_1(esk4_0),k1_zfmisc_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_17])])).
% 0.60/0.79  fof(c_0_33, plain, ![X15, X16]:(~v1_relat_1(X16)|r1_tarski(k2_relat_1(k7_relat_1(X16,X15)),k2_relat_1(X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t99_relat_1])])).
% 0.60/0.79  fof(c_0_34, plain, ![X33, X34, X35]:(~v1_relat_1(X35)|(~r1_tarski(k1_relat_1(X35),X33)|~r1_tarski(k2_relat_1(X35),X34)|m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).
% 0.60/0.79  cnf(c_0_35, plain, (r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X3)|~v4_relat_1(X1,X3)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27])).
% 0.60/0.79  cnf(c_0_36, negated_conjecture, (v4_relat_1(esk4_0,esk1_0)), inference(spm,[status(thm)],[c_0_28, c_0_17])).
% 0.60/0.79  cnf(c_0_37, negated_conjecture, (v1_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_29, c_0_17])).
% 0.60/0.79  cnf(c_0_38, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.60/0.79  cnf(c_0_39, negated_conjecture, (r1_tarski(k2_relat_1(esk4_0),esk3_0)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.60/0.79  cnf(c_0_40, plain, (r1_tarski(k2_relat_1(k7_relat_1(X1,X2)),k2_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.60/0.79  cnf(c_0_41, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X3)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.60/0.79  cnf(c_0_42, negated_conjecture, (r1_tarski(k1_relat_1(k7_relat_1(esk4_0,X1)),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37])])).
% 0.60/0.79  cnf(c_0_43, negated_conjecture, (r1_tarski(X1,esk3_0)|~r1_tarski(X1,k2_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.60/0.79  cnf(c_0_44, negated_conjecture, (r1_tarski(k2_relat_1(k7_relat_1(esk4_0,X1)),k2_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_40, c_0_37])).
% 0.60/0.79  cnf(c_0_45, negated_conjecture, (m1_subset_1(k7_relat_1(esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(esk1_0,X2)))|~v1_relat_1(k7_relat_1(esk4_0,X1))|~r1_tarski(k2_relat_1(k7_relat_1(esk4_0,X1)),X2)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.60/0.79  cnf(c_0_46, negated_conjecture, (r1_tarski(k2_relat_1(k7_relat_1(esk4_0,X1)),esk3_0)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.60/0.79  cnf(c_0_47, negated_conjecture, (m1_subset_1(k7_relat_1(esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))|~v1_relat_1(k7_relat_1(esk4_0,X1))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.60/0.79  cnf(c_0_48, plain, (v4_relat_1(k7_relat_1(X1,X2),X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.60/0.79  cnf(c_0_49, negated_conjecture, (m1_subset_1(k7_relat_1(esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))|~v4_relat_1(esk4_0,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_27]), c_0_37])])).
% 0.60/0.79  fof(c_0_50, plain, ![X29, X30, X31, X32]:(~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))|k5_relset_1(X29,X30,X31,X32)=k7_relat_1(X31,X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_relset_1])])).
% 0.60/0.79  cnf(c_0_51, plain, (r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)|~v4_relat_1(X1,X3)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_48]), c_0_27])).
% 0.60/0.79  cnf(c_0_52, negated_conjecture, (m1_subset_1(k7_relat_1(esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))), inference(spm,[status(thm)],[c_0_49, c_0_36])).
% 0.60/0.79  cnf(c_0_53, plain, (k5_relset_1(X2,X3,X1,X4)=k7_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.60/0.79  cnf(c_0_54, negated_conjecture, (r1_tarski(k1_relat_1(k7_relat_1(esk4_0,X1)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_36]), c_0_37])])).
% 0.60/0.79  cnf(c_0_55, negated_conjecture, (v1_relat_1(k7_relat_1(esk4_0,X1))), inference(spm,[status(thm)],[c_0_29, c_0_52])).
% 0.60/0.79  cnf(c_0_56, negated_conjecture, (~m1_subset_1(k5_relset_1(esk1_0,esk3_0,esk4_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.60/0.79  cnf(c_0_57, negated_conjecture, (k5_relset_1(esk1_0,esk3_0,esk4_0,X1)=k7_relat_1(esk4_0,X1)), inference(spm,[status(thm)],[c_0_53, c_0_17])).
% 0.60/0.79  cnf(c_0_58, negated_conjecture, (m1_subset_1(k7_relat_1(esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~r1_tarski(k2_relat_1(k7_relat_1(esk4_0,X1)),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_54]), c_0_55])])).
% 0.60/0.79  cnf(c_0_59, negated_conjecture, (~m1_subset_1(k7_relat_1(esk4_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(rw,[status(thm)],[c_0_56, c_0_57])).
% 0.60/0.79  cnf(c_0_60, negated_conjecture, (m1_subset_1(k7_relat_1(esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(X1,esk3_0)))), inference(spm,[status(thm)],[c_0_58, c_0_46])).
% 0.60/0.79  cnf(c_0_61, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_60])]), ['proof']).
% 0.60/0.79  # SZS output end CNFRefutation
% 0.60/0.79  # Proof object total steps             : 62
% 0.60/0.79  # Proof object clause steps            : 37
% 0.60/0.79  # Proof object formula steps           : 25
% 0.60/0.79  # Proof object conjectures             : 25
% 0.60/0.79  # Proof object clause conjectures      : 22
% 0.60/0.79  # Proof object formula conjectures     : 3
% 0.60/0.79  # Proof object initial clauses used    : 15
% 0.60/0.79  # Proof object initial formulas used   : 12
% 0.60/0.79  # Proof object generating inferences   : 20
% 0.60/0.79  # Proof object simplifying inferences  : 15
% 0.60/0.79  # Training examples: 0 positive, 0 negative
% 0.60/0.79  # Parsed axioms                        : 12
% 0.60/0.79  # Removed by relevancy pruning/SinE    : 0
% 0.60/0.79  # Initial clauses                      : 18
% 0.60/0.79  # Removed in clause preprocessing      : 0
% 0.60/0.79  # Initial clauses in saturation        : 18
% 0.60/0.79  # Processed clauses                    : 2031
% 0.60/0.79  # ...of these trivial                  : 31
% 0.60/0.79  # ...subsumed                          : 1125
% 0.60/0.79  # ...remaining for further processing  : 875
% 0.60/0.79  # Other redundant clauses eliminated   : 0
% 0.60/0.79  # Clauses deleted for lack of memory   : 0
% 0.60/0.79  # Backward-subsumed                    : 20
% 0.60/0.79  # Backward-rewritten                   : 32
% 0.60/0.79  # Generated clauses                    : 27982
% 0.60/0.79  # ...of the previous two non-trivial   : 25759
% 0.60/0.79  # Contextual simplify-reflections      : 10
% 0.60/0.79  # Paramodulations                      : 27982
% 0.60/0.79  # Factorizations                       : 0
% 0.60/0.79  # Equation resolutions                 : 0
% 0.60/0.79  # Propositional unsat checks           : 0
% 0.60/0.79  #    Propositional check models        : 0
% 0.60/0.79  #    Propositional check unsatisfiable : 0
% 0.60/0.79  #    Propositional clauses             : 0
% 0.60/0.79  #    Propositional clauses after purity: 0
% 0.60/0.79  #    Propositional unsat core size     : 0
% 0.60/0.79  #    Propositional preprocessing time  : 0.000
% 0.60/0.79  #    Propositional encoding time       : 0.000
% 0.60/0.79  #    Propositional solver time         : 0.000
% 0.60/0.79  #    Success case prop preproc time    : 0.000
% 0.60/0.79  #    Success case prop encoding time   : 0.000
% 0.60/0.79  #    Success case prop solver time     : 0.000
% 0.60/0.79  # Current number of processed clauses  : 805
% 0.60/0.79  #    Positive orientable unit clauses  : 101
% 0.60/0.79  #    Positive unorientable unit clauses: 0
% 0.60/0.79  #    Negative unit clauses             : 0
% 0.60/0.79  #    Non-unit-clauses                  : 704
% 0.60/0.79  # Current number of unprocessed clauses: 23724
% 0.60/0.79  # ...number of literals in the above   : 107086
% 0.60/0.79  # Current number of archived formulas  : 0
% 0.60/0.79  # Current number of archived clauses   : 70
% 0.60/0.79  # Clause-clause subsumption calls (NU) : 199260
% 0.60/0.79  # Rec. Clause-clause subsumption calls : 116473
% 0.60/0.79  # Non-unit clause-clause subsumptions  : 1151
% 0.60/0.79  # Unit Clause-clause subsumption calls : 486
% 0.60/0.79  # Rewrite failures with RHS unbound    : 0
% 0.60/0.79  # BW rewrite match attempts            : 272
% 0.60/0.79  # BW rewrite match successes           : 24
% 0.60/0.79  # Condensation attempts                : 0
% 0.60/0.79  # Condensation successes               : 0
% 0.60/0.79  # Termbank termtop insertions          : 472663
% 0.60/0.79  
% 0.60/0.79  # -------------------------------------------------
% 0.60/0.79  # User time                : 0.416 s
% 0.60/0.79  # System time              : 0.023 s
% 0.60/0.79  # Total time               : 0.440 s
% 0.60/0.79  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------

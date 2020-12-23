%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:57:39 EST 2020

% Result     : Theorem 0.52s
% Output     : CNFRefutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 195 expanded)
%              Number of clauses        :   38 (  83 expanded)
%              Number of leaves         :   13 (  49 expanded)
%              Depth                    :   15
%              Number of atoms          :  149 ( 451 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_relset_1)).

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

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(fc23_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v4_relat_1(X3,X2) )
     => ( v1_relat_1(k7_relat_1(X3,X1))
        & v4_relat_1(k7_relat_1(X3,X1),X1)
        & v4_relat_1(k7_relat_1(X3,X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc23_relat_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

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

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t99_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k2_relat_1(k7_relat_1(X2,X1)),k2_relat_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_relat_1)).

fof(t11_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( r1_tarski(k1_relat_1(X3),X1)
          & r1_tarski(k2_relat_1(X3),X2) )
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(redefinition_k5_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k5_relset_1(X1,X2,X3,X4) = k7_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
       => m1_subset_1(k5_relset_1(X1,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(assume_negation,[status(cth)],[t33_relset_1])).

fof(c_0_14,plain,(
    ! [X27,X28,X29] :
      ( ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))
      | k2_relset_1(X27,X28,X29) = k2_relat_1(X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_15,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))
    & ~ m1_subset_1(k5_relset_1(esk1_0,esk3_0,esk4_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

fof(c_0_16,plain,(
    ! [X24,X25,X26] :
      ( ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))
      | m1_subset_1(k2_relset_1(X24,X25,X26),k1_zfmisc_1(X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_relset_1])])).

cnf(c_0_17,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,plain,(
    ! [X12,X13] :
      ( ( ~ v4_relat_1(X13,X12)
        | r1_tarski(k1_relat_1(X13),X12)
        | ~ v1_relat_1(X13) )
      & ( ~ r1_tarski(k1_relat_1(X13),X12)
        | v4_relat_1(X13,X12)
        | ~ v1_relat_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

fof(c_0_20,plain,(
    ! [X14,X15,X16] :
      ( ( v1_relat_1(k7_relat_1(X16,X14))
        | ~ v1_relat_1(X16)
        | ~ v4_relat_1(X16,X15) )
      & ( v4_relat_1(k7_relat_1(X16,X14),X14)
        | ~ v1_relat_1(X16)
        | ~ v4_relat_1(X16,X15) )
      & ( v4_relat_1(k7_relat_1(X16,X14),X15)
        | ~ v1_relat_1(X16)
        | ~ v4_relat_1(X16,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc23_relat_1])])])).

fof(c_0_21,plain,(
    ! [X21,X22,X23] :
      ( ( v4_relat_1(X23,X21)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))) )
      & ( v5_relat_1(X23,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_22,plain,(
    ! [X10,X11] :
      ( ~ v1_relat_1(X10)
      | ~ m1_subset_1(X11,k1_zfmisc_1(X10))
      | v1_relat_1(X11) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_23,plain,(
    ! [X17,X18] : v1_relat_1(k2_zfmisc_1(X17,X18)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_24,plain,(
    ! [X8,X9] :
      ( ( ~ m1_subset_1(X8,k1_zfmisc_1(X9))
        | r1_tarski(X8,X9) )
      & ( ~ r1_tarski(X8,X9)
        | m1_subset_1(X8,k1_zfmisc_1(X9)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_25,plain,
    ( m1_subset_1(k2_relset_1(X2,X3,X1),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,negated_conjecture,
    ( k2_relset_1(esk1_0,esk3_0,esk4_0) = k2_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_27,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( v4_relat_1(k7_relat_1(X1,X2),X3)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_33,plain,(
    ! [X5,X6,X7] :
      ( ~ r1_tarski(X5,X6)
      | ~ r1_tarski(X6,X7)
      | r1_tarski(X5,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(k2_relat_1(esk4_0),k1_zfmisc_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_18])])).

fof(c_0_36,plain,(
    ! [X19,X20] :
      ( ~ v1_relat_1(X20)
      | r1_tarski(k2_relat_1(k7_relat_1(X20,X19)),k2_relat_1(X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t99_relat_1])])).

fof(c_0_37,plain,(
    ! [X34,X35,X36] :
      ( ~ v1_relat_1(X36)
      | ~ r1_tarski(k1_relat_1(X36),X34)
      | ~ r1_tarski(k2_relat_1(X36),X35)
      | m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).

cnf(c_0_38,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X3)
    | ~ v4_relat_1(X1,X3)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])).

cnf(c_0_39,negated_conjecture,
    ( v4_relat_1(esk4_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_18])).

cnf(c_0_40,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_18]),c_0_32])])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_43,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(X1,X2)),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_44,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(k1_relat_1(k7_relat_1(esk4_0,X1)),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(X1,esk3_0)
    | ~ r1_tarski(X1,k2_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(k2_relat_1(k7_relat_1(esk4_0,X1)),k2_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(k7_relat_1(esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(esk1_0,X2)))
    | ~ v1_relat_1(k7_relat_1(esk4_0,X1))
    | ~ r1_tarski(k2_relat_1(k7_relat_1(esk4_0,X1)),X2) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(k2_relat_1(k7_relat_1(esk4_0,X1)),esk3_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(k7_relat_1(esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))
    | ~ v1_relat_1(k7_relat_1(esk4_0,X1)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_51,plain,
    ( v4_relat_1(k7_relat_1(X1,X2),X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(k7_relat_1(esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))
    | ~ v4_relat_1(esk4_0,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_29]),c_0_40])])).

fof(c_0_53,plain,(
    ! [X30,X31,X32,X33] :
      ( ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
      | k5_relset_1(X30,X31,X32,X33) = k7_relat_1(X32,X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_relset_1])])).

cnf(c_0_54,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)
    | ~ v4_relat_1(X1,X3)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_51]),c_0_29])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(k7_relat_1(esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_39])).

cnf(c_0_56,plain,
    ( k5_relset_1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(k1_relat_1(k7_relat_1(esk4_0,X1)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_39]),c_0_40])])).

cnf(c_0_58,negated_conjecture,
    ( v1_relat_1(k7_relat_1(esk4_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_55]),c_0_32])])).

cnf(c_0_59,negated_conjecture,
    ( ~ m1_subset_1(k5_relset_1(esk1_0,esk3_0,esk4_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_60,negated_conjecture,
    ( k5_relset_1(esk1_0,esk3_0,esk4_0,X1) = k7_relat_1(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_18])).

cnf(c_0_61,negated_conjecture,
    ( m1_subset_1(k7_relat_1(esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relat_1(k7_relat_1(esk4_0,X1)),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_57]),c_0_58])])).

cnf(c_0_62,negated_conjecture,
    ( ~ m1_subset_1(k7_relat_1(esk4_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(rw,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_63,negated_conjecture,
    ( m1_subset_1(k7_relat_1(esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(X1,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_61,c_0_49])).

cnf(c_0_64,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_63])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:16:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.52/0.72  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S087N
% 0.52/0.72  # and selection function SelectCQArNpEqFirstUnlessPDom.
% 0.52/0.72  #
% 0.52/0.72  # Preprocessing time       : 0.027 s
% 0.52/0.72  # Presaturation interreduction done
% 0.52/0.72  
% 0.52/0.72  # Proof found!
% 0.52/0.72  # SZS status Theorem
% 0.52/0.72  # SZS output start CNFRefutation
% 0.52/0.72  fof(t33_relset_1, conjecture, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))=>m1_subset_1(k5_relset_1(X1,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_relset_1)).
% 0.52/0.72  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.52/0.72  fof(dt_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k2_relset_1(X1,X2,X3),k1_zfmisc_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 0.52/0.72  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 0.52/0.72  fof(fc23_relat_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v4_relat_1(X3,X2))=>((v1_relat_1(k7_relat_1(X3,X1))&v4_relat_1(k7_relat_1(X3,X1),X1))&v4_relat_1(k7_relat_1(X3,X1),X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc23_relat_1)).
% 0.52/0.72  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.52/0.72  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.52/0.72  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.52/0.72  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.52/0.72  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.52/0.72  fof(t99_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k2_relat_1(k7_relat_1(X2,X1)),k2_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_relat_1)).
% 0.52/0.72  fof(t11_relset_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>((r1_tarski(k1_relat_1(X3),X1)&r1_tarski(k2_relat_1(X3),X2))=>m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 0.52/0.72  fof(redefinition_k5_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k5_relset_1(X1,X2,X3,X4)=k7_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 0.52/0.72  fof(c_0_13, negated_conjecture, ~(![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))=>m1_subset_1(k5_relset_1(X1,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X3))))), inference(assume_negation,[status(cth)],[t33_relset_1])).
% 0.52/0.72  fof(c_0_14, plain, ![X27, X28, X29]:(~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))|k2_relset_1(X27,X28,X29)=k2_relat_1(X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.52/0.72  fof(c_0_15, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))&~m1_subset_1(k5_relset_1(esk1_0,esk3_0,esk4_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.52/0.72  fof(c_0_16, plain, ![X24, X25, X26]:(~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))|m1_subset_1(k2_relset_1(X24,X25,X26),k1_zfmisc_1(X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_relset_1])])).
% 0.52/0.72  cnf(c_0_17, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.52/0.72  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.52/0.72  fof(c_0_19, plain, ![X12, X13]:((~v4_relat_1(X13,X12)|r1_tarski(k1_relat_1(X13),X12)|~v1_relat_1(X13))&(~r1_tarski(k1_relat_1(X13),X12)|v4_relat_1(X13,X12)|~v1_relat_1(X13))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.52/0.72  fof(c_0_20, plain, ![X14, X15, X16]:(((v1_relat_1(k7_relat_1(X16,X14))|(~v1_relat_1(X16)|~v4_relat_1(X16,X15)))&(v4_relat_1(k7_relat_1(X16,X14),X14)|(~v1_relat_1(X16)|~v4_relat_1(X16,X15))))&(v4_relat_1(k7_relat_1(X16,X14),X15)|(~v1_relat_1(X16)|~v4_relat_1(X16,X15)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc23_relat_1])])])).
% 0.52/0.72  fof(c_0_21, plain, ![X21, X22, X23]:((v4_relat_1(X23,X21)|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))))&(v5_relat_1(X23,X22)|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.52/0.72  fof(c_0_22, plain, ![X10, X11]:(~v1_relat_1(X10)|(~m1_subset_1(X11,k1_zfmisc_1(X10))|v1_relat_1(X11))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.52/0.72  fof(c_0_23, plain, ![X17, X18]:v1_relat_1(k2_zfmisc_1(X17,X18)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.52/0.72  fof(c_0_24, plain, ![X8, X9]:((~m1_subset_1(X8,k1_zfmisc_1(X9))|r1_tarski(X8,X9))&(~r1_tarski(X8,X9)|m1_subset_1(X8,k1_zfmisc_1(X9)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.52/0.72  cnf(c_0_25, plain, (m1_subset_1(k2_relset_1(X2,X3,X1),k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.52/0.72  cnf(c_0_26, negated_conjecture, (k2_relset_1(esk1_0,esk3_0,esk4_0)=k2_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.52/0.72  cnf(c_0_27, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.52/0.72  cnf(c_0_28, plain, (v4_relat_1(k7_relat_1(X1,X2),X3)|~v1_relat_1(X1)|~v4_relat_1(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.52/0.72  cnf(c_0_29, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)|~v4_relat_1(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.52/0.72  cnf(c_0_30, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.52/0.72  cnf(c_0_31, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.52/0.72  cnf(c_0_32, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.52/0.72  fof(c_0_33, plain, ![X5, X6, X7]:(~r1_tarski(X5,X6)|~r1_tarski(X6,X7)|r1_tarski(X5,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.52/0.72  cnf(c_0_34, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.52/0.72  cnf(c_0_35, negated_conjecture, (m1_subset_1(k2_relat_1(esk4_0),k1_zfmisc_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_18])])).
% 0.52/0.72  fof(c_0_36, plain, ![X19, X20]:(~v1_relat_1(X20)|r1_tarski(k2_relat_1(k7_relat_1(X20,X19)),k2_relat_1(X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t99_relat_1])])).
% 0.52/0.72  fof(c_0_37, plain, ![X34, X35, X36]:(~v1_relat_1(X36)|(~r1_tarski(k1_relat_1(X36),X34)|~r1_tarski(k2_relat_1(X36),X35)|m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).
% 0.52/0.72  cnf(c_0_38, plain, (r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X3)|~v4_relat_1(X1,X3)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29])).
% 0.52/0.72  cnf(c_0_39, negated_conjecture, (v4_relat_1(esk4_0,esk1_0)), inference(spm,[status(thm)],[c_0_30, c_0_18])).
% 0.52/0.72  cnf(c_0_40, negated_conjecture, (v1_relat_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_18]), c_0_32])])).
% 0.52/0.72  cnf(c_0_41, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.52/0.72  cnf(c_0_42, negated_conjecture, (r1_tarski(k2_relat_1(esk4_0),esk3_0)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.52/0.72  cnf(c_0_43, plain, (r1_tarski(k2_relat_1(k7_relat_1(X1,X2)),k2_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.52/0.72  cnf(c_0_44, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X3)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.52/0.72  cnf(c_0_45, negated_conjecture, (r1_tarski(k1_relat_1(k7_relat_1(esk4_0,X1)),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40])])).
% 0.52/0.72  cnf(c_0_46, negated_conjecture, (r1_tarski(X1,esk3_0)|~r1_tarski(X1,k2_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.52/0.72  cnf(c_0_47, negated_conjecture, (r1_tarski(k2_relat_1(k7_relat_1(esk4_0,X1)),k2_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_43, c_0_40])).
% 0.52/0.72  cnf(c_0_48, negated_conjecture, (m1_subset_1(k7_relat_1(esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(esk1_0,X2)))|~v1_relat_1(k7_relat_1(esk4_0,X1))|~r1_tarski(k2_relat_1(k7_relat_1(esk4_0,X1)),X2)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.52/0.72  cnf(c_0_49, negated_conjecture, (r1_tarski(k2_relat_1(k7_relat_1(esk4_0,X1)),esk3_0)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.52/0.72  cnf(c_0_50, negated_conjecture, (m1_subset_1(k7_relat_1(esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))|~v1_relat_1(k7_relat_1(esk4_0,X1))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.52/0.72  cnf(c_0_51, plain, (v4_relat_1(k7_relat_1(X1,X2),X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.52/0.72  cnf(c_0_52, negated_conjecture, (m1_subset_1(k7_relat_1(esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))|~v4_relat_1(esk4_0,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_29]), c_0_40])])).
% 0.52/0.72  fof(c_0_53, plain, ![X30, X31, X32, X33]:(~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))|k5_relset_1(X30,X31,X32,X33)=k7_relat_1(X32,X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_relset_1])])).
% 0.52/0.72  cnf(c_0_54, plain, (r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)|~v4_relat_1(X1,X3)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_51]), c_0_29])).
% 0.52/0.72  cnf(c_0_55, negated_conjecture, (m1_subset_1(k7_relat_1(esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))), inference(spm,[status(thm)],[c_0_52, c_0_39])).
% 0.52/0.72  cnf(c_0_56, plain, (k5_relset_1(X2,X3,X1,X4)=k7_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.52/0.72  cnf(c_0_57, negated_conjecture, (r1_tarski(k1_relat_1(k7_relat_1(esk4_0,X1)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_39]), c_0_40])])).
% 0.52/0.72  cnf(c_0_58, negated_conjecture, (v1_relat_1(k7_relat_1(esk4_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_55]), c_0_32])])).
% 0.52/0.72  cnf(c_0_59, negated_conjecture, (~m1_subset_1(k5_relset_1(esk1_0,esk3_0,esk4_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.52/0.72  cnf(c_0_60, negated_conjecture, (k5_relset_1(esk1_0,esk3_0,esk4_0,X1)=k7_relat_1(esk4_0,X1)), inference(spm,[status(thm)],[c_0_56, c_0_18])).
% 0.52/0.72  cnf(c_0_61, negated_conjecture, (m1_subset_1(k7_relat_1(esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~r1_tarski(k2_relat_1(k7_relat_1(esk4_0,X1)),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_57]), c_0_58])])).
% 0.52/0.72  cnf(c_0_62, negated_conjecture, (~m1_subset_1(k7_relat_1(esk4_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(rw,[status(thm)],[c_0_59, c_0_60])).
% 0.52/0.72  cnf(c_0_63, negated_conjecture, (m1_subset_1(k7_relat_1(esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(X1,esk3_0)))), inference(spm,[status(thm)],[c_0_61, c_0_49])).
% 0.52/0.72  cnf(c_0_64, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_63])]), ['proof']).
% 0.52/0.72  # SZS output end CNFRefutation
% 0.52/0.72  # Proof object total steps             : 65
% 0.52/0.72  # Proof object clause steps            : 38
% 0.52/0.72  # Proof object formula steps           : 27
% 0.52/0.72  # Proof object conjectures             : 25
% 0.52/0.72  # Proof object clause conjectures      : 22
% 0.52/0.72  # Proof object formula conjectures     : 3
% 0.52/0.72  # Proof object initial clauses used    : 16
% 0.52/0.72  # Proof object initial formulas used   : 13
% 0.52/0.72  # Proof object generating inferences   : 20
% 0.52/0.72  # Proof object simplifying inferences  : 19
% 0.52/0.72  # Training examples: 0 positive, 0 negative
% 0.52/0.72  # Parsed axioms                        : 13
% 0.52/0.72  # Removed by relevancy pruning/SinE    : 0
% 0.52/0.72  # Initial clauses                      : 19
% 0.52/0.72  # Removed in clause preprocessing      : 0
% 0.52/0.72  # Initial clauses in saturation        : 19
% 0.52/0.72  # Processed clauses                    : 2053
% 0.52/0.72  # ...of these trivial                  : 34
% 0.52/0.72  # ...subsumed                          : 1177
% 0.52/0.72  # ...remaining for further processing  : 842
% 0.52/0.72  # Other redundant clauses eliminated   : 0
% 0.52/0.72  # Clauses deleted for lack of memory   : 0
% 0.52/0.72  # Backward-subsumed                    : 4
% 0.52/0.72  # Backward-rewritten                   : 28
% 0.52/0.72  # Generated clauses                    : 29323
% 0.52/0.72  # ...of the previous two non-trivial   : 27127
% 0.52/0.72  # Contextual simplify-reflections      : 10
% 0.52/0.72  # Paramodulations                      : 29323
% 0.52/0.72  # Factorizations                       : 0
% 0.52/0.72  # Equation resolutions                 : 0
% 0.52/0.72  # Propositional unsat checks           : 0
% 0.52/0.72  #    Propositional check models        : 0
% 0.52/0.72  #    Propositional check unsatisfiable : 0
% 0.52/0.72  #    Propositional clauses             : 0
% 0.52/0.72  #    Propositional clauses after purity: 0
% 0.52/0.72  #    Propositional unsat core size     : 0
% 0.52/0.72  #    Propositional preprocessing time  : 0.000
% 0.52/0.72  #    Propositional encoding time       : 0.000
% 0.52/0.72  #    Propositional solver time         : 0.000
% 0.52/0.72  #    Success case prop preproc time    : 0.000
% 0.52/0.72  #    Success case prop encoding time   : 0.000
% 0.52/0.72  #    Success case prop solver time     : 0.000
% 0.52/0.72  # Current number of processed clauses  : 791
% 0.52/0.72  #    Positive orientable unit clauses  : 102
% 0.52/0.72  #    Positive unorientable unit clauses: 0
% 0.52/0.72  #    Negative unit clauses             : 0
% 0.52/0.72  #    Non-unit-clauses                  : 689
% 0.52/0.72  # Current number of unprocessed clauses: 25091
% 0.52/0.72  # ...number of literals in the above   : 112141
% 0.52/0.72  # Current number of archived formulas  : 0
% 0.52/0.72  # Current number of archived clauses   : 51
% 0.52/0.72  # Clause-clause subsumption calls (NU) : 186788
% 0.52/0.72  # Rec. Clause-clause subsumption calls : 103779
% 0.52/0.72  # Non-unit clause-clause subsumptions  : 1187
% 0.52/0.72  # Unit Clause-clause subsumption calls : 587
% 0.52/0.72  # Rewrite failures with RHS unbound    : 0
% 0.52/0.72  # BW rewrite match attempts            : 349
% 0.52/0.72  # BW rewrite match successes           : 14
% 0.52/0.72  # Condensation attempts                : 0
% 0.52/0.72  # Condensation successes               : 0
% 0.52/0.72  # Termbank termtop insertions          : 503112
% 0.52/0.72  
% 0.52/0.72  # -------------------------------------------------
% 0.52/0.72  # User time                : 0.367 s
% 0.52/0.72  # System time              : 0.014 s
% 0.52/0.72  # Total time               : 0.381 s
% 0.52/0.72  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------

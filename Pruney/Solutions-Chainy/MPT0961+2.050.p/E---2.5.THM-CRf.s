%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:58 EST 2020

% Result     : Theorem 5.07s
% Output     : CNFRefutation 5.07s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 676 expanded)
%              Number of clauses        :   45 ( 335 expanded)
%              Number of leaves         :   10 ( 162 expanded)
%              Depth                    :   12
%              Number of atoms          :  199 (2384 expanded)
%              Number of equality atoms :   82 ( 854 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t3_funct_2,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_funct_1(X1)
        & v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t64_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( ( k1_relat_1(X1) = k1_xboole_0
          | k2_relat_1(X1) = k1_xboole_0 )
       => X1 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t29_relset_1,axiom,(
    ! [X1] : m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(t81_relat_1,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(d1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( ( X2 = k1_xboole_0
           => X1 = k1_xboole_0 )
         => ( v1_funct_2(X3,X1,X2)
          <=> X1 = k1_relset_1(X1,X2,X3) ) )
        & ( X2 = k1_xboole_0
         => ( X1 = k1_xboole_0
            | ( v1_funct_2(X3,X1,X2)
            <=> X3 = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(t11_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( r1_tarski(k1_relat_1(X3),X1)
          & r1_tarski(k2_relat_1(X3),X2) )
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ( v1_funct_1(X1)
          & v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) ) ) ),
    inference(assume_negation,[status(cth)],[t3_funct_2])).

fof(c_0_11,plain,(
    ! [X6,X7] :
      ( ( k2_zfmisc_1(X6,X7) != k1_xboole_0
        | X6 = k1_xboole_0
        | X7 = k1_xboole_0 )
      & ( X6 != k1_xboole_0
        | k2_zfmisc_1(X6,X7) = k1_xboole_0 )
      & ( X7 != k1_xboole_0
        | k2_zfmisc_1(X6,X7) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_12,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_funct_1(esk1_0)
    & ( ~ v1_funct_1(esk1_0)
      | ~ v1_funct_2(esk1_0,k1_relat_1(esk1_0),k2_relat_1(esk1_0))
      | ~ m1_subset_1(esk1_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0)))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

fof(c_0_13,plain,(
    ! [X8] :
      ( ( k1_relat_1(X8) != k1_xboole_0
        | X8 = k1_xboole_0
        | ~ v1_relat_1(X8) )
      & ( k2_relat_1(X8) != k1_xboole_0
        | X8 = k1_xboole_0
        | ~ v1_relat_1(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).

fof(c_0_14,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_15,plain,(
    ! [X15] : m1_subset_1(k6_relat_1(X15),k1_zfmisc_1(k2_zfmisc_1(X15,X15))) ),
    inference(variable_rename,[status(thm)],[t29_relset_1])).

cnf(c_0_16,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( ~ v1_funct_1(esk1_0)
    | ~ v1_funct_2(esk1_0,k1_relat_1(esk1_0),k2_relat_1(esk1_0))
    | ~ m1_subset_1(esk1_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( v1_funct_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( X1 = k1_xboole_0
    | k2_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t81_relat_1])).

cnf(c_0_24,negated_conjecture,
    ( ~ v1_funct_2(esk1_0,k1_relat_1(esk1_0),k2_relat_1(esk1_0))
    | ~ m1_subset_1(esk1_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_18])])).

cnf(c_0_25,plain,
    ( X1 = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20])])).

cnf(c_0_26,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_27,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_28,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_30,plain,(
    ! [X16,X17,X18] :
      ( ( ~ v1_funct_2(X18,X16,X17)
        | X16 = k1_relset_1(X16,X17,X18)
        | X17 = k1_xboole_0
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) )
      & ( X16 != k1_relset_1(X16,X17,X18)
        | v1_funct_2(X18,X16,X17)
        | X17 = k1_xboole_0
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) )
      & ( ~ v1_funct_2(X18,X16,X17)
        | X16 = k1_relset_1(X16,X17,X18)
        | X16 != k1_xboole_0
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) )
      & ( X16 != k1_relset_1(X16,X17,X18)
        | v1_funct_2(X18,X16,X17)
        | X16 != k1_xboole_0
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) )
      & ( ~ v1_funct_2(X18,X16,X17)
        | X18 = k1_xboole_0
        | X16 = k1_xboole_0
        | X17 != k1_xboole_0
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) )
      & ( X18 != k1_xboole_0
        | v1_funct_2(X18,X16,X17)
        | X16 = k1_xboole_0
        | X17 != k1_xboole_0
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_31,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_32,plain,(
    ! [X12,X13,X14] :
      ( ~ v1_relat_1(X14)
      | ~ r1_tarski(k1_relat_1(X14),X12)
      | ~ r1_tarski(k2_relat_1(X14),X13)
      | m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_34,negated_conjecture,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ r1_tarski(k2_relat_1(esk1_0),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k2_relat_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_27]),c_0_26]),c_0_27]),c_0_22]),c_0_28]),c_0_29])])).

cnf(c_0_35,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | X3 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_37,plain,
    ( v1_funct_2(X3,X1,X2)
    | X1 != k1_relset_1(X1,X2,X3)
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( ~ v1_funct_2(X1,X1,X1)
    | ~ r1_tarski(k2_relat_1(esk1_0),X1)
    | ~ r1_tarski(X1,k2_relat_1(esk1_0))
    | ~ r1_tarski(X1,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_20])).

cnf(c_0_41,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ v1_funct_2(X2,X1,k1_xboole_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_35]),c_0_36])).

cnf(c_0_42,plain,
    ( v1_funct_2(X1,k1_xboole_0,X2)
    | k1_relset_1(k1_xboole_0,X2,X1) != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_37]),c_0_22])).

fof(c_0_43,plain,(
    ! [X9,X10,X11] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
      | k1_relset_1(X9,X10,X11) = k1_relat_1(X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_44,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_45,negated_conjecture,
    ( ~ v1_funct_2(k2_relat_1(esk1_0),k2_relat_1(esk1_0),k2_relat_1(esk1_0))
    | ~ r1_tarski(k2_relat_1(esk1_0),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k2_relat_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_39]),c_0_39])])).

cnf(c_0_46,plain,
    ( X1 = k1_xboole_0
    | ~ v1_funct_2(X1,X1,k1_xboole_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(ef,[status(thm)],[c_0_41])).

cnf(c_0_47,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,X1)
    | k1_relset_1(k1_xboole_0,X1,k1_xboole_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_42,c_0_28])).

cnf(c_0_48,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_49,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k2_zfmisc_1(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_50,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_39])).

cnf(c_0_51,negated_conjecture,
    ( ~ v1_funct_2(k2_relat_1(esk1_0),k2_relat_1(esk1_0),k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k2_relat_1(esk1_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_39])])).

cnf(c_0_52,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_26]),c_0_22]),c_0_28])])).

cnf(c_0_53,plain,
    ( X1 = k1_xboole_0
    | k2_zfmisc_1(X1,X1) != k1_xboole_0 ),
    inference(ef,[status(thm)],[c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(esk1_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_29])).

cnf(c_0_55,negated_conjecture,
    ( ~ v1_funct_2(k2_relat_1(esk1_0),k2_relat_1(esk1_0),k1_xboole_0)
    | ~ m1_subset_1(k2_relat_1(esk1_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_52])])).

cnf(c_0_56,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(X1,X1))
    | ~ r1_tarski(k2_zfmisc_1(X1,X1),k1_xboole_0) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_20])])).

cnf(c_0_57,plain,
    ( v1_funct_2(X3,X1,X2)
    | X2 = k1_xboole_0
    | X1 != k1_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_58,negated_conjecture,
    ( ~ v1_funct_2(esk1_0,k1_relat_1(esk1_0),k2_relat_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_54])])).

cnf(c_0_59,negated_conjecture,
    ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(k2_relat_1(esk1_0),k2_relat_1(esk1_0)))
    | ~ r1_tarski(k2_zfmisc_1(k2_relat_1(esk1_0),k2_relat_1(esk1_0)),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_52]),c_0_28])])).

cnf(c_0_60,negated_conjecture,
    ( k2_relat_1(esk1_0) = k1_xboole_0
    | k1_relset_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0),esk1_0) != k1_relat_1(esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_54]),c_0_58])).

cnf(c_0_61,negated_conjecture,
    ( ~ v1_funct_2(k2_zfmisc_1(k2_relat_1(esk1_0),k2_relat_1(esk1_0)),k2_zfmisc_1(k2_relat_1(esk1_0),k2_relat_1(esk1_0)),k1_xboole_0)
    | ~ m1_subset_1(k2_zfmisc_1(k2_relat_1(esk1_0),k2_relat_1(esk1_0)),k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_46]),c_0_39])])).

cnf(c_0_62,negated_conjecture,
    ( k2_relat_1(esk1_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_48]),c_0_54])])).

cnf(c_0_63,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_62]),c_0_62]),c_0_22]),c_0_62]),c_0_62]),c_0_22]),c_0_52]),c_0_62]),c_0_62]),c_0_22]),c_0_28])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.33  % Computer   : n001.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 16:28:45 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  # Version: 2.5pre002
% 0.11/0.33  # No SInE strategy applied
% 0.11/0.33  # Trying AutoSched0 for 299 seconds
% 5.07/5.25  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S039A
% 5.07/5.25  # and selection function PSelectUnlessUniqMaxPos.
% 5.07/5.25  #
% 5.07/5.25  # Preprocessing time       : 0.028 s
% 5.07/5.25  # Presaturation interreduction done
% 5.07/5.25  
% 5.07/5.25  # Proof found!
% 5.07/5.25  # SZS status Theorem
% 5.07/5.25  # SZS output start CNFRefutation
% 5.07/5.25  fof(t3_funct_2, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 5.07/5.25  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.07/5.25  fof(t64_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>((k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)=k1_xboole_0)=>X1=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 5.07/5.25  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.07/5.25  fof(t29_relset_1, axiom, ![X1]:m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 5.07/5.25  fof(t81_relat_1, axiom, k6_relat_1(k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 5.07/5.25  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 5.07/5.25  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 5.07/5.25  fof(t11_relset_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>((r1_tarski(k1_relat_1(X3),X1)&r1_tarski(k2_relat_1(X3),X2))=>m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 5.07/5.25  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.07/5.25  fof(c_0_10, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))))), inference(assume_negation,[status(cth)],[t3_funct_2])).
% 5.07/5.25  fof(c_0_11, plain, ![X6, X7]:((k2_zfmisc_1(X6,X7)!=k1_xboole_0|(X6=k1_xboole_0|X7=k1_xboole_0))&((X6!=k1_xboole_0|k2_zfmisc_1(X6,X7)=k1_xboole_0)&(X7!=k1_xboole_0|k2_zfmisc_1(X6,X7)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 5.07/5.25  fof(c_0_12, negated_conjecture, ((v1_relat_1(esk1_0)&v1_funct_1(esk1_0))&(~v1_funct_1(esk1_0)|~v1_funct_2(esk1_0,k1_relat_1(esk1_0),k2_relat_1(esk1_0))|~m1_subset_1(esk1_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 5.07/5.25  fof(c_0_13, plain, ![X8]:((k1_relat_1(X8)!=k1_xboole_0|X8=k1_xboole_0|~v1_relat_1(X8))&(k2_relat_1(X8)!=k1_xboole_0|X8=k1_xboole_0|~v1_relat_1(X8))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).
% 5.07/5.25  fof(c_0_14, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 5.07/5.25  fof(c_0_15, plain, ![X15]:m1_subset_1(k6_relat_1(X15),k1_zfmisc_1(k2_zfmisc_1(X15,X15))), inference(variable_rename,[status(thm)],[t29_relset_1])).
% 5.07/5.25  cnf(c_0_16, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 5.07/5.25  cnf(c_0_17, negated_conjecture, (~v1_funct_1(esk1_0)|~v1_funct_2(esk1_0,k1_relat_1(esk1_0),k2_relat_1(esk1_0))|~m1_subset_1(esk1_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0))))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 5.07/5.25  cnf(c_0_18, negated_conjecture, (v1_funct_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 5.07/5.25  cnf(c_0_19, plain, (X1=k1_xboole_0|k2_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 5.07/5.25  cnf(c_0_20, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 5.07/5.25  cnf(c_0_21, plain, (m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 5.07/5.25  cnf(c_0_22, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_16])).
% 5.07/5.25  cnf(c_0_23, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t81_relat_1])).
% 5.07/5.25  cnf(c_0_24, negated_conjecture, (~v1_funct_2(esk1_0,k1_relat_1(esk1_0),k2_relat_1(esk1_0))|~m1_subset_1(esk1_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_17, c_0_18])])).
% 5.07/5.25  cnf(c_0_25, plain, (X1=k1_xboole_0|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),k1_xboole_0)|~r1_tarski(k1_xboole_0,k2_relat_1(X1))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20])])).
% 5.07/5.25  cnf(c_0_26, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 5.07/5.25  cnf(c_0_27, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 5.07/5.25  cnf(c_0_28, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])).
% 5.07/5.25  cnf(c_0_29, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 5.07/5.25  fof(c_0_30, plain, ![X16, X17, X18]:((((~v1_funct_2(X18,X16,X17)|X16=k1_relset_1(X16,X17,X18)|X17=k1_xboole_0|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))))&(X16!=k1_relset_1(X16,X17,X18)|v1_funct_2(X18,X16,X17)|X17=k1_xboole_0|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))))&((~v1_funct_2(X18,X16,X17)|X16=k1_relset_1(X16,X17,X18)|X16!=k1_xboole_0|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))))&(X16!=k1_relset_1(X16,X17,X18)|v1_funct_2(X18,X16,X17)|X16!=k1_xboole_0|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))))))&((~v1_funct_2(X18,X16,X17)|X18=k1_xboole_0|X16=k1_xboole_0|X17!=k1_xboole_0|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))))&(X18!=k1_xboole_0|v1_funct_2(X18,X16,X17)|X16=k1_xboole_0|X17!=k1_xboole_0|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 5.07/5.25  cnf(c_0_31, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 5.07/5.25  fof(c_0_32, plain, ![X12, X13, X14]:(~v1_relat_1(X14)|(~r1_tarski(k1_relat_1(X14),X12)|~r1_tarski(k2_relat_1(X14),X13)|m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).
% 5.07/5.25  cnf(c_0_33, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_14])).
% 5.07/5.25  cnf(c_0_34, negated_conjecture, (~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)|~r1_tarski(k2_relat_1(esk1_0),k1_xboole_0)|~r1_tarski(k1_xboole_0,k2_relat_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26]), c_0_27]), c_0_26]), c_0_27]), c_0_22]), c_0_28]), c_0_29])])).
% 5.07/5.25  cnf(c_0_35, plain, (X1=k1_xboole_0|X2=k1_xboole_0|~v1_funct_2(X1,X2,X3)|X3!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 5.07/5.25  cnf(c_0_36, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_31])).
% 5.07/5.25  cnf(c_0_37, plain, (v1_funct_2(X3,X1,X2)|X1!=k1_relset_1(X1,X2,X3)|X1!=k1_xboole_0|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 5.07/5.25  cnf(c_0_38, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X3)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 5.07/5.25  cnf(c_0_39, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_33])).
% 5.07/5.25  cnf(c_0_40, negated_conjecture, (~v1_funct_2(X1,X1,X1)|~r1_tarski(k2_relat_1(esk1_0),X1)|~r1_tarski(X1,k2_relat_1(esk1_0))|~r1_tarski(X1,k1_xboole_0)|~r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_34, c_0_20])).
% 5.07/5.25  cnf(c_0_41, plain, (X1=k1_xboole_0|X2=k1_xboole_0|~v1_funct_2(X2,X1,k1_xboole_0)|~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_35]), c_0_36])).
% 5.07/5.25  cnf(c_0_42, plain, (v1_funct_2(X1,k1_xboole_0,X2)|k1_relset_1(k1_xboole_0,X2,X1)!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_37]), c_0_22])).
% 5.07/5.25  fof(c_0_43, plain, ![X9, X10, X11]:(~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))|k1_relset_1(X9,X10,X11)=k1_relat_1(X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 5.07/5.25  cnf(c_0_44, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 5.07/5.25  cnf(c_0_45, negated_conjecture, (~v1_funct_2(k2_relat_1(esk1_0),k2_relat_1(esk1_0),k2_relat_1(esk1_0))|~r1_tarski(k2_relat_1(esk1_0),k1_xboole_0)|~r1_tarski(k1_xboole_0,k2_relat_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_39]), c_0_39])])).
% 5.07/5.25  cnf(c_0_46, plain, (X1=k1_xboole_0|~v1_funct_2(X1,X1,k1_xboole_0)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(ef,[status(thm)],[c_0_41])).
% 5.07/5.25  cnf(c_0_47, plain, (v1_funct_2(k1_xboole_0,k1_xboole_0,X1)|k1_relset_1(k1_xboole_0,X1,k1_xboole_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_42, c_0_28])).
% 5.07/5.25  cnf(c_0_48, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 5.07/5.25  cnf(c_0_49, plain, (X1=k1_xboole_0|X2=k1_xboole_0|k2_zfmisc_1(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 5.07/5.25  cnf(c_0_50, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_44, c_0_39])).
% 5.07/5.25  cnf(c_0_51, negated_conjecture, (~v1_funct_2(k2_relat_1(esk1_0),k2_relat_1(esk1_0),k1_xboole_0)|~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)|~m1_subset_1(k2_relat_1(esk1_0),k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_39])])).
% 5.07/5.25  cnf(c_0_52, plain, (v1_funct_2(k1_xboole_0,k1_xboole_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_26]), c_0_22]), c_0_28])])).
% 5.07/5.25  cnf(c_0_53, plain, (X1=k1_xboole_0|k2_zfmisc_1(X1,X1)!=k1_xboole_0), inference(ef,[status(thm)],[c_0_49])).
% 5.07/5.25  cnf(c_0_54, negated_conjecture, (m1_subset_1(esk1_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0))))), inference(spm,[status(thm)],[c_0_50, c_0_29])).
% 5.07/5.25  cnf(c_0_55, negated_conjecture, (~v1_funct_2(k2_relat_1(esk1_0),k2_relat_1(esk1_0),k1_xboole_0)|~m1_subset_1(k2_relat_1(esk1_0),k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_52])])).
% 5.07/5.25  cnf(c_0_56, plain, (X1=k1_xboole_0|~r1_tarski(k1_xboole_0,k2_zfmisc_1(X1,X1))|~r1_tarski(k2_zfmisc_1(X1,X1),k1_xboole_0)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_20])])).
% 5.07/5.25  cnf(c_0_57, plain, (v1_funct_2(X3,X1,X2)|X2=k1_xboole_0|X1!=k1_relset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 5.07/5.25  cnf(c_0_58, negated_conjecture, (~v1_funct_2(esk1_0,k1_relat_1(esk1_0),k2_relat_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_54])])).
% 5.07/5.25  cnf(c_0_59, negated_conjecture, (~r1_tarski(k1_xboole_0,k2_zfmisc_1(k2_relat_1(esk1_0),k2_relat_1(esk1_0)))|~r1_tarski(k2_zfmisc_1(k2_relat_1(esk1_0),k2_relat_1(esk1_0)),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_52]), c_0_28])])).
% 5.07/5.25  cnf(c_0_60, negated_conjecture, (k2_relat_1(esk1_0)=k1_xboole_0|k1_relset_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0),esk1_0)!=k1_relat_1(esk1_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_54]), c_0_58])).
% 5.07/5.25  cnf(c_0_61, negated_conjecture, (~v1_funct_2(k2_zfmisc_1(k2_relat_1(esk1_0),k2_relat_1(esk1_0)),k2_zfmisc_1(k2_relat_1(esk1_0),k2_relat_1(esk1_0)),k1_xboole_0)|~m1_subset_1(k2_zfmisc_1(k2_relat_1(esk1_0),k2_relat_1(esk1_0)),k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_46]), c_0_39])])).
% 5.07/5.25  cnf(c_0_62, negated_conjecture, (k2_relat_1(esk1_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_48]), c_0_54])])).
% 5.07/5.25  cnf(c_0_63, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_62]), c_0_62]), c_0_22]), c_0_62]), c_0_62]), c_0_22]), c_0_52]), c_0_62]), c_0_62]), c_0_22]), c_0_28])]), ['proof']).
% 5.07/5.25  # SZS output end CNFRefutation
% 5.07/5.25  # Proof object total steps             : 64
% 5.07/5.25  # Proof object clause steps            : 45
% 5.07/5.25  # Proof object formula steps           : 19
% 5.07/5.25  # Proof object conjectures             : 19
% 5.07/5.25  # Proof object clause conjectures      : 16
% 5.07/5.25  # Proof object formula conjectures     : 3
% 5.07/5.25  # Proof object initial clauses used    : 18
% 5.07/5.25  # Proof object initial formulas used   : 10
% 5.07/5.25  # Proof object generating inferences   : 18
% 5.07/5.25  # Proof object simplifying inferences  : 52
% 5.07/5.25  # Training examples: 0 positive, 0 negative
% 5.07/5.25  # Parsed axioms                        : 10
% 5.07/5.25  # Removed by relevancy pruning/SinE    : 0
% 5.07/5.25  # Initial clauses                      : 23
% 5.07/5.25  # Removed in clause preprocessing      : 0
% 5.07/5.25  # Initial clauses in saturation        : 23
% 5.07/5.25  # Processed clauses                    : 18142
% 5.07/5.25  # ...of these trivial                  : 584
% 5.07/5.25  # ...subsumed                          : 15560
% 5.07/5.25  # ...remaining for further processing  : 1998
% 5.07/5.25  # Other redundant clauses eliminated   : 1421
% 5.07/5.25  # Clauses deleted for lack of memory   : 0
% 5.07/5.25  # Backward-subsumed                    : 216
% 5.07/5.25  # Backward-rewritten                   : 634
% 5.07/5.25  # Generated clauses                    : 816522
% 5.07/5.25  # ...of the previous two non-trivial   : 523430
% 5.07/5.25  # Contextual simplify-reflections      : 8
% 5.07/5.25  # Paramodulations                      : 814792
% 5.07/5.25  # Factorizations                       : 310
% 5.07/5.25  # Equation resolutions                 : 1421
% 5.07/5.25  # Propositional unsat checks           : 0
% 5.07/5.25  #    Propositional check models        : 0
% 5.07/5.25  #    Propositional check unsatisfiable : 0
% 5.07/5.25  #    Propositional clauses             : 0
% 5.07/5.25  #    Propositional clauses after purity: 0
% 5.07/5.25  #    Propositional unsat core size     : 0
% 5.07/5.25  #    Propositional preprocessing time  : 0.000
% 5.07/5.25  #    Propositional encoding time       : 0.000
% 5.07/5.25  #    Propositional solver time         : 0.000
% 5.07/5.25  #    Success case prop preproc time    : 0.000
% 5.07/5.25  #    Success case prop encoding time   : 0.000
% 5.07/5.25  #    Success case prop solver time     : 0.000
% 5.07/5.25  # Current number of processed clauses  : 1118
% 5.07/5.25  #    Positive orientable unit clauses  : 27
% 5.07/5.25  #    Positive unorientable unit clauses: 0
% 5.07/5.25  #    Negative unit clauses             : 0
% 5.07/5.25  #    Non-unit-clauses                  : 1091
% 5.07/5.25  # Current number of unprocessed clauses: 502742
% 5.07/5.25  # ...number of literals in the above   : 3428949
% 5.07/5.25  # Current number of archived formulas  : 0
% 5.07/5.25  # Current number of archived clauses   : 872
% 5.07/5.25  # Clause-clause subsumption calls (NU) : 590070
% 5.07/5.25  # Rec. Clause-clause subsumption calls : 329869
% 5.07/5.25  # Non-unit clause-clause subsumptions  : 15763
% 5.07/5.25  # Unit Clause-clause subsumption calls : 7353
% 5.07/5.25  # Rewrite failures with RHS unbound    : 0
% 5.07/5.25  # BW rewrite match attempts            : 395
% 5.07/5.25  # BW rewrite match successes           : 30
% 5.07/5.25  # Condensation attempts                : 0
% 5.07/5.25  # Condensation successes               : 0
% 5.07/5.25  # Termbank termtop insertions          : 18505852
% 5.07/5.27  
% 5.07/5.27  # -------------------------------------------------
% 5.07/5.27  # User time                : 4.724 s
% 5.07/5.27  # System time              : 0.217 s
% 5.07/5.27  # Total time               : 4.941 s
% 5.07/5.27  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------

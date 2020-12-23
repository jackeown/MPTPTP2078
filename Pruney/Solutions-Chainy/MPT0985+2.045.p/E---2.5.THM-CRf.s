%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:02:39 EST 2020

% Result     : Theorem 0.69s
% Output     : CNFRefutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :  144 (17864 expanded)
%              Number of clauses        :  110 (6738 expanded)
%              Number of leaves         :   17 (4539 expanded)
%              Depth                    :   25
%              Number of atoms          :  465 (84840 expanded)
%              Number of equality atoms :  133 (14764 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t31_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( v2_funct_1(X3)
          & k2_relset_1(X1,X2,X3) = X2 )
       => ( v1_funct_1(k2_funct_1(X3))
          & v1_funct_2(k2_funct_1(X3),X2,X1)
          & m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

fof(cc3_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_funct_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

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

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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

fof(cc1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( v1_funct_1(X3)
          & v1_partfun1(X3,X1) )
       => ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

fof(cc1_partfun1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => v1_partfun1(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_partfun1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t3_funct_2,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_funct_1(X1)
        & v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(t55_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
          & k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(cc3_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

fof(t8_boole,axiom,(
    ! [X1,X2] :
      ~ ( v1_xboole_0(X1)
        & X1 != X2
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ( ( v2_funct_1(X3)
            & k2_relset_1(X1,X2,X3) = X2 )
         => ( v1_funct_1(k2_funct_1(X3))
            & v1_funct_2(k2_funct_1(X3),X2,X1)
            & m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t31_funct_2])).

fof(c_0_18,plain,(
    ! [X16,X17] :
      ( ~ v1_relat_1(X16)
      | ~ v1_funct_1(X16)
      | ~ m1_subset_1(X17,k1_zfmisc_1(X16))
      | v1_funct_1(X17) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_funct_1])])])).

fof(c_0_19,plain,(
    ! [X8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X8)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_20,plain,(
    ! [X12,X13] :
      ( ~ v1_relat_1(X12)
      | ~ m1_subset_1(X13,k1_zfmisc_1(X12))
      | v1_relat_1(X13) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_21,negated_conjecture,
    ( v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,esk2_0,esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))
    & v2_funct_1(esk4_0)
    & k2_relset_1(esk2_0,esk3_0,esk4_0) = esk3_0
    & ( ~ v1_funct_1(k2_funct_1(esk4_0))
      | ~ v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)
      | ~ m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

fof(c_0_22,plain,(
    ! [X14,X15] : v1_relat_1(k2_zfmisc_1(X14,X15)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_23,plain,(
    ! [X27,X28,X29] :
      ( ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))
      | k1_relset_1(X27,X28,X29) = k1_relat_1(X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_24,plain,(
    ! [X39,X40,X41] :
      ( ( ~ v1_funct_2(X41,X39,X40)
        | X39 = k1_relset_1(X39,X40,X41)
        | X40 = k1_xboole_0
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))) )
      & ( X39 != k1_relset_1(X39,X40,X41)
        | v1_funct_2(X41,X39,X40)
        | X40 = k1_xboole_0
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))) )
      & ( ~ v1_funct_2(X41,X39,X40)
        | X39 = k1_relset_1(X39,X40,X41)
        | X39 != k1_xboole_0
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))) )
      & ( X39 != k1_relset_1(X39,X40,X41)
        | v1_funct_2(X41,X39,X40)
        | X39 != k1_xboole_0
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))) )
      & ( ~ v1_funct_2(X41,X39,X40)
        | X41 = k1_xboole_0
        | X39 = k1_xboole_0
        | X40 != k1_xboole_0
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))) )
      & ( X41 != k1_xboole_0
        | v1_funct_2(X41,X39,X40)
        | X39 = k1_xboole_0
        | X40 != k1_xboole_0
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_25,plain,
    ( v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_32,plain,(
    ! [X33,X34,X35] :
      ( ( v1_funct_1(X35)
        | ~ v1_funct_1(X35)
        | ~ v1_partfun1(X35,X33)
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))) )
      & ( v1_funct_2(X35,X33,X34)
        | ~ v1_funct_1(X35)
        | ~ v1_partfun1(X35,X33)
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_2])])])).

cnf(c_0_33,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(pm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_35,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_27,c_0_28]),c_0_29])])).

fof(c_0_36,plain,(
    ! [X36,X37,X38] :
      ( ~ v1_xboole_0(X36)
      | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))
      | v1_partfun1(X38,X36) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_partfun1])])])).

fof(c_0_37,plain,(
    ! [X6,X7] :
      ( ( k2_zfmisc_1(X6,X7) != k1_xboole_0
        | X6 = k1_xboole_0
        | X7 = k1_xboole_0 )
      & ( X6 != k1_xboole_0
        | k2_zfmisc_1(X6,X7) = k1_xboole_0 )
      & ( X7 != k1_xboole_0
        | k2_zfmisc_1(X6,X7) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_38,plain,
    ( k1_relset_1(X1,X2,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(pm,[status(thm)],[c_0_30,c_0_26])).

cnf(c_0_39,plain,
    ( k1_relset_1(X1,X2,k1_xboole_0) = X1
    | X2 = k1_xboole_0
    | ~ v1_funct_2(k1_xboole_0,X1,X2) ),
    inference(pm,[status(thm)],[c_0_31,c_0_26])).

cnf(c_0_40,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_41,negated_conjecture,
    ( v1_funct_1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_33,c_0_34]),c_0_35])])).

cnf(c_0_42,plain,
    ( v1_partfun1(X2,X1)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_43,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,plain,
    ( X1 = k1_relat_1(k1_xboole_0)
    | X2 = k1_xboole_0
    | ~ v1_funct_2(k1_xboole_0,X1,X2) ),
    inference(pm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_45,plain,
    ( v1_funct_2(k1_xboole_0,X1,X2)
    | ~ v1_partfun1(k1_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_40,c_0_26]),c_0_41])])).

cnf(c_0_46,plain,
    ( v1_partfun1(X1,X2)
    | X3 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_xboole_0(X2) ),
    inference(pm,[status(thm)],[c_0_42,c_0_43])).

fof(c_0_47,plain,(
    ! [X42] :
      ( ( v1_funct_1(X42)
        | ~ v1_relat_1(X42)
        | ~ v1_funct_1(X42) )
      & ( v1_funct_2(X42,k1_relat_1(X42),k2_relat_1(X42))
        | ~ v1_relat_1(X42)
        | ~ v1_funct_1(X42) )
      & ( m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X42),k2_relat_1(X42))))
        | ~ v1_relat_1(X42)
        | ~ v1_funct_1(X42) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).

fof(c_0_48,plain,(
    ! [X20] :
      ( ( k2_relat_1(X20) = k1_relat_1(k2_funct_1(X20))
        | ~ v2_funct_1(X20)
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20) )
      & ( k1_relat_1(X20) = k2_relat_1(k2_funct_1(X20))
        | ~ v2_funct_1(X20)
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).

fof(c_0_49,plain,(
    ! [X30,X31,X32] :
      ( ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
      | k2_relset_1(X30,X31,X32) = k2_relat_1(X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_50,plain,
    ( X1 = k1_relat_1(k1_xboole_0)
    | X2 = k1_xboole_0
    | ~ v1_partfun1(k1_xboole_0,X1) ),
    inference(pm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_51,plain,
    ( v1_partfun1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_xboole_0(X2) ),
    inference(er,[status(thm)],[c_0_46])).

cnf(c_0_52,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_53,plain,
    ( k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_54,negated_conjecture,
    ( k1_relset_1(esk2_0,esk3_0,esk4_0) = k1_relat_1(esk4_0) ),
    inference(pm,[status(thm)],[c_0_30,c_0_28])).

cnf(c_0_55,negated_conjecture,
    ( v1_funct_2(esk4_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_56,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_57,plain,
    ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_58,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_59,negated_conjecture,
    ( k2_relset_1(esk2_0,esk3_0,esk4_0) = esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_60,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_61,plain,
    ( X1 = k1_relat_1(k1_xboole_0)
    | X2 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_50,c_0_51]),c_0_26])])).

cnf(c_0_62,plain,
    ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(pm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_63,negated_conjecture,
    ( k1_relat_1(esk4_0) = esk2_0
    | k1_xboole_0 = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_31,c_0_28]),c_0_54]),c_0_55])])).

cnf(c_0_64,negated_conjecture,
    ( v2_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_65,plain,
    ( v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(pm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_66,negated_conjecture,
    ( k2_relat_1(esk4_0) = esk3_0 ),
    inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_58,c_0_28]),c_0_59])).

fof(c_0_67,plain,(
    ! [X21,X22,X23] :
      ( ~ v1_xboole_0(X21)
      | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))
      | v1_xboole_0(X23) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_relset_1])])])).

cnf(c_0_68,plain,
    ( X1 = k1_relat_1(k1_xboole_0)
    | v1_xboole_0(X2)
    | ~ v1_xboole_0(X1) ),
    inference(pm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_69,negated_conjecture,
    ( k1_xboole_0 = esk3_0
    | m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(esk4_0)),esk2_0)))
    | ~ v1_funct_1(k2_funct_1(esk4_0))
    | ~ v1_relat_1(k2_funct_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_62,c_0_63]),c_0_64]),c_0_34]),c_0_35])])).

cnf(c_0_70,negated_conjecture,
    ( v1_funct_2(k2_funct_1(esk4_0),esk3_0,k2_relat_1(k2_funct_1(esk4_0)))
    | ~ v1_funct_1(k2_funct_1(esk4_0))
    | ~ v1_relat_1(k2_funct_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_65,c_0_66]),c_0_64]),c_0_34]),c_0_35])])).

fof(c_0_71,plain,(
    ! [X4,X5] :
      ( ~ v1_xboole_0(X4)
      | X4 = X5
      | ~ v1_xboole_0(X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).

cnf(c_0_72,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_73,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | X3 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_74,plain,
    ( X1 = k1_relset_1(X2,X3,k1_xboole_0)
    | v1_xboole_0(X4)
    | ~ v1_xboole_0(X1) ),
    inference(pm,[status(thm)],[c_0_38,c_0_68])).

cnf(c_0_75,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(pm,[status(thm)],[c_0_27,c_0_26])).

cnf(c_0_76,negated_conjecture,
    ( ~ v1_funct_1(k2_funct_1(esk4_0))
    | ~ v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)
    | ~ m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_77,negated_conjecture,
    ( k1_xboole_0 = esk3_0
    | m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))
    | ~ v1_funct_1(k2_funct_1(esk4_0))
    | ~ v1_relat_1(k2_funct_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_69,c_0_57]),c_0_66]),c_0_64]),c_0_34]),c_0_35])])).

cnf(c_0_78,negated_conjecture,
    ( v1_funct_2(k2_funct_1(esk4_0),esk3_0,k1_relat_1(esk4_0))
    | ~ v1_funct_1(k2_funct_1(esk4_0))
    | ~ v1_relat_1(k2_funct_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_70,c_0_53]),c_0_64]),c_0_34]),c_0_35])])).

cnf(c_0_79,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_80,negated_conjecture,
    ( v1_xboole_0(esk4_0)
    | ~ v1_xboole_0(esk2_0) ),
    inference(pm,[status(thm)],[c_0_72,c_0_28])).

cnf(c_0_81,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | k1_xboole_0 != esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_73,c_0_28]),c_0_55])])).

cnf(c_0_82,plain,
    ( k1_relset_1(k1_relat_1(X1),k2_relat_1(X1),X1) = k1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(pm,[status(thm)],[c_0_30,c_0_52])).

cnf(c_0_83,plain,
    ( k1_relset_1(X1,X2,k1_xboole_0) = k1_xboole_0
    | v1_xboole_0(X3) ),
    inference(pm,[status(thm)],[c_0_74,c_0_60])).

cnf(c_0_84,negated_conjecture,
    ( v1_relat_1(k1_xboole_0) ),
    inference(pm,[status(thm)],[c_0_75,c_0_35])).

cnf(c_0_85,negated_conjecture,
    ( k1_xboole_0 = esk3_0
    | ~ v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)
    | ~ v1_funct_1(k2_funct_1(esk4_0))
    | ~ v1_relat_1(k2_funct_1(esk4_0)) ),
    inference(pm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_86,negated_conjecture,
    ( k1_xboole_0 = esk3_0
    | v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)
    | ~ v1_funct_1(k2_funct_1(esk4_0))
    | ~ v1_relat_1(k2_funct_1(esk4_0)) ),
    inference(pm,[status(thm)],[c_0_78,c_0_63])).

fof(c_0_87,plain,(
    ! [X18] :
      ( ( v1_relat_1(k2_funct_1(X18))
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) )
      & ( v1_funct_1(k2_funct_1(X18))
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

cnf(c_0_88,plain,
    ( k1_xboole_0 = X1
    | ~ v1_xboole_0(X1) ),
    inference(pm,[status(thm)],[c_0_79,c_0_60])).

cnf(c_0_89,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | v1_xboole_0(esk4_0)
    | k1_xboole_0 != esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_80,c_0_81]),c_0_60])])).

cnf(c_0_90,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_82,c_0_83]),c_0_41]),c_0_84])])).

cnf(c_0_91,negated_conjecture,
    ( k1_xboole_0 = esk3_0
    | ~ v1_funct_1(k2_funct_1(esk4_0))
    | ~ v1_relat_1(k2_funct_1(esk4_0)) ),
    inference(pm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_92,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

cnf(c_0_93,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | k1_xboole_0 != esk3_0 ),
    inference(pm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_94,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | k1_xboole_0 = X1 ),
    inference(pm,[status(thm)],[c_0_88,c_0_90])).

cnf(c_0_95,negated_conjecture,
    ( k1_xboole_0 = esk3_0
    | ~ v1_relat_1(k2_funct_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_91,c_0_92]),c_0_34]),c_0_35])])).

cnf(c_0_96,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

cnf(c_0_97,negated_conjecture,
    ( k1_relat_1(esk4_0) = k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != esk3_0 ),
    inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_54,c_0_93]),c_0_38])).

cnf(c_0_98,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(ef,[status(thm)],[c_0_94])).

cnf(c_0_99,negated_conjecture,
    ( k1_xboole_0 = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_95,c_0_96]),c_0_34]),c_0_35])])).

cnf(c_0_100,negated_conjecture,
    ( k1_relat_1(esk4_0) = k1_xboole_0
    | k1_xboole_0 != esk3_0 ),
    inference(rw,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_101,negated_conjecture,
    ( esk4_0 = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93,c_0_99]),c_0_99])])).

cnf(c_0_102,negated_conjecture,
    ( v2_funct_1(k1_xboole_0)
    | k1_xboole_0 != esk3_0 ),
    inference(pm,[status(thm)],[c_0_64,c_0_93])).

cnf(c_0_103,plain,
    ( v1_xboole_0(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(k1_relat_1(X1)) ),
    inference(pm,[status(thm)],[c_0_72,c_0_52])).

cnf(c_0_104,plain,
    ( X1 = esk3_0
    | X2 = esk3_0
    | X3 != esk3_0
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_99]),c_0_99]),c_0_99])).

cnf(c_0_105,plain,
    ( k2_zfmisc_1(X1,X2) = esk3_0
    | X2 != esk3_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_99]),c_0_99])).

cnf(c_0_106,plain,
    ( v1_funct_2(k2_funct_1(X1),k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(pm,[status(thm)],[c_0_56,c_0_53])).

cnf(c_0_107,negated_conjecture,
    ( k1_relat_1(esk3_0) = esk3_0 ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_100,c_0_99]),c_0_99])]),c_0_101])).

cnf(c_0_108,negated_conjecture,
    ( v2_funct_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_102,c_0_99]),c_0_99])])).

cnf(c_0_109,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(rw,[status(thm)],[c_0_41,c_0_99])).

cnf(c_0_110,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(rw,[status(thm)],[c_0_84,c_0_99])).

cnf(c_0_111,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)
    | ~ v1_funct_1(k2_funct_1(esk4_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))
    | ~ v1_xboole_0(k2_funct_1(esk4_0))
    | ~ v1_xboole_0(X1) ),
    inference(pm,[status(thm)],[c_0_76,c_0_79])).

cnf(c_0_112,negated_conjecture,
    ( v1_xboole_0(esk4_0)
    | k1_xboole_0 != esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_103,c_0_100]),c_0_60]),c_0_34]),c_0_35])])).

cnf(c_0_113,plain,
    ( X1 = esk3_0
    | X2 = esk3_0
    | X3 != esk3_0
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk3_0)) ),
    inference(pm,[status(thm)],[c_0_104,c_0_105])).

cnf(c_0_114,negated_conjecture,
    ( v1_funct_2(k2_funct_1(esk3_0),k1_relat_1(k2_funct_1(esk3_0)),esk3_0)
    | ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_106,c_0_107]),c_0_108]),c_0_109]),c_0_110])])).

cnf(c_0_115,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)
    | ~ v1_funct_1(k2_funct_1(esk4_0))
    | ~ v1_xboole_0(k2_funct_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_111,c_0_26]),c_0_60])])).

cnf(c_0_116,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ v1_partfun1(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X4))
    | ~ v1_xboole_0(k2_zfmisc_1(X2,X3))
    | ~ v1_xboole_0(X4) ),
    inference(pm,[status(thm)],[c_0_40,c_0_79])).

cnf(c_0_117,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk4_0),esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_52,c_0_66]),c_0_34]),c_0_35])])).

cnf(c_0_118,negated_conjecture,
    ( esk4_0 = X1
    | k1_xboole_0 != esk3_0
    | ~ v1_xboole_0(X1) ),
    inference(pm,[status(thm)],[c_0_79,c_0_112])).

cnf(c_0_119,negated_conjecture,
    ( k1_relat_1(k2_funct_1(esk3_0)) = esk3_0
    | k2_funct_1(esk3_0) = esk3_0
    | ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_relat_1(k2_funct_1(esk3_0))
    | ~ m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(esk3_0)) ),
    inference(pm,[status(thm)],[c_0_113,c_0_114])).

cnf(c_0_120,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(esk3_0))
    | k2_relat_1(X1) != esk3_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(pm,[status(thm)],[c_0_52,c_0_105])).

cnf(c_0_121,negated_conjecture,
    ( ~ v1_partfun1(k2_funct_1(esk4_0),esk3_0)
    | ~ v1_funct_1(k2_funct_1(esk4_0))
    | ~ m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(X1))
    | ~ v1_xboole_0(k2_zfmisc_1(esk3_0,esk2_0))
    | ~ v1_xboole_0(k2_funct_1(esk4_0))
    | ~ v1_xboole_0(X1) ),
    inference(pm,[status(thm)],[c_0_115,c_0_116])).

cnf(c_0_122,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk4_0),esk3_0)))
    | k1_xboole_0 != esk3_0
    | ~ v1_xboole_0(X1) ),
    inference(pm,[status(thm)],[c_0_117,c_0_118])).

cnf(c_0_123,negated_conjecture,
    ( k1_relat_1(k2_funct_1(esk3_0)) = esk3_0
    | k2_funct_1(esk3_0) = esk3_0
    | k2_relat_1(k2_funct_1(esk3_0)) != esk3_0
    | ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(pm,[status(thm)],[c_0_119,c_0_120])).

cnf(c_0_124,negated_conjecture,
    ( k1_xboole_0 != esk3_0
    | ~ v1_partfun1(k2_funct_1(esk4_0),esk3_0)
    | ~ v1_funct_1(k2_funct_1(esk4_0))
    | ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1(esk4_0),esk3_0))
    | ~ v1_xboole_0(k2_zfmisc_1(esk3_0,esk2_0))
    | ~ v1_xboole_0(k2_funct_1(esk4_0)) ),
    inference(pm,[status(thm)],[c_0_121,c_0_122])).

cnf(c_0_125,negated_conjecture,
    ( v1_funct_1(X1)
    | ~ v1_xboole_0(esk4_0)
    | ~ v1_xboole_0(X1) ),
    inference(pm,[status(thm)],[c_0_34,c_0_79])).

cnf(c_0_126,negated_conjecture,
    ( k1_relat_1(k2_funct_1(esk3_0)) = esk3_0
    | k2_funct_1(esk3_0) = esk3_0
    | ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_123,c_0_53]),c_0_107]),c_0_108]),c_0_109]),c_0_110])])).

cnf(c_0_127,plain,
    ( v1_xboole_0(esk3_0) ),
    inference(rw,[status(thm)],[c_0_60,c_0_99])).

cnf(c_0_128,negated_conjecture,
    ( k1_xboole_0 != esk3_0
    | ~ v1_partfun1(k2_funct_1(esk4_0),esk3_0)
    | ~ v1_funct_1(k2_funct_1(esk4_0))
    | ~ v1_xboole_0(k2_zfmisc_1(esk3_0,esk2_0))
    | ~ v1_xboole_0(k2_funct_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_124,c_0_43]),c_0_60])])).

cnf(c_0_129,negated_conjecture,
    ( v1_funct_1(X1)
    | k1_xboole_0 != esk3_0
    | ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_125,c_0_93]),c_0_60])])).

cnf(c_0_130,negated_conjecture,
    ( k2_funct_1(esk3_0) = esk3_0
    | v1_xboole_0(k2_funct_1(esk3_0))
    | ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_103,c_0_126]),c_0_127])])).

cnf(c_0_131,negated_conjecture,
    ( k1_xboole_0 != esk3_0
    | ~ v1_partfun1(k2_funct_1(esk4_0),esk3_0)
    | ~ v1_xboole_0(k2_zfmisc_1(esk3_0,esk2_0))
    | ~ v1_xboole_0(k2_funct_1(esk4_0)) ),
    inference(pm,[status(thm)],[c_0_128,c_0_129])).

cnf(c_0_132,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_133,negated_conjecture,
    ( k2_funct_1(esk3_0) = esk3_0
    | v1_xboole_0(k2_funct_1(esk3_0))
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_130,c_0_92]),c_0_109]),c_0_110])])).

cnf(c_0_134,plain,
    ( v1_partfun1(X1,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(k1_relat_1(X1)) ),
    inference(pm,[status(thm)],[c_0_42,c_0_52])).

cnf(c_0_135,negated_conjecture,
    ( ~ v1_partfun1(k2_funct_1(esk3_0),esk3_0)
    | ~ v1_xboole_0(k2_zfmisc_1(esk3_0,esk2_0))
    | ~ v1_xboole_0(k2_funct_1(esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_131,c_0_99])]),c_0_101]),c_0_101])).

cnf(c_0_136,plain,
    ( k2_zfmisc_1(X1,X2) = esk3_0
    | X1 != esk3_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_132,c_0_99]),c_0_99])).

cnf(c_0_137,negated_conjecture,
    ( esk3_0 = X1
    | ~ v1_xboole_0(X1) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_118,c_0_99])]),c_0_101])).

cnf(c_0_138,negated_conjecture,
    ( k2_funct_1(esk3_0) = esk3_0
    | v1_xboole_0(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_133,c_0_96]),c_0_109]),c_0_110])])).

cnf(c_0_139,plain,
    ( v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_134,c_0_98]),c_0_41]),c_0_84]),c_0_98]),c_0_60])])).

cnf(c_0_140,negated_conjecture,
    ( ~ v1_partfun1(k2_funct_1(esk3_0),esk3_0)
    | ~ v1_xboole_0(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_135,c_0_136]),c_0_127])])).

cnf(c_0_141,negated_conjecture,
    ( k2_funct_1(esk3_0) = esk3_0 ),
    inference(pm,[status(thm)],[c_0_137,c_0_138])).

cnf(c_0_142,plain,
    ( v1_partfun1(esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_139,c_0_99]),c_0_99])).

cnf(c_0_143,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_140,c_0_141]),c_0_142]),c_0_141]),c_0_127])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:16:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.69/0.89  # AutoSched0-Mode selected heuristic G_E___300_C01_S00
% 0.69/0.89  # and selection function NoSelection.
% 0.69/0.89  #
% 0.69/0.89  # Preprocessing time       : 0.048 s
% 0.69/0.89  
% 0.69/0.89  # Proof found!
% 0.69/0.89  # SZS status Theorem
% 0.69/0.89  # SZS output start CNFRefutation
% 0.69/0.89  fof(t31_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 0.69/0.89  fof(cc3_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_funct_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_funct_1)).
% 0.69/0.89  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.69/0.89  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.69/0.89  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.69/0.89  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.69/0.89  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.69/0.89  fof(cc1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_partfun1(X3,X1))=>(v1_funct_1(X3)&v1_funct_2(X3,X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_2)).
% 0.69/0.89  fof(cc1_partfun1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_partfun1(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_partfun1)).
% 0.69/0.89  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.69/0.89  fof(t3_funct_2, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 0.69/0.89  fof(t55_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))&k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 0.69/0.89  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.69/0.89  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.69/0.89  fof(cc3_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 0.69/0.89  fof(t8_boole, axiom, ![X1, X2]:~(((v1_xboole_0(X1)&X1!=X2)&v1_xboole_0(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 0.69/0.89  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 0.69/0.89  fof(c_0_17, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))))))), inference(assume_negation,[status(cth)],[t31_funct_2])).
% 0.69/0.89  fof(c_0_18, plain, ![X16, X17]:(~v1_relat_1(X16)|~v1_funct_1(X16)|(~m1_subset_1(X17,k1_zfmisc_1(X16))|v1_funct_1(X17))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_funct_1])])])).
% 0.69/0.89  fof(c_0_19, plain, ![X8]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X8)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.69/0.89  fof(c_0_20, plain, ![X12, X13]:(~v1_relat_1(X12)|(~m1_subset_1(X13,k1_zfmisc_1(X12))|v1_relat_1(X13))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.69/0.89  fof(c_0_21, negated_conjecture, (((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,esk2_0,esk3_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))))&((v2_funct_1(esk4_0)&k2_relset_1(esk2_0,esk3_0,esk4_0)=esk3_0)&(~v1_funct_1(k2_funct_1(esk4_0))|~v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)|~m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 0.69/0.89  fof(c_0_22, plain, ![X14, X15]:v1_relat_1(k2_zfmisc_1(X14,X15)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.69/0.89  fof(c_0_23, plain, ![X27, X28, X29]:(~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))|k1_relset_1(X27,X28,X29)=k1_relat_1(X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.69/0.89  fof(c_0_24, plain, ![X39, X40, X41]:((((~v1_funct_2(X41,X39,X40)|X39=k1_relset_1(X39,X40,X41)|X40=k1_xboole_0|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))))&(X39!=k1_relset_1(X39,X40,X41)|v1_funct_2(X41,X39,X40)|X40=k1_xboole_0|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))))&((~v1_funct_2(X41,X39,X40)|X39=k1_relset_1(X39,X40,X41)|X39!=k1_xboole_0|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))))&(X39!=k1_relset_1(X39,X40,X41)|v1_funct_2(X41,X39,X40)|X39!=k1_xboole_0|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))))))&((~v1_funct_2(X41,X39,X40)|X41=k1_xboole_0|X39=k1_xboole_0|X40!=k1_xboole_0|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))))&(X41!=k1_xboole_0|v1_funct_2(X41,X39,X40)|X39=k1_xboole_0|X40!=k1_xboole_0|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.69/0.89  cnf(c_0_25, plain, (v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.69/0.89  cnf(c_0_26, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.69/0.89  cnf(c_0_27, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.69/0.89  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.69/0.89  cnf(c_0_29, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.69/0.89  cnf(c_0_30, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.69/0.89  cnf(c_0_31, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.69/0.89  fof(c_0_32, plain, ![X33, X34, X35]:((v1_funct_1(X35)|(~v1_funct_1(X35)|~v1_partfun1(X35,X33))|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))))&(v1_funct_2(X35,X33,X34)|(~v1_funct_1(X35)|~v1_partfun1(X35,X33))|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_2])])])).
% 0.69/0.89  cnf(c_0_33, plain, (v1_funct_1(k1_xboole_0)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(pm,[status(thm)],[c_0_25, c_0_26])).
% 0.69/0.89  cnf(c_0_34, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.69/0.89  cnf(c_0_35, negated_conjecture, (v1_relat_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_27, c_0_28]), c_0_29])])).
% 0.69/0.89  fof(c_0_36, plain, ![X36, X37, X38]:(~v1_xboole_0(X36)|(~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))|v1_partfun1(X38,X36))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_partfun1])])])).
% 0.69/0.89  fof(c_0_37, plain, ![X6, X7]:((k2_zfmisc_1(X6,X7)!=k1_xboole_0|(X6=k1_xboole_0|X7=k1_xboole_0))&((X6!=k1_xboole_0|k2_zfmisc_1(X6,X7)=k1_xboole_0)&(X7!=k1_xboole_0|k2_zfmisc_1(X6,X7)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.69/0.89  cnf(c_0_38, plain, (k1_relset_1(X1,X2,k1_xboole_0)=k1_relat_1(k1_xboole_0)), inference(pm,[status(thm)],[c_0_30, c_0_26])).
% 0.69/0.89  cnf(c_0_39, plain, (k1_relset_1(X1,X2,k1_xboole_0)=X1|X2=k1_xboole_0|~v1_funct_2(k1_xboole_0,X1,X2)), inference(pm,[status(thm)],[c_0_31, c_0_26])).
% 0.69/0.89  cnf(c_0_40, plain, (v1_funct_2(X1,X2,X3)|~v1_funct_1(X1)|~v1_partfun1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.69/0.89  cnf(c_0_41, negated_conjecture, (v1_funct_1(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_33, c_0_34]), c_0_35])])).
% 0.69/0.89  cnf(c_0_42, plain, (v1_partfun1(X2,X1)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.69/0.89  cnf(c_0_43, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.69/0.89  cnf(c_0_44, plain, (X1=k1_relat_1(k1_xboole_0)|X2=k1_xboole_0|~v1_funct_2(k1_xboole_0,X1,X2)), inference(pm,[status(thm)],[c_0_38, c_0_39])).
% 0.69/0.89  cnf(c_0_45, plain, (v1_funct_2(k1_xboole_0,X1,X2)|~v1_partfun1(k1_xboole_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_40, c_0_26]), c_0_41])])).
% 0.69/0.89  cnf(c_0_46, plain, (v1_partfun1(X1,X2)|X3!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))|~v1_xboole_0(X2)), inference(pm,[status(thm)],[c_0_42, c_0_43])).
% 0.69/0.89  fof(c_0_47, plain, ![X42]:(((v1_funct_1(X42)|(~v1_relat_1(X42)|~v1_funct_1(X42)))&(v1_funct_2(X42,k1_relat_1(X42),k2_relat_1(X42))|(~v1_relat_1(X42)|~v1_funct_1(X42))))&(m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X42),k2_relat_1(X42))))|(~v1_relat_1(X42)|~v1_funct_1(X42)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).
% 0.69/0.89  fof(c_0_48, plain, ![X20]:((k2_relat_1(X20)=k1_relat_1(k2_funct_1(X20))|~v2_funct_1(X20)|(~v1_relat_1(X20)|~v1_funct_1(X20)))&(k1_relat_1(X20)=k2_relat_1(k2_funct_1(X20))|~v2_funct_1(X20)|(~v1_relat_1(X20)|~v1_funct_1(X20)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).
% 0.69/0.89  fof(c_0_49, plain, ![X30, X31, X32]:(~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))|k2_relset_1(X30,X31,X32)=k2_relat_1(X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.69/0.89  cnf(c_0_50, plain, (X1=k1_relat_1(k1_xboole_0)|X2=k1_xboole_0|~v1_partfun1(k1_xboole_0,X1)), inference(pm,[status(thm)],[c_0_44, c_0_45])).
% 0.69/0.89  cnf(c_0_51, plain, (v1_partfun1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))|~v1_xboole_0(X2)), inference(er,[status(thm)],[c_0_46])).
% 0.69/0.89  cnf(c_0_52, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.69/0.89  cnf(c_0_53, plain, (k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.69/0.89  cnf(c_0_54, negated_conjecture, (k1_relset_1(esk2_0,esk3_0,esk4_0)=k1_relat_1(esk4_0)), inference(pm,[status(thm)],[c_0_30, c_0_28])).
% 0.69/0.89  cnf(c_0_55, negated_conjecture, (v1_funct_2(esk4_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.69/0.89  cnf(c_0_56, plain, (v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.69/0.89  cnf(c_0_57, plain, (k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.69/0.89  cnf(c_0_58, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.69/0.89  cnf(c_0_59, negated_conjecture, (k2_relset_1(esk2_0,esk3_0,esk4_0)=esk3_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.69/0.89  cnf(c_0_60, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.69/0.89  cnf(c_0_61, plain, (X1=k1_relat_1(k1_xboole_0)|X2=k1_xboole_0|~v1_xboole_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_50, c_0_51]), c_0_26])])).
% 0.69/0.89  cnf(c_0_62, plain, (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(X1))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)), inference(pm,[status(thm)],[c_0_52, c_0_53])).
% 0.69/0.89  cnf(c_0_63, negated_conjecture, (k1_relat_1(esk4_0)=esk2_0|k1_xboole_0=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_31, c_0_28]), c_0_54]), c_0_55])])).
% 0.69/0.89  cnf(c_0_64, negated_conjecture, (v2_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.69/0.89  cnf(c_0_65, plain, (v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(X1))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)), inference(pm,[status(thm)],[c_0_56, c_0_57])).
% 0.69/0.89  cnf(c_0_66, negated_conjecture, (k2_relat_1(esk4_0)=esk3_0), inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_58, c_0_28]), c_0_59])).
% 0.69/0.89  fof(c_0_67, plain, ![X21, X22, X23]:(~v1_xboole_0(X21)|(~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))|v1_xboole_0(X23))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_relset_1])])])).
% 0.69/0.89  cnf(c_0_68, plain, (X1=k1_relat_1(k1_xboole_0)|v1_xboole_0(X2)|~v1_xboole_0(X1)), inference(pm,[status(thm)],[c_0_60, c_0_61])).
% 0.69/0.89  cnf(c_0_69, negated_conjecture, (k1_xboole_0=esk3_0|m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(esk4_0)),esk2_0)))|~v1_funct_1(k2_funct_1(esk4_0))|~v1_relat_1(k2_funct_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_62, c_0_63]), c_0_64]), c_0_34]), c_0_35])])).
% 0.69/0.89  cnf(c_0_70, negated_conjecture, (v1_funct_2(k2_funct_1(esk4_0),esk3_0,k2_relat_1(k2_funct_1(esk4_0)))|~v1_funct_1(k2_funct_1(esk4_0))|~v1_relat_1(k2_funct_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_65, c_0_66]), c_0_64]), c_0_34]), c_0_35])])).
% 0.69/0.89  fof(c_0_71, plain, ![X4, X5]:(~v1_xboole_0(X4)|X4=X5|~v1_xboole_0(X5)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).
% 0.69/0.89  cnf(c_0_72, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.69/0.89  cnf(c_0_73, plain, (X1=k1_xboole_0|X2=k1_xboole_0|~v1_funct_2(X1,X2,X3)|X3!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.69/0.89  cnf(c_0_74, plain, (X1=k1_relset_1(X2,X3,k1_xboole_0)|v1_xboole_0(X4)|~v1_xboole_0(X1)), inference(pm,[status(thm)],[c_0_38, c_0_68])).
% 0.69/0.89  cnf(c_0_75, plain, (v1_relat_1(k1_xboole_0)|~v1_relat_1(X1)), inference(pm,[status(thm)],[c_0_27, c_0_26])).
% 0.69/0.89  cnf(c_0_76, negated_conjecture, (~v1_funct_1(k2_funct_1(esk4_0))|~v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)|~m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.69/0.89  cnf(c_0_77, negated_conjecture, (k1_xboole_0=esk3_0|m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))|~v1_funct_1(k2_funct_1(esk4_0))|~v1_relat_1(k2_funct_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_69, c_0_57]), c_0_66]), c_0_64]), c_0_34]), c_0_35])])).
% 0.69/0.89  cnf(c_0_78, negated_conjecture, (v1_funct_2(k2_funct_1(esk4_0),esk3_0,k1_relat_1(esk4_0))|~v1_funct_1(k2_funct_1(esk4_0))|~v1_relat_1(k2_funct_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_70, c_0_53]), c_0_64]), c_0_34]), c_0_35])])).
% 0.69/0.89  cnf(c_0_79, plain, (X1=X2|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.69/0.89  cnf(c_0_80, negated_conjecture, (v1_xboole_0(esk4_0)|~v1_xboole_0(esk2_0)), inference(pm,[status(thm)],[c_0_72, c_0_28])).
% 0.69/0.89  cnf(c_0_81, negated_conjecture, (esk2_0=k1_xboole_0|esk4_0=k1_xboole_0|k1_xboole_0!=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_73, c_0_28]), c_0_55])])).
% 0.69/0.89  cnf(c_0_82, plain, (k1_relset_1(k1_relat_1(X1),k2_relat_1(X1),X1)=k1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(pm,[status(thm)],[c_0_30, c_0_52])).
% 0.69/0.89  cnf(c_0_83, plain, (k1_relset_1(X1,X2,k1_xboole_0)=k1_xboole_0|v1_xboole_0(X3)), inference(pm,[status(thm)],[c_0_74, c_0_60])).
% 0.69/0.89  cnf(c_0_84, negated_conjecture, (v1_relat_1(k1_xboole_0)), inference(pm,[status(thm)],[c_0_75, c_0_35])).
% 0.69/0.89  cnf(c_0_85, negated_conjecture, (k1_xboole_0=esk3_0|~v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)|~v1_funct_1(k2_funct_1(esk4_0))|~v1_relat_1(k2_funct_1(esk4_0))), inference(pm,[status(thm)],[c_0_76, c_0_77])).
% 0.69/0.89  cnf(c_0_86, negated_conjecture, (k1_xboole_0=esk3_0|v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)|~v1_funct_1(k2_funct_1(esk4_0))|~v1_relat_1(k2_funct_1(esk4_0))), inference(pm,[status(thm)],[c_0_78, c_0_63])).
% 0.69/0.89  fof(c_0_87, plain, ![X18]:((v1_relat_1(k2_funct_1(X18))|(~v1_relat_1(X18)|~v1_funct_1(X18)))&(v1_funct_1(k2_funct_1(X18))|(~v1_relat_1(X18)|~v1_funct_1(X18)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 0.69/0.89  cnf(c_0_88, plain, (k1_xboole_0=X1|~v1_xboole_0(X1)), inference(pm,[status(thm)],[c_0_79, c_0_60])).
% 0.69/0.89  cnf(c_0_89, negated_conjecture, (esk4_0=k1_xboole_0|v1_xboole_0(esk4_0)|k1_xboole_0!=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_80, c_0_81]), c_0_60])])).
% 0.69/0.89  cnf(c_0_90, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0|v1_xboole_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_82, c_0_83]), c_0_41]), c_0_84])])).
% 0.69/0.89  cnf(c_0_91, negated_conjecture, (k1_xboole_0=esk3_0|~v1_funct_1(k2_funct_1(esk4_0))|~v1_relat_1(k2_funct_1(esk4_0))), inference(pm,[status(thm)],[c_0_85, c_0_86])).
% 0.69/0.89  cnf(c_0_92, plain, (v1_funct_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_87])).
% 0.69/0.89  cnf(c_0_93, negated_conjecture, (esk4_0=k1_xboole_0|k1_xboole_0!=esk3_0), inference(pm,[status(thm)],[c_0_88, c_0_89])).
% 0.69/0.89  cnf(c_0_94, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0|k1_xboole_0=X1), inference(pm,[status(thm)],[c_0_88, c_0_90])).
% 0.69/0.89  cnf(c_0_95, negated_conjecture, (k1_xboole_0=esk3_0|~v1_relat_1(k2_funct_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_91, c_0_92]), c_0_34]), c_0_35])])).
% 0.69/0.89  cnf(c_0_96, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_87])).
% 0.69/0.89  cnf(c_0_97, negated_conjecture, (k1_relat_1(esk4_0)=k1_relat_1(k1_xboole_0)|k1_xboole_0!=esk3_0), inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_54, c_0_93]), c_0_38])).
% 0.69/0.89  cnf(c_0_98, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(ef,[status(thm)],[c_0_94])).
% 0.69/0.89  cnf(c_0_99, negated_conjecture, (k1_xboole_0=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_95, c_0_96]), c_0_34]), c_0_35])])).
% 0.69/0.89  cnf(c_0_100, negated_conjecture, (k1_relat_1(esk4_0)=k1_xboole_0|k1_xboole_0!=esk3_0), inference(rw,[status(thm)],[c_0_97, c_0_98])).
% 0.69/0.89  cnf(c_0_101, negated_conjecture, (esk4_0=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93, c_0_99]), c_0_99])])).
% 0.69/0.89  cnf(c_0_102, negated_conjecture, (v2_funct_1(k1_xboole_0)|k1_xboole_0!=esk3_0), inference(pm,[status(thm)],[c_0_64, c_0_93])).
% 0.69/0.89  cnf(c_0_103, plain, (v1_xboole_0(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)|~v1_xboole_0(k1_relat_1(X1))), inference(pm,[status(thm)],[c_0_72, c_0_52])).
% 0.69/0.89  cnf(c_0_104, plain, (X1=esk3_0|X2=esk3_0|X3!=esk3_0|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73, c_0_99]), c_0_99]), c_0_99])).
% 0.69/0.89  cnf(c_0_105, plain, (k2_zfmisc_1(X1,X2)=esk3_0|X2!=esk3_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_99]), c_0_99])).
% 0.69/0.89  cnf(c_0_106, plain, (v1_funct_2(k2_funct_1(X1),k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(X1))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)), inference(pm,[status(thm)],[c_0_56, c_0_53])).
% 0.69/0.89  cnf(c_0_107, negated_conjecture, (k1_relat_1(esk3_0)=esk3_0), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_100, c_0_99]), c_0_99])]), c_0_101])).
% 0.69/0.89  cnf(c_0_108, negated_conjecture, (v2_funct_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_102, c_0_99]), c_0_99])])).
% 0.69/0.89  cnf(c_0_109, negated_conjecture, (v1_funct_1(esk3_0)), inference(rw,[status(thm)],[c_0_41, c_0_99])).
% 0.69/0.89  cnf(c_0_110, negated_conjecture, (v1_relat_1(esk3_0)), inference(rw,[status(thm)],[c_0_84, c_0_99])).
% 0.69/0.89  cnf(c_0_111, negated_conjecture, (~v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)|~v1_funct_1(k2_funct_1(esk4_0))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))|~v1_xboole_0(k2_funct_1(esk4_0))|~v1_xboole_0(X1)), inference(pm,[status(thm)],[c_0_76, c_0_79])).
% 0.69/0.89  cnf(c_0_112, negated_conjecture, (v1_xboole_0(esk4_0)|k1_xboole_0!=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_103, c_0_100]), c_0_60]), c_0_34]), c_0_35])])).
% 0.69/0.89  cnf(c_0_113, plain, (X1=esk3_0|X2=esk3_0|X3!=esk3_0|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(esk3_0))), inference(pm,[status(thm)],[c_0_104, c_0_105])).
% 0.69/0.89  cnf(c_0_114, negated_conjecture, (v1_funct_2(k2_funct_1(esk3_0),k1_relat_1(k2_funct_1(esk3_0)),esk3_0)|~v1_funct_1(k2_funct_1(esk3_0))|~v1_relat_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_106, c_0_107]), c_0_108]), c_0_109]), c_0_110])])).
% 0.69/0.89  cnf(c_0_115, negated_conjecture, (~v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)|~v1_funct_1(k2_funct_1(esk4_0))|~v1_xboole_0(k2_funct_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_111, c_0_26]), c_0_60])])).
% 0.69/0.89  cnf(c_0_116, plain, (v1_funct_2(X1,X2,X3)|~v1_partfun1(X1,X2)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(X4))|~v1_xboole_0(k2_zfmisc_1(X2,X3))|~v1_xboole_0(X4)), inference(pm,[status(thm)],[c_0_40, c_0_79])).
% 0.69/0.89  cnf(c_0_117, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk4_0),esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_52, c_0_66]), c_0_34]), c_0_35])])).
% 0.69/0.89  cnf(c_0_118, negated_conjecture, (esk4_0=X1|k1_xboole_0!=esk3_0|~v1_xboole_0(X1)), inference(pm,[status(thm)],[c_0_79, c_0_112])).
% 0.69/0.89  cnf(c_0_119, negated_conjecture, (k1_relat_1(k2_funct_1(esk3_0))=esk3_0|k2_funct_1(esk3_0)=esk3_0|~v1_funct_1(k2_funct_1(esk3_0))|~v1_relat_1(k2_funct_1(esk3_0))|~m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(esk3_0))), inference(pm,[status(thm)],[c_0_113, c_0_114])).
% 0.69/0.89  cnf(c_0_120, plain, (m1_subset_1(X1,k1_zfmisc_1(esk3_0))|k2_relat_1(X1)!=esk3_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(pm,[status(thm)],[c_0_52, c_0_105])).
% 0.69/0.89  cnf(c_0_121, negated_conjecture, (~v1_partfun1(k2_funct_1(esk4_0),esk3_0)|~v1_funct_1(k2_funct_1(esk4_0))|~m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(X1))|~v1_xboole_0(k2_zfmisc_1(esk3_0,esk2_0))|~v1_xboole_0(k2_funct_1(esk4_0))|~v1_xboole_0(X1)), inference(pm,[status(thm)],[c_0_115, c_0_116])).
% 0.69/0.89  cnf(c_0_122, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk4_0),esk3_0)))|k1_xboole_0!=esk3_0|~v1_xboole_0(X1)), inference(pm,[status(thm)],[c_0_117, c_0_118])).
% 0.69/0.89  cnf(c_0_123, negated_conjecture, (k1_relat_1(k2_funct_1(esk3_0))=esk3_0|k2_funct_1(esk3_0)=esk3_0|k2_relat_1(k2_funct_1(esk3_0))!=esk3_0|~v1_funct_1(k2_funct_1(esk3_0))|~v1_relat_1(k2_funct_1(esk3_0))), inference(pm,[status(thm)],[c_0_119, c_0_120])).
% 0.69/0.89  cnf(c_0_124, negated_conjecture, (k1_xboole_0!=esk3_0|~v1_partfun1(k2_funct_1(esk4_0),esk3_0)|~v1_funct_1(k2_funct_1(esk4_0))|~v1_xboole_0(k2_zfmisc_1(k1_relat_1(esk4_0),esk3_0))|~v1_xboole_0(k2_zfmisc_1(esk3_0,esk2_0))|~v1_xboole_0(k2_funct_1(esk4_0))), inference(pm,[status(thm)],[c_0_121, c_0_122])).
% 0.69/0.89  cnf(c_0_125, negated_conjecture, (v1_funct_1(X1)|~v1_xboole_0(esk4_0)|~v1_xboole_0(X1)), inference(pm,[status(thm)],[c_0_34, c_0_79])).
% 0.69/0.89  cnf(c_0_126, negated_conjecture, (k1_relat_1(k2_funct_1(esk3_0))=esk3_0|k2_funct_1(esk3_0)=esk3_0|~v1_funct_1(k2_funct_1(esk3_0))|~v1_relat_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_123, c_0_53]), c_0_107]), c_0_108]), c_0_109]), c_0_110])])).
% 0.69/0.89  cnf(c_0_127, plain, (v1_xboole_0(esk3_0)), inference(rw,[status(thm)],[c_0_60, c_0_99])).
% 0.69/0.89  cnf(c_0_128, negated_conjecture, (k1_xboole_0!=esk3_0|~v1_partfun1(k2_funct_1(esk4_0),esk3_0)|~v1_funct_1(k2_funct_1(esk4_0))|~v1_xboole_0(k2_zfmisc_1(esk3_0,esk2_0))|~v1_xboole_0(k2_funct_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_124, c_0_43]), c_0_60])])).
% 0.69/0.89  cnf(c_0_129, negated_conjecture, (v1_funct_1(X1)|k1_xboole_0!=esk3_0|~v1_xboole_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_125, c_0_93]), c_0_60])])).
% 0.69/0.89  cnf(c_0_130, negated_conjecture, (k2_funct_1(esk3_0)=esk3_0|v1_xboole_0(k2_funct_1(esk3_0))|~v1_funct_1(k2_funct_1(esk3_0))|~v1_relat_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_103, c_0_126]), c_0_127])])).
% 0.69/0.89  cnf(c_0_131, negated_conjecture, (k1_xboole_0!=esk3_0|~v1_partfun1(k2_funct_1(esk4_0),esk3_0)|~v1_xboole_0(k2_zfmisc_1(esk3_0,esk2_0))|~v1_xboole_0(k2_funct_1(esk4_0))), inference(pm,[status(thm)],[c_0_128, c_0_129])).
% 0.69/0.89  cnf(c_0_132, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.69/0.89  cnf(c_0_133, negated_conjecture, (k2_funct_1(esk3_0)=esk3_0|v1_xboole_0(k2_funct_1(esk3_0))|~v1_relat_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_130, c_0_92]), c_0_109]), c_0_110])])).
% 0.69/0.89  cnf(c_0_134, plain, (v1_partfun1(X1,k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~v1_xboole_0(k1_relat_1(X1))), inference(pm,[status(thm)],[c_0_42, c_0_52])).
% 0.69/0.89  cnf(c_0_135, negated_conjecture, (~v1_partfun1(k2_funct_1(esk3_0),esk3_0)|~v1_xboole_0(k2_zfmisc_1(esk3_0,esk2_0))|~v1_xboole_0(k2_funct_1(esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_131, c_0_99])]), c_0_101]), c_0_101])).
% 0.69/0.89  cnf(c_0_136, plain, (k2_zfmisc_1(X1,X2)=esk3_0|X1!=esk3_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_132, c_0_99]), c_0_99])).
% 0.69/0.89  cnf(c_0_137, negated_conjecture, (esk3_0=X1|~v1_xboole_0(X1)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_118, c_0_99])]), c_0_101])).
% 0.69/0.89  cnf(c_0_138, negated_conjecture, (k2_funct_1(esk3_0)=esk3_0|v1_xboole_0(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_133, c_0_96]), c_0_109]), c_0_110])])).
% 0.69/0.89  cnf(c_0_139, plain, (v1_partfun1(k1_xboole_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_134, c_0_98]), c_0_41]), c_0_84]), c_0_98]), c_0_60])])).
% 0.69/0.89  cnf(c_0_140, negated_conjecture, (~v1_partfun1(k2_funct_1(esk3_0),esk3_0)|~v1_xboole_0(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_135, c_0_136]), c_0_127])])).
% 0.69/0.89  cnf(c_0_141, negated_conjecture, (k2_funct_1(esk3_0)=esk3_0), inference(pm,[status(thm)],[c_0_137, c_0_138])).
% 0.69/0.89  cnf(c_0_142, plain, (v1_partfun1(esk3_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_139, c_0_99]), c_0_99])).
% 0.69/0.89  cnf(c_0_143, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_140, c_0_141]), c_0_142]), c_0_141]), c_0_127])]), ['proof']).
% 0.69/0.89  # SZS output end CNFRefutation
% 0.69/0.89  # Proof object total steps             : 144
% 0.69/0.89  # Proof object clause steps            : 110
% 0.69/0.89  # Proof object formula steps           : 34
% 0.69/0.89  # Proof object conjectures             : 60
% 0.69/0.89  # Proof object clause conjectures      : 57
% 0.69/0.89  # Proof object formula conjectures     : 3
% 0.69/0.89  # Proof object initial clauses used    : 27
% 0.69/0.89  # Proof object initial formulas used   : 17
% 0.69/0.89  # Proof object generating inferences   : 69
% 0.69/0.89  # Proof object simplifying inferences  : 115
% 0.69/0.89  # Training examples: 0 positive, 0 negative
% 0.69/0.89  # Parsed axioms                        : 20
% 0.69/0.89  # Removed by relevancy pruning/SinE    : 0
% 0.69/0.89  # Initial clauses                      : 38
% 0.69/0.89  # Removed in clause preprocessing      : 2
% 0.69/0.89  # Initial clauses in saturation        : 36
% 0.69/0.89  # Processed clauses                    : 5615
% 0.69/0.89  # ...of these trivial                  : 155
% 0.69/0.89  # ...subsumed                          : 4315
% 0.69/0.89  # ...remaining for further processing  : 1145
% 0.69/0.89  # Other redundant clauses eliminated   : 0
% 0.69/0.89  # Clauses deleted for lack of memory   : 0
% 0.69/0.89  # Backward-subsumed                    : 288
% 0.69/0.89  # Backward-rewritten                   : 701
% 0.69/0.89  # Generated clauses                    : 39716
% 0.69/0.89  # ...of the previous two non-trivial   : 37890
% 0.69/0.89  # Contextual simplify-reflections      : 0
% 0.69/0.89  # Paramodulations                      : 39699
% 0.69/0.89  # Factorizations                       : 14
% 0.69/0.89  # Equation resolutions                 : 3
% 0.69/0.89  # Propositional unsat checks           : 0
% 0.69/0.89  #    Propositional check models        : 0
% 0.69/0.89  #    Propositional check unsatisfiable : 0
% 0.69/0.89  #    Propositional clauses             : 0
% 0.69/0.89  #    Propositional clauses after purity: 0
% 0.69/0.89  #    Propositional unsat core size     : 0
% 0.69/0.89  #    Propositional preprocessing time  : 0.000
% 0.69/0.89  #    Propositional encoding time       : 0.000
% 0.69/0.89  #    Propositional solver time         : 0.000
% 0.69/0.89  #    Success case prop preproc time    : 0.000
% 0.69/0.89  #    Success case prop encoding time   : 0.000
% 0.69/0.89  #    Success case prop solver time     : 0.000
% 0.69/0.89  # Current number of processed clauses  : 156
% 0.69/0.89  #    Positive orientable unit clauses  : 18
% 0.69/0.89  #    Positive unorientable unit clauses: 0
% 0.69/0.89  #    Negative unit clauses             : 3
% 0.69/0.89  #    Non-unit-clauses                  : 135
% 0.69/0.89  # Current number of unprocessed clauses: 29054
% 0.69/0.89  # ...number of literals in the above   : 169157
% 0.69/0.89  # Current number of archived formulas  : 0
% 0.69/0.89  # Current number of archived clauses   : 989
% 0.69/0.89  # Clause-clause subsumption calls (NU) : 83167
% 0.69/0.89  # Rec. Clause-clause subsumption calls : 44439
% 0.69/0.89  # Non-unit clause-clause subsumptions  : 4158
% 0.69/0.89  # Unit Clause-clause subsumption calls : 758
% 0.69/0.89  # Rewrite failures with RHS unbound    : 65
% 0.69/0.89  # BW rewrite match attempts            : 60
% 0.69/0.89  # BW rewrite match successes           : 22
% 0.69/0.89  # Condensation attempts                : 0
% 0.69/0.89  # Condensation successes               : 0
% 0.69/0.89  # Termbank termtop insertions          : 251634
% 0.69/0.90  
% 0.69/0.90  # -------------------------------------------------
% 0.69/0.90  # User time                : 0.532 s
% 0.69/0.90  # System time              : 0.023 s
% 0.69/0.90  # Total time               : 0.555 s
% 0.69/0.90  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------

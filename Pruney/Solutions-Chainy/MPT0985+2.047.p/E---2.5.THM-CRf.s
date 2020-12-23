%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:02:39 EST 2020

% Result     : Theorem 0.63s
% Output     : CNFRefutation 0.63s
% Verified   : 
% Statistics : Number of formulae       :  133 (6302 expanded)
%              Number of clauses        :   97 (2393 expanded)
%              Number of leaves         :   18 (1553 expanded)
%              Depth                    :   20
%              Number of atoms          :  407 (31661 expanded)
%              Number of equality atoms :   94 (5610 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

fof(t3_funct_2,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_funct_1(X1)
        & v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(t55_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
          & k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(cc1_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(t8_boole,axiom,(
    ! [X1,X2] :
      ~ ( v1_xboole_0(X1)
        & X1 != X2
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(cc4_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

fof(dt_k6_partfun1,axiom,(
    ! [X1] :
      ( v1_partfun1(k6_partfun1(X1),X1)
      & m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(cc3_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_funct_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(rc2_funct_1,axiom,(
    ? [X1] :
      ( v1_relat_1(X1)
      & v1_funct_1(X1)
      & v2_funct_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_funct_1)).

fof(cc1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( v1_funct_1(X3)
          & v1_partfun1(X3,X1) )
       => ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

fof(c_0_18,negated_conjecture,(
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

fof(c_0_19,plain,(
    ! [X38] :
      ( ( v1_funct_1(X38)
        | ~ v1_relat_1(X38)
        | ~ v1_funct_1(X38) )
      & ( v1_funct_2(X38,k1_relat_1(X38),k2_relat_1(X38))
        | ~ v1_relat_1(X38)
        | ~ v1_funct_1(X38) )
      & ( m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X38),k2_relat_1(X38))))
        | ~ v1_relat_1(X38)
        | ~ v1_funct_1(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).

fof(c_0_20,plain,(
    ! [X18] :
      ( ( k2_relat_1(X18) = k1_relat_1(k2_funct_1(X18))
        | ~ v2_funct_1(X18)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) )
      & ( k1_relat_1(X18) = k2_relat_1(k2_funct_1(X18))
        | ~ v2_funct_1(X18)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).

fof(c_0_21,plain,(
    ! [X28,X29,X30] :
      ( ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))
      | k2_relset_1(X28,X29,X30) = k2_relat_1(X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_22,negated_conjecture,
    ( v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,esk2_0,esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))
    & v2_funct_1(esk4_0)
    & k2_relset_1(esk2_0,esk3_0,esk4_0) = esk3_0
    & ( ~ v1_funct_1(k2_funct_1(esk4_0))
      | ~ v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)
      | ~ m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

fof(c_0_23,plain,(
    ! [X19,X20,X21] :
      ( ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
      | v1_relat_1(X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_24,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( k2_relset_1(esk2_0,esk3_0,esk4_0) = esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_30,plain,(
    ! [X25,X26,X27] :
      ( ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
      | k1_relset_1(X25,X26,X27) = k1_relat_1(X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_31,plain,
    ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(pm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( k2_relat_1(esk4_0) = esk3_0 ),
    inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_26,c_0_27]),c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( v2_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_35,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(pm,[status(thm)],[c_0_29,c_0_27])).

fof(c_0_36,plain,(
    ! [X34,X35,X36] :
      ( ( ~ v1_funct_2(X36,X34,X35)
        | X34 = k1_relset_1(X34,X35,X36)
        | X35 = k1_xboole_0
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) )
      & ( X34 != k1_relset_1(X34,X35,X36)
        | v1_funct_2(X36,X34,X35)
        | X35 = k1_xboole_0
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) )
      & ( ~ v1_funct_2(X36,X34,X35)
        | X34 = k1_relset_1(X34,X35,X36)
        | X34 != k1_xboole_0
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) )
      & ( X34 != k1_relset_1(X34,X35,X36)
        | v1_funct_2(X36,X34,X35)
        | X34 != k1_xboole_0
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) )
      & ( ~ v1_funct_2(X36,X34,X35)
        | X36 = k1_xboole_0
        | X34 = k1_xboole_0
        | X35 != k1_xboole_0
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) )
      & ( X36 != k1_xboole_0
        | v1_funct_2(X36,X34,X35)
        | X34 = k1_xboole_0
        | X35 != k1_xboole_0
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_37,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_39,plain,(
    ! [X9,X10] :
      ( ~ v1_xboole_0(X9)
      | ~ m1_subset_1(X10,k1_zfmisc_1(X9))
      | v1_xboole_0(X10) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,k2_relat_1(k2_funct_1(esk4_0)))))
    | ~ v1_funct_1(k2_funct_1(esk4_0))
    | ~ v1_relat_1(k2_funct_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34]),c_0_35])])).

cnf(c_0_41,plain,
    ( k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_42,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( k1_relset_1(esk2_0,esk3_0,esk4_0) = k1_relat_1(esk4_0) ),
    inference(pm,[status(thm)],[c_0_37,c_0_27])).

cnf(c_0_44,negated_conjecture,
    ( v1_funct_2(esk4_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_45,plain,
    ( v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(pm,[status(thm)],[c_0_38,c_0_25])).

fof(c_0_46,plain,(
    ! [X4,X5] :
      ( ~ v1_xboole_0(X4)
      | X4 = X5
      | ~ v1_xboole_0(X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).

cnf(c_0_47,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_48,plain,(
    ! [X6,X7] :
      ( ( k2_zfmisc_1(X6,X7) != k1_xboole_0
        | X6 = k1_xboole_0
        | X7 = k1_xboole_0 )
      & ( X6 != k1_xboole_0
        | k2_zfmisc_1(X6,X7) = k1_xboole_0 )
      & ( X7 != k1_xboole_0
        | k2_zfmisc_1(X6,X7) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,k1_relat_1(esk4_0))))
    | ~ v1_funct_1(k2_funct_1(esk4_0))
    | ~ v1_relat_1(k2_funct_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_40,c_0_41]),c_0_33]),c_0_34]),c_0_35])])).

cnf(c_0_50,negated_conjecture,
    ( k1_relat_1(esk4_0) = esk2_0
    | k1_xboole_0 = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_42,c_0_27]),c_0_43]),c_0_44])])).

cnf(c_0_51,negated_conjecture,
    ( v1_funct_2(k2_funct_1(esk4_0),esk3_0,k2_relat_1(k2_funct_1(esk4_0)))
    | ~ v1_funct_1(k2_funct_1(esk4_0))
    | ~ v1_relat_1(k2_funct_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_45,c_0_32]),c_0_33]),c_0_34]),c_0_35])])).

cnf(c_0_52,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_53,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_54,negated_conjecture,
    ( v1_xboole_0(esk4_0)
    | ~ v1_xboole_0(k2_zfmisc_1(esk2_0,esk3_0)) ),
    inference(pm,[status(thm)],[c_0_47,c_0_27])).

cnf(c_0_55,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_56,negated_conjecture,
    ( ~ v1_funct_1(k2_funct_1(esk4_0))
    | ~ v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)
    | ~ m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_57,negated_conjecture,
    ( k1_xboole_0 = esk3_0
    | m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))
    | ~ v1_funct_1(k2_funct_1(esk4_0))
    | ~ v1_relat_1(k2_funct_1(esk4_0)) ),
    inference(pm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_58,negated_conjecture,
    ( v1_funct_2(k2_funct_1(esk4_0),esk3_0,k1_relat_1(esk4_0))
    | ~ v1_funct_1(k2_funct_1(esk4_0))
    | ~ v1_relat_1(k2_funct_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_51,c_0_41]),c_0_33]),c_0_34]),c_0_35])])).

cnf(c_0_59,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_60,plain,
    ( k1_xboole_0 = X1
    | ~ v1_xboole_0(X1) ),
    inference(pm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_61,negated_conjecture,
    ( v1_xboole_0(esk4_0)
    | k1_xboole_0 != esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_54,c_0_55]),c_0_53])])).

cnf(c_0_62,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(k2_zfmisc_1(esk2_0,esk3_0))
    | ~ v1_xboole_0(X1) ),
    inference(pm,[status(thm)],[c_0_27,c_0_52])).

cnf(c_0_63,negated_conjecture,
    ( k1_xboole_0 = esk3_0
    | ~ v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)
    | ~ v1_funct_1(k2_funct_1(esk4_0))
    | ~ v1_relat_1(k2_funct_1(esk4_0)) ),
    inference(pm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_64,negated_conjecture,
    ( k1_xboole_0 = esk3_0
    | v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)
    | ~ v1_funct_1(k2_funct_1(esk4_0))
    | ~ v1_relat_1(k2_funct_1(esk4_0)) ),
    inference(pm,[status(thm)],[c_0_58,c_0_50])).

fof(c_0_65,plain,(
    ! [X16] :
      ( ( v1_relat_1(k2_funct_1(X16))
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( v1_funct_1(k2_funct_1(X16))
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

cnf(c_0_66,negated_conjecture,
    ( k1_xboole_0 != esk3_0
    | ~ v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)
    | ~ v1_funct_1(k2_funct_1(esk4_0))
    | ~ m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(pm,[status(thm)],[c_0_56,c_0_59])).

cnf(c_0_67,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | k1_xboole_0 != esk3_0 ),
    inference(pm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(X1))
    | k1_xboole_0 != esk3_0
    | ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_62,c_0_55]),c_0_53])])).

cnf(c_0_69,negated_conjecture,
    ( esk4_0 = X1
    | k1_xboole_0 != esk3_0
    | ~ v1_xboole_0(X1) ),
    inference(pm,[status(thm)],[c_0_52,c_0_61])).

cnf(c_0_70,negated_conjecture,
    ( k1_xboole_0 = esk3_0
    | ~ v1_funct_1(k2_funct_1(esk4_0))
    | ~ v1_relat_1(k2_funct_1(esk4_0)) ),
    inference(pm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_71,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

fof(c_0_72,plain,(
    ! [X22,X23,X24] :
      ( ~ v1_xboole_0(X22)
      | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X23,X22)))
      | v1_xboole_0(X24) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).

fof(c_0_73,plain,(
    ! [X37] :
      ( v1_partfun1(k6_partfun1(X37),X37)
      & m1_subset_1(k6_partfun1(X37),k1_zfmisc_1(k2_zfmisc_1(X37,X37))) ) ),
    inference(variable_rename,[status(thm)],[dt_k6_partfun1])).

fof(c_0_74,plain,(
    ! [X14,X15] :
      ( ~ v1_relat_1(X14)
      | ~ v1_funct_1(X14)
      | ~ m1_subset_1(X15,k1_zfmisc_1(X14))
      | v1_funct_1(X15) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_funct_1])])])).

fof(c_0_75,plain,(
    ! [X8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X8)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_76,negated_conjecture,
    ( k1_xboole_0 != esk3_0
    | ~ v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)
    | ~ v1_funct_1(k2_funct_1(esk4_0))
    | ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(pm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_77,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | k1_xboole_0 != esk3_0
    | ~ v1_xboole_0(X2)
    | ~ v1_xboole_0(X1) ),
    inference(pm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_78,negated_conjecture,
    ( k1_xboole_0 = esk3_0
    | ~ v1_relat_1(k2_funct_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_70,c_0_71]),c_0_34]),c_0_35])])).

cnf(c_0_79,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_80,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_81,plain,
    ( m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_82,plain,
    ( v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_83,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

fof(c_0_84,plain,
    ( v1_relat_1(esk1_0)
    & v1_funct_1(esk1_0)
    & v2_funct_1(esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc2_funct_1])])).

cnf(c_0_85,negated_conjecture,
    ( k1_xboole_0 != esk3_0
    | ~ v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)
    | ~ v1_funct_1(k2_funct_1(esk4_0))
    | ~ v1_xboole_0(k2_funct_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_76,c_0_77]),c_0_53])])).

cnf(c_0_86,negated_conjecture,
    ( k1_xboole_0 = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_78,c_0_79]),c_0_34]),c_0_35])])).

cnf(c_0_87,plain,
    ( v1_xboole_0(k6_partfun1(X1))
    | ~ v1_xboole_0(X1) ),
    inference(pm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_88,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(pm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_89,plain,
    ( v1_funct_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_90,plain,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_91,plain,
    ( m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k1_xboole_0))
    | X1 != k1_xboole_0 ),
    inference(pm,[status(thm)],[c_0_81,c_0_55])).

cnf(c_0_92,negated_conjecture,
    ( k1_xboole_0 != esk3_0
    | ~ v1_funct_2(k2_funct_1(k1_xboole_0),esk3_0,esk2_0)
    | ~ v1_funct_1(k2_funct_1(esk4_0))
    | ~ v1_xboole_0(k2_funct_1(k1_xboole_0)) ),
    inference(pm,[status(thm)],[c_0_85,c_0_67])).

cnf(c_0_93,negated_conjecture,
    ( esk4_0 = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_86]),c_0_86])])).

cnf(c_0_94,plain,
    ( k6_partfun1(X1) = X2
    | ~ v1_xboole_0(X2)
    | ~ v1_xboole_0(X1) ),
    inference(pm,[status(thm)],[c_0_52,c_0_87])).

cnf(c_0_95,plain,
    ( v1_funct_1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_88,c_0_89]),c_0_90])])).

cnf(c_0_96,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(pm,[status(thm)],[c_0_29,c_0_83])).

cnf(c_0_97,plain,
    ( v1_xboole_0(k6_partfun1(X1))
    | X1 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_47,c_0_91]),c_0_53])])).

cnf(c_0_98,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(esk3_0),esk3_0,esk2_0)
    | ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_xboole_0(k2_funct_1(esk3_0)) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_92,c_0_86]),c_0_86]),c_0_86])]),c_0_93])).

cnf(c_0_99,negated_conjecture,
    ( k6_partfun1(X1) = esk4_0
    | k1_xboole_0 != esk3_0
    | ~ v1_xboole_0(X1) ),
    inference(pm,[status(thm)],[c_0_94,c_0_61])).

cnf(c_0_100,plain,
    ( v1_funct_1(k6_partfun1(X1))
    | X1 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_82,c_0_91]),c_0_95]),c_0_96])])).

cnf(c_0_101,plain,
    ( k6_partfun1(X1) = X2
    | X1 != k1_xboole_0
    | ~ v1_xboole_0(X2) ),
    inference(pm,[status(thm)],[c_0_52,c_0_97])).

cnf(c_0_102,negated_conjecture,
    ( ~ v1_funct_2(k6_partfun1(X1),esk3_0,esk2_0)
    | ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_xboole_0(k2_funct_1(esk3_0))
    | ~ v1_xboole_0(X1) ),
    inference(pm,[status(thm)],[c_0_98,c_0_94])).

cnf(c_0_103,negated_conjecture,
    ( k6_partfun1(X1) = esk3_0
    | ~ v1_xboole_0(X1) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_99,c_0_86])]),c_0_93])).

cnf(c_0_104,plain,
    ( v1_funct_1(X1)
    | X2 != k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(pm,[status(thm)],[c_0_100,c_0_101])).

cnf(c_0_105,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,k1_relat_1(esk3_0))))
    | ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_93]),c_0_93]),c_0_93]),c_0_93])).

cnf(c_0_106,plain,
    ( k2_zfmisc_1(X1,X2) = esk3_0
    | X1 != esk3_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_86]),c_0_86])).

cnf(c_0_107,plain,
    ( v1_partfun1(k6_partfun1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_108,negated_conjecture,
    ( ~ v1_funct_2(esk3_0,esk3_0,esk2_0)
    | ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_xboole_0(k2_funct_1(esk3_0))
    | ~ v1_xboole_0(X1) ),
    inference(pm,[status(thm)],[c_0_102,c_0_103])).

cnf(c_0_109,plain,
    ( v1_funct_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(er,[status(thm)],[c_0_104])).

cnf(c_0_110,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(esk3_0))
    | ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(pm,[status(thm)],[c_0_105,c_0_106])).

cnf(c_0_111,plain,
    ( v1_xboole_0(esk3_0) ),
    inference(rw,[status(thm)],[c_0_53,c_0_86])).

cnf(c_0_112,plain,
    ( v1_partfun1(X1,X2)
    | ~ v1_xboole_0(k6_partfun1(X2))
    | ~ v1_xboole_0(X1) ),
    inference(pm,[status(thm)],[c_0_107,c_0_52])).

cnf(c_0_113,plain,
    ( k6_partfun1(X1) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(pm,[status(thm)],[c_0_60,c_0_87])).

cnf(c_0_114,negated_conjecture,
    ( ~ v1_funct_2(esk3_0,esk3_0,esk2_0)
    | ~ v1_xboole_0(k2_funct_1(esk3_0))
    | ~ v1_xboole_0(X1) ),
    inference(pm,[status(thm)],[c_0_108,c_0_109])).

cnf(c_0_115,plain,
    ( v1_xboole_0(k6_partfun1(X1))
    | X1 != esk3_0 ),
    inference(rw,[status(thm)],[c_0_97,c_0_86])).

cnf(c_0_116,negated_conjecture,
    ( v1_xboole_0(k2_funct_1(esk3_0))
    | ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_47,c_0_110]),c_0_111])])).

cnf(c_0_117,plain,
    ( v1_funct_1(esk3_0) ),
    inference(rw,[status(thm)],[c_0_95,c_0_86])).

cnf(c_0_118,plain,
    ( v1_relat_1(esk3_0) ),
    inference(rw,[status(thm)],[c_0_96,c_0_86])).

fof(c_0_119,plain,(
    ! [X31,X32,X33] :
      ( ( v1_funct_1(X33)
        | ~ v1_funct_1(X33)
        | ~ v1_partfun1(X33,X31)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) )
      & ( v1_funct_2(X33,X31,X32)
        | ~ v1_funct_1(X33)
        | ~ v1_partfun1(X33,X31)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_2])])])).

cnf(c_0_120,plain,
    ( v1_partfun1(X1,X2)
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_112,c_0_113]),c_0_53])])).

cnf(c_0_121,negated_conjecture,
    ( X1 != esk3_0
    | ~ v1_funct_2(esk3_0,esk3_0,esk2_0)
    | ~ v1_xboole_0(k2_funct_1(esk3_0)) ),
    inference(pm,[status(thm)],[c_0_114,c_0_115])).

cnf(c_0_122,negated_conjecture,
    ( v1_xboole_0(k2_funct_1(esk3_0))
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_116,c_0_71]),c_0_117]),c_0_118])])).

cnf(c_0_123,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_119])).

cnf(c_0_124,negated_conjecture,
    ( v1_partfun1(esk4_0,X1)
    | k1_xboole_0 != esk3_0
    | ~ v1_xboole_0(X1) ),
    inference(pm,[status(thm)],[c_0_120,c_0_61])).

cnf(c_0_125,negated_conjecture,
    ( ~ v1_funct_2(esk3_0,esk3_0,esk2_0)
    | ~ v1_xboole_0(k2_funct_1(esk3_0)) ),
    inference(er,[status(thm)],[c_0_121])).

cnf(c_0_126,negated_conjecture,
    ( v1_xboole_0(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_122,c_0_79]),c_0_117]),c_0_118])])).

cnf(c_0_127,plain,
    ( v1_funct_2(k1_xboole_0,X1,X2)
    | ~ v1_partfun1(k1_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_123,c_0_83]),c_0_95])])).

cnf(c_0_128,negated_conjecture,
    ( v1_partfun1(esk3_0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_124,c_0_86])]),c_0_93])).

cnf(c_0_129,negated_conjecture,
    ( ~ v1_funct_2(esk3_0,esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_125,c_0_126])])).

cnf(c_0_130,plain,
    ( v1_funct_2(esk3_0,X1,X2)
    | ~ v1_partfun1(esk3_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_127,c_0_86]),c_0_86])).

cnf(c_0_131,negated_conjecture,
    ( v1_partfun1(esk3_0,esk3_0) ),
    inference(pm,[status(thm)],[c_0_128,c_0_111])).

cnf(c_0_132,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_129,c_0_130]),c_0_131])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n018.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:24:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.63/0.83  # AutoSched0-Mode selected heuristic G_E___300_C01_S00
% 0.63/0.83  # and selection function NoSelection.
% 0.63/0.83  #
% 0.63/0.83  # Preprocessing time       : 0.028 s
% 0.63/0.83  
% 0.63/0.83  # Proof found!
% 0.63/0.83  # SZS status Theorem
% 0.63/0.83  # SZS output start CNFRefutation
% 0.63/0.83  fof(t31_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 0.63/0.83  fof(t3_funct_2, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 0.63/0.83  fof(t55_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))&k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 0.63/0.83  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.63/0.83  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.63/0.83  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.63/0.83  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 0.63/0.83  fof(cc1_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_xboole_0(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 0.63/0.83  fof(t8_boole, axiom, ![X1, X2]:~(((v1_xboole_0(X1)&X1!=X2)&v1_xboole_0(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 0.63/0.83  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.63/0.83  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.63/0.83  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 0.63/0.83  fof(cc4_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 0.63/0.83  fof(dt_k6_partfun1, axiom, ![X1]:(v1_partfun1(k6_partfun1(X1),X1)&m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 0.63/0.83  fof(cc3_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_funct_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_funct_1)).
% 0.63/0.83  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.63/0.83  fof(rc2_funct_1, axiom, ?[X1]:((v1_relat_1(X1)&v1_funct_1(X1))&v2_funct_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc2_funct_1)).
% 0.63/0.83  fof(cc1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_partfun1(X3,X1))=>(v1_funct_1(X3)&v1_funct_2(X3,X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_2)).
% 0.63/0.83  fof(c_0_18, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))))))), inference(assume_negation,[status(cth)],[t31_funct_2])).
% 0.63/0.83  fof(c_0_19, plain, ![X38]:(((v1_funct_1(X38)|(~v1_relat_1(X38)|~v1_funct_1(X38)))&(v1_funct_2(X38,k1_relat_1(X38),k2_relat_1(X38))|(~v1_relat_1(X38)|~v1_funct_1(X38))))&(m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X38),k2_relat_1(X38))))|(~v1_relat_1(X38)|~v1_funct_1(X38)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).
% 0.63/0.83  fof(c_0_20, plain, ![X18]:((k2_relat_1(X18)=k1_relat_1(k2_funct_1(X18))|~v2_funct_1(X18)|(~v1_relat_1(X18)|~v1_funct_1(X18)))&(k1_relat_1(X18)=k2_relat_1(k2_funct_1(X18))|~v2_funct_1(X18)|(~v1_relat_1(X18)|~v1_funct_1(X18)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).
% 0.63/0.83  fof(c_0_21, plain, ![X28, X29, X30]:(~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))|k2_relset_1(X28,X29,X30)=k2_relat_1(X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.63/0.83  fof(c_0_22, negated_conjecture, (((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,esk2_0,esk3_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))))&((v2_funct_1(esk4_0)&k2_relset_1(esk2_0,esk3_0,esk4_0)=esk3_0)&(~v1_funct_1(k2_funct_1(esk4_0))|~v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)|~m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 0.63/0.83  fof(c_0_23, plain, ![X19, X20, X21]:(~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))|v1_relat_1(X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.63/0.83  cnf(c_0_24, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.63/0.83  cnf(c_0_25, plain, (k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.63/0.83  cnf(c_0_26, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.63/0.83  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.63/0.83  cnf(c_0_28, negated_conjecture, (k2_relset_1(esk2_0,esk3_0,esk4_0)=esk3_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.63/0.83  cnf(c_0_29, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.63/0.83  fof(c_0_30, plain, ![X25, X26, X27]:(~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))|k1_relset_1(X25,X26,X27)=k1_relat_1(X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.63/0.83  cnf(c_0_31, plain, (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(X1))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)), inference(pm,[status(thm)],[c_0_24, c_0_25])).
% 0.63/0.83  cnf(c_0_32, negated_conjecture, (k2_relat_1(esk4_0)=esk3_0), inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_26, c_0_27]), c_0_28])).
% 0.63/0.83  cnf(c_0_33, negated_conjecture, (v2_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.63/0.83  cnf(c_0_34, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.63/0.83  cnf(c_0_35, negated_conjecture, (v1_relat_1(esk4_0)), inference(pm,[status(thm)],[c_0_29, c_0_27])).
% 0.63/0.83  fof(c_0_36, plain, ![X34, X35, X36]:((((~v1_funct_2(X36,X34,X35)|X34=k1_relset_1(X34,X35,X36)|X35=k1_xboole_0|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))))&(X34!=k1_relset_1(X34,X35,X36)|v1_funct_2(X36,X34,X35)|X35=k1_xboole_0|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))))&((~v1_funct_2(X36,X34,X35)|X34=k1_relset_1(X34,X35,X36)|X34!=k1_xboole_0|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))))&(X34!=k1_relset_1(X34,X35,X36)|v1_funct_2(X36,X34,X35)|X34!=k1_xboole_0|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))))))&((~v1_funct_2(X36,X34,X35)|X36=k1_xboole_0|X34=k1_xboole_0|X35!=k1_xboole_0|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))))&(X36!=k1_xboole_0|v1_funct_2(X36,X34,X35)|X34=k1_xboole_0|X35!=k1_xboole_0|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.63/0.83  cnf(c_0_37, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.63/0.83  cnf(c_0_38, plain, (v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.63/0.83  fof(c_0_39, plain, ![X9, X10]:(~v1_xboole_0(X9)|(~m1_subset_1(X10,k1_zfmisc_1(X9))|v1_xboole_0(X10))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).
% 0.63/0.83  cnf(c_0_40, negated_conjecture, (m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,k2_relat_1(k2_funct_1(esk4_0)))))|~v1_funct_1(k2_funct_1(esk4_0))|~v1_relat_1(k2_funct_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_31, c_0_32]), c_0_33]), c_0_34]), c_0_35])])).
% 0.63/0.83  cnf(c_0_41, plain, (k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.63/0.83  cnf(c_0_42, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.63/0.83  cnf(c_0_43, negated_conjecture, (k1_relset_1(esk2_0,esk3_0,esk4_0)=k1_relat_1(esk4_0)), inference(pm,[status(thm)],[c_0_37, c_0_27])).
% 0.63/0.83  cnf(c_0_44, negated_conjecture, (v1_funct_2(esk4_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.63/0.83  cnf(c_0_45, plain, (v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(X1))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)), inference(pm,[status(thm)],[c_0_38, c_0_25])).
% 0.63/0.83  fof(c_0_46, plain, ![X4, X5]:(~v1_xboole_0(X4)|X4=X5|~v1_xboole_0(X5)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).
% 0.63/0.83  cnf(c_0_47, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.63/0.83  fof(c_0_48, plain, ![X6, X7]:((k2_zfmisc_1(X6,X7)!=k1_xboole_0|(X6=k1_xboole_0|X7=k1_xboole_0))&((X6!=k1_xboole_0|k2_zfmisc_1(X6,X7)=k1_xboole_0)&(X7!=k1_xboole_0|k2_zfmisc_1(X6,X7)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.63/0.83  cnf(c_0_49, negated_conjecture, (m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,k1_relat_1(esk4_0))))|~v1_funct_1(k2_funct_1(esk4_0))|~v1_relat_1(k2_funct_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_40, c_0_41]), c_0_33]), c_0_34]), c_0_35])])).
% 0.63/0.83  cnf(c_0_50, negated_conjecture, (k1_relat_1(esk4_0)=esk2_0|k1_xboole_0=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_42, c_0_27]), c_0_43]), c_0_44])])).
% 0.63/0.83  cnf(c_0_51, negated_conjecture, (v1_funct_2(k2_funct_1(esk4_0),esk3_0,k2_relat_1(k2_funct_1(esk4_0)))|~v1_funct_1(k2_funct_1(esk4_0))|~v1_relat_1(k2_funct_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_45, c_0_32]), c_0_33]), c_0_34]), c_0_35])])).
% 0.63/0.83  cnf(c_0_52, plain, (X1=X2|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.63/0.83  cnf(c_0_53, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.63/0.83  cnf(c_0_54, negated_conjecture, (v1_xboole_0(esk4_0)|~v1_xboole_0(k2_zfmisc_1(esk2_0,esk3_0))), inference(pm,[status(thm)],[c_0_47, c_0_27])).
% 0.63/0.83  cnf(c_0_55, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.63/0.83  cnf(c_0_56, negated_conjecture, (~v1_funct_1(k2_funct_1(esk4_0))|~v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)|~m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.63/0.83  cnf(c_0_57, negated_conjecture, (k1_xboole_0=esk3_0|m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))|~v1_funct_1(k2_funct_1(esk4_0))|~v1_relat_1(k2_funct_1(esk4_0))), inference(pm,[status(thm)],[c_0_49, c_0_50])).
% 0.63/0.83  cnf(c_0_58, negated_conjecture, (v1_funct_2(k2_funct_1(esk4_0),esk3_0,k1_relat_1(esk4_0))|~v1_funct_1(k2_funct_1(esk4_0))|~v1_relat_1(k2_funct_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_51, c_0_41]), c_0_33]), c_0_34]), c_0_35])])).
% 0.63/0.83  cnf(c_0_59, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.63/0.83  cnf(c_0_60, plain, (k1_xboole_0=X1|~v1_xboole_0(X1)), inference(pm,[status(thm)],[c_0_52, c_0_53])).
% 0.63/0.83  cnf(c_0_61, negated_conjecture, (v1_xboole_0(esk4_0)|k1_xboole_0!=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_54, c_0_55]), c_0_53])])).
% 0.63/0.83  cnf(c_0_62, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(X1))|~v1_xboole_0(k2_zfmisc_1(esk2_0,esk3_0))|~v1_xboole_0(X1)), inference(pm,[status(thm)],[c_0_27, c_0_52])).
% 0.63/0.83  cnf(c_0_63, negated_conjecture, (k1_xboole_0=esk3_0|~v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)|~v1_funct_1(k2_funct_1(esk4_0))|~v1_relat_1(k2_funct_1(esk4_0))), inference(pm,[status(thm)],[c_0_56, c_0_57])).
% 0.63/0.83  cnf(c_0_64, negated_conjecture, (k1_xboole_0=esk3_0|v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)|~v1_funct_1(k2_funct_1(esk4_0))|~v1_relat_1(k2_funct_1(esk4_0))), inference(pm,[status(thm)],[c_0_58, c_0_50])).
% 0.63/0.83  fof(c_0_65, plain, ![X16]:((v1_relat_1(k2_funct_1(X16))|(~v1_relat_1(X16)|~v1_funct_1(X16)))&(v1_funct_1(k2_funct_1(X16))|(~v1_relat_1(X16)|~v1_funct_1(X16)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 0.63/0.83  cnf(c_0_66, negated_conjecture, (k1_xboole_0!=esk3_0|~v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)|~v1_funct_1(k2_funct_1(esk4_0))|~m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k1_xboole_0))), inference(pm,[status(thm)],[c_0_56, c_0_59])).
% 0.63/0.83  cnf(c_0_67, negated_conjecture, (esk4_0=k1_xboole_0|k1_xboole_0!=esk3_0), inference(pm,[status(thm)],[c_0_60, c_0_61])).
% 0.63/0.83  cnf(c_0_68, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(X1))|k1_xboole_0!=esk3_0|~v1_xboole_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_62, c_0_55]), c_0_53])])).
% 0.63/0.83  cnf(c_0_69, negated_conjecture, (esk4_0=X1|k1_xboole_0!=esk3_0|~v1_xboole_0(X1)), inference(pm,[status(thm)],[c_0_52, c_0_61])).
% 0.63/0.83  cnf(c_0_70, negated_conjecture, (k1_xboole_0=esk3_0|~v1_funct_1(k2_funct_1(esk4_0))|~v1_relat_1(k2_funct_1(esk4_0))), inference(pm,[status(thm)],[c_0_63, c_0_64])).
% 0.63/0.83  cnf(c_0_71, plain, (v1_funct_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.63/0.83  fof(c_0_72, plain, ![X22, X23, X24]:(~v1_xboole_0(X22)|(~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X23,X22)))|v1_xboole_0(X24))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).
% 0.63/0.83  fof(c_0_73, plain, ![X37]:(v1_partfun1(k6_partfun1(X37),X37)&m1_subset_1(k6_partfun1(X37),k1_zfmisc_1(k2_zfmisc_1(X37,X37)))), inference(variable_rename,[status(thm)],[dt_k6_partfun1])).
% 0.63/0.83  fof(c_0_74, plain, ![X14, X15]:(~v1_relat_1(X14)|~v1_funct_1(X14)|(~m1_subset_1(X15,k1_zfmisc_1(X14))|v1_funct_1(X15))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_funct_1])])])).
% 0.63/0.83  fof(c_0_75, plain, ![X8]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X8)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.63/0.83  cnf(c_0_76, negated_conjecture, (k1_xboole_0!=esk3_0|~v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)|~v1_funct_1(k2_funct_1(esk4_0))|~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))), inference(pm,[status(thm)],[c_0_66, c_0_67])).
% 0.63/0.83  cnf(c_0_77, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(X2))|k1_xboole_0!=esk3_0|~v1_xboole_0(X2)|~v1_xboole_0(X1)), inference(pm,[status(thm)],[c_0_68, c_0_69])).
% 0.63/0.83  cnf(c_0_78, negated_conjecture, (k1_xboole_0=esk3_0|~v1_relat_1(k2_funct_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_70, c_0_71]), c_0_34]), c_0_35])])).
% 0.63/0.83  cnf(c_0_79, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.63/0.83  cnf(c_0_80, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.63/0.83  cnf(c_0_81, plain, (m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.63/0.83  cnf(c_0_82, plain, (v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.63/0.83  cnf(c_0_83, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.63/0.83  fof(c_0_84, plain, ((v1_relat_1(esk1_0)&v1_funct_1(esk1_0))&v2_funct_1(esk1_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc2_funct_1])])).
% 0.63/0.83  cnf(c_0_85, negated_conjecture, (k1_xboole_0!=esk3_0|~v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)|~v1_funct_1(k2_funct_1(esk4_0))|~v1_xboole_0(k2_funct_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_76, c_0_77]), c_0_53])])).
% 0.63/0.83  cnf(c_0_86, negated_conjecture, (k1_xboole_0=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_78, c_0_79]), c_0_34]), c_0_35])])).
% 0.63/0.83  cnf(c_0_87, plain, (v1_xboole_0(k6_partfun1(X1))|~v1_xboole_0(X1)), inference(pm,[status(thm)],[c_0_80, c_0_81])).
% 0.63/0.83  cnf(c_0_88, plain, (v1_funct_1(k1_xboole_0)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(pm,[status(thm)],[c_0_82, c_0_83])).
% 0.63/0.83  cnf(c_0_89, plain, (v1_funct_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_84])).
% 0.63/0.83  cnf(c_0_90, plain, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_84])).
% 0.63/0.83  cnf(c_0_91, plain, (m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k1_xboole_0))|X1!=k1_xboole_0), inference(pm,[status(thm)],[c_0_81, c_0_55])).
% 0.63/0.83  cnf(c_0_92, negated_conjecture, (k1_xboole_0!=esk3_0|~v1_funct_2(k2_funct_1(k1_xboole_0),esk3_0,esk2_0)|~v1_funct_1(k2_funct_1(esk4_0))|~v1_xboole_0(k2_funct_1(k1_xboole_0))), inference(pm,[status(thm)],[c_0_85, c_0_67])).
% 0.63/0.83  cnf(c_0_93, negated_conjecture, (esk4_0=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_86]), c_0_86])])).
% 0.63/0.83  cnf(c_0_94, plain, (k6_partfun1(X1)=X2|~v1_xboole_0(X2)|~v1_xboole_0(X1)), inference(pm,[status(thm)],[c_0_52, c_0_87])).
% 0.63/0.83  cnf(c_0_95, plain, (v1_funct_1(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_88, c_0_89]), c_0_90])])).
% 0.63/0.83  cnf(c_0_96, plain, (v1_relat_1(k1_xboole_0)), inference(pm,[status(thm)],[c_0_29, c_0_83])).
% 0.63/0.83  cnf(c_0_97, plain, (v1_xboole_0(k6_partfun1(X1))|X1!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_47, c_0_91]), c_0_53])])).
% 0.63/0.83  cnf(c_0_98, negated_conjecture, (~v1_funct_2(k2_funct_1(esk3_0),esk3_0,esk2_0)|~v1_funct_1(k2_funct_1(esk3_0))|~v1_xboole_0(k2_funct_1(esk3_0))), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_92, c_0_86]), c_0_86]), c_0_86])]), c_0_93])).
% 0.63/0.83  cnf(c_0_99, negated_conjecture, (k6_partfun1(X1)=esk4_0|k1_xboole_0!=esk3_0|~v1_xboole_0(X1)), inference(pm,[status(thm)],[c_0_94, c_0_61])).
% 0.63/0.83  cnf(c_0_100, plain, (v1_funct_1(k6_partfun1(X1))|X1!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_82, c_0_91]), c_0_95]), c_0_96])])).
% 0.63/0.83  cnf(c_0_101, plain, (k6_partfun1(X1)=X2|X1!=k1_xboole_0|~v1_xboole_0(X2)), inference(pm,[status(thm)],[c_0_52, c_0_97])).
% 0.63/0.83  cnf(c_0_102, negated_conjecture, (~v1_funct_2(k6_partfun1(X1),esk3_0,esk2_0)|~v1_funct_1(k2_funct_1(esk3_0))|~v1_xboole_0(k2_funct_1(esk3_0))|~v1_xboole_0(X1)), inference(pm,[status(thm)],[c_0_98, c_0_94])).
% 0.63/0.83  cnf(c_0_103, negated_conjecture, (k6_partfun1(X1)=esk3_0|~v1_xboole_0(X1)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_99, c_0_86])]), c_0_93])).
% 0.63/0.83  cnf(c_0_104, plain, (v1_funct_1(X1)|X2!=k1_xboole_0|~v1_xboole_0(X1)), inference(pm,[status(thm)],[c_0_100, c_0_101])).
% 0.63/0.83  cnf(c_0_105, negated_conjecture, (m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,k1_relat_1(esk3_0))))|~v1_funct_1(k2_funct_1(esk3_0))|~v1_relat_1(k2_funct_1(esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_93]), c_0_93]), c_0_93]), c_0_93])).
% 0.63/0.83  cnf(c_0_106, plain, (k2_zfmisc_1(X1,X2)=esk3_0|X1!=esk3_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_86]), c_0_86])).
% 0.63/0.83  cnf(c_0_107, plain, (v1_partfun1(k6_partfun1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.63/0.83  cnf(c_0_108, negated_conjecture, (~v1_funct_2(esk3_0,esk3_0,esk2_0)|~v1_funct_1(k2_funct_1(esk3_0))|~v1_xboole_0(k2_funct_1(esk3_0))|~v1_xboole_0(X1)), inference(pm,[status(thm)],[c_0_102, c_0_103])).
% 0.63/0.83  cnf(c_0_109, plain, (v1_funct_1(X1)|~v1_xboole_0(X1)), inference(er,[status(thm)],[c_0_104])).
% 0.63/0.83  cnf(c_0_110, negated_conjecture, (m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(esk3_0))|~v1_funct_1(k2_funct_1(esk3_0))|~v1_relat_1(k2_funct_1(esk3_0))), inference(pm,[status(thm)],[c_0_105, c_0_106])).
% 0.63/0.83  cnf(c_0_111, plain, (v1_xboole_0(esk3_0)), inference(rw,[status(thm)],[c_0_53, c_0_86])).
% 0.63/0.83  cnf(c_0_112, plain, (v1_partfun1(X1,X2)|~v1_xboole_0(k6_partfun1(X2))|~v1_xboole_0(X1)), inference(pm,[status(thm)],[c_0_107, c_0_52])).
% 0.63/0.83  cnf(c_0_113, plain, (k6_partfun1(X1)=k1_xboole_0|~v1_xboole_0(X1)), inference(pm,[status(thm)],[c_0_60, c_0_87])).
% 0.63/0.83  cnf(c_0_114, negated_conjecture, (~v1_funct_2(esk3_0,esk3_0,esk2_0)|~v1_xboole_0(k2_funct_1(esk3_0))|~v1_xboole_0(X1)), inference(pm,[status(thm)],[c_0_108, c_0_109])).
% 0.63/0.83  cnf(c_0_115, plain, (v1_xboole_0(k6_partfun1(X1))|X1!=esk3_0), inference(rw,[status(thm)],[c_0_97, c_0_86])).
% 0.63/0.83  cnf(c_0_116, negated_conjecture, (v1_xboole_0(k2_funct_1(esk3_0))|~v1_funct_1(k2_funct_1(esk3_0))|~v1_relat_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_47, c_0_110]), c_0_111])])).
% 0.63/0.83  cnf(c_0_117, plain, (v1_funct_1(esk3_0)), inference(rw,[status(thm)],[c_0_95, c_0_86])).
% 0.63/0.83  cnf(c_0_118, plain, (v1_relat_1(esk3_0)), inference(rw,[status(thm)],[c_0_96, c_0_86])).
% 0.63/0.83  fof(c_0_119, plain, ![X31, X32, X33]:((v1_funct_1(X33)|(~v1_funct_1(X33)|~v1_partfun1(X33,X31))|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))))&(v1_funct_2(X33,X31,X32)|(~v1_funct_1(X33)|~v1_partfun1(X33,X31))|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_2])])])).
% 0.63/0.83  cnf(c_0_120, plain, (v1_partfun1(X1,X2)|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_112, c_0_113]), c_0_53])])).
% 0.63/0.83  cnf(c_0_121, negated_conjecture, (X1!=esk3_0|~v1_funct_2(esk3_0,esk3_0,esk2_0)|~v1_xboole_0(k2_funct_1(esk3_0))), inference(pm,[status(thm)],[c_0_114, c_0_115])).
% 0.63/0.83  cnf(c_0_122, negated_conjecture, (v1_xboole_0(k2_funct_1(esk3_0))|~v1_relat_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_116, c_0_71]), c_0_117]), c_0_118])])).
% 0.63/0.83  cnf(c_0_123, plain, (v1_funct_2(X1,X2,X3)|~v1_funct_1(X1)|~v1_partfun1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_119])).
% 0.63/0.83  cnf(c_0_124, negated_conjecture, (v1_partfun1(esk4_0,X1)|k1_xboole_0!=esk3_0|~v1_xboole_0(X1)), inference(pm,[status(thm)],[c_0_120, c_0_61])).
% 0.63/0.83  cnf(c_0_125, negated_conjecture, (~v1_funct_2(esk3_0,esk3_0,esk2_0)|~v1_xboole_0(k2_funct_1(esk3_0))), inference(er,[status(thm)],[c_0_121])).
% 0.63/0.83  cnf(c_0_126, negated_conjecture, (v1_xboole_0(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_122, c_0_79]), c_0_117]), c_0_118])])).
% 0.63/0.83  cnf(c_0_127, plain, (v1_funct_2(k1_xboole_0,X1,X2)|~v1_partfun1(k1_xboole_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_123, c_0_83]), c_0_95])])).
% 0.63/0.83  cnf(c_0_128, negated_conjecture, (v1_partfun1(esk3_0,X1)|~v1_xboole_0(X1)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_124, c_0_86])]), c_0_93])).
% 0.63/0.83  cnf(c_0_129, negated_conjecture, (~v1_funct_2(esk3_0,esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_125, c_0_126])])).
% 0.63/0.83  cnf(c_0_130, plain, (v1_funct_2(esk3_0,X1,X2)|~v1_partfun1(esk3_0,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_127, c_0_86]), c_0_86])).
% 0.63/0.83  cnf(c_0_131, negated_conjecture, (v1_partfun1(esk3_0,esk3_0)), inference(pm,[status(thm)],[c_0_128, c_0_111])).
% 0.63/0.83  cnf(c_0_132, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_129, c_0_130]), c_0_131])]), ['proof']).
% 0.63/0.83  # SZS output end CNFRefutation
% 0.63/0.83  # Proof object total steps             : 133
% 0.63/0.83  # Proof object clause steps            : 97
% 0.63/0.83  # Proof object formula steps           : 36
% 0.63/0.83  # Proof object conjectures             : 53
% 0.63/0.83  # Proof object clause conjectures      : 50
% 0.63/0.83  # Proof object formula conjectures     : 3
% 0.63/0.83  # Proof object initial clauses used    : 29
% 0.63/0.83  # Proof object initial formulas used   : 18
% 0.63/0.83  # Proof object generating inferences   : 56
% 0.63/0.83  # Proof object simplifying inferences  : 81
% 0.63/0.83  # Training examples: 0 positive, 0 negative
% 0.63/0.83  # Parsed axioms                        : 19
% 0.63/0.83  # Removed by relevancy pruning/SinE    : 0
% 0.63/0.83  # Initial clauses                      : 39
% 0.63/0.83  # Removed in clause preprocessing      : 2
% 0.63/0.83  # Initial clauses in saturation        : 37
% 0.63/0.83  # Processed clauses                    : 4609
% 0.63/0.83  # ...of these trivial                  : 126
% 0.63/0.83  # ...subsumed                          : 3316
% 0.63/0.83  # ...remaining for further processing  : 1167
% 0.63/0.83  # Other redundant clauses eliminated   : 0
% 0.63/0.83  # Clauses deleted for lack of memory   : 0
% 0.63/0.83  # Backward-subsumed                    : 350
% 0.63/0.83  # Backward-rewritten                   : 548
% 0.63/0.83  # Generated clauses                    : 36235
% 0.63/0.83  # ...of the previous two non-trivial   : 34338
% 0.63/0.83  # Contextual simplify-reflections      : 0
% 0.63/0.83  # Paramodulations                      : 36197
% 0.63/0.83  # Factorizations                       : 0
% 0.63/0.83  # Equation resolutions                 : 38
% 0.63/0.83  # Propositional unsat checks           : 0
% 0.63/0.83  #    Propositional check models        : 0
% 0.63/0.83  #    Propositional check unsatisfiable : 0
% 0.63/0.83  #    Propositional clauses             : 0
% 0.63/0.83  #    Propositional clauses after purity: 0
% 0.63/0.83  #    Propositional unsat core size     : 0
% 0.63/0.83  #    Propositional preprocessing time  : 0.000
% 0.63/0.83  #    Propositional encoding time       : 0.000
% 0.63/0.83  #    Propositional solver time         : 0.000
% 0.63/0.83  #    Success case prop preproc time    : 0.000
% 0.63/0.83  #    Success case prop encoding time   : 0.000
% 0.63/0.83  #    Success case prop solver time     : 0.000
% 0.63/0.83  # Current number of processed clauses  : 269
% 0.63/0.83  #    Positive orientable unit clauses  : 21
% 0.63/0.83  #    Positive unorientable unit clauses: 4
% 0.63/0.83  #    Negative unit clauses             : 5
% 0.63/0.83  #    Non-unit-clauses                  : 239
% 0.63/0.83  # Current number of unprocessed clauses: 27224
% 0.63/0.83  # ...number of literals in the above   : 140608
% 0.63/0.83  # Current number of archived formulas  : 0
% 0.63/0.83  # Current number of archived clauses   : 898
% 0.63/0.83  # Clause-clause subsumption calls (NU) : 85451
% 0.63/0.83  # Rec. Clause-clause subsumption calls : 51736
% 0.63/0.83  # Non-unit clause-clause subsumptions  : 3351
% 0.63/0.83  # Unit Clause-clause subsumption calls : 1091
% 0.63/0.83  # Rewrite failures with RHS unbound    : 132
% 0.63/0.83  # BW rewrite match attempts            : 61
% 0.63/0.83  # BW rewrite match successes           : 18
% 0.63/0.83  # Condensation attempts                : 0
% 0.63/0.83  # Condensation successes               : 0
% 0.63/0.83  # Termbank termtop insertions          : 253423
% 0.63/0.83  
% 0.63/0.83  # -------------------------------------------------
% 0.63/0.83  # User time                : 0.475 s
% 0.63/0.83  # System time              : 0.018 s
% 0.63/0.83  # Total time               : 0.493 s
% 0.63/0.83  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------

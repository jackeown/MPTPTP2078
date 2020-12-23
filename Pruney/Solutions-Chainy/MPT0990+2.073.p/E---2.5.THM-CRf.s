%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:03:09 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  123 (19900 expanded)
%              Number of clauses        :   86 (6938 expanded)
%              Number of leaves         :   18 (5002 expanded)
%              Depth                    :   24
%              Number of atoms          :  419 (134574 expanded)
%              Number of equality atoms :  134 (41798 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal clause size      :   40 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t36_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X2,X1)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) )
         => ( ( k2_relset_1(X1,X2,X3) = X2
              & r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1))
              & v2_funct_1(X3) )
           => ( X1 = k1_xboole_0
              | X2 = k1_xboole_0
              | X4 = k2_funct_1(X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(dt_k6_partfun1,axiom,(
    ! [X1] :
      ( v1_partfun1(k6_partfun1(X1),X1)
      & m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(redefinition_r2_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_relset_1(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(dt_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => ( v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))
        & m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(t35_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( k2_relset_1(X1,X2,X3) = X2
          & v2_funct_1(X3) )
       => ( X2 = k1_xboole_0
          | ( k5_relat_1(X3,k2_funct_1(X3)) = k6_partfun1(X1)
            & k5_relat_1(k2_funct_1(X3),X3) = k6_partfun1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).

fof(redefinition_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k1_partfun1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(fc4_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v2_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(t30_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X5] :
          ( ( v1_funct_1(X5)
            & v1_funct_2(X5,X2,X3)
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
         => ( ( v2_funct_1(k1_partfun1(X1,X2,X2,X3,X4,X5))
              & k2_relset_1(X1,X2,X4) = X2 )
           => ( ( X3 = k1_xboole_0
                & X2 != k1_xboole_0 )
              | ( v2_funct_1(X4)
                & v2_funct_1(X5) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_funct_2)).

fof(t24_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X2,X1)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) )
         => ( r2_relset_1(X2,X2,k1_partfun1(X2,X1,X1,X2,X4,X3),k6_partfun1(X2))
           => k2_relset_1(X1,X2,X3) = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t55_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => k5_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(X1,k5_relat_1(X2,X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(t80_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(X1,k6_relat_1(k2_relat_1(X1))) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(t78_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

fof(t55_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
          & k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ! [X4] :
            ( ( v1_funct_1(X4)
              & v1_funct_2(X4,X2,X1)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) )
           => ( ( k2_relset_1(X1,X2,X3) = X2
                & r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1))
                & v2_funct_1(X3) )
             => ( X1 = k1_xboole_0
                | X2 = k1_xboole_0
                | X4 = k2_funct_1(X3) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t36_funct_2])).

fof(c_0_19,negated_conjecture,
    ( v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,esk1_0,esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    & v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,esk2_0,esk1_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))
    & k2_relset_1(esk1_0,esk2_0,esk3_0) = esk2_0
    & r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_partfun1(esk1_0))
    & v2_funct_1(esk3_0)
    & esk1_0 != k1_xboole_0
    & esk2_0 != k1_xboole_0
    & esk4_0 != k2_funct_1(esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

fof(c_0_20,plain,(
    ! [X40] : k6_partfun1(X40) = k6_relat_1(X40) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

fof(c_0_21,plain,(
    ! [X33] :
      ( v1_partfun1(k6_partfun1(X33),X33)
      & m1_subset_1(k6_partfun1(X33),k1_zfmisc_1(k2_zfmisc_1(X33,X33))) ) ),
    inference(variable_rename,[status(thm)],[dt_k6_partfun1])).

fof(c_0_22,plain,(
    ! [X23,X24,X25,X26] :
      ( ( ~ r2_relset_1(X23,X24,X25,X26)
        | X25 = X26
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) )
      & ( X25 != X26
        | r2_relset_1(X23,X24,X25,X26)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).

cnf(c_0_23,negated_conjecture,
    ( r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_partfun1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,plain,
    ( m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,plain,
    ( X3 = X4
    | ~ r2_relset_1(X1,X2,X3,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_relat_1(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_28,plain,
    ( m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(rw,[status(thm)],[c_0_25,c_0_24])).

fof(c_0_29,plain,(
    ! [X27,X28,X29,X30,X31,X32] :
      ( ( v1_funct_1(k1_partfun1(X27,X28,X29,X30,X31,X32))
        | ~ v1_funct_1(X31)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))
        | ~ v1_funct_1(X32)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) )
      & ( m1_subset_1(k1_partfun1(X27,X28,X29,X30,X31,X32),k1_zfmisc_1(k2_zfmisc_1(X27,X30)))
        | ~ v1_funct_1(X31)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))
        | ~ v1_funct_1(X32)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).

fof(c_0_30,plain,(
    ! [X50,X51,X52] :
      ( ( k5_relat_1(X52,k2_funct_1(X52)) = k6_partfun1(X50)
        | X51 = k1_xboole_0
        | k2_relset_1(X50,X51,X52) != X51
        | ~ v2_funct_1(X52)
        | ~ v1_funct_1(X52)
        | ~ v1_funct_2(X52,X50,X51)
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51))) )
      & ( k5_relat_1(k2_funct_1(X52),X52) = k6_partfun1(X51)
        | X51 = k1_xboole_0
        | k2_relset_1(X50,X51,X52) != X51
        | ~ v2_funct_1(X52)
        | ~ v1_funct_1(X52)
        | ~ v1_funct_2(X52,X50,X51)
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_funct_2])])])).

fof(c_0_31,plain,(
    ! [X34,X35,X36,X37,X38,X39] :
      ( ~ v1_funct_1(X38)
      | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))
      | ~ v1_funct_1(X39)
      | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))
      | k1_partfun1(X34,X35,X36,X37,X38,X39) = k5_relat_1(X38,X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).

cnf(c_0_32,negated_conjecture,
    ( k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0) = k6_relat_1(esk1_0)
    | ~ m1_subset_1(k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])])).

cnf(c_0_33,plain,
    ( m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X6)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_36,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_37,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_38,plain,
    ( k5_relat_1(k2_funct_1(X1),X1) = k6_partfun1(X2)
    | X2 = k1_xboole_0
    | k2_relset_1(X3,X2,X1) != X2
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,plain,
    ( k1_partfun1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_40,negated_conjecture,
    ( k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0) = k6_relat_1(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_35]),c_0_36]),c_0_37])])).

fof(c_0_41,plain,(
    ! [X14] :
      ( v1_relat_1(k6_relat_1(X14))
      & v2_funct_1(k6_relat_1(X14)) ) ),
    inference(variable_rename,[status(thm)],[fc4_funct_1])).

cnf(c_0_42,plain,
    ( X2 = k1_xboole_0
    | k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(X2)
    | k2_relset_1(X3,X2,X1) != X2
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(rw,[status(thm)],[c_0_38,c_0_24])).

cnf(c_0_43,negated_conjecture,
    ( v1_funct_2(esk4_0,esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_44,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_45,plain,(
    ! [X45,X46,X47,X48,X49] :
      ( ( v2_funct_1(X48)
        | X47 = k1_xboole_0
        | ~ v2_funct_1(k1_partfun1(X45,X46,X46,X47,X48,X49))
        | k2_relset_1(X45,X46,X48) != X46
        | ~ v1_funct_1(X49)
        | ~ v1_funct_2(X49,X46,X47)
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X46,X47)))
        | ~ v1_funct_1(X48)
        | ~ v1_funct_2(X48,X45,X46)
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X45,X46))) )
      & ( v2_funct_1(X49)
        | X47 = k1_xboole_0
        | ~ v2_funct_1(k1_partfun1(X45,X46,X46,X47,X48,X49))
        | k2_relset_1(X45,X46,X48) != X46
        | ~ v1_funct_1(X49)
        | ~ v1_funct_2(X49,X46,X47)
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X46,X47)))
        | ~ v1_funct_1(X48)
        | ~ v1_funct_2(X48,X45,X46)
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X45,X46))) )
      & ( v2_funct_1(X48)
        | X46 != k1_xboole_0
        | ~ v2_funct_1(k1_partfun1(X45,X46,X46,X47,X48,X49))
        | k2_relset_1(X45,X46,X48) != X46
        | ~ v1_funct_1(X49)
        | ~ v1_funct_2(X49,X46,X47)
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X46,X47)))
        | ~ v1_funct_1(X48)
        | ~ v1_funct_2(X48,X45,X46)
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X45,X46))) )
      & ( v2_funct_1(X49)
        | X46 != k1_xboole_0
        | ~ v2_funct_1(k1_partfun1(X45,X46,X46,X47,X48,X49))
        | k2_relset_1(X45,X46,X48) != X46
        | ~ v1_funct_1(X49)
        | ~ v1_funct_2(X49,X46,X47)
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X46,X47)))
        | ~ v1_funct_1(X48)
        | ~ v1_funct_2(X48,X45,X46)
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X45,X46))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_funct_2])])])])).

cnf(c_0_46,negated_conjecture,
    ( k6_relat_1(esk1_0) = k5_relat_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_34]),c_0_35]),c_0_36]),c_0_37])])).

cnf(c_0_47,plain,
    ( v2_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_48,plain,(
    ! [X41,X42,X43,X44] :
      ( ~ v1_funct_1(X43)
      | ~ v1_funct_2(X43,X41,X42)
      | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))
      | ~ v1_funct_1(X44)
      | ~ v1_funct_2(X44,X42,X41)
      | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X41)))
      | ~ r2_relset_1(X42,X42,k1_partfun1(X42,X41,X41,X42,X44,X43),k6_partfun1(X42))
      | k2_relset_1(X41,X42,X43) = X42 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_funct_2])])])).

cnf(c_0_49,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk4_0),esk4_0) = k6_relat_1(esk1_0)
    | k2_relset_1(esk2_0,esk1_0,esk4_0) != esk1_0
    | ~ v2_funct_1(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_34]),c_0_43]),c_0_36])]),c_0_44])).

cnf(c_0_50,plain,
    ( v2_funct_1(X1)
    | X2 = k1_xboole_0
    | ~ v2_funct_1(k1_partfun1(X3,X4,X4,X2,X5,X1))
    | k2_relset_1(X3,X4,X5) != X4
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X4,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,X3,X4)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_51,negated_conjecture,
    ( k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0) = k5_relat_1(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_40,c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( k2_relset_1(esk1_0,esk2_0,esk3_0) = esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_53,negated_conjecture,
    ( v1_funct_2(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_54,negated_conjecture,
    ( v2_funct_1(k5_relat_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_46])).

cnf(c_0_55,plain,
    ( k2_relset_1(X2,X3,X1) = X3
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X3,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ r2_relset_1(X3,X3,k1_partfun1(X3,X2,X2,X3,X4,X1),k6_partfun1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_56,negated_conjecture,
    ( r2_relset_1(esk1_0,esk1_0,k6_relat_1(esk1_0),k6_relat_1(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_27,c_0_40])).

cnf(c_0_57,plain,
    ( k5_relat_1(X1,k2_funct_1(X1)) = k6_partfun1(X2)
    | X3 = k1_xboole_0
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_58,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk4_0),esk4_0) = k5_relat_1(esk3_0,esk4_0)
    | k2_relset_1(esk2_0,esk1_0,esk4_0) != esk1_0
    | ~ v2_funct_1(esk4_0) ),
    inference(rw,[status(thm)],[c_0_49,c_0_46])).

cnf(c_0_59,negated_conjecture,
    ( v2_funct_1(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52]),c_0_53]),c_0_43]),c_0_35]),c_0_34]),c_0_54]),c_0_37]),c_0_36])]),c_0_44])).

cnf(c_0_60,plain,
    ( k2_relset_1(X2,X3,X1) = X3
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X4,X3,X2)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_relset_1(X3,X3,k1_partfun1(X3,X2,X2,X3,X4,X1),k6_relat_1(X3)) ),
    inference(rw,[status(thm)],[c_0_55,c_0_24])).

cnf(c_0_61,negated_conjecture,
    ( r2_relset_1(esk1_0,esk1_0,k5_relat_1(esk3_0,esk4_0),k5_relat_1(esk3_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_46]),c_0_46])).

fof(c_0_62,plain,(
    ! [X17,X18,X19] :
      ( ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))
      | v1_relat_1(X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_63,plain,
    ( X3 = k1_xboole_0
    | k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(X2)
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_57,c_0_24])).

fof(c_0_64,plain,(
    ! [X7,X8,X9] :
      ( ~ v1_relat_1(X7)
      | ~ v1_relat_1(X8)
      | ~ v1_relat_1(X9)
      | k5_relat_1(k5_relat_1(X7,X8),X9) = k5_relat_1(X7,k5_relat_1(X8,X9)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_relat_1])])])).

cnf(c_0_65,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk4_0),esk4_0) = k5_relat_1(esk3_0,esk4_0)
    | k2_relset_1(esk2_0,esk1_0,esk4_0) != esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_59])])).

cnf(c_0_66,negated_conjecture,
    ( k2_relset_1(esk2_0,esk1_0,esk4_0) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_51]),c_0_53]),c_0_43]),c_0_46]),c_0_61]),c_0_35]),c_0_34]),c_0_37]),c_0_36])])).

cnf(c_0_67,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_68,negated_conjecture,
    ( k5_relat_1(esk4_0,k2_funct_1(esk4_0)) = k6_relat_1(esk2_0)
    | k2_relset_1(esk2_0,esk1_0,esk4_0) != esk1_0
    | ~ v2_funct_1(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_34]),c_0_43]),c_0_36])]),c_0_44])).

cnf(c_0_69,plain,
    ( k5_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(X1,k5_relat_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_70,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk4_0),esk4_0) = k5_relat_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_66])])).

cnf(c_0_71,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_34])).

cnf(c_0_72,negated_conjecture,
    ( k5_relat_1(esk4_0,k2_funct_1(esk4_0)) = k6_relat_1(esk2_0)
    | k2_relset_1(esk2_0,esk1_0,esk4_0) != esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_59])])).

fof(c_0_73,plain,(
    ! [X20,X21,X22] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
      | k2_relset_1(X20,X21,X22) = k2_relat_1(X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_74,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk4_0),k5_relat_1(esk4_0,X1)) = k5_relat_1(k5_relat_1(esk3_0,esk4_0),X1)
    | ~ v1_relat_1(k2_funct_1(esk4_0))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71])])).

cnf(c_0_75,negated_conjecture,
    ( k5_relat_1(esk4_0,k2_funct_1(esk4_0)) = k6_relat_1(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_66])])).

fof(c_0_76,plain,(
    ! [X12] :
      ( ~ v1_relat_1(X12)
      | k5_relat_1(X12,k6_relat_1(k2_relat_1(X12))) = X12 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_relat_1])])).

fof(c_0_77,plain,(
    ! [X10] :
      ( k1_relat_1(k6_relat_1(X10)) = X10
      & k2_relat_1(k6_relat_1(X10)) = X10 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

cnf(c_0_78,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_79,negated_conjecture,
    ( k5_relat_1(k5_relat_1(esk3_0,esk4_0),k2_funct_1(esk4_0)) = k5_relat_1(k2_funct_1(esk4_0),k6_relat_1(esk2_0))
    | ~ v1_relat_1(k2_funct_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_80,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_35])).

cnf(c_0_81,plain,
    ( k5_relat_1(X1,k6_relat_1(k2_relat_1(X1))) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_82,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_83,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_84,plain,
    ( k2_relset_1(X1,X2,X3) = k2_relset_1(X4,X5,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) ),
    inference(spm,[status(thm)],[c_0_78,c_0_78])).

cnf(c_0_85,negated_conjecture,
    ( k5_relat_1(esk4_0,k5_relat_1(k2_funct_1(esk4_0),X1)) = k5_relat_1(k6_relat_1(esk2_0),X1)
    | ~ v1_relat_1(k2_funct_1(esk4_0))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_75]),c_0_71])])).

cnf(c_0_86,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk4_0),k6_relat_1(esk2_0)) = k5_relat_1(esk3_0,k6_relat_1(esk2_0))
    | ~ v1_relat_1(k2_funct_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_79]),c_0_75]),c_0_71]),c_0_80])])).

cnf(c_0_87,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X1)) = k6_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_83])])).

cnf(c_0_88,plain,
    ( k5_relat_1(X1,k6_relat_1(k2_relset_1(X2,X3,X1))) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_78]),c_0_67])).

fof(c_0_89,plain,(
    ! [X11] :
      ( ~ v1_relat_1(X11)
      | k5_relat_1(k6_relat_1(k1_relat_1(X11)),X11) = X11 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_relat_1])])).

fof(c_0_90,plain,(
    ! [X15] :
      ( ( k2_relat_1(X15) = k1_relat_1(k2_funct_1(X15))
        | ~ v2_funct_1(X15)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( k1_relat_1(X15) = k2_relat_1(k2_funct_1(X15))
        | ~ v2_funct_1(X15)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).

fof(c_0_91,plain,(
    ! [X13] :
      ( ( v1_relat_1(k2_funct_1(X13))
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) )
      & ( v1_funct_1(k2_funct_1(X13))
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

cnf(c_0_92,negated_conjecture,
    ( k2_relset_1(X1,X2,esk4_0) = esk1_0
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_84]),c_0_34])])).

cnf(c_0_93,negated_conjecture,
    ( k5_relat_1(esk4_0,k5_relat_1(esk3_0,k6_relat_1(esk2_0))) = k6_relat_1(esk2_0)
    | ~ v1_relat_1(k2_funct_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_87]),c_0_83])])).

cnf(c_0_94,negated_conjecture,
    ( k5_relat_1(esk3_0,k6_relat_1(esk2_0)) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_52]),c_0_35])])).

cnf(c_0_95,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_89])).

cnf(c_0_96,plain,
    ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_97,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_91])).

cnf(c_0_98,negated_conjecture,
    ( k2_relat_1(esk4_0) = esk1_0
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_78,c_0_92])).

cnf(c_0_99,negated_conjecture,
    ( k6_relat_1(esk2_0) = k5_relat_1(esk4_0,esk3_0)
    | ~ v1_relat_1(k2_funct_1(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_93,c_0_94])).

cnf(c_0_100,plain,
    ( k5_relat_1(k6_relat_1(k2_relat_1(X1)),k2_funct_1(X1)) = k2_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_97])).

cnf(c_0_101,negated_conjecture,
    ( k2_relat_1(esk4_0) = esk1_0 ),
    inference(spm,[status(thm)],[c_0_98,c_0_34])).

cnf(c_0_102,negated_conjecture,
    ( k6_relat_1(esk2_0) = k5_relat_1(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_97]),c_0_36]),c_0_71])])).

cnf(c_0_103,negated_conjecture,
    ( k5_relat_1(k5_relat_1(esk3_0,esk4_0),k2_funct_1(esk4_0)) = k2_funct_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_46]),c_0_59]),c_0_36]),c_0_71])])).

cnf(c_0_104,negated_conjecture,
    ( k5_relat_1(esk3_0,k5_relat_1(esk4_0,esk3_0)) = esk3_0 ),
    inference(rw,[status(thm)],[c_0_94,c_0_102])).

cnf(c_0_105,negated_conjecture,
    ( v2_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_106,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_107,negated_conjecture,
    ( k2_funct_1(esk4_0) = esk3_0
    | ~ v1_relat_1(k2_funct_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_103]),c_0_75]),c_0_102]),c_0_104]),c_0_71]),c_0_80])])).

cnf(c_0_108,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk3_0),esk3_0) = k6_relat_1(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_35]),c_0_52]),c_0_53]),c_0_105]),c_0_37])]),c_0_106])).

cnf(c_0_109,plain,
    ( k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_110,negated_conjecture,
    ( k2_funct_1(esk4_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_97]),c_0_36]),c_0_71])])).

cnf(c_0_111,negated_conjecture,
    ( k5_relat_1(k6_relat_1(esk2_0),esk4_0) = k5_relat_1(esk4_0,k5_relat_1(esk3_0,esk4_0))
    | ~ v1_relat_1(k2_funct_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_70]),c_0_71])])).

cnf(c_0_112,negated_conjecture,
    ( k5_relat_1(esk4_0,k5_relat_1(esk3_0,esk4_0)) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_66]),c_0_46]),c_0_34])])).

cnf(c_0_113,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk3_0),k5_relat_1(esk3_0,X1)) = k5_relat_1(k6_relat_1(esk2_0),X1)
    | ~ v1_relat_1(k2_funct_1(esk3_0))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_108]),c_0_80])])).

cnf(c_0_114,plain,
    ( k5_relat_1(k2_funct_1(X1),k6_relat_1(k1_relat_1(X1))) = k2_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_109]),c_0_97])).

cnf(c_0_115,negated_conjecture,
    ( k1_relat_1(esk3_0) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_110]),c_0_101]),c_0_59]),c_0_36]),c_0_71])])).

cnf(c_0_116,negated_conjecture,
    ( k5_relat_1(k5_relat_1(esk4_0,esk3_0),esk4_0) = esk4_0
    | ~ v1_relat_1(k2_funct_1(esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_111,c_0_102]),c_0_112])).

cnf(c_0_117,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk3_0),k5_relat_1(esk3_0,X1)) = k5_relat_1(k5_relat_1(esk4_0,esk3_0),X1)
    | ~ v1_relat_1(k2_funct_1(esk3_0))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_113,c_0_102])).

cnf(c_0_118,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk3_0),k5_relat_1(esk3_0,esk4_0)) = k2_funct_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_115]),c_0_46]),c_0_105]),c_0_37]),c_0_80])])).

cnf(c_0_119,negated_conjecture,
    ( k5_relat_1(k5_relat_1(esk4_0,esk3_0),esk4_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_116,c_0_110]),c_0_80])])).

cnf(c_0_120,negated_conjecture,
    ( esk4_0 != k2_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_121,negated_conjecture,
    ( ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_118]),c_0_119]),c_0_71])]),c_0_120])).

cnf(c_0_122,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_97]),c_0_37]),c_0_80])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:42:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.42  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.42  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.42  #
% 0.20/0.42  # Preprocessing time       : 0.029 s
% 0.20/0.42  # Presaturation interreduction done
% 0.20/0.42  
% 0.20/0.42  # Proof found!
% 0.20/0.42  # SZS status Theorem
% 0.20/0.42  # SZS output start CNFRefutation
% 0.20/0.42  fof(t36_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(((k2_relset_1(X1,X2,X3)=X2&r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1)))&v2_funct_1(X3))=>(X1=k1_xboole_0|X2=k1_xboole_0|X4=k2_funct_1(X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 0.20/0.42  fof(redefinition_k6_partfun1, axiom, ![X1]:k6_partfun1(X1)=k6_relat_1(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 0.20/0.42  fof(dt_k6_partfun1, axiom, ![X1]:(v1_partfun1(k6_partfun1(X1),X1)&m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 0.20/0.42  fof(redefinition_r2_relset_1, axiom, ![X1, X2, X3, X4]:((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_relset_1(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 0.20/0.42  fof(dt_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>(v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))&m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 0.20/0.42  fof(t35_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((k2_relset_1(X1,X2,X3)=X2&v2_funct_1(X3))=>(X2=k1_xboole_0|(k5_relat_1(X3,k2_funct_1(X3))=k6_partfun1(X1)&k5_relat_1(k2_funct_1(X3),X3)=k6_partfun1(X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 0.20/0.42  fof(redefinition_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>k1_partfun1(X1,X2,X3,X4,X5,X6)=k5_relat_1(X5,X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 0.20/0.42  fof(fc4_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v2_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 0.20/0.42  fof(t30_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X2,X3))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>((v2_funct_1(k1_partfun1(X1,X2,X2,X3,X4,X5))&k2_relset_1(X1,X2,X4)=X2)=>((X3=k1_xboole_0&X2!=k1_xboole_0)|(v2_funct_1(X4)&v2_funct_1(X5)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_funct_2)).
% 0.20/0.42  fof(t24_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(r2_relset_1(X2,X2,k1_partfun1(X2,X1,X1,X2,X4,X3),k6_partfun1(X2))=>k2_relset_1(X1,X2,X3)=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 0.20/0.42  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.20/0.42  fof(t55_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>k5_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(X1,k5_relat_1(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 0.20/0.42  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.20/0.42  fof(t80_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k5_relat_1(X1,k6_relat_1(k2_relat_1(X1)))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 0.20/0.42  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 0.20/0.42  fof(t78_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_relat_1)).
% 0.20/0.42  fof(t55_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))&k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 0.20/0.42  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 0.20/0.42  fof(c_0_18, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(((k2_relset_1(X1,X2,X3)=X2&r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1)))&v2_funct_1(X3))=>(X1=k1_xboole_0|X2=k1_xboole_0|X4=k2_funct_1(X3)))))), inference(assume_negation,[status(cth)],[t36_funct_2])).
% 0.20/0.42  fof(c_0_19, negated_conjecture, (((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,esk1_0,esk2_0))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))))&(((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,esk2_0,esk1_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))))&(((k2_relset_1(esk1_0,esk2_0,esk3_0)=esk2_0&r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_partfun1(esk1_0)))&v2_funct_1(esk3_0))&((esk1_0!=k1_xboole_0&esk2_0!=k1_xboole_0)&esk4_0!=k2_funct_1(esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 0.20/0.42  fof(c_0_20, plain, ![X40]:k6_partfun1(X40)=k6_relat_1(X40), inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).
% 0.20/0.42  fof(c_0_21, plain, ![X33]:(v1_partfun1(k6_partfun1(X33),X33)&m1_subset_1(k6_partfun1(X33),k1_zfmisc_1(k2_zfmisc_1(X33,X33)))), inference(variable_rename,[status(thm)],[dt_k6_partfun1])).
% 0.20/0.42  fof(c_0_22, plain, ![X23, X24, X25, X26]:((~r2_relset_1(X23,X24,X25,X26)|X25=X26|(~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))))&(X25!=X26|r2_relset_1(X23,X24,X25,X26)|(~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).
% 0.20/0.42  cnf(c_0_23, negated_conjecture, (r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_partfun1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.42  cnf(c_0_24, plain, (k6_partfun1(X1)=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.42  cnf(c_0_25, plain, (m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.42  cnf(c_0_26, plain, (X3=X4|~r2_relset_1(X1,X2,X3,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.42  cnf(c_0_27, negated_conjecture, (r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_relat_1(esk1_0))), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 0.20/0.42  cnf(c_0_28, plain, (m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(rw,[status(thm)],[c_0_25, c_0_24])).
% 0.20/0.42  fof(c_0_29, plain, ![X27, X28, X29, X30, X31, X32]:((v1_funct_1(k1_partfun1(X27,X28,X29,X30,X31,X32))|(~v1_funct_1(X31)|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))|~v1_funct_1(X32)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))))&(m1_subset_1(k1_partfun1(X27,X28,X29,X30,X31,X32),k1_zfmisc_1(k2_zfmisc_1(X27,X30)))|(~v1_funct_1(X31)|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))|~v1_funct_1(X32)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).
% 0.20/0.42  fof(c_0_30, plain, ![X50, X51, X52]:((k5_relat_1(X52,k2_funct_1(X52))=k6_partfun1(X50)|X51=k1_xboole_0|(k2_relset_1(X50,X51,X52)!=X51|~v2_funct_1(X52))|(~v1_funct_1(X52)|~v1_funct_2(X52,X50,X51)|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51)))))&(k5_relat_1(k2_funct_1(X52),X52)=k6_partfun1(X51)|X51=k1_xboole_0|(k2_relset_1(X50,X51,X52)!=X51|~v2_funct_1(X52))|(~v1_funct_1(X52)|~v1_funct_2(X52,X50,X51)|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_funct_2])])])).
% 0.20/0.42  fof(c_0_31, plain, ![X34, X35, X36, X37, X38, X39]:(~v1_funct_1(X38)|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))|~v1_funct_1(X39)|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))|k1_partfun1(X34,X35,X36,X37,X38,X39)=k5_relat_1(X38,X39)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).
% 0.20/0.42  cnf(c_0_32, negated_conjecture, (k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0)=k6_relat_1(esk1_0)|~m1_subset_1(k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])])).
% 0.20/0.42  cnf(c_0_33, plain, (m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X6)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.42  cnf(c_0_34, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.42  cnf(c_0_35, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.42  cnf(c_0_36, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.42  cnf(c_0_37, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.42  cnf(c_0_38, plain, (k5_relat_1(k2_funct_1(X1),X1)=k6_partfun1(X2)|X2=k1_xboole_0|k2_relset_1(X3,X2,X1)!=X2|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.42  cnf(c_0_39, plain, (k1_partfun1(X2,X3,X5,X6,X1,X4)=k5_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.42  cnf(c_0_40, negated_conjecture, (k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0)=k6_relat_1(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34]), c_0_35]), c_0_36]), c_0_37])])).
% 0.20/0.42  fof(c_0_41, plain, ![X14]:(v1_relat_1(k6_relat_1(X14))&v2_funct_1(k6_relat_1(X14))), inference(variable_rename,[status(thm)],[fc4_funct_1])).
% 0.20/0.42  cnf(c_0_42, plain, (X2=k1_xboole_0|k5_relat_1(k2_funct_1(X1),X1)=k6_relat_1(X2)|k2_relset_1(X3,X2,X1)!=X2|~v1_funct_1(X1)|~v2_funct_1(X1)|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(rw,[status(thm)],[c_0_38, c_0_24])).
% 0.20/0.42  cnf(c_0_43, negated_conjecture, (v1_funct_2(esk4_0,esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.42  cnf(c_0_44, negated_conjecture, (esk1_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.42  fof(c_0_45, plain, ![X45, X46, X47, X48, X49]:(((v2_funct_1(X48)|X47=k1_xboole_0|(~v2_funct_1(k1_partfun1(X45,X46,X46,X47,X48,X49))|k2_relset_1(X45,X46,X48)!=X46)|(~v1_funct_1(X49)|~v1_funct_2(X49,X46,X47)|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X46,X47))))|(~v1_funct_1(X48)|~v1_funct_2(X48,X45,X46)|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))))&(v2_funct_1(X49)|X47=k1_xboole_0|(~v2_funct_1(k1_partfun1(X45,X46,X46,X47,X48,X49))|k2_relset_1(X45,X46,X48)!=X46)|(~v1_funct_1(X49)|~v1_funct_2(X49,X46,X47)|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X46,X47))))|(~v1_funct_1(X48)|~v1_funct_2(X48,X45,X46)|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X45,X46))))))&((v2_funct_1(X48)|X46!=k1_xboole_0|(~v2_funct_1(k1_partfun1(X45,X46,X46,X47,X48,X49))|k2_relset_1(X45,X46,X48)!=X46)|(~v1_funct_1(X49)|~v1_funct_2(X49,X46,X47)|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X46,X47))))|(~v1_funct_1(X48)|~v1_funct_2(X48,X45,X46)|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))))&(v2_funct_1(X49)|X46!=k1_xboole_0|(~v2_funct_1(k1_partfun1(X45,X46,X46,X47,X48,X49))|k2_relset_1(X45,X46,X48)!=X46)|(~v1_funct_1(X49)|~v1_funct_2(X49,X46,X47)|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X46,X47))))|(~v1_funct_1(X48)|~v1_funct_2(X48,X45,X46)|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X45,X46))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_funct_2])])])])).
% 0.20/0.42  cnf(c_0_46, negated_conjecture, (k6_relat_1(esk1_0)=k5_relat_1(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_34]), c_0_35]), c_0_36]), c_0_37])])).
% 0.20/0.42  cnf(c_0_47, plain, (v2_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.42  fof(c_0_48, plain, ![X41, X42, X43, X44]:(~v1_funct_1(X43)|~v1_funct_2(X43,X41,X42)|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))|(~v1_funct_1(X44)|~v1_funct_2(X44,X42,X41)|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X41)))|(~r2_relset_1(X42,X42,k1_partfun1(X42,X41,X41,X42,X44,X43),k6_partfun1(X42))|k2_relset_1(X41,X42,X43)=X42))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_funct_2])])])).
% 0.20/0.42  cnf(c_0_49, negated_conjecture, (k5_relat_1(k2_funct_1(esk4_0),esk4_0)=k6_relat_1(esk1_0)|k2_relset_1(esk2_0,esk1_0,esk4_0)!=esk1_0|~v2_funct_1(esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_34]), c_0_43]), c_0_36])]), c_0_44])).
% 0.20/0.42  cnf(c_0_50, plain, (v2_funct_1(X1)|X2=k1_xboole_0|~v2_funct_1(k1_partfun1(X3,X4,X4,X2,X5,X1))|k2_relset_1(X3,X4,X5)!=X4|~v1_funct_1(X1)|~v1_funct_2(X1,X4,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|~v1_funct_1(X5)|~v1_funct_2(X5,X3,X4)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.20/0.42  cnf(c_0_51, negated_conjecture, (k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0)=k5_relat_1(esk3_0,esk4_0)), inference(rw,[status(thm)],[c_0_40, c_0_46])).
% 0.20/0.42  cnf(c_0_52, negated_conjecture, (k2_relset_1(esk1_0,esk2_0,esk3_0)=esk2_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.42  cnf(c_0_53, negated_conjecture, (v1_funct_2(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.42  cnf(c_0_54, negated_conjecture, (v2_funct_1(k5_relat_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_47, c_0_46])).
% 0.20/0.42  cnf(c_0_55, plain, (k2_relset_1(X2,X3,X1)=X3|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~v1_funct_2(X4,X3,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~r2_relset_1(X3,X3,k1_partfun1(X3,X2,X2,X3,X4,X1),k6_partfun1(X3))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.20/0.42  cnf(c_0_56, negated_conjecture, (r2_relset_1(esk1_0,esk1_0,k6_relat_1(esk1_0),k6_relat_1(esk1_0))), inference(rw,[status(thm)],[c_0_27, c_0_40])).
% 0.20/0.42  cnf(c_0_57, plain, (k5_relat_1(X1,k2_funct_1(X1))=k6_partfun1(X2)|X3=k1_xboole_0|k2_relset_1(X2,X3,X1)!=X3|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.42  cnf(c_0_58, negated_conjecture, (k5_relat_1(k2_funct_1(esk4_0),esk4_0)=k5_relat_1(esk3_0,esk4_0)|k2_relset_1(esk2_0,esk1_0,esk4_0)!=esk1_0|~v2_funct_1(esk4_0)), inference(rw,[status(thm)],[c_0_49, c_0_46])).
% 0.20/0.42  cnf(c_0_59, negated_conjecture, (v2_funct_1(esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52]), c_0_53]), c_0_43]), c_0_35]), c_0_34]), c_0_54]), c_0_37]), c_0_36])]), c_0_44])).
% 0.20/0.42  cnf(c_0_60, plain, (k2_relset_1(X2,X3,X1)=X3|~v1_funct_1(X4)|~v1_funct_1(X1)|~v1_funct_2(X4,X3,X2)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_relset_1(X3,X3,k1_partfun1(X3,X2,X2,X3,X4,X1),k6_relat_1(X3))), inference(rw,[status(thm)],[c_0_55, c_0_24])).
% 0.20/0.42  cnf(c_0_61, negated_conjecture, (r2_relset_1(esk1_0,esk1_0,k5_relat_1(esk3_0,esk4_0),k5_relat_1(esk3_0,esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_46]), c_0_46])).
% 0.20/0.42  fof(c_0_62, plain, ![X17, X18, X19]:(~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))|v1_relat_1(X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.20/0.42  cnf(c_0_63, plain, (X3=k1_xboole_0|k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(X2)|k2_relset_1(X2,X3,X1)!=X3|~v1_funct_1(X1)|~v2_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(rw,[status(thm)],[c_0_57, c_0_24])).
% 0.20/0.42  fof(c_0_64, plain, ![X7, X8, X9]:(~v1_relat_1(X7)|(~v1_relat_1(X8)|(~v1_relat_1(X9)|k5_relat_1(k5_relat_1(X7,X8),X9)=k5_relat_1(X7,k5_relat_1(X8,X9))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_relat_1])])])).
% 0.20/0.42  cnf(c_0_65, negated_conjecture, (k5_relat_1(k2_funct_1(esk4_0),esk4_0)=k5_relat_1(esk3_0,esk4_0)|k2_relset_1(esk2_0,esk1_0,esk4_0)!=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_59])])).
% 0.20/0.42  cnf(c_0_66, negated_conjecture, (k2_relset_1(esk2_0,esk1_0,esk4_0)=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_51]), c_0_53]), c_0_43]), c_0_46]), c_0_61]), c_0_35]), c_0_34]), c_0_37]), c_0_36])])).
% 0.20/0.42  cnf(c_0_67, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.20/0.42  cnf(c_0_68, negated_conjecture, (k5_relat_1(esk4_0,k2_funct_1(esk4_0))=k6_relat_1(esk2_0)|k2_relset_1(esk2_0,esk1_0,esk4_0)!=esk1_0|~v2_funct_1(esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_34]), c_0_43]), c_0_36])]), c_0_44])).
% 0.20/0.42  cnf(c_0_69, plain, (k5_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(X1,k5_relat_1(X2,X3))|~v1_relat_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.20/0.42  cnf(c_0_70, negated_conjecture, (k5_relat_1(k2_funct_1(esk4_0),esk4_0)=k5_relat_1(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_66])])).
% 0.20/0.42  cnf(c_0_71, negated_conjecture, (v1_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_67, c_0_34])).
% 0.20/0.42  cnf(c_0_72, negated_conjecture, (k5_relat_1(esk4_0,k2_funct_1(esk4_0))=k6_relat_1(esk2_0)|k2_relset_1(esk2_0,esk1_0,esk4_0)!=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_59])])).
% 0.20/0.42  fof(c_0_73, plain, ![X20, X21, X22]:(~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))|k2_relset_1(X20,X21,X22)=k2_relat_1(X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.20/0.42  cnf(c_0_74, negated_conjecture, (k5_relat_1(k2_funct_1(esk4_0),k5_relat_1(esk4_0,X1))=k5_relat_1(k5_relat_1(esk3_0,esk4_0),X1)|~v1_relat_1(k2_funct_1(esk4_0))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_71])])).
% 0.20/0.42  cnf(c_0_75, negated_conjecture, (k5_relat_1(esk4_0,k2_funct_1(esk4_0))=k6_relat_1(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_72, c_0_66])])).
% 0.20/0.42  fof(c_0_76, plain, ![X12]:(~v1_relat_1(X12)|k5_relat_1(X12,k6_relat_1(k2_relat_1(X12)))=X12), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_relat_1])])).
% 0.20/0.42  fof(c_0_77, plain, ![X10]:(k1_relat_1(k6_relat_1(X10))=X10&k2_relat_1(k6_relat_1(X10))=X10), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.20/0.42  cnf(c_0_78, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.20/0.42  cnf(c_0_79, negated_conjecture, (k5_relat_1(k5_relat_1(esk3_0,esk4_0),k2_funct_1(esk4_0))=k5_relat_1(k2_funct_1(esk4_0),k6_relat_1(esk2_0))|~v1_relat_1(k2_funct_1(esk4_0))), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.20/0.42  cnf(c_0_80, negated_conjecture, (v1_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_67, c_0_35])).
% 0.20/0.42  cnf(c_0_81, plain, (k5_relat_1(X1,k6_relat_1(k2_relat_1(X1)))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.20/0.42  cnf(c_0_82, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.20/0.42  cnf(c_0_83, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.42  cnf(c_0_84, plain, (k2_relset_1(X1,X2,X3)=k2_relset_1(X4,X5,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))), inference(spm,[status(thm)],[c_0_78, c_0_78])).
% 0.20/0.42  cnf(c_0_85, negated_conjecture, (k5_relat_1(esk4_0,k5_relat_1(k2_funct_1(esk4_0),X1))=k5_relat_1(k6_relat_1(esk2_0),X1)|~v1_relat_1(k2_funct_1(esk4_0))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_75]), c_0_71])])).
% 0.20/0.42  cnf(c_0_86, negated_conjecture, (k5_relat_1(k2_funct_1(esk4_0),k6_relat_1(esk2_0))=k5_relat_1(esk3_0,k6_relat_1(esk2_0))|~v1_relat_1(k2_funct_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_79]), c_0_75]), c_0_71]), c_0_80])])).
% 0.20/0.42  cnf(c_0_87, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X1))=k6_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_83])])).
% 0.20/0.42  cnf(c_0_88, plain, (k5_relat_1(X1,k6_relat_1(k2_relset_1(X2,X3,X1)))=X1|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_78]), c_0_67])).
% 0.20/0.42  fof(c_0_89, plain, ![X11]:(~v1_relat_1(X11)|k5_relat_1(k6_relat_1(k1_relat_1(X11)),X11)=X11), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_relat_1])])).
% 0.20/0.42  fof(c_0_90, plain, ![X15]:((k2_relat_1(X15)=k1_relat_1(k2_funct_1(X15))|~v2_funct_1(X15)|(~v1_relat_1(X15)|~v1_funct_1(X15)))&(k1_relat_1(X15)=k2_relat_1(k2_funct_1(X15))|~v2_funct_1(X15)|(~v1_relat_1(X15)|~v1_funct_1(X15)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).
% 0.20/0.42  fof(c_0_91, plain, ![X13]:((v1_relat_1(k2_funct_1(X13))|(~v1_relat_1(X13)|~v1_funct_1(X13)))&(v1_funct_1(k2_funct_1(X13))|(~v1_relat_1(X13)|~v1_funct_1(X13)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 0.20/0.42  cnf(c_0_92, negated_conjecture, (k2_relset_1(X1,X2,esk4_0)=esk1_0|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_84]), c_0_34])])).
% 0.20/0.42  cnf(c_0_93, negated_conjecture, (k5_relat_1(esk4_0,k5_relat_1(esk3_0,k6_relat_1(esk2_0)))=k6_relat_1(esk2_0)|~v1_relat_1(k2_funct_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_87]), c_0_83])])).
% 0.20/0.42  cnf(c_0_94, negated_conjecture, (k5_relat_1(esk3_0,k6_relat_1(esk2_0))=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_52]), c_0_35])])).
% 0.20/0.42  cnf(c_0_95, plain, (k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1)=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_89])).
% 0.20/0.42  cnf(c_0_96, plain, (k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_90])).
% 0.20/0.42  cnf(c_0_97, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_91])).
% 0.20/0.42  cnf(c_0_98, negated_conjecture, (k2_relat_1(esk4_0)=esk1_0|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_78, c_0_92])).
% 0.20/0.42  cnf(c_0_99, negated_conjecture, (k6_relat_1(esk2_0)=k5_relat_1(esk4_0,esk3_0)|~v1_relat_1(k2_funct_1(esk4_0))), inference(rw,[status(thm)],[c_0_93, c_0_94])).
% 0.20/0.42  cnf(c_0_100, plain, (k5_relat_1(k6_relat_1(k2_relat_1(X1)),k2_funct_1(X1))=k2_funct_1(X1)|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_96]), c_0_97])).
% 0.20/0.42  cnf(c_0_101, negated_conjecture, (k2_relat_1(esk4_0)=esk1_0), inference(spm,[status(thm)],[c_0_98, c_0_34])).
% 0.20/0.42  cnf(c_0_102, negated_conjecture, (k6_relat_1(esk2_0)=k5_relat_1(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_97]), c_0_36]), c_0_71])])).
% 0.20/0.42  cnf(c_0_103, negated_conjecture, (k5_relat_1(k5_relat_1(esk3_0,esk4_0),k2_funct_1(esk4_0))=k2_funct_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_101]), c_0_46]), c_0_59]), c_0_36]), c_0_71])])).
% 0.20/0.42  cnf(c_0_104, negated_conjecture, (k5_relat_1(esk3_0,k5_relat_1(esk4_0,esk3_0))=esk3_0), inference(rw,[status(thm)],[c_0_94, c_0_102])).
% 0.20/0.42  cnf(c_0_105, negated_conjecture, (v2_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.42  cnf(c_0_106, negated_conjecture, (esk2_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.42  cnf(c_0_107, negated_conjecture, (k2_funct_1(esk4_0)=esk3_0|~v1_relat_1(k2_funct_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_103]), c_0_75]), c_0_102]), c_0_104]), c_0_71]), c_0_80])])).
% 0.20/0.42  cnf(c_0_108, negated_conjecture, (k5_relat_1(k2_funct_1(esk3_0),esk3_0)=k6_relat_1(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_35]), c_0_52]), c_0_53]), c_0_105]), c_0_37])]), c_0_106])).
% 0.20/0.42  cnf(c_0_109, plain, (k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_90])).
% 0.20/0.42  cnf(c_0_110, negated_conjecture, (k2_funct_1(esk4_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_97]), c_0_36]), c_0_71])])).
% 0.20/0.42  cnf(c_0_111, negated_conjecture, (k5_relat_1(k6_relat_1(esk2_0),esk4_0)=k5_relat_1(esk4_0,k5_relat_1(esk3_0,esk4_0))|~v1_relat_1(k2_funct_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_70]), c_0_71])])).
% 0.20/0.42  cnf(c_0_112, negated_conjecture, (k5_relat_1(esk4_0,k5_relat_1(esk3_0,esk4_0))=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_66]), c_0_46]), c_0_34])])).
% 0.20/0.42  cnf(c_0_113, negated_conjecture, (k5_relat_1(k2_funct_1(esk3_0),k5_relat_1(esk3_0,X1))=k5_relat_1(k6_relat_1(esk2_0),X1)|~v1_relat_1(k2_funct_1(esk3_0))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_108]), c_0_80])])).
% 0.20/0.42  cnf(c_0_114, plain, (k5_relat_1(k2_funct_1(X1),k6_relat_1(k1_relat_1(X1)))=k2_funct_1(X1)|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_109]), c_0_97])).
% 0.20/0.42  cnf(c_0_115, negated_conjecture, (k1_relat_1(esk3_0)=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_110]), c_0_101]), c_0_59]), c_0_36]), c_0_71])])).
% 0.20/0.42  cnf(c_0_116, negated_conjecture, (k5_relat_1(k5_relat_1(esk4_0,esk3_0),esk4_0)=esk4_0|~v1_relat_1(k2_funct_1(esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_111, c_0_102]), c_0_112])).
% 0.20/0.42  cnf(c_0_117, negated_conjecture, (k5_relat_1(k2_funct_1(esk3_0),k5_relat_1(esk3_0,X1))=k5_relat_1(k5_relat_1(esk4_0,esk3_0),X1)|~v1_relat_1(k2_funct_1(esk3_0))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_113, c_0_102])).
% 0.20/0.42  cnf(c_0_118, negated_conjecture, (k5_relat_1(k2_funct_1(esk3_0),k5_relat_1(esk3_0,esk4_0))=k2_funct_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_115]), c_0_46]), c_0_105]), c_0_37]), c_0_80])])).
% 0.20/0.42  cnf(c_0_119, negated_conjecture, (k5_relat_1(k5_relat_1(esk4_0,esk3_0),esk4_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_116, c_0_110]), c_0_80])])).
% 0.20/0.42  cnf(c_0_120, negated_conjecture, (esk4_0!=k2_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.42  cnf(c_0_121, negated_conjecture, (~v1_relat_1(k2_funct_1(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_118]), c_0_119]), c_0_71])]), c_0_120])).
% 0.20/0.42  cnf(c_0_122, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121, c_0_97]), c_0_37]), c_0_80])]), ['proof']).
% 0.20/0.42  # SZS output end CNFRefutation
% 0.20/0.42  # Proof object total steps             : 123
% 0.20/0.42  # Proof object clause steps            : 86
% 0.20/0.42  # Proof object formula steps           : 37
% 0.20/0.42  # Proof object conjectures             : 60
% 0.20/0.42  # Proof object clause conjectures      : 57
% 0.20/0.42  # Proof object formula conjectures     : 3
% 0.20/0.42  # Proof object initial clauses used    : 32
% 0.20/0.42  # Proof object initial formulas used   : 18
% 0.20/0.42  # Proof object generating inferences   : 36
% 0.20/0.42  # Proof object simplifying inferences  : 132
% 0.20/0.42  # Training examples: 0 positive, 0 negative
% 0.20/0.42  # Parsed axioms                        : 19
% 0.20/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.42  # Initial clauses                      : 42
% 0.20/0.42  # Removed in clause preprocessing      : 1
% 0.20/0.42  # Initial clauses in saturation        : 41
% 0.20/0.42  # Processed clauses                    : 511
% 0.20/0.42  # ...of these trivial                  : 28
% 0.20/0.42  # ...subsumed                          : 176
% 0.20/0.42  # ...remaining for further processing  : 307
% 0.20/0.42  # Other redundant clauses eliminated   : 3
% 0.20/0.42  # Clauses deleted for lack of memory   : 0
% 0.20/0.42  # Backward-subsumed                    : 10
% 0.20/0.42  # Backward-rewritten                   : 128
% 0.20/0.42  # Generated clauses                    : 1286
% 0.20/0.42  # ...of the previous two non-trivial   : 1099
% 0.20/0.42  # Contextual simplify-reflections      : 13
% 0.20/0.42  # Paramodulations                      : 1283
% 0.20/0.42  # Factorizations                       : 0
% 0.20/0.42  # Equation resolutions                 : 3
% 0.20/0.42  # Propositional unsat checks           : 0
% 0.20/0.42  #    Propositional check models        : 0
% 0.20/0.42  #    Propositional check unsatisfiable : 0
% 0.20/0.42  #    Propositional clauses             : 0
% 0.20/0.42  #    Propositional clauses after purity: 0
% 0.20/0.42  #    Propositional unsat core size     : 0
% 0.20/0.42  #    Propositional preprocessing time  : 0.000
% 0.20/0.42  #    Propositional encoding time       : 0.000
% 0.20/0.42  #    Propositional solver time         : 0.000
% 0.20/0.42  #    Success case prop preproc time    : 0.000
% 0.20/0.42  #    Success case prop encoding time   : 0.000
% 0.20/0.42  #    Success case prop solver time     : 0.000
% 0.20/0.42  # Current number of processed clauses  : 125
% 0.20/0.42  #    Positive orientable unit clauses  : 52
% 0.20/0.42  #    Positive unorientable unit clauses: 0
% 0.20/0.42  #    Negative unit clauses             : 4
% 0.20/0.42  #    Non-unit-clauses                  : 69
% 0.20/0.42  # Current number of unprocessed clauses: 648
% 0.20/0.42  # ...number of literals in the above   : 2551
% 0.20/0.42  # Current number of archived formulas  : 0
% 0.20/0.42  # Current number of archived clauses   : 180
% 0.20/0.42  # Clause-clause subsumption calls (NU) : 3247
% 0.20/0.42  # Rec. Clause-clause subsumption calls : 2136
% 0.20/0.42  # Non-unit clause-clause subsumptions  : 194
% 0.20/0.42  # Unit Clause-clause subsumption calls : 373
% 0.20/0.42  # Rewrite failures with RHS unbound    : 0
% 0.20/0.42  # BW rewrite match attempts            : 26
% 0.20/0.42  # BW rewrite match successes           : 22
% 0.20/0.42  # Condensation attempts                : 0
% 0.20/0.42  # Condensation successes               : 0
% 0.20/0.42  # Termbank termtop insertions          : 33533
% 0.20/0.42  
% 0.20/0.42  # -------------------------------------------------
% 0.20/0.42  # User time                : 0.073 s
% 0.20/0.42  # System time              : 0.003 s
% 0.20/0.42  # Total time               : 0.077 s
% 0.20/0.42  # Maximum resident set size: 1604 pages
%------------------------------------------------------------------------------

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
% DateTime   : Thu Dec  3 11:03:08 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :  144 (7168 expanded)
%              Number of clauses        :   99 (2547 expanded)
%              Number of leaves         :   22 (1805 expanded)
%              Depth                    :   24
%              Number of atoms          :  481 (46898 expanded)
%              Number of equality atoms :  152 (14717 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal clause size      :   40 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t58_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k1_relat_1(k5_relat_1(X1,k2_funct_1(X1))) = k1_relat_1(X1)
          & k2_relat_1(k5_relat_1(X1,k2_funct_1(X1))) = k1_relat_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(t55_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => k5_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(X1,k5_relat_1(X2,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

fof(t78_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

fof(dt_k6_partfun1,axiom,(
    ! [X1] :
      ( v1_partfun1(k6_partfun1(X1),X1)
      & m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(t79_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k2_relat_1(X2),X1)
       => k5_relat_1(X2,k6_relat_1(X1)) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(redefinition_r2_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_relset_1(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(dt_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => ( v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))
        & m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(redefinition_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k1_partfun1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(t52_funct_1,axiom,(
    ! [X1] : v2_funct_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_funct_2)).

fof(t55_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
          & k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(c_0_22,plain,(
    ! [X60,X61,X62] :
      ( ( k5_relat_1(X62,k2_funct_1(X62)) = k6_partfun1(X60)
        | X61 = k1_xboole_0
        | k2_relset_1(X60,X61,X62) != X61
        | ~ v2_funct_1(X62)
        | ~ v1_funct_1(X62)
        | ~ v1_funct_2(X62,X60,X61)
        | ~ m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X60,X61))) )
      & ( k5_relat_1(k2_funct_1(X62),X62) = k6_partfun1(X61)
        | X61 = k1_xboole_0
        | k2_relset_1(X60,X61,X62) != X61
        | ~ v2_funct_1(X62)
        | ~ v1_funct_1(X62)
        | ~ v1_funct_2(X62,X60,X61)
        | ~ m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X60,X61))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_funct_2])])])).

fof(c_0_23,plain,(
    ! [X50] : k6_partfun1(X50) = k6_relat_1(X50) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

fof(c_0_24,negated_conjecture,(
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

cnf(c_0_25,plain,
    ( k5_relat_1(X1,k2_funct_1(X1)) = k6_partfun1(X2)
    | X3 = k1_xboole_0
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_26,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_27,negated_conjecture,
    ( v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,esk2_0,esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))
    & v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,esk3_0,esk2_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))
    & k2_relset_1(esk2_0,esk3_0,esk4_0) = esk3_0
    & r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,esk5_0),k6_partfun1(esk2_0))
    & v2_funct_1(esk4_0)
    & esk2_0 != k1_xboole_0
    & esk3_0 != k1_xboole_0
    & esk5_0 != k2_funct_1(esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).

fof(c_0_28,plain,(
    ! [X27,X28,X29] :
      ( ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))
      | v1_relat_1(X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_29,plain,(
    ! [X25] :
      ( ( k1_relat_1(k5_relat_1(X25,k2_funct_1(X25))) = k1_relat_1(X25)
        | ~ v2_funct_1(X25)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) )
      & ( k2_relat_1(k5_relat_1(X25,k2_funct_1(X25))) = k1_relat_1(X25)
        | ~ v2_funct_1(X25)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t58_funct_1])])])).

cnf(c_0_30,plain,
    ( X3 = k1_xboole_0
    | k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(X2)
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( k2_relset_1(esk2_0,esk3_0,esk4_0) = esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( v1_funct_2(esk4_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( v2_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_37,plain,(
    ! [X18] :
      ( k1_relat_1(k6_relat_1(X18)) = X18
      & k2_relat_1(k6_relat_1(X18)) = X18 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

cnf(c_0_38,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_39,plain,(
    ! [X15,X16,X17] :
      ( ~ v1_relat_1(X15)
      | ~ v1_relat_1(X16)
      | ~ v1_relat_1(X17)
      | k5_relat_1(k5_relat_1(X15,X16),X17) = k5_relat_1(X15,k5_relat_1(X16,X17)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_relat_1])])])).

cnf(c_0_40,plain,
    ( k5_relat_1(k2_funct_1(X1),X1) = k6_partfun1(X2)
    | X2 = k1_xboole_0
    | k2_relset_1(X3,X2,X1) != X2
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_41,plain,(
    ! [X19] :
      ( ~ v1_relat_1(X19)
      | k5_relat_1(k6_relat_1(k1_relat_1(X19)),X19) = X19 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_relat_1])])).

cnf(c_0_42,plain,
    ( k1_relat_1(k5_relat_1(X1,k2_funct_1(X1))) = k1_relat_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_43,negated_conjecture,
    ( k5_relat_1(esk4_0,k2_funct_1(esk4_0)) = k6_relat_1(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_44,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_45,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_31])).

fof(c_0_46,plain,(
    ! [X43] :
      ( v1_partfun1(k6_partfun1(X43),X43)
      & m1_subset_1(k6_partfun1(X43),k1_zfmisc_1(k2_zfmisc_1(X43,X43))) ) ),
    inference(variable_rename,[status(thm)],[dt_k6_partfun1])).

cnf(c_0_47,plain,
    ( k5_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(X1,k5_relat_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_48,plain,
    ( X2 = k1_xboole_0
    | k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(X2)
    | k2_relset_1(X3,X2,X1) != X2
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(rw,[status(thm)],[c_0_40,c_0_26])).

cnf(c_0_49,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_50,negated_conjecture,
    ( k1_relat_1(esk4_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44]),c_0_34]),c_0_35]),c_0_45])])).

cnf(c_0_51,plain,
    ( m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( k5_relat_1(esk4_0,k5_relat_1(k2_funct_1(esk4_0),X1)) = k5_relat_1(k6_relat_1(esk2_0),X1)
    | ~ v1_relat_1(k2_funct_1(esk4_0))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_43]),c_0_45])])).

cnf(c_0_53,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk4_0),esk4_0) = k6_relat_1(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_54,negated_conjecture,
    ( k5_relat_1(k6_relat_1(esk2_0),esk4_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_45])])).

cnf(c_0_55,plain,
    ( m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(rw,[status(thm)],[c_0_51,c_0_26])).

fof(c_0_56,plain,(
    ! [X20,X21] :
      ( ~ v1_relat_1(X21)
      | ~ r1_tarski(k2_relat_1(X21),X20)
      | k5_relat_1(X21,k6_relat_1(X20)) = X21 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_relat_1])])).

fof(c_0_57,plain,(
    ! [X13,X14] :
      ( ( ~ m1_subset_1(X13,k1_zfmisc_1(X14))
        | r1_tarski(X13,X14) )
      & ( ~ r1_tarski(X13,X14)
        | m1_subset_1(X13,k1_zfmisc_1(X14)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_58,plain,(
    ! [X33,X34,X35,X36] :
      ( ( ~ r2_relset_1(X33,X34,X35,X36)
        | X35 = X36
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X33,X34))) )
      & ( X35 != X36
        | r2_relset_1(X33,X34,X35,X36)
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X33,X34))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).

cnf(c_0_59,negated_conjecture,
    ( r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,esk5_0),k6_partfun1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_60,negated_conjecture,
    ( k5_relat_1(esk4_0,k6_relat_1(esk3_0)) = esk4_0
    | ~ v1_relat_1(k2_funct_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54]),c_0_45])])).

cnf(c_0_61,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_55])).

cnf(c_0_62,plain,
    ( k5_relat_1(X1,k6_relat_1(X2)) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_63,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_64,plain,
    ( X3 = X4
    | ~ r2_relset_1(X1,X2,X3,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_65,negated_conjecture,
    ( r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,esk5_0),k6_relat_1(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_59,c_0_26])).

fof(c_0_66,plain,(
    ! [X37,X38,X39,X40,X41,X42] :
      ( ( v1_funct_1(k1_partfun1(X37,X38,X39,X40,X41,X42))
        | ~ v1_funct_1(X41)
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))
        | ~ v1_funct_1(X42)
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X39,X40))) )
      & ( m1_subset_1(k1_partfun1(X37,X38,X39,X40,X41,X42),k1_zfmisc_1(k2_zfmisc_1(X37,X40)))
        | ~ v1_funct_1(X41)
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))
        | ~ v1_funct_1(X42)
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X39,X40))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).

cnf(c_0_67,negated_conjecture,
    ( k5_relat_1(esk4_0,k5_relat_1(k6_relat_1(esk3_0),X1)) = k5_relat_1(esk4_0,X1)
    | ~ v1_relat_1(k2_funct_1(esk4_0))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_60]),c_0_61]),c_0_45])])).

cnf(c_0_68,plain,
    ( k5_relat_1(X1,k6_relat_1(X2)) = X1
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(k2_relat_1(X1),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_69,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_70,plain,(
    ! [X44,X45,X46,X47,X48,X49] :
      ( ~ v1_funct_1(X48)
      | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))
      | ~ v1_funct_1(X49)
      | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X46,X47)))
      | k1_partfun1(X44,X45,X46,X47,X48,X49) = k5_relat_1(X48,X49) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).

cnf(c_0_71,negated_conjecture,
    ( k1_partfun1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,esk5_0) = k6_relat_1(esk2_0)
    | ~ m1_subset_1(k1_partfun1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_55])])).

cnf(c_0_72,plain,
    ( m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X6)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_73,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_74,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_75,negated_conjecture,
    ( k5_relat_1(esk4_0,k6_relat_1(esk3_0)) = k5_relat_1(esk4_0,k6_relat_1(X1))
    | ~ v1_relat_1(k2_funct_1(esk4_0))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_61]),c_0_61]),c_0_69])])).

fof(c_0_76,plain,(
    ! [X51,X52,X53,X54] :
      ( ~ v1_funct_1(X53)
      | ~ v1_funct_2(X53,X51,X52)
      | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))
      | ~ v1_funct_1(X54)
      | ~ v1_funct_2(X54,X52,X51)
      | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X51)))
      | ~ r2_relset_1(X52,X52,k1_partfun1(X52,X51,X51,X52,X54,X53),k6_partfun1(X52))
      | k2_relset_1(X51,X52,X53) = X52 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_funct_2])])])).

cnf(c_0_77,plain,
    ( k1_partfun1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_78,negated_conjecture,
    ( k1_partfun1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,esk5_0) = k6_relat_1(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_73]),c_0_35]),c_0_74]),c_0_31])])).

cnf(c_0_79,negated_conjecture,
    ( k5_relat_1(esk4_0,k6_relat_1(X1)) = esk4_0
    | ~ v1_relat_1(k2_funct_1(esk4_0))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_75])).

cnf(c_0_80,plain,
    ( k2_relset_1(X2,X3,X1) = X3
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X3,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ r2_relset_1(X3,X3,k1_partfun1(X3,X2,X2,X3,X4,X1),k6_partfun1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_81,negated_conjecture,
    ( k6_relat_1(esk2_0) = k5_relat_1(esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_73]),c_0_35]),c_0_74]),c_0_31])])).

cnf(c_0_82,negated_conjecture,
    ( k5_relat_1(esk4_0,k5_relat_1(k6_relat_1(X1),X2)) = k5_relat_1(esk4_0,X2)
    | ~ v1_relat_1(k2_funct_1(esk4_0))
    | ~ v1_relat_1(X2)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_79]),c_0_61]),c_0_45])])).

fof(c_0_83,plain,(
    ! [X22] :
      ( ( v1_relat_1(k2_funct_1(X22))
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( v1_funct_1(k2_funct_1(X22))
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

fof(c_0_84,plain,(
    ! [X12] : m1_subset_1(k2_subset_1(X12),k1_zfmisc_1(X12)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_85,plain,(
    ! [X11] : k2_subset_1(X11) = X11 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_86,plain,
    ( k2_relset_1(X2,X3,X1) = X3
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X4,X3,X2)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_relset_1(X3,X3,k1_partfun1(X3,X2,X2,X3,X4,X1),k6_relat_1(X3)) ),
    inference(rw,[status(thm)],[c_0_80,c_0_26])).

cnf(c_0_87,negated_conjecture,
    ( k1_partfun1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,esk5_0) = k5_relat_1(esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_78,c_0_81])).

cnf(c_0_88,negated_conjecture,
    ( v1_funct_2(esk5_0,esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_89,plain,
    ( r2_relset_1(X3,X4,X1,X2)
    | X1 != X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

fof(c_0_90,plain,(
    ! [X30,X31,X32] :
      ( ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
      | k2_relset_1(X30,X31,X32) = k2_relat_1(X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_91,negated_conjecture,
    ( k5_relat_1(esk4_0,k6_relat_1(X1)) = k5_relat_1(esk4_0,k6_relat_1(X2))
    | ~ v1_relat_1(k2_funct_1(esk4_0))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_68]),c_0_61]),c_0_61]),c_0_69])])).

cnf(c_0_92,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_93,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_94,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_95,negated_conjecture,
    ( k2_relset_1(esk3_0,esk2_0,esk5_0) = esk2_0
    | ~ r2_relset_1(esk2_0,esk2_0,k5_relat_1(esk4_0,esk5_0),k5_relat_1(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_33]),c_0_88]),c_0_81]),c_0_35]),c_0_73]),c_0_31]),c_0_74])])).

cnf(c_0_96,plain,
    ( r2_relset_1(X1,X2,X3,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(er,[status(thm)],[c_0_89])).

cnf(c_0_97,negated_conjecture,
    ( m1_subset_1(k5_relat_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_81])).

cnf(c_0_98,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

fof(c_0_99,plain,(
    ! [X23] : v2_funct_1(k6_relat_1(X23)) ),
    inference(variable_rename,[status(thm)],[t52_funct_1])).

cnf(c_0_100,negated_conjecture,
    ( k5_relat_1(esk4_0,k6_relat_1(X1)) = k5_relat_1(esk4_0,k6_relat_1(X2))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_35]),c_0_45])])).

cnf(c_0_101,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_93,c_0_94])).

cnf(c_0_102,negated_conjecture,
    ( k2_relset_1(esk3_0,esk2_0,esk5_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_97])])).

cnf(c_0_103,plain,
    ( k2_relset_1(X1,X2,X3) = k2_relset_1(X4,X5,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) ),
    inference(spm,[status(thm)],[c_0_98,c_0_98])).

fof(c_0_104,plain,(
    ! [X55,X56,X57,X58,X59] :
      ( ( v2_funct_1(X58)
        | X57 = k1_xboole_0
        | ~ v2_funct_1(k1_partfun1(X55,X56,X56,X57,X58,X59))
        | k2_relset_1(X55,X56,X58) != X56
        | ~ v1_funct_1(X59)
        | ~ v1_funct_2(X59,X56,X57)
        | ~ m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X56,X57)))
        | ~ v1_funct_1(X58)
        | ~ v1_funct_2(X58,X55,X56)
        | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X55,X56))) )
      & ( v2_funct_1(X59)
        | X57 = k1_xboole_0
        | ~ v2_funct_1(k1_partfun1(X55,X56,X56,X57,X58,X59))
        | k2_relset_1(X55,X56,X58) != X56
        | ~ v1_funct_1(X59)
        | ~ v1_funct_2(X59,X56,X57)
        | ~ m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X56,X57)))
        | ~ v1_funct_1(X58)
        | ~ v1_funct_2(X58,X55,X56)
        | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X55,X56))) )
      & ( v2_funct_1(X58)
        | X56 != k1_xboole_0
        | ~ v2_funct_1(k1_partfun1(X55,X56,X56,X57,X58,X59))
        | k2_relset_1(X55,X56,X58) != X56
        | ~ v1_funct_1(X59)
        | ~ v1_funct_2(X59,X56,X57)
        | ~ m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X56,X57)))
        | ~ v1_funct_1(X58)
        | ~ v1_funct_2(X58,X55,X56)
        | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X55,X56))) )
      & ( v2_funct_1(X59)
        | X56 != k1_xboole_0
        | ~ v2_funct_1(k1_partfun1(X55,X56,X56,X57,X58,X59))
        | k2_relset_1(X55,X56,X58) != X56
        | ~ v1_funct_1(X59)
        | ~ v1_funct_2(X59,X56,X57)
        | ~ m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X56,X57)))
        | ~ v1_funct_1(X58)
        | ~ v1_funct_2(X58,X55,X56)
        | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X55,X56))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_funct_2])])])])).

cnf(c_0_105,plain,
    ( v2_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_99])).

cnf(c_0_106,negated_conjecture,
    ( k5_relat_1(esk4_0,k6_relat_1(esk3_0)) = k5_relat_1(esk4_0,k6_relat_1(X1))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_100,c_0_101])).

fof(c_0_107,plain,(
    ! [X24] :
      ( ( k2_relat_1(X24) = k1_relat_1(k2_funct_1(X24))
        | ~ v2_funct_1(X24)
        | ~ v1_relat_1(X24)
        | ~ v1_funct_1(X24) )
      & ( k1_relat_1(X24) = k2_relat_1(k2_funct_1(X24))
        | ~ v2_funct_1(X24)
        | ~ v1_relat_1(X24)
        | ~ v1_funct_1(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).

cnf(c_0_108,negated_conjecture,
    ( k2_relset_1(X1,X2,esk5_0) = esk2_0
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_103]),c_0_74])])).

cnf(c_0_109,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_110,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_104])).

cnf(c_0_111,negated_conjecture,
    ( v2_funct_1(k5_relat_1(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_105,c_0_81])).

cnf(c_0_112,negated_conjecture,
    ( k5_relat_1(esk4_0,k6_relat_1(esk3_0)) = esk4_0
    | ~ m1_subset_1(k2_relat_1(esk4_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_106]),c_0_45])])).

cnf(c_0_113,plain,
    ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_107])).

cnf(c_0_114,negated_conjecture,
    ( k2_relat_1(esk5_0) = esk2_0
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_98,c_0_108])).

cnf(c_0_115,negated_conjecture,
    ( k5_relat_1(esk5_0,k2_funct_1(esk5_0)) = k6_relat_1(esk3_0)
    | k2_relset_1(esk3_0,esk2_0,esk5_0) != esk2_0
    | ~ v2_funct_1(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_74]),c_0_88]),c_0_73])]),c_0_109])).

cnf(c_0_116,negated_conjecture,
    ( v2_funct_1(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_87]),c_0_32]),c_0_33]),c_0_88]),c_0_111]),c_0_35]),c_0_73]),c_0_31]),c_0_74])]),c_0_109])).

cnf(c_0_117,negated_conjecture,
    ( k5_relat_1(esk4_0,k6_relat_1(esk3_0)) = esk4_0
    | ~ m1_subset_1(k2_relset_1(X1,X2,esk4_0),k1_zfmisc_1(X3))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_112,c_0_98])).

cnf(c_0_118,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_74])).

cnf(c_0_119,plain,
    ( k5_relat_1(k6_relat_1(k2_relat_1(X1)),k2_funct_1(X1)) = k2_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_113]),c_0_92])).

cnf(c_0_120,negated_conjecture,
    ( k2_relat_1(esk5_0) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_114,c_0_74])).

cnf(c_0_121,negated_conjecture,
    ( k5_relat_1(esk5_0,k2_funct_1(esk5_0)) = k6_relat_1(esk3_0)
    | k2_relset_1(esk3_0,esk2_0,esk5_0) != esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_115,c_0_116])])).

cnf(c_0_122,negated_conjecture,
    ( k5_relat_1(esk4_0,k6_relat_1(esk3_0)) = esk4_0
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_32]),c_0_31])])).

cnf(c_0_123,negated_conjecture,
    ( k1_relat_1(esk5_0) = esk3_0
    | k2_relset_1(esk3_0,esk2_0,esk5_0) != esk2_0
    | ~ v2_funct_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_115]),c_0_44]),c_0_73]),c_0_118])])).

cnf(c_0_124,negated_conjecture,
    ( k5_relat_1(k5_relat_1(esk4_0,esk5_0),k2_funct_1(esk5_0)) = k2_funct_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_120]),c_0_81]),c_0_116]),c_0_73]),c_0_118])])).

cnf(c_0_125,negated_conjecture,
    ( k5_relat_1(esk5_0,k2_funct_1(esk5_0)) = k6_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_121,c_0_102])])).

cnf(c_0_126,negated_conjecture,
    ( k5_relat_1(esk4_0,k6_relat_1(esk3_0)) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_122,c_0_101])).

cnf(c_0_127,negated_conjecture,
    ( k1_relat_1(esk5_0) = esk3_0
    | k2_relset_1(esk3_0,esk2_0,esk5_0) != esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_123,c_0_116])])).

cnf(c_0_128,negated_conjecture,
    ( k2_funct_1(esk5_0) = esk4_0
    | ~ v1_relat_1(k2_funct_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_124]),c_0_125]),c_0_126]),c_0_118]),c_0_45])])).

cnf(c_0_129,negated_conjecture,
    ( k5_relat_1(esk5_0,k5_relat_1(k2_funct_1(esk5_0),X1)) = k5_relat_1(k6_relat_1(esk3_0),X1)
    | k2_relset_1(esk3_0,esk2_0,esk5_0) != esk2_0
    | ~ v2_funct_1(esk5_0)
    | ~ v1_relat_1(k2_funct_1(esk5_0))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_115]),c_0_118])])).

cnf(c_0_130,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk5_0),esk5_0) = k6_relat_1(esk2_0)
    | k2_relset_1(esk3_0,esk2_0,esk5_0) != esk2_0
    | ~ v2_funct_1(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_74]),c_0_88]),c_0_73])]),c_0_109])).

cnf(c_0_131,negated_conjecture,
    ( k1_relat_1(esk5_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_127,c_0_102])])).

cnf(c_0_132,plain,
    ( k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_107])).

cnf(c_0_133,negated_conjecture,
    ( k2_funct_1(esk5_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_92]),c_0_73]),c_0_118])])).

cnf(c_0_134,negated_conjecture,
    ( k5_relat_1(k6_relat_1(esk3_0),esk5_0) = k5_relat_1(esk5_0,k6_relat_1(esk2_0))
    | k2_relset_1(esk3_0,esk2_0,esk5_0) != esk2_0
    | ~ v2_funct_1(esk5_0)
    | ~ v1_relat_1(k2_funct_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129,c_0_130]),c_0_118])])).

cnf(c_0_135,negated_conjecture,
    ( k5_relat_1(k6_relat_1(esk3_0),esk5_0) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_131]),c_0_118])])).

cnf(c_0_136,negated_conjecture,
    ( k2_relat_1(esk4_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132,c_0_133]),c_0_131]),c_0_116]),c_0_73]),c_0_118])])).

cnf(c_0_137,negated_conjecture,
    ( k6_relat_1(esk3_0) = k5_relat_1(esk5_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_125,c_0_133])).

cnf(c_0_138,negated_conjecture,
    ( k5_relat_1(esk5_0,k5_relat_1(esk4_0,esk5_0)) = esk5_0
    | ~ v1_relat_1(k2_funct_1(esk5_0)) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_134,c_0_81]),c_0_102]),c_0_116])]),c_0_135])).

cnf(c_0_139,negated_conjecture,
    ( k5_relat_1(k5_relat_1(esk5_0,esk4_0),k2_funct_1(esk4_0)) = k2_funct_1(esk4_0) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_136]),c_0_34]),c_0_35]),c_0_45])]),c_0_137])).

cnf(c_0_140,negated_conjecture,
    ( k5_relat_1(esk5_0,k5_relat_1(esk4_0,esk5_0)) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_138,c_0_133]),c_0_45])])).

cnf(c_0_141,negated_conjecture,
    ( esk5_0 != k2_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_142,negated_conjecture,
    ( ~ v1_relat_1(k2_funct_1(esk4_0)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_139]),c_0_43]),c_0_81]),c_0_45]),c_0_118])]),c_0_140]),c_0_141])).

cnf(c_0_143,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_142,c_0_92]),c_0_35]),c_0_45])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:29:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.12/0.40  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.12/0.40  #
% 0.12/0.40  # Preprocessing time       : 0.030 s
% 0.12/0.40  # Presaturation interreduction done
% 0.12/0.40  
% 0.12/0.40  # Proof found!
% 0.12/0.40  # SZS status Theorem
% 0.12/0.40  # SZS output start CNFRefutation
% 0.12/0.40  fof(t35_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((k2_relset_1(X1,X2,X3)=X2&v2_funct_1(X3))=>(X2=k1_xboole_0|(k5_relat_1(X3,k2_funct_1(X3))=k6_partfun1(X1)&k5_relat_1(k2_funct_1(X3),X3)=k6_partfun1(X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_2)).
% 0.12/0.40  fof(redefinition_k6_partfun1, axiom, ![X1]:k6_partfun1(X1)=k6_relat_1(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 0.12/0.40  fof(t36_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(((k2_relset_1(X1,X2,X3)=X2&r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1)))&v2_funct_1(X3))=>(X1=k1_xboole_0|X2=k1_xboole_0|X4=k2_funct_1(X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 0.12/0.40  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.12/0.40  fof(t58_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k1_relat_1(k5_relat_1(X1,k2_funct_1(X1)))=k1_relat_1(X1)&k2_relat_1(k5_relat_1(X1,k2_funct_1(X1)))=k1_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_funct_1)).
% 0.12/0.40  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 0.12/0.40  fof(t55_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>k5_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(X1,k5_relat_1(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 0.12/0.40  fof(t78_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_relat_1)).
% 0.12/0.40  fof(dt_k6_partfun1, axiom, ![X1]:(v1_partfun1(k6_partfun1(X1),X1)&m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 0.12/0.40  fof(t79_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k2_relat_1(X2),X1)=>k5_relat_1(X2,k6_relat_1(X1))=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 0.12/0.40  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.12/0.40  fof(redefinition_r2_relset_1, axiom, ![X1, X2, X3, X4]:((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_relset_1(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 0.12/0.40  fof(dt_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>(v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))&m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 0.12/0.40  fof(redefinition_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>k1_partfun1(X1,X2,X3,X4,X5,X6)=k5_relat_1(X5,X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 0.12/0.40  fof(t24_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(r2_relset_1(X2,X2,k1_partfun1(X2,X1,X1,X2,X4,X3),k6_partfun1(X2))=>k2_relset_1(X1,X2,X3)=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 0.12/0.40  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 0.12/0.40  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.12/0.40  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 0.12/0.40  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.12/0.40  fof(t52_funct_1, axiom, ![X1]:v2_funct_1(k6_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_funct_1)).
% 0.12/0.40  fof(t30_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X2,X3))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>((v2_funct_1(k1_partfun1(X1,X2,X2,X3,X4,X5))&k2_relset_1(X1,X2,X4)=X2)=>((X3=k1_xboole_0&X2!=k1_xboole_0)|(v2_funct_1(X4)&v2_funct_1(X5)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_funct_2)).
% 0.12/0.40  fof(t55_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))&k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 0.12/0.40  fof(c_0_22, plain, ![X60, X61, X62]:((k5_relat_1(X62,k2_funct_1(X62))=k6_partfun1(X60)|X61=k1_xboole_0|(k2_relset_1(X60,X61,X62)!=X61|~v2_funct_1(X62))|(~v1_funct_1(X62)|~v1_funct_2(X62,X60,X61)|~m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X60,X61)))))&(k5_relat_1(k2_funct_1(X62),X62)=k6_partfun1(X61)|X61=k1_xboole_0|(k2_relset_1(X60,X61,X62)!=X61|~v2_funct_1(X62))|(~v1_funct_1(X62)|~v1_funct_2(X62,X60,X61)|~m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X60,X61)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_funct_2])])])).
% 0.12/0.40  fof(c_0_23, plain, ![X50]:k6_partfun1(X50)=k6_relat_1(X50), inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).
% 0.12/0.40  fof(c_0_24, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(((k2_relset_1(X1,X2,X3)=X2&r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1)))&v2_funct_1(X3))=>(X1=k1_xboole_0|X2=k1_xboole_0|X4=k2_funct_1(X3)))))), inference(assume_negation,[status(cth)],[t36_funct_2])).
% 0.12/0.40  cnf(c_0_25, plain, (k5_relat_1(X1,k2_funct_1(X1))=k6_partfun1(X2)|X3=k1_xboole_0|k2_relset_1(X2,X3,X1)!=X3|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.40  cnf(c_0_26, plain, (k6_partfun1(X1)=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.12/0.40  fof(c_0_27, negated_conjecture, (((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,esk2_0,esk3_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))))&(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,esk3_0,esk2_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))))&(((k2_relset_1(esk2_0,esk3_0,esk4_0)=esk3_0&r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,esk5_0),k6_partfun1(esk2_0)))&v2_funct_1(esk4_0))&((esk2_0!=k1_xboole_0&esk3_0!=k1_xboole_0)&esk5_0!=k2_funct_1(esk4_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).
% 0.12/0.40  fof(c_0_28, plain, ![X27, X28, X29]:(~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))|v1_relat_1(X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.12/0.40  fof(c_0_29, plain, ![X25]:((k1_relat_1(k5_relat_1(X25,k2_funct_1(X25)))=k1_relat_1(X25)|~v2_funct_1(X25)|(~v1_relat_1(X25)|~v1_funct_1(X25)))&(k2_relat_1(k5_relat_1(X25,k2_funct_1(X25)))=k1_relat_1(X25)|~v2_funct_1(X25)|(~v1_relat_1(X25)|~v1_funct_1(X25)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t58_funct_1])])])).
% 0.12/0.40  cnf(c_0_30, plain, (X3=k1_xboole_0|k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(X2)|k2_relset_1(X2,X3,X1)!=X3|~v1_funct_1(X1)|~v2_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 0.12/0.40  cnf(c_0_31, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.12/0.40  cnf(c_0_32, negated_conjecture, (k2_relset_1(esk2_0,esk3_0,esk4_0)=esk3_0), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.12/0.40  cnf(c_0_33, negated_conjecture, (v1_funct_2(esk4_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.12/0.40  cnf(c_0_34, negated_conjecture, (v2_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.12/0.40  cnf(c_0_35, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.12/0.40  cnf(c_0_36, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.12/0.40  fof(c_0_37, plain, ![X18]:(k1_relat_1(k6_relat_1(X18))=X18&k2_relat_1(k6_relat_1(X18))=X18), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.12/0.40  cnf(c_0_38, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.12/0.40  fof(c_0_39, plain, ![X15, X16, X17]:(~v1_relat_1(X15)|(~v1_relat_1(X16)|(~v1_relat_1(X17)|k5_relat_1(k5_relat_1(X15,X16),X17)=k5_relat_1(X15,k5_relat_1(X16,X17))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_relat_1])])])).
% 0.12/0.40  cnf(c_0_40, plain, (k5_relat_1(k2_funct_1(X1),X1)=k6_partfun1(X2)|X2=k1_xboole_0|k2_relset_1(X3,X2,X1)!=X2|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.40  fof(c_0_41, plain, ![X19]:(~v1_relat_1(X19)|k5_relat_1(k6_relat_1(k1_relat_1(X19)),X19)=X19), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_relat_1])])).
% 0.12/0.40  cnf(c_0_42, plain, (k1_relat_1(k5_relat_1(X1,k2_funct_1(X1)))=k1_relat_1(X1)|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.12/0.40  cnf(c_0_43, negated_conjecture, (k5_relat_1(esk4_0,k2_funct_1(esk4_0))=k6_relat_1(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32]), c_0_33]), c_0_34]), c_0_35])]), c_0_36])).
% 0.12/0.40  cnf(c_0_44, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.12/0.40  cnf(c_0_45, negated_conjecture, (v1_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_38, c_0_31])).
% 0.12/0.40  fof(c_0_46, plain, ![X43]:(v1_partfun1(k6_partfun1(X43),X43)&m1_subset_1(k6_partfun1(X43),k1_zfmisc_1(k2_zfmisc_1(X43,X43)))), inference(variable_rename,[status(thm)],[dt_k6_partfun1])).
% 0.12/0.40  cnf(c_0_47, plain, (k5_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(X1,k5_relat_1(X2,X3))|~v1_relat_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.12/0.40  cnf(c_0_48, plain, (X2=k1_xboole_0|k5_relat_1(k2_funct_1(X1),X1)=k6_relat_1(X2)|k2_relset_1(X3,X2,X1)!=X2|~v1_funct_1(X1)|~v2_funct_1(X1)|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(rw,[status(thm)],[c_0_40, c_0_26])).
% 0.12/0.40  cnf(c_0_49, plain, (k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1)=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.12/0.40  cnf(c_0_50, negated_conjecture, (k1_relat_1(esk4_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44]), c_0_34]), c_0_35]), c_0_45])])).
% 0.12/0.40  cnf(c_0_51, plain, (m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.12/0.40  cnf(c_0_52, negated_conjecture, (k5_relat_1(esk4_0,k5_relat_1(k2_funct_1(esk4_0),X1))=k5_relat_1(k6_relat_1(esk2_0),X1)|~v1_relat_1(k2_funct_1(esk4_0))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_43]), c_0_45])])).
% 0.12/0.40  cnf(c_0_53, negated_conjecture, (k5_relat_1(k2_funct_1(esk4_0),esk4_0)=k6_relat_1(esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_31]), c_0_32]), c_0_33]), c_0_34]), c_0_35])]), c_0_36])).
% 0.12/0.40  cnf(c_0_54, negated_conjecture, (k5_relat_1(k6_relat_1(esk2_0),esk4_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_45])])).
% 0.12/0.40  cnf(c_0_55, plain, (m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(rw,[status(thm)],[c_0_51, c_0_26])).
% 0.12/0.40  fof(c_0_56, plain, ![X20, X21]:(~v1_relat_1(X21)|(~r1_tarski(k2_relat_1(X21),X20)|k5_relat_1(X21,k6_relat_1(X20))=X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_relat_1])])).
% 0.12/0.40  fof(c_0_57, plain, ![X13, X14]:((~m1_subset_1(X13,k1_zfmisc_1(X14))|r1_tarski(X13,X14))&(~r1_tarski(X13,X14)|m1_subset_1(X13,k1_zfmisc_1(X14)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.12/0.40  fof(c_0_58, plain, ![X33, X34, X35, X36]:((~r2_relset_1(X33,X34,X35,X36)|X35=X36|(~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))))&(X35!=X36|r2_relset_1(X33,X34,X35,X36)|(~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).
% 0.12/0.40  cnf(c_0_59, negated_conjecture, (r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,esk5_0),k6_partfun1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.12/0.40  cnf(c_0_60, negated_conjecture, (k5_relat_1(esk4_0,k6_relat_1(esk3_0))=esk4_0|~v1_relat_1(k2_funct_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54]), c_0_45])])).
% 0.12/0.40  cnf(c_0_61, plain, (v1_relat_1(k6_relat_1(X1))), inference(spm,[status(thm)],[c_0_38, c_0_55])).
% 0.12/0.40  cnf(c_0_62, plain, (k5_relat_1(X1,k6_relat_1(X2))=X1|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.12/0.40  cnf(c_0_63, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.12/0.40  cnf(c_0_64, plain, (X3=X4|~r2_relset_1(X1,X2,X3,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.12/0.40  cnf(c_0_65, negated_conjecture, (r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,esk5_0),k6_relat_1(esk2_0))), inference(rw,[status(thm)],[c_0_59, c_0_26])).
% 0.12/0.40  fof(c_0_66, plain, ![X37, X38, X39, X40, X41, X42]:((v1_funct_1(k1_partfun1(X37,X38,X39,X40,X41,X42))|(~v1_funct_1(X41)|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))|~v1_funct_1(X42)|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))))&(m1_subset_1(k1_partfun1(X37,X38,X39,X40,X41,X42),k1_zfmisc_1(k2_zfmisc_1(X37,X40)))|(~v1_funct_1(X41)|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))|~v1_funct_1(X42)|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).
% 0.12/0.40  cnf(c_0_67, negated_conjecture, (k5_relat_1(esk4_0,k5_relat_1(k6_relat_1(esk3_0),X1))=k5_relat_1(esk4_0,X1)|~v1_relat_1(k2_funct_1(esk4_0))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_60]), c_0_61]), c_0_45])])).
% 0.12/0.40  cnf(c_0_68, plain, (k5_relat_1(X1,k6_relat_1(X2))=X1|~v1_relat_1(X1)|~m1_subset_1(k2_relat_1(X1),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.12/0.40  cnf(c_0_69, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.12/0.40  fof(c_0_70, plain, ![X44, X45, X46, X47, X48, X49]:(~v1_funct_1(X48)|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))|~v1_funct_1(X49)|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X46,X47)))|k1_partfun1(X44,X45,X46,X47,X48,X49)=k5_relat_1(X48,X49)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).
% 0.12/0.40  cnf(c_0_71, negated_conjecture, (k1_partfun1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,esk5_0)=k6_relat_1(esk2_0)|~m1_subset_1(k1_partfun1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_55])])).
% 0.12/0.40  cnf(c_0_72, plain, (m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X6)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.12/0.40  cnf(c_0_73, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.12/0.40  cnf(c_0_74, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.12/0.40  cnf(c_0_75, negated_conjecture, (k5_relat_1(esk4_0,k6_relat_1(esk3_0))=k5_relat_1(esk4_0,k6_relat_1(X1))|~v1_relat_1(k2_funct_1(esk4_0))|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_61]), c_0_61]), c_0_69])])).
% 0.12/0.40  fof(c_0_76, plain, ![X51, X52, X53, X54]:(~v1_funct_1(X53)|~v1_funct_2(X53,X51,X52)|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))|(~v1_funct_1(X54)|~v1_funct_2(X54,X52,X51)|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X51)))|(~r2_relset_1(X52,X52,k1_partfun1(X52,X51,X51,X52,X54,X53),k6_partfun1(X52))|k2_relset_1(X51,X52,X53)=X52))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_funct_2])])])).
% 0.12/0.40  cnf(c_0_77, plain, (k1_partfun1(X2,X3,X5,X6,X1,X4)=k5_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.12/0.40  cnf(c_0_78, negated_conjecture, (k1_partfun1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,esk5_0)=k6_relat_1(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_73]), c_0_35]), c_0_74]), c_0_31])])).
% 0.12/0.40  cnf(c_0_79, negated_conjecture, (k5_relat_1(esk4_0,k6_relat_1(X1))=esk4_0|~v1_relat_1(k2_funct_1(esk4_0))|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_60, c_0_75])).
% 0.12/0.40  cnf(c_0_80, plain, (k2_relset_1(X2,X3,X1)=X3|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~v1_funct_2(X4,X3,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~r2_relset_1(X3,X3,k1_partfun1(X3,X2,X2,X3,X4,X1),k6_partfun1(X3))), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.12/0.40  cnf(c_0_81, negated_conjecture, (k6_relat_1(esk2_0)=k5_relat_1(esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_73]), c_0_35]), c_0_74]), c_0_31])])).
% 0.12/0.40  cnf(c_0_82, negated_conjecture, (k5_relat_1(esk4_0,k5_relat_1(k6_relat_1(X1),X2))=k5_relat_1(esk4_0,X2)|~v1_relat_1(k2_funct_1(esk4_0))|~v1_relat_1(X2)|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_79]), c_0_61]), c_0_45])])).
% 0.12/0.40  fof(c_0_83, plain, ![X22]:((v1_relat_1(k2_funct_1(X22))|(~v1_relat_1(X22)|~v1_funct_1(X22)))&(v1_funct_1(k2_funct_1(X22))|(~v1_relat_1(X22)|~v1_funct_1(X22)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 0.12/0.40  fof(c_0_84, plain, ![X12]:m1_subset_1(k2_subset_1(X12),k1_zfmisc_1(X12)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.12/0.40  fof(c_0_85, plain, ![X11]:k2_subset_1(X11)=X11, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.12/0.40  cnf(c_0_86, plain, (k2_relset_1(X2,X3,X1)=X3|~v1_funct_1(X4)|~v1_funct_1(X1)|~v1_funct_2(X4,X3,X2)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_relset_1(X3,X3,k1_partfun1(X3,X2,X2,X3,X4,X1),k6_relat_1(X3))), inference(rw,[status(thm)],[c_0_80, c_0_26])).
% 0.12/0.40  cnf(c_0_87, negated_conjecture, (k1_partfun1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,esk5_0)=k5_relat_1(esk4_0,esk5_0)), inference(rw,[status(thm)],[c_0_78, c_0_81])).
% 0.12/0.40  cnf(c_0_88, negated_conjecture, (v1_funct_2(esk5_0,esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.12/0.40  cnf(c_0_89, plain, (r2_relset_1(X3,X4,X1,X2)|X1!=X2|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.12/0.40  fof(c_0_90, plain, ![X30, X31, X32]:(~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))|k2_relset_1(X30,X31,X32)=k2_relat_1(X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.12/0.40  cnf(c_0_91, negated_conjecture, (k5_relat_1(esk4_0,k6_relat_1(X1))=k5_relat_1(esk4_0,k6_relat_1(X2))|~v1_relat_1(k2_funct_1(esk4_0))|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_68]), c_0_61]), c_0_61]), c_0_69])])).
% 0.12/0.40  cnf(c_0_92, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_83])).
% 0.12/0.40  cnf(c_0_93, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_84])).
% 0.12/0.40  cnf(c_0_94, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_85])).
% 0.12/0.40  cnf(c_0_95, negated_conjecture, (k2_relset_1(esk3_0,esk2_0,esk5_0)=esk2_0|~r2_relset_1(esk2_0,esk2_0,k5_relat_1(esk4_0,esk5_0),k5_relat_1(esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_33]), c_0_88]), c_0_81]), c_0_35]), c_0_73]), c_0_31]), c_0_74])])).
% 0.12/0.40  cnf(c_0_96, plain, (r2_relset_1(X1,X2,X3,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(er,[status(thm)],[c_0_89])).
% 0.12/0.40  cnf(c_0_97, negated_conjecture, (m1_subset_1(k5_relat_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))), inference(spm,[status(thm)],[c_0_55, c_0_81])).
% 0.12/0.40  cnf(c_0_98, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_90])).
% 0.12/0.40  fof(c_0_99, plain, ![X23]:v2_funct_1(k6_relat_1(X23)), inference(variable_rename,[status(thm)],[t52_funct_1])).
% 0.12/0.40  cnf(c_0_100, negated_conjecture, (k5_relat_1(esk4_0,k6_relat_1(X1))=k5_relat_1(esk4_0,k6_relat_1(X2))|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_35]), c_0_45])])).
% 0.12/0.40  cnf(c_0_101, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_93, c_0_94])).
% 0.12/0.40  cnf(c_0_102, negated_conjecture, (k2_relset_1(esk3_0,esk2_0,esk5_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_96]), c_0_97])])).
% 0.12/0.40  cnf(c_0_103, plain, (k2_relset_1(X1,X2,X3)=k2_relset_1(X4,X5,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))), inference(spm,[status(thm)],[c_0_98, c_0_98])).
% 0.12/0.40  fof(c_0_104, plain, ![X55, X56, X57, X58, X59]:(((v2_funct_1(X58)|X57=k1_xboole_0|(~v2_funct_1(k1_partfun1(X55,X56,X56,X57,X58,X59))|k2_relset_1(X55,X56,X58)!=X56)|(~v1_funct_1(X59)|~v1_funct_2(X59,X56,X57)|~m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X56,X57))))|(~v1_funct_1(X58)|~v1_funct_2(X58,X55,X56)|~m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X55,X56)))))&(v2_funct_1(X59)|X57=k1_xboole_0|(~v2_funct_1(k1_partfun1(X55,X56,X56,X57,X58,X59))|k2_relset_1(X55,X56,X58)!=X56)|(~v1_funct_1(X59)|~v1_funct_2(X59,X56,X57)|~m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X56,X57))))|(~v1_funct_1(X58)|~v1_funct_2(X58,X55,X56)|~m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X55,X56))))))&((v2_funct_1(X58)|X56!=k1_xboole_0|(~v2_funct_1(k1_partfun1(X55,X56,X56,X57,X58,X59))|k2_relset_1(X55,X56,X58)!=X56)|(~v1_funct_1(X59)|~v1_funct_2(X59,X56,X57)|~m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X56,X57))))|(~v1_funct_1(X58)|~v1_funct_2(X58,X55,X56)|~m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X55,X56)))))&(v2_funct_1(X59)|X56!=k1_xboole_0|(~v2_funct_1(k1_partfun1(X55,X56,X56,X57,X58,X59))|k2_relset_1(X55,X56,X58)!=X56)|(~v1_funct_1(X59)|~v1_funct_2(X59,X56,X57)|~m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X56,X57))))|(~v1_funct_1(X58)|~v1_funct_2(X58,X55,X56)|~m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X55,X56))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_funct_2])])])])).
% 0.12/0.40  cnf(c_0_105, plain, (v2_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_99])).
% 0.12/0.40  cnf(c_0_106, negated_conjecture, (k5_relat_1(esk4_0,k6_relat_1(esk3_0))=k5_relat_1(esk4_0,k6_relat_1(X1))|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_100, c_0_101])).
% 0.12/0.40  fof(c_0_107, plain, ![X24]:((k2_relat_1(X24)=k1_relat_1(k2_funct_1(X24))|~v2_funct_1(X24)|(~v1_relat_1(X24)|~v1_funct_1(X24)))&(k1_relat_1(X24)=k2_relat_1(k2_funct_1(X24))|~v2_funct_1(X24)|(~v1_relat_1(X24)|~v1_funct_1(X24)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).
% 0.12/0.40  cnf(c_0_108, negated_conjecture, (k2_relset_1(X1,X2,esk5_0)=esk2_0|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_103]), c_0_74])])).
% 0.12/0.40  cnf(c_0_109, negated_conjecture, (esk2_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.12/0.40  cnf(c_0_110, plain, (v2_funct_1(X1)|X2=k1_xboole_0|~v2_funct_1(k1_partfun1(X3,X4,X4,X2,X5,X1))|k2_relset_1(X3,X4,X5)!=X4|~v1_funct_1(X1)|~v1_funct_2(X1,X4,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|~v1_funct_1(X5)|~v1_funct_2(X5,X3,X4)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_104])).
% 0.12/0.40  cnf(c_0_111, negated_conjecture, (v2_funct_1(k5_relat_1(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_105, c_0_81])).
% 0.12/0.40  cnf(c_0_112, negated_conjecture, (k5_relat_1(esk4_0,k6_relat_1(esk3_0))=esk4_0|~m1_subset_1(k2_relat_1(esk4_0),k1_zfmisc_1(X1))|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_106]), c_0_45])])).
% 0.12/0.40  cnf(c_0_113, plain, (k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_107])).
% 0.12/0.40  cnf(c_0_114, negated_conjecture, (k2_relat_1(esk5_0)=esk2_0|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_98, c_0_108])).
% 0.12/0.40  cnf(c_0_115, negated_conjecture, (k5_relat_1(esk5_0,k2_funct_1(esk5_0))=k6_relat_1(esk3_0)|k2_relset_1(esk3_0,esk2_0,esk5_0)!=esk2_0|~v2_funct_1(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_74]), c_0_88]), c_0_73])]), c_0_109])).
% 0.12/0.40  cnf(c_0_116, negated_conjecture, (v2_funct_1(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_87]), c_0_32]), c_0_33]), c_0_88]), c_0_111]), c_0_35]), c_0_73]), c_0_31]), c_0_74])]), c_0_109])).
% 0.12/0.40  cnf(c_0_117, negated_conjecture, (k5_relat_1(esk4_0,k6_relat_1(esk3_0))=esk4_0|~m1_subset_1(k2_relset_1(X1,X2,esk4_0),k1_zfmisc_1(X3))|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(esk3_0,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_112, c_0_98])).
% 0.12/0.40  cnf(c_0_118, negated_conjecture, (v1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_38, c_0_74])).
% 0.12/0.40  cnf(c_0_119, plain, (k5_relat_1(k6_relat_1(k2_relat_1(X1)),k2_funct_1(X1))=k2_funct_1(X1)|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_113]), c_0_92])).
% 0.12/0.40  cnf(c_0_120, negated_conjecture, (k2_relat_1(esk5_0)=esk2_0), inference(spm,[status(thm)],[c_0_114, c_0_74])).
% 0.12/0.40  cnf(c_0_121, negated_conjecture, (k5_relat_1(esk5_0,k2_funct_1(esk5_0))=k6_relat_1(esk3_0)|k2_relset_1(esk3_0,esk2_0,esk5_0)!=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_115, c_0_116])])).
% 0.12/0.40  cnf(c_0_122, negated_conjecture, (k5_relat_1(esk4_0,k6_relat_1(esk3_0))=esk4_0|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_32]), c_0_31])])).
% 0.12/0.40  cnf(c_0_123, negated_conjecture, (k1_relat_1(esk5_0)=esk3_0|k2_relset_1(esk3_0,esk2_0,esk5_0)!=esk2_0|~v2_funct_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_115]), c_0_44]), c_0_73]), c_0_118])])).
% 0.12/0.40  cnf(c_0_124, negated_conjecture, (k5_relat_1(k5_relat_1(esk4_0,esk5_0),k2_funct_1(esk5_0))=k2_funct_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_120]), c_0_81]), c_0_116]), c_0_73]), c_0_118])])).
% 0.12/0.40  cnf(c_0_125, negated_conjecture, (k5_relat_1(esk5_0,k2_funct_1(esk5_0))=k6_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_121, c_0_102])])).
% 0.12/0.40  cnf(c_0_126, negated_conjecture, (k5_relat_1(esk4_0,k6_relat_1(esk3_0))=esk4_0), inference(spm,[status(thm)],[c_0_122, c_0_101])).
% 0.12/0.40  cnf(c_0_127, negated_conjecture, (k1_relat_1(esk5_0)=esk3_0|k2_relset_1(esk3_0,esk2_0,esk5_0)!=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_123, c_0_116])])).
% 0.12/0.40  cnf(c_0_128, negated_conjecture, (k2_funct_1(esk5_0)=esk4_0|~v1_relat_1(k2_funct_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_124]), c_0_125]), c_0_126]), c_0_118]), c_0_45])])).
% 0.12/0.40  cnf(c_0_129, negated_conjecture, (k5_relat_1(esk5_0,k5_relat_1(k2_funct_1(esk5_0),X1))=k5_relat_1(k6_relat_1(esk3_0),X1)|k2_relset_1(esk3_0,esk2_0,esk5_0)!=esk2_0|~v2_funct_1(esk5_0)|~v1_relat_1(k2_funct_1(esk5_0))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_115]), c_0_118])])).
% 0.12/0.40  cnf(c_0_130, negated_conjecture, (k5_relat_1(k2_funct_1(esk5_0),esk5_0)=k6_relat_1(esk2_0)|k2_relset_1(esk3_0,esk2_0,esk5_0)!=esk2_0|~v2_funct_1(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_74]), c_0_88]), c_0_73])]), c_0_109])).
% 0.12/0.40  cnf(c_0_131, negated_conjecture, (k1_relat_1(esk5_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_127, c_0_102])])).
% 0.12/0.40  cnf(c_0_132, plain, (k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_107])).
% 0.12/0.40  cnf(c_0_133, negated_conjecture, (k2_funct_1(esk5_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_92]), c_0_73]), c_0_118])])).
% 0.12/0.40  cnf(c_0_134, negated_conjecture, (k5_relat_1(k6_relat_1(esk3_0),esk5_0)=k5_relat_1(esk5_0,k6_relat_1(esk2_0))|k2_relset_1(esk3_0,esk2_0,esk5_0)!=esk2_0|~v2_funct_1(esk5_0)|~v1_relat_1(k2_funct_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129, c_0_130]), c_0_118])])).
% 0.12/0.40  cnf(c_0_135, negated_conjecture, (k5_relat_1(k6_relat_1(esk3_0),esk5_0)=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_131]), c_0_118])])).
% 0.12/0.40  cnf(c_0_136, negated_conjecture, (k2_relat_1(esk4_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132, c_0_133]), c_0_131]), c_0_116]), c_0_73]), c_0_118])])).
% 0.12/0.40  cnf(c_0_137, negated_conjecture, (k6_relat_1(esk3_0)=k5_relat_1(esk5_0,esk4_0)), inference(rw,[status(thm)],[c_0_125, c_0_133])).
% 0.12/0.40  cnf(c_0_138, negated_conjecture, (k5_relat_1(esk5_0,k5_relat_1(esk4_0,esk5_0))=esk5_0|~v1_relat_1(k2_funct_1(esk5_0))), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_134, c_0_81]), c_0_102]), c_0_116])]), c_0_135])).
% 0.12/0.40  cnf(c_0_139, negated_conjecture, (k5_relat_1(k5_relat_1(esk5_0,esk4_0),k2_funct_1(esk4_0))=k2_funct_1(esk4_0)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_136]), c_0_34]), c_0_35]), c_0_45])]), c_0_137])).
% 0.12/0.40  cnf(c_0_140, negated_conjecture, (k5_relat_1(esk5_0,k5_relat_1(esk4_0,esk5_0))=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_138, c_0_133]), c_0_45])])).
% 0.12/0.40  cnf(c_0_141, negated_conjecture, (esk5_0!=k2_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.12/0.40  cnf(c_0_142, negated_conjecture, (~v1_relat_1(k2_funct_1(esk4_0))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_139]), c_0_43]), c_0_81]), c_0_45]), c_0_118])]), c_0_140]), c_0_141])).
% 0.12/0.40  cnf(c_0_143, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_142, c_0_92]), c_0_35]), c_0_45])]), ['proof']).
% 0.12/0.40  # SZS output end CNFRefutation
% 0.12/0.40  # Proof object total steps             : 144
% 0.12/0.40  # Proof object clause steps            : 99
% 0.12/0.40  # Proof object formula steps           : 45
% 0.12/0.40  # Proof object conjectures             : 67
% 0.12/0.40  # Proof object clause conjectures      : 64
% 0.12/0.40  # Proof object formula conjectures     : 3
% 0.12/0.40  # Proof object initial clauses used    : 37
% 0.12/0.40  # Proof object initial formulas used   : 22
% 0.12/0.40  # Proof object generating inferences   : 47
% 0.12/0.40  # Proof object simplifying inferences  : 156
% 0.12/0.40  # Training examples: 0 positive, 0 negative
% 0.12/0.40  # Parsed axioms                        : 27
% 0.12/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.40  # Initial clauses                      : 51
% 0.12/0.40  # Removed in clause preprocessing      : 2
% 0.12/0.40  # Initial clauses in saturation        : 49
% 0.12/0.40  # Processed clauses                    : 410
% 0.12/0.40  # ...of these trivial                  : 14
% 0.12/0.40  # ...subsumed                          : 109
% 0.12/0.40  # ...remaining for further processing  : 287
% 0.12/0.40  # Other redundant clauses eliminated   : 3
% 0.12/0.40  # Clauses deleted for lack of memory   : 0
% 0.12/0.40  # Backward-subsumed                    : 23
% 0.12/0.40  # Backward-rewritten                   : 74
% 0.12/0.40  # Generated clauses                    : 900
% 0.12/0.40  # ...of the previous two non-trivial   : 787
% 0.12/0.40  # Contextual simplify-reflections      : 5
% 0.12/0.40  # Paramodulations                      : 897
% 0.12/0.40  # Factorizations                       : 0
% 0.12/0.40  # Equation resolutions                 : 3
% 0.12/0.40  # Propositional unsat checks           : 0
% 0.12/0.40  #    Propositional check models        : 0
% 0.12/0.40  #    Propositional check unsatisfiable : 0
% 0.12/0.40  #    Propositional clauses             : 0
% 0.12/0.40  #    Propositional clauses after purity: 0
% 0.12/0.40  #    Propositional unsat core size     : 0
% 0.12/0.40  #    Propositional preprocessing time  : 0.000
% 0.12/0.40  #    Propositional encoding time       : 0.000
% 0.12/0.40  #    Propositional solver time         : 0.000
% 0.12/0.40  #    Success case prop preproc time    : 0.000
% 0.12/0.40  #    Success case prop encoding time   : 0.000
% 0.12/0.40  #    Success case prop solver time     : 0.000
% 0.12/0.40  # Current number of processed clauses  : 138
% 0.12/0.40  #    Positive orientable unit clauses  : 56
% 0.12/0.40  #    Positive unorientable unit clauses: 0
% 0.12/0.40  #    Negative unit clauses             : 4
% 0.12/0.40  #    Non-unit-clauses                  : 78
% 0.12/0.40  # Current number of unprocessed clauses: 463
% 0.12/0.40  # ...number of literals in the above   : 2024
% 0.12/0.40  # Current number of archived formulas  : 0
% 0.12/0.40  # Current number of archived clauses   : 148
% 0.12/0.40  # Clause-clause subsumption calls (NU) : 3259
% 0.12/0.40  # Rec. Clause-clause subsumption calls : 1538
% 0.12/0.40  # Non-unit clause-clause subsumptions  : 133
% 0.12/0.40  # Unit Clause-clause subsumption calls : 146
% 0.12/0.40  # Rewrite failures with RHS unbound    : 0
% 0.12/0.40  # BW rewrite match attempts            : 17
% 0.12/0.40  # BW rewrite match successes           : 15
% 0.12/0.40  # Condensation attempts                : 0
% 0.12/0.40  # Condensation successes               : 0
% 0.12/0.40  # Termbank termtop insertions          : 24931
% 0.12/0.40  
% 0.12/0.40  # -------------------------------------------------
% 0.12/0.40  # User time                : 0.066 s
% 0.12/0.40  # System time              : 0.002 s
% 0.12/0.40  # Total time               : 0.068 s
% 0.12/0.40  # Maximum resident set size: 1612 pages
%------------------------------------------------------------------------------

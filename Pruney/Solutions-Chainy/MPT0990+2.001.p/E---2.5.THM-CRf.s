%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:02:58 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  161 (33836 expanded)
%              Number of clauses        :  120 (12189 expanded)
%              Number of leaves         :   20 (8326 expanded)
%              Depth                    :   21
%              Number of atoms          :  551 (233553 expanded)
%              Number of equality atoms :  169 (71648 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal clause size      :   40 (   2 average)
%              Maximal term depth       :    5 (   2 average)

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

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(dt_k6_partfun1,axiom,(
    ! [X1] :
      ( v1_partfun1(k6_partfun1(X1),X1)
      & m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(t55_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
          & k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(t31_funct_2,axiom,(
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

fof(t47_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(k1_relat_1(X1),k2_relat_1(X2))
           => k2_relat_1(k5_relat_1(X2,X1)) = k2_relat_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(fc4_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v2_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(redefinition_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k1_partfun1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

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

fof(dt_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => ( v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))
        & m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(redefinition_r2_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_relset_1(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

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

fof(t64_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( ( v2_funct_1(X1)
              & k2_relat_1(X2) = k1_relat_1(X1)
              & k5_relat_1(X2,X1) = k6_relat_1(k2_relat_1(X1)) )
           => X2 = k2_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).

fof(c_0_20,negated_conjecture,(
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

fof(c_0_21,plain,(
    ! [X20,X21,X22] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
      | v1_relat_1(X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_22,negated_conjecture,
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).

fof(c_0_23,plain,(
    ! [X26,X27,X28] :
      ( ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
      | k2_relset_1(X26,X27,X28) = k2_relat_1(X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_24,plain,(
    ! [X39] :
      ( v1_partfun1(k6_partfun1(X39),X39)
      & m1_subset_1(k6_partfun1(X39),k1_zfmisc_1(k2_zfmisc_1(X39,X39))) ) ),
    inference(variable_rename,[status(thm)],[dt_k6_partfun1])).

fof(c_0_25,plain,(
    ! [X46] : k6_partfun1(X46) = k6_relat_1(X46) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

fof(c_0_26,plain,(
    ! [X17] :
      ( ( k2_relat_1(X17) = k1_relat_1(k2_funct_1(X17))
        | ~ v2_funct_1(X17)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) )
      & ( k1_relat_1(X17) = k2_relat_1(k2_funct_1(X17))
        | ~ v2_funct_1(X17)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).

cnf(c_0_27,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( k2_relset_1(esk1_0,esk2_0,esk3_0) = esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_31,plain,(
    ! [X23,X24,X25] :
      ( ( v4_relat_1(X25,X23)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) )
      & ( v5_relat_1(X25,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_32,plain,
    ( m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_34,plain,(
    ! [X56,X57,X58] :
      ( ( v1_funct_1(k2_funct_1(X58))
        | ~ v2_funct_1(X58)
        | k2_relset_1(X56,X57,X58) != X57
        | ~ v1_funct_1(X58)
        | ~ v1_funct_2(X58,X56,X57)
        | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57))) )
      & ( v1_funct_2(k2_funct_1(X58),X57,X56)
        | ~ v2_funct_1(X58)
        | k2_relset_1(X56,X57,X58) != X57
        | ~ v1_funct_1(X58)
        | ~ v1_funct_2(X58,X56,X57)
        | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57))) )
      & ( m1_subset_1(k2_funct_1(X58),k1_zfmisc_1(k2_zfmisc_1(X57,X56)))
        | ~ v2_funct_1(X58)
        | k2_relset_1(X56,X57,X58) != X57
        | ~ v1_funct_1(X58)
        | ~ v1_funct_2(X58,X56,X57)
        | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_funct_2])])])).

fof(c_0_35,plain,(
    ! [X13,X14] :
      ( ~ v1_relat_1(X13)
      | ~ v1_relat_1(X14)
      | ~ r1_tarski(k1_relat_1(X13),k2_relat_1(X14))
      | k2_relat_1(k5_relat_1(X14,X13)) = k2_relat_1(X13) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t47_relat_1])])])).

cnf(c_0_36,plain,
    ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,negated_conjecture,
    ( v2_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_38,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_39,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_40,negated_conjecture,
    ( k2_relat_1(esk3_0) = esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_28]),c_0_30])).

cnf(c_0_41,plain,
    ( k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_42,plain,(
    ! [X9,X10] :
      ( ( ~ v4_relat_1(X10,X9)
        | r1_tarski(k1_relat_1(X10),X9)
        | ~ v1_relat_1(X10) )
      & ( ~ r1_tarski(k1_relat_1(X10),X9)
        | v4_relat_1(X10,X9)
        | ~ v1_relat_1(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

cnf(c_0_43,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_44,plain,
    ( m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(rw,[status(thm)],[c_0_32,c_0_33])).

fof(c_0_45,plain,(
    ! [X15] :
      ( k1_relat_1(k6_relat_1(X15)) = X15
      & k2_relat_1(k6_relat_1(X15)) = X15 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_46,plain,(
    ! [X16] :
      ( v1_relat_1(k6_relat_1(X16))
      & v2_funct_1(k6_relat_1(X16)) ) ),
    inference(variable_rename,[status(thm)],[fc4_funct_1])).

cnf(c_0_47,plain,
    ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v2_funct_1(X1)
    | k2_relset_1(X3,X2,X1) != X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_48,plain,(
    ! [X40,X41,X42,X43,X44,X45] :
      ( ~ v1_funct_1(X44)
      | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))
      | ~ v1_funct_1(X45)
      | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))
      | k1_partfun1(X40,X41,X42,X43,X44,X45) = k5_relat_1(X44,X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).

cnf(c_0_49,plain,
    ( k2_relat_1(k5_relat_1(X2,X1)) = k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k1_relat_1(X1),k2_relat_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_50,negated_conjecture,
    ( k1_relat_1(k2_funct_1(esk3_0)) = esk2_0 ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38]),c_0_39])]),c_0_40])).

cnf(c_0_51,negated_conjecture,
    ( k2_relat_1(k2_funct_1(esk3_0)) = k1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_37]),c_0_38]),c_0_39])])).

cnf(c_0_52,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_53,plain,
    ( v4_relat_1(k6_relat_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_54,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_55,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

fof(c_0_56,plain,(
    ! [X7,X8] :
      ( ~ v1_relat_1(X7)
      | ~ m1_subset_1(X8,k1_zfmisc_1(X7))
      | v1_relat_1(X8) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X2,X1,esk3_0) != X1
    | ~ v1_funct_2(esk3_0,X2,X1)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_38]),c_0_37])])).

cnf(c_0_58,negated_conjecture,
    ( v1_funct_2(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_59,plain,(
    ! [X11,X12] : v1_relat_1(k2_zfmisc_1(X11,X12)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_60,plain,(
    ! [X59,X60,X61] :
      ( ( k5_relat_1(X61,k2_funct_1(X61)) = k6_partfun1(X59)
        | X60 = k1_xboole_0
        | k2_relset_1(X59,X60,X61) != X60
        | ~ v2_funct_1(X61)
        | ~ v1_funct_1(X61)
        | ~ v1_funct_2(X61,X59,X60)
        | ~ m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X59,X60))) )
      & ( k5_relat_1(k2_funct_1(X61),X61) = k6_partfun1(X60)
        | X60 = k1_xboole_0
        | k2_relset_1(X59,X60,X61) != X60
        | ~ v2_funct_1(X61)
        | ~ v1_funct_1(X61)
        | ~ v1_funct_2(X61,X59,X60)
        | ~ m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X59,X60))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_funct_2])])])).

cnf(c_0_61,plain,
    ( k1_partfun1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_62,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_63,negated_conjecture,
    ( k2_relat_1(k5_relat_1(X1,k2_funct_1(esk3_0))) = k1_relat_1(esk3_0)
    | ~ r1_tarski(esk2_0,k2_relat_1(X1))
    | ~ v1_relat_1(k2_funct_1(esk3_0))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])).

cnf(c_0_64,plain,
    ( r1_tarski(X1,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54]),c_0_55])])).

cnf(c_0_65,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_66,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_30]),c_0_58]),c_0_28])])).

cnf(c_0_67,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_68,plain,
    ( k5_relat_1(X1,k2_funct_1(X1)) = k6_partfun1(X2)
    | X3 = k1_xboole_0
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_69,negated_conjecture,
    ( k1_partfun1(esk1_0,esk2_0,X1,X2,esk3_0,X3) = k5_relat_1(esk3_0,X3)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_28]),c_0_38])])).

cnf(c_0_70,negated_conjecture,
    ( v1_funct_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_28]),c_0_30]),c_0_58]),c_0_38]),c_0_37])])).

fof(c_0_71,plain,(
    ! [X33,X34,X35,X36,X37,X38] :
      ( ( v1_funct_1(k1_partfun1(X33,X34,X35,X36,X37,X38))
        | ~ v1_funct_1(X37)
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
        | ~ v1_funct_1(X38)
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) )
      & ( m1_subset_1(k1_partfun1(X33,X34,X35,X36,X37,X38),k1_zfmisc_1(k2_zfmisc_1(X33,X36)))
        | ~ v1_funct_1(X37)
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
        | ~ v1_funct_1(X38)
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).

cnf(c_0_72,negated_conjecture,
    ( k2_relat_1(k5_relat_1(esk3_0,k2_funct_1(esk3_0))) = k1_relat_1(esk3_0)
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_39]),c_0_40]),c_0_64])])).

cnf(c_0_73,negated_conjecture,
    ( v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67])])).

cnf(c_0_74,plain,
    ( X3 = k1_xboole_0
    | k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(X2)
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_68,c_0_33])).

cnf(c_0_75,negated_conjecture,
    ( k5_relat_1(esk3_0,k2_funct_1(esk3_0)) = k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_66]),c_0_70])])).

cnf(c_0_76,plain,
    ( m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X6)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_77,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_78,negated_conjecture,
    ( k2_relat_1(k5_relat_1(esk3_0,k2_funct_1(esk3_0))) = k1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_73])])).

cnf(c_0_79,negated_conjecture,
    ( k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,k2_funct_1(esk3_0)) = k6_relat_1(X1)
    | X2 = k1_xboole_0
    | k2_relset_1(X1,X2,esk3_0) != X2
    | ~ v1_funct_2(esk3_0,X1,X2)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_37]),c_0_38])]),c_0_75])).

cnf(c_0_80,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_81,negated_conjecture,
    ( m1_subset_1(k1_partfun1(esk1_0,esk2_0,X1,X2,esk3_0,X3),k1_zfmisc_1(k2_zfmisc_1(esk1_0,X2)))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_28]),c_0_38])])).

cnf(c_0_82,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_83,negated_conjecture,
    ( v4_relat_1(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_77])).

cnf(c_0_84,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_77])).

cnf(c_0_85,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

fof(c_0_86,plain,(
    ! [X29,X30,X31,X32] :
      ( ( ~ r2_relset_1(X29,X30,X31,X32)
        | X31 = X32
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) )
      & ( X31 != X32
        | r2_relset_1(X29,X30,X31,X32)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).

cnf(c_0_87,negated_conjecture,
    ( k2_relat_1(k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,k2_funct_1(esk3_0))) = k1_relat_1(esk3_0) ),
    inference(rw,[status(thm)],[c_0_78,c_0_75])).

cnf(c_0_88,negated_conjecture,
    ( k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,k2_funct_1(esk3_0)) = k6_relat_1(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_28]),c_0_30]),c_0_58])]),c_0_80])).

cnf(c_0_89,negated_conjecture,
    ( m1_subset_1(k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_77]),c_0_82])])).

cnf(c_0_90,negated_conjecture,
    ( k2_relat_1(k5_relat_1(esk3_0,X1)) = k2_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),esk2_0)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_40]),c_0_39])])).

cnf(c_0_91,negated_conjecture,
    ( k2_relat_1(esk4_0) = k2_relset_1(esk2_0,esk1_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_77])).

cnf(c_0_92,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk4_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_83]),c_0_84])])).

cnf(c_0_93,plain,
    ( k2_relat_1(k5_relat_1(X1,k6_relat_1(X2))) = X2
    | ~ r1_tarski(X2,k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_54]),c_0_85]),c_0_55])])).

cnf(c_0_94,plain,
    ( X3 = X4
    | ~ r2_relset_1(X1,X2,X3,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_95,negated_conjecture,
    ( r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_partfun1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_96,negated_conjecture,
    ( k2_relat_1(k5_relat_1(k2_funct_1(esk3_0),X1)) = k2_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),k1_relat_1(esk3_0))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_51]),c_0_73])])).

cnf(c_0_97,negated_conjecture,
    ( k1_relat_1(esk3_0) = esk1_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87,c_0_88]),c_0_85])).

cnf(c_0_98,negated_conjecture,
    ( v4_relat_1(k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_89])).

cnf(c_0_99,negated_conjecture,
    ( v1_relat_1(k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_89]),c_0_67])])).

cnf(c_0_100,negated_conjecture,
    ( k2_relat_1(k5_relat_1(esk3_0,esk4_0)) = k2_relset_1(esk2_0,esk1_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_84]),c_0_91]),c_0_92])])).

cnf(c_0_101,negated_conjecture,
    ( k5_relat_1(esk3_0,esk4_0) = k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_77]),c_0_82])])).

cnf(c_0_102,negated_conjecture,
    ( k2_relat_1(k5_relat_1(k2_funct_1(esk3_0),k6_relat_1(X1))) = X1
    | ~ r1_tarski(X1,k1_relat_1(esk3_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_73]),c_0_51])).

fof(c_0_103,plain,(
    ! [X51,X52,X53,X54,X55] :
      ( ( v2_funct_1(X54)
        | X53 = k1_xboole_0
        | ~ v2_funct_1(k1_partfun1(X51,X52,X52,X53,X54,X55))
        | k2_relset_1(X51,X52,X54) != X52
        | ~ v1_funct_1(X55)
        | ~ v1_funct_2(X55,X52,X53)
        | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))
        | ~ v1_funct_1(X54)
        | ~ v1_funct_2(X54,X51,X52)
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X51,X52))) )
      & ( v2_funct_1(X55)
        | X53 = k1_xboole_0
        | ~ v2_funct_1(k1_partfun1(X51,X52,X52,X53,X54,X55))
        | k2_relset_1(X51,X52,X54) != X52
        | ~ v1_funct_1(X55)
        | ~ v1_funct_2(X55,X52,X53)
        | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))
        | ~ v1_funct_1(X54)
        | ~ v1_funct_2(X54,X51,X52)
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X51,X52))) )
      & ( v2_funct_1(X54)
        | X52 != k1_xboole_0
        | ~ v2_funct_1(k1_partfun1(X51,X52,X52,X53,X54,X55))
        | k2_relset_1(X51,X52,X54) != X52
        | ~ v1_funct_1(X55)
        | ~ v1_funct_2(X55,X52,X53)
        | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))
        | ~ v1_funct_1(X54)
        | ~ v1_funct_2(X54,X51,X52)
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X51,X52))) )
      & ( v2_funct_1(X55)
        | X52 != k1_xboole_0
        | ~ v2_funct_1(k1_partfun1(X51,X52,X52,X53,X54,X55))
        | k2_relset_1(X51,X52,X54) != X52
        | ~ v1_funct_1(X55)
        | ~ v1_funct_2(X55,X52,X53)
        | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))
        | ~ v1_funct_1(X54)
        | ~ v1_funct_2(X54,X51,X52)
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X51,X52))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_funct_2])])])])).

cnf(c_0_104,negated_conjecture,
    ( k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0) = X1
    | ~ r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(spm,[status(thm)],[c_0_94,c_0_89])).

cnf(c_0_105,negated_conjecture,
    ( r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_relat_1(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_95,c_0_33])).

cnf(c_0_106,negated_conjecture,
    ( k2_relat_1(k5_relat_1(k2_funct_1(esk3_0),X1)) = k2_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),esk1_0)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_96,c_0_97])).

cnf(c_0_107,negated_conjecture,
    ( r1_tarski(k1_relat_1(k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0)),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_98]),c_0_99])])).

cnf(c_0_108,negated_conjecture,
    ( k2_relat_1(k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0)) = k2_relset_1(esk2_0,esk1_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_100,c_0_101])).

cnf(c_0_109,negated_conjecture,
    ( k2_relat_1(k5_relat_1(k2_funct_1(esk3_0),k6_relat_1(k1_relat_1(esk3_0)))) = k1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_102,c_0_64])).

cnf(c_0_110,negated_conjecture,
    ( v1_funct_2(esk4_0,esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_111,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_103])).

cnf(c_0_112,negated_conjecture,
    ( k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0) = k6_relat_1(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_44]),c_0_105])])).

cnf(c_0_113,plain,
    ( v2_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_114,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_115,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X2,X1,esk4_0) != X1
    | ~ v1_funct_2(esk4_0,X2,X1)
    | ~ v2_funct_1(esk4_0)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_47,c_0_82])).

cnf(c_0_116,negated_conjecture,
    ( k2_relat_1(k5_relat_1(k2_funct_1(esk3_0),k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0))) = k2_relset_1(esk2_0,esk1_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_107]),c_0_108]),c_0_99])])).

cnf(c_0_117,negated_conjecture,
    ( k2_relat_1(k5_relat_1(k2_funct_1(esk3_0),k6_relat_1(esk1_0))) = esk1_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_109,c_0_97]),c_0_97])).

cnf(c_0_118,negated_conjecture,
    ( v1_funct_1(k2_funct_1(esk4_0))
    | k2_relset_1(esk2_0,esk1_0,esk4_0) != esk1_0
    | ~ v2_funct_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_77]),c_0_110]),c_0_82])])).

cnf(c_0_119,negated_conjecture,
    ( v2_funct_1(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_112]),c_0_30]),c_0_58]),c_0_110]),c_0_38]),c_0_82]),c_0_113]),c_0_28]),c_0_77])]),c_0_114])).

cnf(c_0_120,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    | k2_relset_1(esk2_0,esk1_0,esk4_0) != esk1_0
    | ~ v2_funct_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_77]),c_0_110])])).

cnf(c_0_121,negated_conjecture,
    ( k2_relset_1(esk2_0,esk1_0,esk4_0) = esk1_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_116,c_0_112]),c_0_117])).

cnf(c_0_122,plain,
    ( v2_funct_1(X1)
    | X2 = k1_xboole_0
    | ~ v2_funct_1(k1_partfun1(X3,X4,X4,X2,X1,X5))
    | k2_relset_1(X3,X4,X1) != X4
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,X4,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_103])).

cnf(c_0_123,plain,
    ( v1_funct_2(k2_funct_1(X1),X2,X3)
    | ~ v2_funct_1(X1)
    | k2_relset_1(X3,X2,X1) != X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_124,negated_conjecture,
    ( v1_funct_1(k2_funct_1(esk4_0))
    | k2_relset_1(esk2_0,esk1_0,esk4_0) != esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_118,c_0_119])])).

cnf(c_0_125,plain,
    ( k5_relat_1(k2_funct_1(X1),X1) = k6_partfun1(X2)
    | X2 = k1_xboole_0
    | k2_relset_1(X3,X2,X1) != X2
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_126,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_120,c_0_119])]),c_0_121])])).

fof(c_0_127,plain,(
    ! [X18,X19] :
      ( ~ v1_relat_1(X18)
      | ~ v1_funct_1(X18)
      | ~ v1_relat_1(X19)
      | ~ v1_funct_1(X19)
      | ~ v2_funct_1(X18)
      | k2_relat_1(X19) != k1_relat_1(X18)
      | k5_relat_1(X19,X18) != k6_relat_1(k2_relat_1(X18))
      | X19 = k2_funct_1(X18) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_funct_1])])])).

cnf(c_0_128,negated_conjecture,
    ( X1 = k1_xboole_0
    | v2_funct_1(X2)
    | k2_relset_1(X3,X4,X2) != X4
    | ~ v1_funct_2(esk4_0,X4,X1)
    | ~ v1_funct_2(X2,X3,X4)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(k1_partfun1(X3,X4,X4,X1,X2,esk4_0))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(spm,[status(thm)],[c_0_122,c_0_82])).

cnf(c_0_129,negated_conjecture,
    ( v1_funct_2(k2_funct_1(esk4_0),esk1_0,esk2_0)
    | k2_relset_1(esk2_0,esk1_0,esk4_0) != esk1_0
    | ~ v2_funct_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_110]),c_0_82]),c_0_77])])).

cnf(c_0_130,negated_conjecture,
    ( k2_relat_1(k2_funct_1(esk4_0)) = k1_relat_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_119]),c_0_82]),c_0_84])])).

cnf(c_0_131,negated_conjecture,
    ( v1_funct_1(k2_funct_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_124,c_0_121])])).

cnf(c_0_132,plain,
    ( X2 = k1_xboole_0
    | k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(X2)
    | k2_relset_1(X3,X2,X1) != X2
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(rw,[status(thm)],[c_0_125,c_0_33])).

cnf(c_0_133,negated_conjecture,
    ( k1_relat_1(k2_funct_1(esk4_0)) = esk1_0 ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_119]),c_0_91]),c_0_82]),c_0_84])]),c_0_121])).

cnf(c_0_134,negated_conjecture,
    ( v1_relat_1(k2_funct_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_126]),c_0_67])])).

cnf(c_0_135,plain,
    ( X2 = k2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X1)
    | k2_relat_1(X2) != k1_relat_1(X1)
    | k5_relat_1(X2,X1) != k6_relat_1(k2_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_127])).

cnf(c_0_136,negated_conjecture,
    ( v2_funct_1(X1)
    | k2_relset_1(X2,esk2_0,X1) != esk2_0
    | ~ v1_funct_2(X1,X2,esk2_0)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(k1_partfun1(X2,esk2_0,esk2_0,esk1_0,X1,esk4_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_77]),c_0_110])]),c_0_114])).

cnf(c_0_137,negated_conjecture,
    ( v1_funct_2(k2_funct_1(esk4_0),esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_129,c_0_119])]),c_0_121])])).

cnf(c_0_138,negated_conjecture,
    ( k2_relset_1(esk1_0,esk2_0,k2_funct_1(esk4_0)) = k1_relat_1(esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_126]),c_0_130])).

cnf(c_0_139,negated_conjecture,
    ( k1_partfun1(esk1_0,esk2_0,X1,X2,k2_funct_1(esk4_0),X3) = k5_relat_1(k2_funct_1(esk4_0),X3)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_126]),c_0_131])])).

cnf(c_0_140,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk4_0),esk4_0) = k6_relat_1(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132,c_0_121]),c_0_110]),c_0_82]),c_0_119]),c_0_77])]),c_0_114])).

cnf(c_0_141,negated_conjecture,
    ( k2_relat_1(k5_relat_1(X1,k2_funct_1(esk4_0))) = k1_relat_1(esk4_0)
    | ~ r1_tarski(esk1_0,k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_133]),c_0_130]),c_0_134])])).

cnf(c_0_142,negated_conjecture,
    ( k2_relat_1(esk4_0) = esk1_0 ),
    inference(rw,[status(thm)],[c_0_91,c_0_121])).

cnf(c_0_143,negated_conjecture,
    ( k5_relat_1(esk4_0,k2_funct_1(esk4_0)) = k6_relat_1(X1)
    | X2 = k1_xboole_0
    | k2_relset_1(X1,X2,esk4_0) != X2
    | ~ v1_funct_2(esk4_0,X1,X2)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_119]),c_0_82])])).

cnf(c_0_144,negated_conjecture,
    ( X1 = k2_funct_1(k2_funct_1(esk4_0))
    | k5_relat_1(X1,k2_funct_1(esk4_0)) != k6_relat_1(k1_relat_1(esk4_0))
    | k2_relat_1(X1) != esk1_0
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(k2_funct_1(esk4_0))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_131]),c_0_130]),c_0_133]),c_0_134])])).

cnf(c_0_145,negated_conjecture,
    ( v2_funct_1(k2_funct_1(esk4_0))
    | k1_relat_1(esk4_0) != esk2_0
    | ~ v2_funct_1(k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,k2_funct_1(esk4_0),esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136,c_0_137]),c_0_131])]),c_0_138]),c_0_126])])).

cnf(c_0_146,negated_conjecture,
    ( k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,k2_funct_1(esk4_0),esk4_0) = k6_relat_1(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_139,c_0_77]),c_0_140]),c_0_82])])).

cnf(c_0_147,negated_conjecture,
    ( k2_relat_1(k5_relat_1(esk4_0,k2_funct_1(esk4_0))) = k1_relat_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_141,c_0_142]),c_0_64]),c_0_84])])).

cnf(c_0_148,negated_conjecture,
    ( k5_relat_1(esk4_0,k2_funct_1(esk4_0)) = k6_relat_1(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_77]),c_0_121]),c_0_110])]),c_0_114])).

cnf(c_0_149,negated_conjecture,
    ( X1 = k2_funct_1(esk4_0)
    | k5_relat_1(X1,esk4_0) != k6_relat_1(k2_relset_1(esk2_0,esk1_0,esk4_0))
    | k2_relat_1(X1) != k1_relat_1(esk4_0)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(esk4_0)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_82]),c_0_84])]),c_0_91])).

cnf(c_0_150,negated_conjecture,
    ( k2_funct_1(k2_funct_1(esk4_0)) = esk4_0
    | k5_relat_1(esk4_0,k2_funct_1(esk4_0)) != k6_relat_1(k1_relat_1(esk4_0))
    | ~ v2_funct_1(k2_funct_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_144,c_0_142]),c_0_82]),c_0_84])])).

cnf(c_0_151,negated_conjecture,
    ( v2_funct_1(k2_funct_1(esk4_0))
    | k1_relat_1(esk4_0) != esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_145,c_0_146]),c_0_113])])).

cnf(c_0_152,negated_conjecture,
    ( k1_relat_1(esk4_0) = esk2_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_147,c_0_148]),c_0_85])).

cnf(c_0_153,negated_conjecture,
    ( X1 = k2_funct_1(esk4_0)
    | k5_relat_1(X1,esk4_0) != k6_relat_1(esk1_0)
    | k2_relat_1(X1) != k1_relat_1(esk4_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_149,c_0_119])]),c_0_121])).

cnf(c_0_154,negated_conjecture,
    ( k2_funct_1(k2_funct_1(esk4_0)) = esk4_0
    | k6_relat_1(k1_relat_1(esk4_0)) != k6_relat_1(esk2_0)
    | ~ v2_funct_1(k2_funct_1(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_150,c_0_148])).

cnf(c_0_155,negated_conjecture,
    ( v2_funct_1(k2_funct_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_151,c_0_152])])).

cnf(c_0_156,negated_conjecture,
    ( X1 = k2_funct_1(esk4_0)
    | k5_relat_1(X1,esk4_0) != k6_relat_1(esk1_0)
    | k2_relat_1(X1) != esk2_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_153,c_0_152])).

cnf(c_0_157,negated_conjecture,
    ( k2_funct_1(k2_funct_1(esk4_0)) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_154,c_0_152])]),c_0_155])])).

cnf(c_0_158,negated_conjecture,
    ( k2_funct_1(esk4_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_156,c_0_40]),c_0_101]),c_0_112]),c_0_38]),c_0_39])])).

cnf(c_0_159,negated_conjecture,
    ( esk4_0 != k2_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_160,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_157,c_0_158]),c_0_159]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.32  % Computer   : n017.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % WCLimit    : 600
% 0.13/0.32  % DateTime   : Tue Dec  1 20:51:16 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.33  # No SInE strategy applied
% 0.13/0.33  # Trying AutoSched0 for 299 seconds
% 0.19/0.47  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S05EI
% 0.19/0.47  # and selection function SelectDivPreferIntoLits.
% 0.19/0.47  #
% 0.19/0.47  # Preprocessing time       : 0.029 s
% 0.19/0.47  # Presaturation interreduction done
% 0.19/0.47  
% 0.19/0.47  # Proof found!
% 0.19/0.47  # SZS status Theorem
% 0.19/0.47  # SZS output start CNFRefutation
% 0.19/0.47  fof(t36_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(((k2_relset_1(X1,X2,X3)=X2&r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1)))&v2_funct_1(X3))=>(X1=k1_xboole_0|X2=k1_xboole_0|X4=k2_funct_1(X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 0.19/0.47  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.19/0.47  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.19/0.47  fof(dt_k6_partfun1, axiom, ![X1]:(v1_partfun1(k6_partfun1(X1),X1)&m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 0.19/0.47  fof(redefinition_k6_partfun1, axiom, ![X1]:k6_partfun1(X1)=k6_relat_1(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 0.19/0.47  fof(t55_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))&k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 0.19/0.47  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.19/0.47  fof(t31_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 0.19/0.47  fof(t47_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X1),k2_relat_1(X2))=>k2_relat_1(k5_relat_1(X2,X1))=k2_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_relat_1)).
% 0.19/0.47  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 0.19/0.47  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 0.19/0.47  fof(fc4_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v2_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 0.19/0.47  fof(redefinition_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>k1_partfun1(X1,X2,X3,X4,X5,X6)=k5_relat_1(X5,X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 0.19/0.47  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.19/0.47  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.19/0.47  fof(t35_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((k2_relset_1(X1,X2,X3)=X2&v2_funct_1(X3))=>(X2=k1_xboole_0|(k5_relat_1(X3,k2_funct_1(X3))=k6_partfun1(X1)&k5_relat_1(k2_funct_1(X3),X3)=k6_partfun1(X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 0.19/0.47  fof(dt_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>(v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))&m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 0.19/0.47  fof(redefinition_r2_relset_1, axiom, ![X1, X2, X3, X4]:((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_relset_1(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 0.19/0.47  fof(t30_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X2,X3))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>((v2_funct_1(k1_partfun1(X1,X2,X2,X3,X4,X5))&k2_relset_1(X1,X2,X4)=X2)=>((X3=k1_xboole_0&X2!=k1_xboole_0)|(v2_funct_1(X4)&v2_funct_1(X5)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_funct_2)).
% 0.19/0.47  fof(t64_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(((v2_funct_1(X1)&k2_relat_1(X2)=k1_relat_1(X1))&k5_relat_1(X2,X1)=k6_relat_1(k2_relat_1(X1)))=>X2=k2_funct_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_1)).
% 0.19/0.47  fof(c_0_20, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(((k2_relset_1(X1,X2,X3)=X2&r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1)))&v2_funct_1(X3))=>(X1=k1_xboole_0|X2=k1_xboole_0|X4=k2_funct_1(X3)))))), inference(assume_negation,[status(cth)],[t36_funct_2])).
% 0.19/0.47  fof(c_0_21, plain, ![X20, X21, X22]:(~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))|v1_relat_1(X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.19/0.47  fof(c_0_22, negated_conjecture, (((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,esk1_0,esk2_0))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))))&(((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,esk2_0,esk1_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))))&(((k2_relset_1(esk1_0,esk2_0,esk3_0)=esk2_0&r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_partfun1(esk1_0)))&v2_funct_1(esk3_0))&((esk1_0!=k1_xboole_0&esk2_0!=k1_xboole_0)&esk4_0!=k2_funct_1(esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).
% 0.19/0.47  fof(c_0_23, plain, ![X26, X27, X28]:(~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))|k2_relset_1(X26,X27,X28)=k2_relat_1(X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.19/0.47  fof(c_0_24, plain, ![X39]:(v1_partfun1(k6_partfun1(X39),X39)&m1_subset_1(k6_partfun1(X39),k1_zfmisc_1(k2_zfmisc_1(X39,X39)))), inference(variable_rename,[status(thm)],[dt_k6_partfun1])).
% 0.19/0.47  fof(c_0_25, plain, ![X46]:k6_partfun1(X46)=k6_relat_1(X46), inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).
% 0.19/0.47  fof(c_0_26, plain, ![X17]:((k2_relat_1(X17)=k1_relat_1(k2_funct_1(X17))|~v2_funct_1(X17)|(~v1_relat_1(X17)|~v1_funct_1(X17)))&(k1_relat_1(X17)=k2_relat_1(k2_funct_1(X17))|~v2_funct_1(X17)|(~v1_relat_1(X17)|~v1_funct_1(X17)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).
% 0.19/0.47  cnf(c_0_27, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.47  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.47  cnf(c_0_29, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.47  cnf(c_0_30, negated_conjecture, (k2_relset_1(esk1_0,esk2_0,esk3_0)=esk2_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.47  fof(c_0_31, plain, ![X23, X24, X25]:((v4_relat_1(X25,X23)|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))))&(v5_relat_1(X25,X24)|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.19/0.47  cnf(c_0_32, plain, (m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.47  cnf(c_0_33, plain, (k6_partfun1(X1)=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.47  fof(c_0_34, plain, ![X56, X57, X58]:(((v1_funct_1(k2_funct_1(X58))|(~v2_funct_1(X58)|k2_relset_1(X56,X57,X58)!=X57)|(~v1_funct_1(X58)|~v1_funct_2(X58,X56,X57)|~m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57)))))&(v1_funct_2(k2_funct_1(X58),X57,X56)|(~v2_funct_1(X58)|k2_relset_1(X56,X57,X58)!=X57)|(~v1_funct_1(X58)|~v1_funct_2(X58,X56,X57)|~m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57))))))&(m1_subset_1(k2_funct_1(X58),k1_zfmisc_1(k2_zfmisc_1(X57,X56)))|(~v2_funct_1(X58)|k2_relset_1(X56,X57,X58)!=X57)|(~v1_funct_1(X58)|~v1_funct_2(X58,X56,X57)|~m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_funct_2])])])).
% 0.19/0.47  fof(c_0_35, plain, ![X13, X14]:(~v1_relat_1(X13)|(~v1_relat_1(X14)|(~r1_tarski(k1_relat_1(X13),k2_relat_1(X14))|k2_relat_1(k5_relat_1(X14,X13))=k2_relat_1(X13)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t47_relat_1])])])).
% 0.19/0.47  cnf(c_0_36, plain, (k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.47  cnf(c_0_37, negated_conjecture, (v2_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.47  cnf(c_0_38, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.47  cnf(c_0_39, negated_conjecture, (v1_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.19/0.47  cnf(c_0_40, negated_conjecture, (k2_relat_1(esk3_0)=esk2_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_28]), c_0_30])).
% 0.19/0.47  cnf(c_0_41, plain, (k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.47  fof(c_0_42, plain, ![X9, X10]:((~v4_relat_1(X10,X9)|r1_tarski(k1_relat_1(X10),X9)|~v1_relat_1(X10))&(~r1_tarski(k1_relat_1(X10),X9)|v4_relat_1(X10,X9)|~v1_relat_1(X10))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.19/0.47  cnf(c_0_43, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.47  cnf(c_0_44, plain, (m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(rw,[status(thm)],[c_0_32, c_0_33])).
% 0.19/0.47  fof(c_0_45, plain, ![X15]:(k1_relat_1(k6_relat_1(X15))=X15&k2_relat_1(k6_relat_1(X15))=X15), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.19/0.47  fof(c_0_46, plain, ![X16]:(v1_relat_1(k6_relat_1(X16))&v2_funct_1(k6_relat_1(X16))), inference(variable_rename,[status(thm)],[fc4_funct_1])).
% 0.19/0.47  cnf(c_0_47, plain, (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v2_funct_1(X1)|k2_relset_1(X3,X2,X1)!=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.47  fof(c_0_48, plain, ![X40, X41, X42, X43, X44, X45]:(~v1_funct_1(X44)|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))|~v1_funct_1(X45)|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))|k1_partfun1(X40,X41,X42,X43,X44,X45)=k5_relat_1(X44,X45)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).
% 0.19/0.47  cnf(c_0_49, plain, (k2_relat_1(k5_relat_1(X2,X1))=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(k1_relat_1(X1),k2_relat_1(X2))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.47  cnf(c_0_50, negated_conjecture, (k1_relat_1(k2_funct_1(esk3_0))=esk2_0), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38]), c_0_39])]), c_0_40])).
% 0.19/0.47  cnf(c_0_51, negated_conjecture, (k2_relat_1(k2_funct_1(esk3_0))=k1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_37]), c_0_38]), c_0_39])])).
% 0.19/0.47  cnf(c_0_52, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.47  cnf(c_0_53, plain, (v4_relat_1(k6_relat_1(X1),X1)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.19/0.47  cnf(c_0_54, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.19/0.47  cnf(c_0_55, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.19/0.47  fof(c_0_56, plain, ![X7, X8]:(~v1_relat_1(X7)|(~m1_subset_1(X8,k1_zfmisc_1(X7))|v1_relat_1(X8))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.19/0.47  cnf(c_0_57, negated_conjecture, (m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|k2_relset_1(X2,X1,esk3_0)!=X1|~v1_funct_2(esk3_0,X2,X1)|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_38]), c_0_37])])).
% 0.19/0.47  cnf(c_0_58, negated_conjecture, (v1_funct_2(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.47  fof(c_0_59, plain, ![X11, X12]:v1_relat_1(k2_zfmisc_1(X11,X12)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.19/0.47  fof(c_0_60, plain, ![X59, X60, X61]:((k5_relat_1(X61,k2_funct_1(X61))=k6_partfun1(X59)|X60=k1_xboole_0|(k2_relset_1(X59,X60,X61)!=X60|~v2_funct_1(X61))|(~v1_funct_1(X61)|~v1_funct_2(X61,X59,X60)|~m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X59,X60)))))&(k5_relat_1(k2_funct_1(X61),X61)=k6_partfun1(X60)|X60=k1_xboole_0|(k2_relset_1(X59,X60,X61)!=X60|~v2_funct_1(X61))|(~v1_funct_1(X61)|~v1_funct_2(X61,X59,X60)|~m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X59,X60)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_funct_2])])])).
% 0.19/0.47  cnf(c_0_61, plain, (k1_partfun1(X2,X3,X5,X6,X1,X4)=k5_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.47  cnf(c_0_62, plain, (v1_funct_1(k2_funct_1(X1))|~v2_funct_1(X1)|k2_relset_1(X2,X3,X1)!=X3|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.47  cnf(c_0_63, negated_conjecture, (k2_relat_1(k5_relat_1(X1,k2_funct_1(esk3_0)))=k1_relat_1(esk3_0)|~r1_tarski(esk2_0,k2_relat_1(X1))|~v1_relat_1(k2_funct_1(esk3_0))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51])).
% 0.19/0.47  cnf(c_0_64, plain, (r1_tarski(X1,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54]), c_0_55])])).
% 0.19/0.47  cnf(c_0_65, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.19/0.47  cnf(c_0_66, negated_conjecture, (m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_30]), c_0_58]), c_0_28])])).
% 0.19/0.47  cnf(c_0_67, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.19/0.47  cnf(c_0_68, plain, (k5_relat_1(X1,k2_funct_1(X1))=k6_partfun1(X2)|X3=k1_xboole_0|k2_relset_1(X2,X3,X1)!=X3|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.19/0.47  cnf(c_0_69, negated_conjecture, (k1_partfun1(esk1_0,esk2_0,X1,X2,esk3_0,X3)=k5_relat_1(esk3_0,X3)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_28]), c_0_38])])).
% 0.19/0.47  cnf(c_0_70, negated_conjecture, (v1_funct_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_28]), c_0_30]), c_0_58]), c_0_38]), c_0_37])])).
% 0.19/0.47  fof(c_0_71, plain, ![X33, X34, X35, X36, X37, X38]:((v1_funct_1(k1_partfun1(X33,X34,X35,X36,X37,X38))|(~v1_funct_1(X37)|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))|~v1_funct_1(X38)|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))))&(m1_subset_1(k1_partfun1(X33,X34,X35,X36,X37,X38),k1_zfmisc_1(k2_zfmisc_1(X33,X36)))|(~v1_funct_1(X37)|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))|~v1_funct_1(X38)|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).
% 0.19/0.47  cnf(c_0_72, negated_conjecture, (k2_relat_1(k5_relat_1(esk3_0,k2_funct_1(esk3_0)))=k1_relat_1(esk3_0)|~v1_relat_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_39]), c_0_40]), c_0_64])])).
% 0.19/0.47  cnf(c_0_73, negated_conjecture, (v1_relat_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67])])).
% 0.19/0.47  cnf(c_0_74, plain, (X3=k1_xboole_0|k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(X2)|k2_relset_1(X2,X3,X1)!=X3|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(rw,[status(thm)],[c_0_68, c_0_33])).
% 0.19/0.47  cnf(c_0_75, negated_conjecture, (k5_relat_1(esk3_0,k2_funct_1(esk3_0))=k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_66]), c_0_70])])).
% 0.19/0.47  cnf(c_0_76, plain, (m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X6)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.19/0.47  cnf(c_0_77, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.47  cnf(c_0_78, negated_conjecture, (k2_relat_1(k5_relat_1(esk3_0,k2_funct_1(esk3_0)))=k1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_72, c_0_73])])).
% 0.19/0.47  cnf(c_0_79, negated_conjecture, (k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,k2_funct_1(esk3_0))=k6_relat_1(X1)|X2=k1_xboole_0|k2_relset_1(X1,X2,esk3_0)!=X2|~v1_funct_2(esk3_0,X1,X2)|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_37]), c_0_38])]), c_0_75])).
% 0.19/0.47  cnf(c_0_80, negated_conjecture, (esk2_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.47  cnf(c_0_81, negated_conjecture, (m1_subset_1(k1_partfun1(esk1_0,esk2_0,X1,X2,esk3_0,X3),k1_zfmisc_1(k2_zfmisc_1(esk1_0,X2)))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_28]), c_0_38])])).
% 0.19/0.47  cnf(c_0_82, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.47  cnf(c_0_83, negated_conjecture, (v4_relat_1(esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_43, c_0_77])).
% 0.19/0.47  cnf(c_0_84, negated_conjecture, (v1_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_27, c_0_77])).
% 0.19/0.47  cnf(c_0_85, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.19/0.47  fof(c_0_86, plain, ![X29, X30, X31, X32]:((~r2_relset_1(X29,X30,X31,X32)|X31=X32|(~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))))&(X31!=X32|r2_relset_1(X29,X30,X31,X32)|(~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).
% 0.19/0.47  cnf(c_0_87, negated_conjecture, (k2_relat_1(k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,k2_funct_1(esk3_0)))=k1_relat_1(esk3_0)), inference(rw,[status(thm)],[c_0_78, c_0_75])).
% 0.19/0.47  cnf(c_0_88, negated_conjecture, (k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,k2_funct_1(esk3_0))=k6_relat_1(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_28]), c_0_30]), c_0_58])]), c_0_80])).
% 0.19/0.47  cnf(c_0_89, negated_conjecture, (m1_subset_1(k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_77]), c_0_82])])).
% 0.19/0.47  cnf(c_0_90, negated_conjecture, (k2_relat_1(k5_relat_1(esk3_0,X1))=k2_relat_1(X1)|~r1_tarski(k1_relat_1(X1),esk2_0)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_40]), c_0_39])])).
% 0.19/0.47  cnf(c_0_91, negated_conjecture, (k2_relat_1(esk4_0)=k2_relset_1(esk2_0,esk1_0,esk4_0)), inference(spm,[status(thm)],[c_0_29, c_0_77])).
% 0.19/0.47  cnf(c_0_92, negated_conjecture, (r1_tarski(k1_relat_1(esk4_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_83]), c_0_84])])).
% 0.19/0.47  cnf(c_0_93, plain, (k2_relat_1(k5_relat_1(X1,k6_relat_1(X2)))=X2|~r1_tarski(X2,k2_relat_1(X1))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_54]), c_0_85]), c_0_55])])).
% 0.19/0.47  cnf(c_0_94, plain, (X3=X4|~r2_relset_1(X1,X2,X3,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_86])).
% 0.19/0.47  cnf(c_0_95, negated_conjecture, (r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_partfun1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.47  cnf(c_0_96, negated_conjecture, (k2_relat_1(k5_relat_1(k2_funct_1(esk3_0),X1))=k2_relat_1(X1)|~r1_tarski(k1_relat_1(X1),k1_relat_1(esk3_0))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_51]), c_0_73])])).
% 0.19/0.47  cnf(c_0_97, negated_conjecture, (k1_relat_1(esk3_0)=esk1_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87, c_0_88]), c_0_85])).
% 0.19/0.47  cnf(c_0_98, negated_conjecture, (v4_relat_1(k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),esk1_0)), inference(spm,[status(thm)],[c_0_43, c_0_89])).
% 0.19/0.47  cnf(c_0_99, negated_conjecture, (v1_relat_1(k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_89]), c_0_67])])).
% 0.19/0.47  cnf(c_0_100, negated_conjecture, (k2_relat_1(k5_relat_1(esk3_0,esk4_0))=k2_relset_1(esk2_0,esk1_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_84]), c_0_91]), c_0_92])])).
% 0.19/0.47  cnf(c_0_101, negated_conjecture, (k5_relat_1(esk3_0,esk4_0)=k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_77]), c_0_82])])).
% 0.19/0.47  cnf(c_0_102, negated_conjecture, (k2_relat_1(k5_relat_1(k2_funct_1(esk3_0),k6_relat_1(X1)))=X1|~r1_tarski(X1,k1_relat_1(esk3_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_73]), c_0_51])).
% 0.19/0.47  fof(c_0_103, plain, ![X51, X52, X53, X54, X55]:(((v2_funct_1(X54)|X53=k1_xboole_0|(~v2_funct_1(k1_partfun1(X51,X52,X52,X53,X54,X55))|k2_relset_1(X51,X52,X54)!=X52)|(~v1_funct_1(X55)|~v1_funct_2(X55,X52,X53)|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X52,X53))))|(~v1_funct_1(X54)|~v1_funct_2(X54,X51,X52)|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))))&(v2_funct_1(X55)|X53=k1_xboole_0|(~v2_funct_1(k1_partfun1(X51,X52,X52,X53,X54,X55))|k2_relset_1(X51,X52,X54)!=X52)|(~v1_funct_1(X55)|~v1_funct_2(X55,X52,X53)|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X52,X53))))|(~v1_funct_1(X54)|~v1_funct_2(X54,X51,X52)|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X51,X52))))))&((v2_funct_1(X54)|X52!=k1_xboole_0|(~v2_funct_1(k1_partfun1(X51,X52,X52,X53,X54,X55))|k2_relset_1(X51,X52,X54)!=X52)|(~v1_funct_1(X55)|~v1_funct_2(X55,X52,X53)|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X52,X53))))|(~v1_funct_1(X54)|~v1_funct_2(X54,X51,X52)|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))))&(v2_funct_1(X55)|X52!=k1_xboole_0|(~v2_funct_1(k1_partfun1(X51,X52,X52,X53,X54,X55))|k2_relset_1(X51,X52,X54)!=X52)|(~v1_funct_1(X55)|~v1_funct_2(X55,X52,X53)|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X52,X53))))|(~v1_funct_1(X54)|~v1_funct_2(X54,X51,X52)|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X51,X52))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_funct_2])])])])).
% 0.19/0.47  cnf(c_0_104, negated_conjecture, (k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0)=X1|~r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(spm,[status(thm)],[c_0_94, c_0_89])).
% 0.19/0.47  cnf(c_0_105, negated_conjecture, (r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_relat_1(esk1_0))), inference(rw,[status(thm)],[c_0_95, c_0_33])).
% 0.19/0.47  cnf(c_0_106, negated_conjecture, (k2_relat_1(k5_relat_1(k2_funct_1(esk3_0),X1))=k2_relat_1(X1)|~r1_tarski(k1_relat_1(X1),esk1_0)|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_96, c_0_97])).
% 0.19/0.47  cnf(c_0_107, negated_conjecture, (r1_tarski(k1_relat_1(k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0)),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_98]), c_0_99])])).
% 0.19/0.47  cnf(c_0_108, negated_conjecture, (k2_relat_1(k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0))=k2_relset_1(esk2_0,esk1_0,esk4_0)), inference(rw,[status(thm)],[c_0_100, c_0_101])).
% 0.19/0.47  cnf(c_0_109, negated_conjecture, (k2_relat_1(k5_relat_1(k2_funct_1(esk3_0),k6_relat_1(k1_relat_1(esk3_0))))=k1_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_102, c_0_64])).
% 0.19/0.47  cnf(c_0_110, negated_conjecture, (v1_funct_2(esk4_0,esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.47  cnf(c_0_111, plain, (v2_funct_1(X1)|X2=k1_xboole_0|~v2_funct_1(k1_partfun1(X3,X4,X4,X2,X5,X1))|k2_relset_1(X3,X4,X5)!=X4|~v1_funct_1(X1)|~v1_funct_2(X1,X4,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|~v1_funct_1(X5)|~v1_funct_2(X5,X3,X4)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_103])).
% 0.19/0.47  cnf(c_0_112, negated_conjecture, (k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0)=k6_relat_1(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_44]), c_0_105])])).
% 0.19/0.47  cnf(c_0_113, plain, (v2_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.19/0.47  cnf(c_0_114, negated_conjecture, (esk1_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.47  cnf(c_0_115, negated_conjecture, (m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|k2_relset_1(X2,X1,esk4_0)!=X1|~v1_funct_2(esk4_0,X2,X1)|~v2_funct_1(esk4_0)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))), inference(spm,[status(thm)],[c_0_47, c_0_82])).
% 0.19/0.47  cnf(c_0_116, negated_conjecture, (k2_relat_1(k5_relat_1(k2_funct_1(esk3_0),k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0)))=k2_relset_1(esk2_0,esk1_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_107]), c_0_108]), c_0_99])])).
% 0.19/0.47  cnf(c_0_117, negated_conjecture, (k2_relat_1(k5_relat_1(k2_funct_1(esk3_0),k6_relat_1(esk1_0)))=esk1_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_109, c_0_97]), c_0_97])).
% 0.19/0.47  cnf(c_0_118, negated_conjecture, (v1_funct_1(k2_funct_1(esk4_0))|k2_relset_1(esk2_0,esk1_0,esk4_0)!=esk1_0|~v2_funct_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_77]), c_0_110]), c_0_82])])).
% 0.19/0.47  cnf(c_0_119, negated_conjecture, (v2_funct_1(esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_112]), c_0_30]), c_0_58]), c_0_110]), c_0_38]), c_0_82]), c_0_113]), c_0_28]), c_0_77])]), c_0_114])).
% 0.19/0.47  cnf(c_0_120, negated_conjecture, (m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))|k2_relset_1(esk2_0,esk1_0,esk4_0)!=esk1_0|~v2_funct_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_77]), c_0_110])])).
% 0.19/0.47  cnf(c_0_121, negated_conjecture, (k2_relset_1(esk2_0,esk1_0,esk4_0)=esk1_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_116, c_0_112]), c_0_117])).
% 0.19/0.47  cnf(c_0_122, plain, (v2_funct_1(X1)|X2=k1_xboole_0|~v2_funct_1(k1_partfun1(X3,X4,X4,X2,X1,X5))|k2_relset_1(X3,X4,X1)!=X4|~v1_funct_1(X5)|~v1_funct_2(X5,X4,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_103])).
% 0.19/0.47  cnf(c_0_123, plain, (v1_funct_2(k2_funct_1(X1),X2,X3)|~v2_funct_1(X1)|k2_relset_1(X3,X2,X1)!=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.47  cnf(c_0_124, negated_conjecture, (v1_funct_1(k2_funct_1(esk4_0))|k2_relset_1(esk2_0,esk1_0,esk4_0)!=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_118, c_0_119])])).
% 0.19/0.47  cnf(c_0_125, plain, (k5_relat_1(k2_funct_1(X1),X1)=k6_partfun1(X2)|X2=k1_xboole_0|k2_relset_1(X3,X2,X1)!=X2|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.19/0.47  cnf(c_0_126, negated_conjecture, (m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_120, c_0_119])]), c_0_121])])).
% 0.19/0.47  fof(c_0_127, plain, ![X18, X19]:(~v1_relat_1(X18)|~v1_funct_1(X18)|(~v1_relat_1(X19)|~v1_funct_1(X19)|(~v2_funct_1(X18)|k2_relat_1(X19)!=k1_relat_1(X18)|k5_relat_1(X19,X18)!=k6_relat_1(k2_relat_1(X18))|X19=k2_funct_1(X18)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_funct_1])])])).
% 0.19/0.47  cnf(c_0_128, negated_conjecture, (X1=k1_xboole_0|v2_funct_1(X2)|k2_relset_1(X3,X4,X2)!=X4|~v1_funct_2(esk4_0,X4,X1)|~v1_funct_2(X2,X3,X4)|~v1_funct_1(X2)|~v2_funct_1(k1_partfun1(X3,X4,X4,X1,X2,esk4_0))|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(spm,[status(thm)],[c_0_122, c_0_82])).
% 0.19/0.47  cnf(c_0_129, negated_conjecture, (v1_funct_2(k2_funct_1(esk4_0),esk1_0,esk2_0)|k2_relset_1(esk2_0,esk1_0,esk4_0)!=esk1_0|~v2_funct_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123, c_0_110]), c_0_82]), c_0_77])])).
% 0.19/0.47  cnf(c_0_130, negated_conjecture, (k2_relat_1(k2_funct_1(esk4_0))=k1_relat_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_119]), c_0_82]), c_0_84])])).
% 0.19/0.47  cnf(c_0_131, negated_conjecture, (v1_funct_1(k2_funct_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_124, c_0_121])])).
% 0.19/0.47  cnf(c_0_132, plain, (X2=k1_xboole_0|k5_relat_1(k2_funct_1(X1),X1)=k6_relat_1(X2)|k2_relset_1(X3,X2,X1)!=X2|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(rw,[status(thm)],[c_0_125, c_0_33])).
% 0.19/0.47  cnf(c_0_133, negated_conjecture, (k1_relat_1(k2_funct_1(esk4_0))=esk1_0), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_119]), c_0_91]), c_0_82]), c_0_84])]), c_0_121])).
% 0.19/0.47  cnf(c_0_134, negated_conjecture, (v1_relat_1(k2_funct_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_126]), c_0_67])])).
% 0.19/0.47  cnf(c_0_135, plain, (X2=k2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v2_funct_1(X1)|k2_relat_1(X2)!=k1_relat_1(X1)|k5_relat_1(X2,X1)!=k6_relat_1(k2_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_127])).
% 0.19/0.47  cnf(c_0_136, negated_conjecture, (v2_funct_1(X1)|k2_relset_1(X2,esk2_0,X1)!=esk2_0|~v1_funct_2(X1,X2,esk2_0)|~v1_funct_1(X1)|~v2_funct_1(k1_partfun1(X2,esk2_0,esk2_0,esk1_0,X1,esk4_0))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,esk2_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_77]), c_0_110])]), c_0_114])).
% 0.19/0.47  cnf(c_0_137, negated_conjecture, (v1_funct_2(k2_funct_1(esk4_0),esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_129, c_0_119])]), c_0_121])])).
% 0.19/0.47  cnf(c_0_138, negated_conjecture, (k2_relset_1(esk1_0,esk2_0,k2_funct_1(esk4_0))=k1_relat_1(esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_126]), c_0_130])).
% 0.19/0.47  cnf(c_0_139, negated_conjecture, (k1_partfun1(esk1_0,esk2_0,X1,X2,k2_funct_1(esk4_0),X3)=k5_relat_1(k2_funct_1(esk4_0),X3)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_126]), c_0_131])])).
% 0.19/0.47  cnf(c_0_140, negated_conjecture, (k5_relat_1(k2_funct_1(esk4_0),esk4_0)=k6_relat_1(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132, c_0_121]), c_0_110]), c_0_82]), c_0_119]), c_0_77])]), c_0_114])).
% 0.19/0.47  cnf(c_0_141, negated_conjecture, (k2_relat_1(k5_relat_1(X1,k2_funct_1(esk4_0)))=k1_relat_1(esk4_0)|~r1_tarski(esk1_0,k2_relat_1(X1))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_133]), c_0_130]), c_0_134])])).
% 0.19/0.47  cnf(c_0_142, negated_conjecture, (k2_relat_1(esk4_0)=esk1_0), inference(rw,[status(thm)],[c_0_91, c_0_121])).
% 0.19/0.47  cnf(c_0_143, negated_conjecture, (k5_relat_1(esk4_0,k2_funct_1(esk4_0))=k6_relat_1(X1)|X2=k1_xboole_0|k2_relset_1(X1,X2,esk4_0)!=X2|~v1_funct_2(esk4_0,X1,X2)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_119]), c_0_82])])).
% 0.19/0.47  cnf(c_0_144, negated_conjecture, (X1=k2_funct_1(k2_funct_1(esk4_0))|k5_relat_1(X1,k2_funct_1(esk4_0))!=k6_relat_1(k1_relat_1(esk4_0))|k2_relat_1(X1)!=esk1_0|~v1_funct_1(X1)|~v2_funct_1(k2_funct_1(esk4_0))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135, c_0_131]), c_0_130]), c_0_133]), c_0_134])])).
% 0.19/0.47  cnf(c_0_145, negated_conjecture, (v2_funct_1(k2_funct_1(esk4_0))|k1_relat_1(esk4_0)!=esk2_0|~v2_funct_1(k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,k2_funct_1(esk4_0),esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136, c_0_137]), c_0_131])]), c_0_138]), c_0_126])])).
% 0.19/0.47  cnf(c_0_146, negated_conjecture, (k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,k2_funct_1(esk4_0),esk4_0)=k6_relat_1(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_139, c_0_77]), c_0_140]), c_0_82])])).
% 0.19/0.47  cnf(c_0_147, negated_conjecture, (k2_relat_1(k5_relat_1(esk4_0,k2_funct_1(esk4_0)))=k1_relat_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_141, c_0_142]), c_0_64]), c_0_84])])).
% 0.19/0.47  cnf(c_0_148, negated_conjecture, (k5_relat_1(esk4_0,k2_funct_1(esk4_0))=k6_relat_1(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143, c_0_77]), c_0_121]), c_0_110])]), c_0_114])).
% 0.19/0.47  cnf(c_0_149, negated_conjecture, (X1=k2_funct_1(esk4_0)|k5_relat_1(X1,esk4_0)!=k6_relat_1(k2_relset_1(esk2_0,esk1_0,esk4_0))|k2_relat_1(X1)!=k1_relat_1(esk4_0)|~v1_funct_1(X1)|~v2_funct_1(esk4_0)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135, c_0_82]), c_0_84])]), c_0_91])).
% 0.19/0.47  cnf(c_0_150, negated_conjecture, (k2_funct_1(k2_funct_1(esk4_0))=esk4_0|k5_relat_1(esk4_0,k2_funct_1(esk4_0))!=k6_relat_1(k1_relat_1(esk4_0))|~v2_funct_1(k2_funct_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_144, c_0_142]), c_0_82]), c_0_84])])).
% 0.19/0.47  cnf(c_0_151, negated_conjecture, (v2_funct_1(k2_funct_1(esk4_0))|k1_relat_1(esk4_0)!=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_145, c_0_146]), c_0_113])])).
% 0.19/0.47  cnf(c_0_152, negated_conjecture, (k1_relat_1(esk4_0)=esk2_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_147, c_0_148]), c_0_85])).
% 0.19/0.47  cnf(c_0_153, negated_conjecture, (X1=k2_funct_1(esk4_0)|k5_relat_1(X1,esk4_0)!=k6_relat_1(esk1_0)|k2_relat_1(X1)!=k1_relat_1(esk4_0)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_149, c_0_119])]), c_0_121])).
% 0.19/0.47  cnf(c_0_154, negated_conjecture, (k2_funct_1(k2_funct_1(esk4_0))=esk4_0|k6_relat_1(k1_relat_1(esk4_0))!=k6_relat_1(esk2_0)|~v2_funct_1(k2_funct_1(esk4_0))), inference(rw,[status(thm)],[c_0_150, c_0_148])).
% 0.19/0.47  cnf(c_0_155, negated_conjecture, (v2_funct_1(k2_funct_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_151, c_0_152])])).
% 0.19/0.47  cnf(c_0_156, negated_conjecture, (X1=k2_funct_1(esk4_0)|k5_relat_1(X1,esk4_0)!=k6_relat_1(esk1_0)|k2_relat_1(X1)!=esk2_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_153, c_0_152])).
% 0.19/0.47  cnf(c_0_157, negated_conjecture, (k2_funct_1(k2_funct_1(esk4_0))=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_154, c_0_152])]), c_0_155])])).
% 0.19/0.47  cnf(c_0_158, negated_conjecture, (k2_funct_1(esk4_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_156, c_0_40]), c_0_101]), c_0_112]), c_0_38]), c_0_39])])).
% 0.19/0.47  cnf(c_0_159, negated_conjecture, (esk4_0!=k2_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.47  cnf(c_0_160, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_157, c_0_158]), c_0_159]), ['proof']).
% 0.19/0.47  # SZS output end CNFRefutation
% 0.19/0.47  # Proof object total steps             : 161
% 0.19/0.47  # Proof object clause steps            : 120
% 0.19/0.47  # Proof object formula steps           : 41
% 0.19/0.47  # Proof object conjectures             : 91
% 0.19/0.47  # Proof object clause conjectures      : 88
% 0.19/0.47  # Proof object formula conjectures     : 3
% 0.19/0.47  # Proof object initial clauses used    : 38
% 0.19/0.47  # Proof object initial formulas used   : 20
% 0.19/0.47  # Proof object generating inferences   : 58
% 0.19/0.47  # Proof object simplifying inferences  : 187
% 0.19/0.47  # Training examples: 0 positive, 0 negative
% 0.19/0.47  # Parsed axioms                        : 21
% 0.19/0.47  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.47  # Initial clauses                      : 46
% 0.19/0.47  # Removed in clause preprocessing      : 1
% 0.19/0.47  # Initial clauses in saturation        : 45
% 0.19/0.47  # Processed clauses                    : 934
% 0.19/0.47  # ...of these trivial                  : 48
% 0.19/0.47  # ...subsumed                          : 85
% 0.19/0.47  # ...remaining for further processing  : 801
% 0.19/0.47  # Other redundant clauses eliminated   : 12
% 0.19/0.47  # Clauses deleted for lack of memory   : 0
% 0.19/0.47  # Backward-subsumed                    : 2
% 0.19/0.47  # Backward-rewritten                   : 370
% 0.19/0.47  # Generated clauses                    : 1970
% 0.19/0.47  # ...of the previous two non-trivial   : 2143
% 0.19/0.47  # Contextual simplify-reflections      : 0
% 0.19/0.47  # Paramodulations                      : 1958
% 0.19/0.47  # Factorizations                       : 0
% 0.19/0.47  # Equation resolutions                 : 12
% 0.19/0.47  # Propositional unsat checks           : 0
% 0.19/0.47  #    Propositional check models        : 0
% 0.19/0.47  #    Propositional check unsatisfiable : 0
% 0.19/0.47  #    Propositional clauses             : 0
% 0.19/0.47  #    Propositional clauses after purity: 0
% 0.19/0.47  #    Propositional unsat core size     : 0
% 0.19/0.47  #    Propositional preprocessing time  : 0.000
% 0.19/0.47  #    Propositional encoding time       : 0.000
% 0.19/0.47  #    Propositional solver time         : 0.000
% 0.19/0.47  #    Success case prop preproc time    : 0.000
% 0.19/0.47  #    Success case prop encoding time   : 0.000
% 0.19/0.47  #    Success case prop solver time     : 0.000
% 0.19/0.47  # Current number of processed clauses  : 381
% 0.19/0.47  #    Positive orientable unit clauses  : 155
% 0.19/0.47  #    Positive unorientable unit clauses: 0
% 0.19/0.47  #    Negative unit clauses             : 5
% 0.19/0.47  #    Non-unit-clauses                  : 221
% 0.19/0.47  # Current number of unprocessed clauses: 1264
% 0.19/0.47  # ...number of literals in the above   : 3893
% 0.19/0.47  # Current number of archived formulas  : 0
% 0.19/0.47  # Current number of archived clauses   : 418
% 0.19/0.47  # Clause-clause subsumption calls (NU) : 10609
% 0.19/0.47  # Rec. Clause-clause subsumption calls : 6834
% 0.19/0.47  # Non-unit clause-clause subsumptions  : 87
% 0.19/0.47  # Unit Clause-clause subsumption calls : 1451
% 0.19/0.47  # Rewrite failures with RHS unbound    : 0
% 0.19/0.47  # BW rewrite match attempts            : 882
% 0.19/0.47  # BW rewrite match successes           : 38
% 0.19/0.47  # Condensation attempts                : 0
% 0.19/0.47  # Condensation successes               : 0
% 0.19/0.47  # Termbank termtop insertions          : 77745
% 0.19/0.47  
% 0.19/0.47  # -------------------------------------------------
% 0.19/0.47  # User time                : 0.134 s
% 0.19/0.47  # System time              : 0.007 s
% 0.19/0.47  # Total time               : 0.141 s
% 0.19/0.47  # Maximum resident set size: 1604 pages
%------------------------------------------------------------------------------

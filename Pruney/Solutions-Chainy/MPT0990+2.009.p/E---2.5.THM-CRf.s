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
% DateTime   : Thu Dec  3 11:03:00 EST 2020

% Result     : Theorem 0.58s
% Output     : CNFRefutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :  135 (1372 expanded)
%              Number of clauses        :   94 ( 536 expanded)
%              Number of leaves         :   20 ( 331 expanded)
%              Depth                    :   21
%              Number of atoms          :  360 (8062 expanded)
%              Number of equality atoms :   96 (2494 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   12 (   2 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t55_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => k5_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(X1,k5_relat_1(X2,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

fof(t29_relset_1,axiom,(
    ! [X1] : m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(t61_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(k1_relat_1(X1))
          & k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(k2_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(t80_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(X1,k6_relat_1(k2_relat_1(X1))) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(t44_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k1_relat_1(k5_relat_1(X1,X2)),k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(t55_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
          & k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(redefinition_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k1_partfun1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

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

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(t209_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => X2 = k7_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(t94_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k5_relat_1(k6_relat_1(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

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
    ! [X25,X26,X27] :
      ( ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
      | v1_relat_1(X27) ) ),
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
    ! [X15,X16,X17] :
      ( ~ v1_relat_1(X15)
      | ~ v1_relat_1(X16)
      | ~ v1_relat_1(X17)
      | k5_relat_1(k5_relat_1(X15,X16),X17) = k5_relat_1(X15,k5_relat_1(X16,X17)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_relat_1])])])).

cnf(c_0_24,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_26,plain,(
    ! [X38] : m1_subset_1(k6_relat_1(X38),k1_zfmisc_1(k2_zfmisc_1(X38,X38))) ),
    inference(variable_rename,[status(thm)],[t29_relset_1])).

cnf(c_0_27,plain,
    ( k5_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(X1,k5_relat_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_29,plain,
    ( m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( k5_relat_1(k5_relat_1(X1,esk3_0),X2) = k5_relat_1(X1,k5_relat_1(esk3_0,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_31,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_29])).

fof(c_0_32,plain,(
    ! [X24] :
      ( ( k5_relat_1(X24,k2_funct_1(X24)) = k6_relat_1(k1_relat_1(X24))
        | ~ v2_funct_1(X24)
        | ~ v1_relat_1(X24)
        | ~ v1_funct_1(X24) )
      & ( k5_relat_1(k2_funct_1(X24),X24) = k6_relat_1(k2_relat_1(X24))
        | ~ v2_funct_1(X24)
        | ~ v1_relat_1(X24)
        | ~ v1_funct_1(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_funct_1])])])).

cnf(c_0_33,negated_conjecture,
    ( k5_relat_1(k5_relat_1(X1,esk3_0),k6_relat_1(X2)) = k5_relat_1(X1,k5_relat_1(esk3_0,k6_relat_1(X2)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_34,plain,
    ( k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(k2_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_35,negated_conjecture,
    ( v2_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_36,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_37,plain,(
    ! [X22] :
      ( ( v1_relat_1(k2_funct_1(X22))
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( v1_funct_1(k2_funct_1(X22))
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

fof(c_0_38,plain,(
    ! [X19] :
      ( ~ v1_relat_1(X19)
      | k5_relat_1(X19,k6_relat_1(k2_relat_1(X19))) = X19 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_relat_1])])).

fof(c_0_39,plain,(
    ! [X18] :
      ( k1_relat_1(k6_relat_1(X18)) = X18
      & k2_relat_1(k6_relat_1(X18)) = X18 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_40,plain,(
    ! [X9,X10] :
      ( ( ~ v4_relat_1(X10,X9)
        | r1_tarski(k1_relat_1(X10),X9)
        | ~ v1_relat_1(X10) )
      & ( ~ r1_tarski(k1_relat_1(X10),X9)
        | v4_relat_1(X10,X9)
        | ~ v1_relat_1(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

fof(c_0_41,plain,(
    ! [X13,X14] :
      ( ~ v1_relat_1(X13)
      | ~ v1_relat_1(X14)
      | r1_tarski(k1_relat_1(k5_relat_1(X13,X14)),k1_relat_1(X13)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_relat_1])])])).

cnf(c_0_42,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk3_0),k5_relat_1(esk3_0,k6_relat_1(X1))) = k5_relat_1(k6_relat_1(k2_relat_1(esk3_0)),k6_relat_1(X1))
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_36]),c_0_28])])).

cnf(c_0_43,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,plain,
    ( k5_relat_1(X1,k6_relat_1(k2_relat_1(X1))) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_45,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,plain,
    ( v4_relat_1(X1,X2)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_47,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(X1,X2)),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_48,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk3_0),k5_relat_1(esk3_0,k6_relat_1(X1))) = k5_relat_1(k6_relat_1(k2_relat_1(esk3_0)),k6_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_36]),c_0_28])])).

cnf(c_0_49,negated_conjecture,
    ( k5_relat_1(esk3_0,k6_relat_1(k2_relat_1(esk3_0))) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_44,c_0_28])).

cnf(c_0_50,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X1)) = k6_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_31]),c_0_45])).

fof(c_0_51,plain,(
    ! [X31,X32,X33] :
      ( ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))
      | k2_relset_1(X31,X32,X33) = k2_relat_1(X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_52,plain,(
    ! [X23] :
      ( ( k2_relat_1(X23) = k1_relat_1(k2_funct_1(X23))
        | ~ v2_funct_1(X23)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23) )
      & ( k1_relat_1(X23) = k2_relat_1(k2_funct_1(X23))
        | ~ v2_funct_1(X23)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).

cnf(c_0_53,plain,
    ( v4_relat_1(k5_relat_1(X1,X2),k1_relat_1(X1))
    | ~ v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_54,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk3_0),esk3_0) = k6_relat_1(k2_relat_1(esk3_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50])).

cnf(c_0_55,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_56,negated_conjecture,
    ( k2_relset_1(esk1_0,esk2_0,esk3_0) = esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_57,plain,
    ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_58,negated_conjecture,
    ( v4_relat_1(k6_relat_1(k2_relat_1(esk3_0)),k1_relat_1(k2_funct_1(esk3_0)))
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_31]),c_0_28])])).

fof(c_0_59,plain,(
    ! [X51] : k6_partfun1(X51) = k6_relat_1(X51) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

fof(c_0_60,plain,(
    ! [X45,X46,X47,X48,X49,X50] :
      ( ~ v1_funct_1(X49)
      | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))
      | ~ v1_funct_1(X50)
      | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))
      | k1_partfun1(X45,X46,X47,X48,X49,X50) = k5_relat_1(X49,X50) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).

cnf(c_0_61,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_62,negated_conjecture,
    ( esk2_0 = k2_relat_1(esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_25]),c_0_56])).

fof(c_0_63,plain,(
    ! [X7,X8] :
      ( ( r1_tarski(X7,X8)
        | X7 != X8 )
      & ( r1_tarski(X8,X7)
        | X7 != X8 )
      & ( ~ r1_tarski(X7,X8)
        | ~ r1_tarski(X8,X7)
        | X7 = X8 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_64,plain,
    ( v4_relat_1(k2_funct_1(X1),X2)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_46,c_0_57])).

cnf(c_0_65,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_66,negated_conjecture,
    ( v4_relat_1(k6_relat_1(k2_relat_1(esk3_0)),k1_relat_1(k2_funct_1(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_43]),c_0_36]),c_0_28])])).

cnf(c_0_67,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_68,negated_conjecture,
    ( r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_partfun1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_69,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_70,plain,
    ( k1_partfun1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_71,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(esk3_0),esk1_0))) ),
    inference(rw,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_72,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_73,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_74,plain,
    ( v4_relat_1(k2_funct_1(X1),X2)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_64,c_0_43])).

cnf(c_0_75,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk3_0),k1_relat_1(k2_funct_1(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67]),c_0_31])])).

fof(c_0_76,plain,(
    ! [X34,X35,X36,X37] :
      ( ( ~ r2_relset_1(X34,X35,X36,X37)
        | X36 = X37
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) )
      & ( X36 != X37
        | r2_relset_1(X34,X35,X36,X37)
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).

cnf(c_0_77,negated_conjecture,
    ( r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_relat_1(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_78,negated_conjecture,
    ( k1_partfun1(X1,X2,k2_relat_1(esk3_0),esk1_0,X3,esk4_0) = k5_relat_1(X3,esk4_0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_72])])).

cnf(c_0_79,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,k2_relat_1(esk3_0)))) ),
    inference(rw,[status(thm)],[c_0_25,c_0_62])).

fof(c_0_80,plain,(
    ! [X39,X40,X41,X42,X43,X44] :
      ( ( v1_funct_1(k1_partfun1(X39,X40,X41,X42,X43,X44))
        | ~ v1_funct_1(X43)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))
        | ~ v1_funct_1(X44)
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X41,X42))) )
      & ( m1_subset_1(k1_partfun1(X39,X40,X41,X42,X43,X44),k1_zfmisc_1(k2_zfmisc_1(X39,X42)))
        | ~ v1_funct_1(X43)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))
        | ~ v1_funct_1(X44)
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X41,X42))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).

cnf(c_0_81,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_73])).

cnf(c_0_82,negated_conjecture,
    ( v4_relat_1(k2_funct_1(esk3_0),k1_relat_1(k2_funct_1(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_35]),c_0_36]),c_0_28])])).

fof(c_0_83,plain,(
    ! [X28,X29,X30] :
      ( ( v4_relat_1(X30,X28)
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29))) )
      & ( v5_relat_1(X30,X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_84,plain,
    ( X3 = X4
    | ~ r2_relset_1(X1,X2,X3,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_85,negated_conjecture,
    ( r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,k2_relat_1(esk3_0),k2_relat_1(esk3_0),esk1_0,esk3_0,esk4_0),k6_relat_1(esk1_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_77,c_0_62]),c_0_62])).

cnf(c_0_86,negated_conjecture,
    ( k1_partfun1(esk1_0,k2_relat_1(esk3_0),k2_relat_1(esk3_0),esk1_0,esk3_0,esk4_0) = k5_relat_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_36])])).

cnf(c_0_87,plain,
    ( m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X6)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

fof(c_0_88,plain,(
    ! [X11,X12] :
      ( ~ v1_relat_1(X12)
      | ~ v4_relat_1(X12,X11)
      | X12 = k7_relat_1(X12,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).

cnf(c_0_89,plain,
    ( v4_relat_1(X1,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_81])).

cnf(c_0_90,negated_conjecture,
    ( v4_relat_1(k2_funct_1(esk3_0),k2_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_57]),c_0_35]),c_0_36]),c_0_28])])).

cnf(c_0_91,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

fof(c_0_92,plain,(
    ! [X20,X21] :
      ( ~ v1_relat_1(X21)
      | k7_relat_1(X21,X20) = k5_relat_1(k6_relat_1(X20),X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).

cnf(c_0_93,plain,
    ( X1 = k6_relat_1(X2)
    | ~ r2_relset_1(X2,X2,X1,k6_relat_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(spm,[status(thm)],[c_0_84,c_0_29])).

cnf(c_0_94,negated_conjecture,
    ( r2_relset_1(esk1_0,esk1_0,k5_relat_1(esk3_0,esk4_0),k6_relat_1(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_95,negated_conjecture,
    ( m1_subset_1(k1_partfun1(X1,X2,k2_relat_1(esk3_0),esk1_0,X3,esk4_0),k1_zfmisc_1(k2_zfmisc_1(X1,esk1_0)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_71]),c_0_72])])).

cnf(c_0_96,plain,
    ( X1 = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

cnf(c_0_97,plain,
    ( v4_relat_1(k2_funct_1(X1),k1_relat_1(k2_funct_1(X1)))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_89,c_0_43])).

cnf(c_0_98,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_99,negated_conjecture,
    ( r1_tarski(k1_relat_1(k2_funct_1(esk3_0)),k2_relat_1(esk3_0))
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_90])).

cnf(c_0_100,negated_conjecture,
    ( v4_relat_1(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_91,c_0_61])).

cnf(c_0_101,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_61])).

cnf(c_0_102,plain,
    ( k7_relat_1(X1,X2) = k5_relat_1(k6_relat_1(X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_92])).

cnf(c_0_103,negated_conjecture,
    ( v4_relat_1(esk3_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_91,c_0_25])).

cnf(c_0_104,negated_conjecture,
    ( k6_relat_1(esk1_0) = k5_relat_1(esk3_0,esk4_0)
    | ~ m1_subset_1(k5_relat_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(spm,[status(thm)],[c_0_93,c_0_94])).

cnf(c_0_105,negated_conjecture,
    ( m1_subset_1(k5_relat_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_79]),c_0_86]),c_0_36])])).

cnf(c_0_106,plain,
    ( k7_relat_1(k2_funct_1(X1),k1_relat_1(k2_funct_1(X1))) = k2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_96,c_0_97])).

cnf(c_0_107,negated_conjecture,
    ( k1_relat_1(k2_funct_1(esk3_0)) = k2_relat_1(esk3_0)
    | ~ r1_tarski(k1_relat_1(k2_funct_1(esk3_0)),k2_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_98,c_0_75])).

cnf(c_0_108,negated_conjecture,
    ( r1_tarski(k1_relat_1(k2_funct_1(esk3_0)),k2_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_43]),c_0_36]),c_0_28])])).

cnf(c_0_109,negated_conjecture,
    ( k7_relat_1(esk4_0,esk2_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_100]),c_0_101])])).

cnf(c_0_110,negated_conjecture,
    ( k7_relat_1(esk4_0,X1) = k5_relat_1(k6_relat_1(X1),esk4_0) ),
    inference(spm,[status(thm)],[c_0_102,c_0_101])).

cnf(c_0_111,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk3_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_103]),c_0_28])])).

cnf(c_0_112,negated_conjecture,
    ( k6_relat_1(esk1_0) = k5_relat_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_104,c_0_105])])).

cnf(c_0_113,negated_conjecture,
    ( r1_tarski(k1_relat_1(k5_relat_1(esk3_0,X1)),k1_relat_1(esk3_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_28])).

cnf(c_0_114,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk3_0),k5_relat_1(esk3_0,X1)) = k5_relat_1(k6_relat_1(k2_relat_1(esk3_0)),X1)
    | ~ v1_relat_1(k2_funct_1(esk3_0))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_34]),c_0_35]),c_0_36]),c_0_28])])).

cnf(c_0_115,plain,
    ( k7_relat_1(k2_funct_1(X1),k1_relat_1(k2_funct_1(X1))) = k2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_106,c_0_43])).

cnf(c_0_116,negated_conjecture,
    ( k1_relat_1(k2_funct_1(esk3_0)) = k2_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_107,c_0_108])])).

cnf(c_0_117,negated_conjecture,
    ( k5_relat_1(k5_relat_1(X1,esk3_0),esk4_0) = k5_relat_1(X1,k5_relat_1(esk3_0,esk4_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_101])).

cnf(c_0_118,negated_conjecture,
    ( k5_relat_1(k6_relat_1(k2_relat_1(esk3_0)),esk4_0) = esk4_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_109,c_0_62]),c_0_110])).

cnf(c_0_119,negated_conjecture,
    ( esk1_0 = k1_relat_1(esk3_0)
    | ~ r1_tarski(esk1_0,k1_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_98,c_0_111])).

cnf(c_0_120,negated_conjecture,
    ( esk1_0 = k1_relat_1(k5_relat_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_112])).

cnf(c_0_121,negated_conjecture,
    ( r1_tarski(k1_relat_1(k5_relat_1(esk3_0,esk4_0)),k1_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_113,c_0_101])).

cnf(c_0_122,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk3_0),k5_relat_1(esk3_0,X1)) = k5_relat_1(k6_relat_1(k2_relat_1(esk3_0)),X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_43]),c_0_36]),c_0_28])])).

cnf(c_0_123,plain,
    ( k7_relat_1(k2_funct_1(X1),X2) = k5_relat_1(k6_relat_1(X2),k2_funct_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_102,c_0_43])).

cnf(c_0_124,negated_conjecture,
    ( k7_relat_1(k2_funct_1(esk3_0),k2_relat_1(esk3_0)) = k2_funct_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_116]),c_0_36]),c_0_28])])).

cnf(c_0_125,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk3_0),k5_relat_1(esk3_0,esk4_0)) = esk4_0
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_34]),c_0_118]),c_0_35]),c_0_36]),c_0_28])])).

cnf(c_0_126,negated_conjecture,
    ( k1_relat_1(k5_relat_1(esk3_0,esk4_0)) = k1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_119,c_0_120]),c_0_120]),c_0_121])])).

cnf(c_0_127,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk3_0),k5_relat_1(esk3_0,k2_funct_1(X1))) = k5_relat_1(k6_relat_1(k2_relat_1(esk3_0)),k2_funct_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_122,c_0_43])).

cnf(c_0_128,plain,
    ( k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_129,negated_conjecture,
    ( k5_relat_1(k6_relat_1(k2_relat_1(esk3_0)),k2_funct_1(esk3_0)) = k2_funct_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_124]),c_0_36]),c_0_28])])).

cnf(c_0_130,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk3_0),k5_relat_1(esk3_0,esk4_0)) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_43]),c_0_36]),c_0_28])])).

cnf(c_0_131,negated_conjecture,
    ( k5_relat_1(esk3_0,esk4_0) = k6_relat_1(k1_relat_1(esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_112,c_0_120]),c_0_126])).

cnf(c_0_132,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk3_0),k6_relat_1(k1_relat_1(esk3_0))) = k2_funct_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_128]),c_0_129]),c_0_36]),c_0_28]),c_0_35])])).

cnf(c_0_133,negated_conjecture,
    ( esk4_0 != k2_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_134,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_130,c_0_131]),c_0_132]),c_0_133]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:39:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.58/0.75  # AutoSched0-Mode selected heuristic H_____042_B03_F1_AE_Q4_SP_S2S
% 0.58/0.75  # and selection function SelectNewComplexAHP.
% 0.58/0.75  #
% 0.58/0.75  # Preprocessing time       : 0.029 s
% 0.58/0.75  
% 0.58/0.75  # Proof found!
% 0.58/0.75  # SZS status Theorem
% 0.58/0.75  # SZS output start CNFRefutation
% 0.58/0.75  fof(t36_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(((k2_relset_1(X1,X2,X3)=X2&r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1)))&v2_funct_1(X3))=>(X1=k1_xboole_0|X2=k1_xboole_0|X4=k2_funct_1(X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 0.58/0.75  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.58/0.75  fof(t55_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>k5_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(X1,k5_relat_1(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 0.58/0.75  fof(t29_relset_1, axiom, ![X1]:m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 0.58/0.75  fof(t61_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(k1_relat_1(X1))&k5_relat_1(k2_funct_1(X1),X1)=k6_relat_1(k2_relat_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 0.58/0.75  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 0.58/0.75  fof(t80_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k5_relat_1(X1,k6_relat_1(k2_relat_1(X1)))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 0.58/0.75  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 0.58/0.75  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 0.58/0.75  fof(t44_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k5_relat_1(X1,X2)),k1_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_relat_1)).
% 0.58/0.75  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.58/0.75  fof(t55_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))&k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 0.58/0.75  fof(redefinition_k6_partfun1, axiom, ![X1]:k6_partfun1(X1)=k6_relat_1(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 0.58/0.75  fof(redefinition_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>k1_partfun1(X1,X2,X3,X4,X5,X6)=k5_relat_1(X5,X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 0.58/0.75  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.58/0.75  fof(redefinition_r2_relset_1, axiom, ![X1, X2, X3, X4]:((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_relset_1(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 0.58/0.75  fof(dt_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>(v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))&m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 0.58/0.75  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.58/0.75  fof(t209_relat_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>X2=k7_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 0.58/0.75  fof(t94_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k5_relat_1(k6_relat_1(X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 0.58/0.75  fof(c_0_20, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(((k2_relset_1(X1,X2,X3)=X2&r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1)))&v2_funct_1(X3))=>(X1=k1_xboole_0|X2=k1_xboole_0|X4=k2_funct_1(X3)))))), inference(assume_negation,[status(cth)],[t36_funct_2])).
% 0.58/0.75  fof(c_0_21, plain, ![X25, X26, X27]:(~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))|v1_relat_1(X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.58/0.75  fof(c_0_22, negated_conjecture, (((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,esk1_0,esk2_0))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))))&(((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,esk2_0,esk1_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))))&(((k2_relset_1(esk1_0,esk2_0,esk3_0)=esk2_0&r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_partfun1(esk1_0)))&v2_funct_1(esk3_0))&((esk1_0!=k1_xboole_0&esk2_0!=k1_xboole_0)&esk4_0!=k2_funct_1(esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).
% 0.58/0.75  fof(c_0_23, plain, ![X15, X16, X17]:(~v1_relat_1(X15)|(~v1_relat_1(X16)|(~v1_relat_1(X17)|k5_relat_1(k5_relat_1(X15,X16),X17)=k5_relat_1(X15,k5_relat_1(X16,X17))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_relat_1])])])).
% 0.58/0.75  cnf(c_0_24, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.58/0.75  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.58/0.75  fof(c_0_26, plain, ![X38]:m1_subset_1(k6_relat_1(X38),k1_zfmisc_1(k2_zfmisc_1(X38,X38))), inference(variable_rename,[status(thm)],[t29_relset_1])).
% 0.58/0.75  cnf(c_0_27, plain, (k5_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(X1,k5_relat_1(X2,X3))|~v1_relat_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.58/0.75  cnf(c_0_28, negated_conjecture, (v1_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.58/0.75  cnf(c_0_29, plain, (m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.58/0.75  cnf(c_0_30, negated_conjecture, (k5_relat_1(k5_relat_1(X1,esk3_0),X2)=k5_relat_1(X1,k5_relat_1(esk3_0,X2))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.58/0.75  cnf(c_0_31, plain, (v1_relat_1(k6_relat_1(X1))), inference(spm,[status(thm)],[c_0_24, c_0_29])).
% 0.58/0.75  fof(c_0_32, plain, ![X24]:((k5_relat_1(X24,k2_funct_1(X24))=k6_relat_1(k1_relat_1(X24))|~v2_funct_1(X24)|(~v1_relat_1(X24)|~v1_funct_1(X24)))&(k5_relat_1(k2_funct_1(X24),X24)=k6_relat_1(k2_relat_1(X24))|~v2_funct_1(X24)|(~v1_relat_1(X24)|~v1_funct_1(X24)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_funct_1])])])).
% 0.58/0.75  cnf(c_0_33, negated_conjecture, (k5_relat_1(k5_relat_1(X1,esk3_0),k6_relat_1(X2))=k5_relat_1(X1,k5_relat_1(esk3_0,k6_relat_1(X2)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.58/0.75  cnf(c_0_34, plain, (k5_relat_1(k2_funct_1(X1),X1)=k6_relat_1(k2_relat_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.58/0.75  cnf(c_0_35, negated_conjecture, (v2_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.58/0.75  cnf(c_0_36, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.58/0.75  fof(c_0_37, plain, ![X22]:((v1_relat_1(k2_funct_1(X22))|(~v1_relat_1(X22)|~v1_funct_1(X22)))&(v1_funct_1(k2_funct_1(X22))|(~v1_relat_1(X22)|~v1_funct_1(X22)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 0.58/0.75  fof(c_0_38, plain, ![X19]:(~v1_relat_1(X19)|k5_relat_1(X19,k6_relat_1(k2_relat_1(X19)))=X19), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_relat_1])])).
% 0.58/0.75  fof(c_0_39, plain, ![X18]:(k1_relat_1(k6_relat_1(X18))=X18&k2_relat_1(k6_relat_1(X18))=X18), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.58/0.75  fof(c_0_40, plain, ![X9, X10]:((~v4_relat_1(X10,X9)|r1_tarski(k1_relat_1(X10),X9)|~v1_relat_1(X10))&(~r1_tarski(k1_relat_1(X10),X9)|v4_relat_1(X10,X9)|~v1_relat_1(X10))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.58/0.75  fof(c_0_41, plain, ![X13, X14]:(~v1_relat_1(X13)|(~v1_relat_1(X14)|r1_tarski(k1_relat_1(k5_relat_1(X13,X14)),k1_relat_1(X13)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_relat_1])])])).
% 0.58/0.75  cnf(c_0_42, negated_conjecture, (k5_relat_1(k2_funct_1(esk3_0),k5_relat_1(esk3_0,k6_relat_1(X1)))=k5_relat_1(k6_relat_1(k2_relat_1(esk3_0)),k6_relat_1(X1))|~v1_relat_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35]), c_0_36]), c_0_28])])).
% 0.58/0.75  cnf(c_0_43, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.58/0.75  cnf(c_0_44, plain, (k5_relat_1(X1,k6_relat_1(k2_relat_1(X1)))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.58/0.75  cnf(c_0_45, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.58/0.75  cnf(c_0_46, plain, (v4_relat_1(X1,X2)|~r1_tarski(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.58/0.75  cnf(c_0_47, plain, (r1_tarski(k1_relat_1(k5_relat_1(X1,X2)),k1_relat_1(X1))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.58/0.75  cnf(c_0_48, negated_conjecture, (k5_relat_1(k2_funct_1(esk3_0),k5_relat_1(esk3_0,k6_relat_1(X1)))=k5_relat_1(k6_relat_1(k2_relat_1(esk3_0)),k6_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_36]), c_0_28])])).
% 0.58/0.75  cnf(c_0_49, negated_conjecture, (k5_relat_1(esk3_0,k6_relat_1(k2_relat_1(esk3_0)))=esk3_0), inference(spm,[status(thm)],[c_0_44, c_0_28])).
% 0.58/0.75  cnf(c_0_50, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X1))=k6_relat_1(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_31]), c_0_45])).
% 0.58/0.75  fof(c_0_51, plain, ![X31, X32, X33]:(~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))|k2_relset_1(X31,X32,X33)=k2_relat_1(X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.58/0.75  fof(c_0_52, plain, ![X23]:((k2_relat_1(X23)=k1_relat_1(k2_funct_1(X23))|~v2_funct_1(X23)|(~v1_relat_1(X23)|~v1_funct_1(X23)))&(k1_relat_1(X23)=k2_relat_1(k2_funct_1(X23))|~v2_funct_1(X23)|(~v1_relat_1(X23)|~v1_funct_1(X23)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).
% 0.58/0.75  cnf(c_0_53, plain, (v4_relat_1(k5_relat_1(X1,X2),k1_relat_1(X1))|~v1_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.58/0.75  cnf(c_0_54, negated_conjecture, (k5_relat_1(k2_funct_1(esk3_0),esk3_0)=k6_relat_1(k2_relat_1(esk3_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50])).
% 0.58/0.75  cnf(c_0_55, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.58/0.75  cnf(c_0_56, negated_conjecture, (k2_relset_1(esk1_0,esk2_0,esk3_0)=esk2_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.58/0.75  cnf(c_0_57, plain, (k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.58/0.75  cnf(c_0_58, negated_conjecture, (v4_relat_1(k6_relat_1(k2_relat_1(esk3_0)),k1_relat_1(k2_funct_1(esk3_0)))|~v1_relat_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_31]), c_0_28])])).
% 0.58/0.75  fof(c_0_59, plain, ![X51]:k6_partfun1(X51)=k6_relat_1(X51), inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).
% 0.58/0.75  fof(c_0_60, plain, ![X45, X46, X47, X48, X49, X50]:(~v1_funct_1(X49)|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))|~v1_funct_1(X50)|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))|k1_partfun1(X45,X46,X47,X48,X49,X50)=k5_relat_1(X49,X50)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).
% 0.58/0.75  cnf(c_0_61, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.58/0.75  cnf(c_0_62, negated_conjecture, (esk2_0=k2_relat_1(esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_25]), c_0_56])).
% 0.58/0.75  fof(c_0_63, plain, ![X7, X8]:(((r1_tarski(X7,X8)|X7!=X8)&(r1_tarski(X8,X7)|X7!=X8))&(~r1_tarski(X7,X8)|~r1_tarski(X8,X7)|X7=X8)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.58/0.75  cnf(c_0_64, plain, (v4_relat_1(k2_funct_1(X1),X2)|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_46, c_0_57])).
% 0.58/0.75  cnf(c_0_65, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.58/0.75  cnf(c_0_66, negated_conjecture, (v4_relat_1(k6_relat_1(k2_relat_1(esk3_0)),k1_relat_1(k2_funct_1(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_43]), c_0_36]), c_0_28])])).
% 0.58/0.75  cnf(c_0_67, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.58/0.75  cnf(c_0_68, negated_conjecture, (r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_partfun1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.58/0.75  cnf(c_0_69, plain, (k6_partfun1(X1)=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.58/0.75  cnf(c_0_70, plain, (k1_partfun1(X2,X3,X5,X6,X1,X4)=k5_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.58/0.75  cnf(c_0_71, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(esk3_0),esk1_0)))), inference(rw,[status(thm)],[c_0_61, c_0_62])).
% 0.58/0.75  cnf(c_0_72, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.58/0.75  cnf(c_0_73, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.58/0.75  cnf(c_0_74, plain, (v4_relat_1(k2_funct_1(X1),X2)|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_64, c_0_43])).
% 0.58/0.75  cnf(c_0_75, negated_conjecture, (r1_tarski(k2_relat_1(esk3_0),k1_relat_1(k2_funct_1(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67]), c_0_31])])).
% 0.58/0.75  fof(c_0_76, plain, ![X34, X35, X36, X37]:((~r2_relset_1(X34,X35,X36,X37)|X36=X37|(~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))))&(X36!=X37|r2_relset_1(X34,X35,X36,X37)|(~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).
% 0.58/0.75  cnf(c_0_77, negated_conjecture, (r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_relat_1(esk1_0))), inference(rw,[status(thm)],[c_0_68, c_0_69])).
% 0.58/0.75  cnf(c_0_78, negated_conjecture, (k1_partfun1(X1,X2,k2_relat_1(esk3_0),esk1_0,X3,esk4_0)=k5_relat_1(X3,esk4_0)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_72])])).
% 0.58/0.75  cnf(c_0_79, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,k2_relat_1(esk3_0))))), inference(rw,[status(thm)],[c_0_25, c_0_62])).
% 0.58/0.75  fof(c_0_80, plain, ![X39, X40, X41, X42, X43, X44]:((v1_funct_1(k1_partfun1(X39,X40,X41,X42,X43,X44))|(~v1_funct_1(X43)|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))|~v1_funct_1(X44)|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))))&(m1_subset_1(k1_partfun1(X39,X40,X41,X42,X43,X44),k1_zfmisc_1(k2_zfmisc_1(X39,X42)))|(~v1_funct_1(X43)|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))|~v1_funct_1(X44)|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).
% 0.58/0.75  cnf(c_0_81, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_73])).
% 0.58/0.75  cnf(c_0_82, negated_conjecture, (v4_relat_1(k2_funct_1(esk3_0),k1_relat_1(k2_funct_1(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_35]), c_0_36]), c_0_28])])).
% 0.58/0.75  fof(c_0_83, plain, ![X28, X29, X30]:((v4_relat_1(X30,X28)|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29))))&(v5_relat_1(X30,X29)|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.58/0.75  cnf(c_0_84, plain, (X3=X4|~r2_relset_1(X1,X2,X3,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.58/0.75  cnf(c_0_85, negated_conjecture, (r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,k2_relat_1(esk3_0),k2_relat_1(esk3_0),esk1_0,esk3_0,esk4_0),k6_relat_1(esk1_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_77, c_0_62]), c_0_62])).
% 0.58/0.75  cnf(c_0_86, negated_conjecture, (k1_partfun1(esk1_0,k2_relat_1(esk3_0),k2_relat_1(esk3_0),esk1_0,esk3_0,esk4_0)=k5_relat_1(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_36])])).
% 0.58/0.75  cnf(c_0_87, plain, (m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X6)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.58/0.75  fof(c_0_88, plain, ![X11, X12]:(~v1_relat_1(X12)|~v4_relat_1(X12,X11)|X12=k7_relat_1(X12,X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).
% 0.58/0.75  cnf(c_0_89, plain, (v4_relat_1(X1,k1_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_46, c_0_81])).
% 0.58/0.75  cnf(c_0_90, negated_conjecture, (v4_relat_1(k2_funct_1(esk3_0),k2_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_57]), c_0_35]), c_0_36]), c_0_28])])).
% 0.58/0.75  cnf(c_0_91, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_83])).
% 0.58/0.75  fof(c_0_92, plain, ![X20, X21]:(~v1_relat_1(X21)|k7_relat_1(X21,X20)=k5_relat_1(k6_relat_1(X20),X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).
% 0.58/0.75  cnf(c_0_93, plain, (X1=k6_relat_1(X2)|~r2_relset_1(X2,X2,X1,k6_relat_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))), inference(spm,[status(thm)],[c_0_84, c_0_29])).
% 0.58/0.75  cnf(c_0_94, negated_conjecture, (r2_relset_1(esk1_0,esk1_0,k5_relat_1(esk3_0,esk4_0),k6_relat_1(esk1_0))), inference(rw,[status(thm)],[c_0_85, c_0_86])).
% 0.58/0.75  cnf(c_0_95, negated_conjecture, (m1_subset_1(k1_partfun1(X1,X2,k2_relat_1(esk3_0),esk1_0,X3,esk4_0),k1_zfmisc_1(k2_zfmisc_1(X1,esk1_0)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_71]), c_0_72])])).
% 0.58/0.75  cnf(c_0_96, plain, (X1=k7_relat_1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_88])).
% 0.58/0.75  cnf(c_0_97, plain, (v4_relat_1(k2_funct_1(X1),k1_relat_1(k2_funct_1(X1)))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_89, c_0_43])).
% 0.58/0.75  cnf(c_0_98, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.58/0.75  cnf(c_0_99, negated_conjecture, (r1_tarski(k1_relat_1(k2_funct_1(esk3_0)),k2_relat_1(esk3_0))|~v1_relat_1(k2_funct_1(esk3_0))), inference(spm,[status(thm)],[c_0_65, c_0_90])).
% 0.58/0.75  cnf(c_0_100, negated_conjecture, (v4_relat_1(esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_91, c_0_61])).
% 0.58/0.75  cnf(c_0_101, negated_conjecture, (v1_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_24, c_0_61])).
% 0.58/0.75  cnf(c_0_102, plain, (k7_relat_1(X1,X2)=k5_relat_1(k6_relat_1(X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_92])).
% 0.58/0.75  cnf(c_0_103, negated_conjecture, (v4_relat_1(esk3_0,esk1_0)), inference(spm,[status(thm)],[c_0_91, c_0_25])).
% 0.58/0.75  cnf(c_0_104, negated_conjecture, (k6_relat_1(esk1_0)=k5_relat_1(esk3_0,esk4_0)|~m1_subset_1(k5_relat_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(spm,[status(thm)],[c_0_93, c_0_94])).
% 0.58/0.75  cnf(c_0_105, negated_conjecture, (m1_subset_1(k5_relat_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_79]), c_0_86]), c_0_36])])).
% 0.58/0.75  cnf(c_0_106, plain, (k7_relat_1(k2_funct_1(X1),k1_relat_1(k2_funct_1(X1)))=k2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_96, c_0_97])).
% 0.58/0.75  cnf(c_0_107, negated_conjecture, (k1_relat_1(k2_funct_1(esk3_0))=k2_relat_1(esk3_0)|~r1_tarski(k1_relat_1(k2_funct_1(esk3_0)),k2_relat_1(esk3_0))), inference(spm,[status(thm)],[c_0_98, c_0_75])).
% 0.58/0.75  cnf(c_0_108, negated_conjecture, (r1_tarski(k1_relat_1(k2_funct_1(esk3_0)),k2_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_43]), c_0_36]), c_0_28])])).
% 0.58/0.75  cnf(c_0_109, negated_conjecture, (k7_relat_1(esk4_0,esk2_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_100]), c_0_101])])).
% 0.58/0.75  cnf(c_0_110, negated_conjecture, (k7_relat_1(esk4_0,X1)=k5_relat_1(k6_relat_1(X1),esk4_0)), inference(spm,[status(thm)],[c_0_102, c_0_101])).
% 0.58/0.75  cnf(c_0_111, negated_conjecture, (r1_tarski(k1_relat_1(esk3_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_103]), c_0_28])])).
% 0.58/0.75  cnf(c_0_112, negated_conjecture, (k6_relat_1(esk1_0)=k5_relat_1(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_104, c_0_105])])).
% 0.58/0.75  cnf(c_0_113, negated_conjecture, (r1_tarski(k1_relat_1(k5_relat_1(esk3_0,X1)),k1_relat_1(esk3_0))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_47, c_0_28])).
% 0.58/0.75  cnf(c_0_114, negated_conjecture, (k5_relat_1(k2_funct_1(esk3_0),k5_relat_1(esk3_0,X1))=k5_relat_1(k6_relat_1(k2_relat_1(esk3_0)),X1)|~v1_relat_1(k2_funct_1(esk3_0))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_34]), c_0_35]), c_0_36]), c_0_28])])).
% 0.58/0.75  cnf(c_0_115, plain, (k7_relat_1(k2_funct_1(X1),k1_relat_1(k2_funct_1(X1)))=k2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_106, c_0_43])).
% 0.58/0.75  cnf(c_0_116, negated_conjecture, (k1_relat_1(k2_funct_1(esk3_0))=k2_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_107, c_0_108])])).
% 0.58/0.75  cnf(c_0_117, negated_conjecture, (k5_relat_1(k5_relat_1(X1,esk3_0),esk4_0)=k5_relat_1(X1,k5_relat_1(esk3_0,esk4_0))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_30, c_0_101])).
% 0.58/0.75  cnf(c_0_118, negated_conjecture, (k5_relat_1(k6_relat_1(k2_relat_1(esk3_0)),esk4_0)=esk4_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_109, c_0_62]), c_0_110])).
% 0.58/0.75  cnf(c_0_119, negated_conjecture, (esk1_0=k1_relat_1(esk3_0)|~r1_tarski(esk1_0,k1_relat_1(esk3_0))), inference(spm,[status(thm)],[c_0_98, c_0_111])).
% 0.58/0.75  cnf(c_0_120, negated_conjecture, (esk1_0=k1_relat_1(k5_relat_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_67, c_0_112])).
% 0.58/0.75  cnf(c_0_121, negated_conjecture, (r1_tarski(k1_relat_1(k5_relat_1(esk3_0,esk4_0)),k1_relat_1(esk3_0))), inference(spm,[status(thm)],[c_0_113, c_0_101])).
% 0.58/0.75  cnf(c_0_122, negated_conjecture, (k5_relat_1(k2_funct_1(esk3_0),k5_relat_1(esk3_0,X1))=k5_relat_1(k6_relat_1(k2_relat_1(esk3_0)),X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_43]), c_0_36]), c_0_28])])).
% 0.58/0.75  cnf(c_0_123, plain, (k7_relat_1(k2_funct_1(X1),X2)=k5_relat_1(k6_relat_1(X2),k2_funct_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_102, c_0_43])).
% 0.58/0.75  cnf(c_0_124, negated_conjecture, (k7_relat_1(k2_funct_1(esk3_0),k2_relat_1(esk3_0))=k2_funct_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_116]), c_0_36]), c_0_28])])).
% 0.58/0.75  cnf(c_0_125, negated_conjecture, (k5_relat_1(k2_funct_1(esk3_0),k5_relat_1(esk3_0,esk4_0))=esk4_0|~v1_relat_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_34]), c_0_118]), c_0_35]), c_0_36]), c_0_28])])).
% 0.58/0.75  cnf(c_0_126, negated_conjecture, (k1_relat_1(k5_relat_1(esk3_0,esk4_0))=k1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_119, c_0_120]), c_0_120]), c_0_121])])).
% 0.58/0.75  cnf(c_0_127, negated_conjecture, (k5_relat_1(k2_funct_1(esk3_0),k5_relat_1(esk3_0,k2_funct_1(X1)))=k5_relat_1(k6_relat_1(k2_relat_1(esk3_0)),k2_funct_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_122, c_0_43])).
% 0.58/0.75  cnf(c_0_128, plain, (k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(k1_relat_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.58/0.75  cnf(c_0_129, negated_conjecture, (k5_relat_1(k6_relat_1(k2_relat_1(esk3_0)),k2_funct_1(esk3_0))=k2_funct_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123, c_0_124]), c_0_36]), c_0_28])])).
% 0.58/0.75  cnf(c_0_130, negated_conjecture, (k5_relat_1(k2_funct_1(esk3_0),k5_relat_1(esk3_0,esk4_0))=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125, c_0_43]), c_0_36]), c_0_28])])).
% 0.58/0.75  cnf(c_0_131, negated_conjecture, (k5_relat_1(esk3_0,esk4_0)=k6_relat_1(k1_relat_1(esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_112, c_0_120]), c_0_126])).
% 0.58/0.75  cnf(c_0_132, negated_conjecture, (k5_relat_1(k2_funct_1(esk3_0),k6_relat_1(k1_relat_1(esk3_0)))=k2_funct_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127, c_0_128]), c_0_129]), c_0_36]), c_0_28]), c_0_35])])).
% 0.58/0.75  cnf(c_0_133, negated_conjecture, (esk4_0!=k2_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.58/0.75  cnf(c_0_134, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_130, c_0_131]), c_0_132]), c_0_133]), ['proof']).
% 0.58/0.75  # SZS output end CNFRefutation
% 0.58/0.75  # Proof object total steps             : 135
% 0.58/0.75  # Proof object clause steps            : 94
% 0.58/0.75  # Proof object formula steps           : 41
% 0.58/0.75  # Proof object conjectures             : 62
% 0.58/0.75  # Proof object clause conjectures      : 59
% 0.58/0.75  # Proof object formula conjectures     : 3
% 0.58/0.75  # Proof object initial clauses used    : 31
% 0.58/0.75  # Proof object initial formulas used   : 20
% 0.58/0.75  # Proof object generating inferences   : 51
% 0.58/0.75  # Proof object simplifying inferences  : 91
% 0.58/0.75  # Training examples: 0 positive, 0 negative
% 0.58/0.75  # Parsed axioms                        : 20
% 0.58/0.75  # Removed by relevancy pruning/SinE    : 0
% 0.58/0.75  # Initial clauses                      : 41
% 0.58/0.75  # Removed in clause preprocessing      : 1
% 0.58/0.75  # Initial clauses in saturation        : 40
% 0.58/0.75  # Processed clauses                    : 3141
% 0.58/0.75  # ...of these trivial                  : 348
% 0.58/0.75  # ...subsumed                          : 1465
% 0.58/0.75  # ...remaining for further processing  : 1328
% 0.58/0.75  # Other redundant clauses eliminated   : 3
% 0.58/0.75  # Clauses deleted for lack of memory   : 0
% 0.58/0.75  # Backward-subsumed                    : 60
% 0.58/0.75  # Backward-rewritten                   : 387
% 0.58/0.75  # Generated clauses                    : 23606
% 0.58/0.75  # ...of the previous two non-trivial   : 21191
% 0.58/0.75  # Contextual simplify-reflections      : 0
% 0.58/0.75  # Paramodulations                      : 23603
% 0.58/0.75  # Factorizations                       : 0
% 0.58/0.75  # Equation resolutions                 : 3
% 0.58/0.75  # Propositional unsat checks           : 0
% 0.58/0.75  #    Propositional check models        : 0
% 0.58/0.75  #    Propositional check unsatisfiable : 0
% 0.58/0.75  #    Propositional clauses             : 0
% 0.58/0.75  #    Propositional clauses after purity: 0
% 0.58/0.75  #    Propositional unsat core size     : 0
% 0.58/0.75  #    Propositional preprocessing time  : 0.000
% 0.58/0.75  #    Propositional encoding time       : 0.000
% 0.58/0.75  #    Propositional solver time         : 0.000
% 0.58/0.75  #    Success case prop preproc time    : 0.000
% 0.58/0.75  #    Success case prop encoding time   : 0.000
% 0.58/0.75  #    Success case prop solver time     : 0.000
% 0.58/0.75  # Current number of processed clauses  : 878
% 0.58/0.75  #    Positive orientable unit clauses  : 242
% 0.58/0.75  #    Positive unorientable unit clauses: 8
% 0.58/0.75  #    Negative unit clauses             : 3
% 0.58/0.75  #    Non-unit-clauses                  : 625
% 0.58/0.75  # Current number of unprocessed clauses: 17886
% 0.58/0.75  # ...number of literals in the above   : 60162
% 0.58/0.75  # Current number of archived formulas  : 0
% 0.58/0.75  # Current number of archived clauses   : 448
% 0.58/0.75  # Clause-clause subsumption calls (NU) : 24655
% 0.58/0.75  # Rec. Clause-clause subsumption calls : 20201
% 0.58/0.75  # Non-unit clause-clause subsumptions  : 1422
% 0.58/0.75  # Unit Clause-clause subsumption calls : 2606
% 0.58/0.75  # Rewrite failures with RHS unbound    : 0
% 0.58/0.75  # BW rewrite match attempts            : 3631
% 0.58/0.75  # BW rewrite match successes           : 117
% 0.58/0.75  # Condensation attempts                : 0
% 0.58/0.75  # Condensation successes               : 0
% 0.58/0.75  # Termbank termtop insertions          : 612956
% 0.58/0.75  
% 0.58/0.75  # -------------------------------------------------
% 0.58/0.75  # User time                : 0.393 s
% 0.58/0.75  # System time              : 0.017 s
% 0.58/0.75  # Total time               : 0.410 s
% 0.58/0.75  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:03:14 EST 2020

% Result     : Theorem 2.81s
% Output     : CNFRefutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :  153 (1356 expanded)
%              Number of clauses        :  104 ( 537 expanded)
%              Number of leaves         :   24 ( 353 expanded)
%              Depth                    :   16
%              Number of atoms          :  411 (6188 expanded)
%              Number of equality atoms :  108 (1700 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   12 (   2 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(t55_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
          & k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

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

fof(dt_k6_partfun1,axiom,(
    ! [X1] :
      ( v1_partfun1(k6_partfun1(X1),X1)
      & m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(t55_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => k5_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(X1,k5_relat_1(X2,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

fof(t45_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k2_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

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

fof(t61_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(k1_relat_1(X1))
          & k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(k2_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(t77_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X1)
       => k5_relat_1(k6_relat_1(X1),X2) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

fof(t54_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k4_relat_1(k5_relat_1(X1,X2)) = k5_relat_1(k4_relat_1(X2),k4_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

fof(t72_relat_1,axiom,(
    ! [X1] : k4_relat_1(k6_relat_1(X1)) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).

fof(dt_k4_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k4_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

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

fof(d9_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => k2_funct_1(X1) = k4_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

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

fof(c_0_25,plain,(
    ! [X11,X12] :
      ( ( ~ v4_relat_1(X12,X11)
        | r1_tarski(k1_relat_1(X12),X11)
        | ~ v1_relat_1(X12) )
      & ( ~ r1_tarski(k1_relat_1(X12),X11)
        | v4_relat_1(X12,X11)
        | ~ v1_relat_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

fof(c_0_26,plain,(
    ! [X30] :
      ( ( k2_relat_1(X30) = k1_relat_1(k2_funct_1(X30))
        | ~ v2_funct_1(X30)
        | ~ v1_relat_1(X30)
        | ~ v1_funct_1(X30) )
      & ( k1_relat_1(X30) = k2_relat_1(k2_funct_1(X30))
        | ~ v2_funct_1(X30)
        | ~ v1_relat_1(X30)
        | ~ v1_funct_1(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).

fof(c_0_27,plain,(
    ! [X9,X10] :
      ( ~ v1_relat_1(X9)
      | ~ m1_subset_1(X10,k1_zfmisc_1(X9))
      | v1_relat_1(X10) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_28,negated_conjecture,
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).

fof(c_0_29,plain,(
    ! [X14,X15] : v1_relat_1(k2_zfmisc_1(X14,X15)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_30,plain,(
    ! [X48] :
      ( v1_partfun1(k6_partfun1(X48),X48)
      & m1_subset_1(k6_partfun1(X48),k1_zfmisc_1(k2_zfmisc_1(X48,X48))) ) ),
    inference(variable_rename,[status(thm)],[dt_k6_partfun1])).

fof(c_0_31,plain,(
    ! [X55] : k6_partfun1(X55) = k6_relat_1(X55) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

cnf(c_0_32,plain,
    ( v4_relat_1(X1,X2)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_34,plain,(
    ! [X29] :
      ( ( v1_relat_1(k2_funct_1(X29))
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) )
      & ( v1_funct_1(k2_funct_1(X29))
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

fof(c_0_35,plain,(
    ! [X20,X21,X22] :
      ( ~ v1_relat_1(X20)
      | ~ v1_relat_1(X21)
      | ~ v1_relat_1(X22)
      | k5_relat_1(k5_relat_1(X20,X21),X22) = k5_relat_1(X20,k5_relat_1(X21,X22)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_relat_1])])])).

cnf(c_0_36,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,plain,
    ( v4_relat_1(k2_funct_1(X1),X2)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_42,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_43,plain,(
    ! [X16,X17] :
      ( ~ v1_relat_1(X16)
      | ~ v1_relat_1(X17)
      | r1_tarski(k2_relat_1(k5_relat_1(X16,X17)),k2_relat_1(X17)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_relat_1])])])).

fof(c_0_44,plain,(
    ! [X27] :
      ( ~ v1_relat_1(X27)
      | k5_relat_1(X27,k6_relat_1(k2_relat_1(X27))) = X27 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_relat_1])])).

cnf(c_0_45,plain,
    ( k5_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(X1,k5_relat_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_46,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38])])).

cnf(c_0_47,plain,
    ( m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(rw,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_48,plain,
    ( v4_relat_1(k2_funct_1(X1),X2)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_49,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_50,plain,
    ( k5_relat_1(X1,k6_relat_1(k2_relat_1(X1))) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_51,plain,(
    ! [X23] :
      ( k1_relat_1(k6_relat_1(X23)) = X23
      & k2_relat_1(k6_relat_1(X23)) = X23 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

cnf(c_0_52,negated_conjecture,
    ( k5_relat_1(k5_relat_1(esk3_0,X1),X2) = k5_relat_1(esk3_0,k5_relat_1(X1,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_53,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_47]),c_0_38])])).

fof(c_0_54,plain,(
    ! [X31] :
      ( ( k5_relat_1(X31,k2_funct_1(X31)) = k6_relat_1(k1_relat_1(X31))
        | ~ v2_funct_1(X31)
        | ~ v1_relat_1(X31)
        | ~ v1_funct_1(X31) )
      & ( k5_relat_1(k2_funct_1(X31),X31) = k6_relat_1(k2_relat_1(X31))
        | ~ v2_funct_1(X31)
        | ~ v1_relat_1(X31)
        | ~ v1_funct_1(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_funct_1])])])).

cnf(c_0_55,plain,
    ( v4_relat_1(k2_funct_1(k5_relat_1(X1,X2)),k2_relat_1(X2))
    | ~ v2_funct_1(k5_relat_1(X1,X2))
    | ~ v1_funct_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_56,negated_conjecture,
    ( k5_relat_1(esk3_0,k6_relat_1(k2_relat_1(esk3_0))) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_50,c_0_46])).

cnf(c_0_57,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_58,negated_conjecture,
    ( v2_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_59,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_60,negated_conjecture,
    ( k5_relat_1(k5_relat_1(esk3_0,X1),k6_relat_1(X2)) = k5_relat_1(esk3_0,k5_relat_1(X1,k6_relat_1(X2)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_61,plain,
    ( k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_62,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_63,negated_conjecture,
    ( v4_relat_1(k2_funct_1(esk3_0),k2_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57]),c_0_58]),c_0_59]),c_0_46]),c_0_53])])).

fof(c_0_64,plain,(
    ! [X32,X33,X34] :
      ( ( v4_relat_1(X34,X32)
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) )
      & ( v5_relat_1(X34,X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_65,plain,(
    ! [X35,X36,X37] :
      ( ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))
      | k2_relset_1(X35,X36,X37) = k2_relat_1(X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_66,negated_conjecture,
    ( k5_relat_1(esk3_0,k5_relat_1(k2_funct_1(esk3_0),k6_relat_1(X1))) = k5_relat_1(k6_relat_1(k1_relat_1(esk3_0)),k6_relat_1(X1))
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_58]),c_0_59]),c_0_46])])).

cnf(c_0_67,negated_conjecture,
    ( k5_relat_1(k5_relat_1(X1,esk3_0),X2) = k5_relat_1(X1,k5_relat_1(esk3_0,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_68,plain,
    ( k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(k2_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

fof(c_0_69,plain,(
    ! [X25,X26] :
      ( ~ v1_relat_1(X26)
      | ~ r1_tarski(k1_relat_1(X26),X25)
      | k5_relat_1(k6_relat_1(X25),X26) = X26 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t77_relat_1])])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(k1_relat_1(k2_funct_1(esk3_0)),k2_relat_1(esk3_0))
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_71,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_72,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_73,negated_conjecture,
    ( k2_relset_1(esk1_0,esk2_0,esk3_0) = esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_74,negated_conjecture,
    ( k5_relat_1(esk3_0,k5_relat_1(k2_funct_1(esk3_0),k6_relat_1(X1))) = k5_relat_1(k6_relat_1(k1_relat_1(esk3_0)),k6_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_42]),c_0_59]),c_0_46])])).

cnf(c_0_75,plain,
    ( k5_relat_1(k2_funct_1(X1),k6_relat_1(k2_relat_1(k2_funct_1(X1)))) = k2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_42])).

cnf(c_0_76,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk3_0),k5_relat_1(esk3_0,X1)) = k5_relat_1(k6_relat_1(k2_relat_1(esk3_0)),X1)
    | ~ v1_relat_1(k2_funct_1(esk3_0))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_58]),c_0_59]),c_0_46])])).

cnf(c_0_77,plain,
    ( k5_relat_1(k6_relat_1(X2),X1) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_78,negated_conjecture,
    ( r1_tarski(k1_relat_1(k2_funct_1(esk3_0)),k2_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_42]),c_0_59]),c_0_46])])).

fof(c_0_79,plain,(
    ! [X18,X19] :
      ( ~ v1_relat_1(X18)
      | ~ v1_relat_1(X19)
      | k4_relat_1(k5_relat_1(X18,X19)) = k5_relat_1(k4_relat_1(X19),k4_relat_1(X18)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_relat_1])])])).

fof(c_0_80,plain,(
    ! [X24] : k4_relat_1(k6_relat_1(X24)) = k6_relat_1(X24) ),
    inference(variable_rename,[status(thm)],[t72_relat_1])).

fof(c_0_81,plain,(
    ! [X13] :
      ( ~ v1_relat_1(X13)
      | v1_relat_1(k4_relat_1(X13)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relat_1])])).

cnf(c_0_82,negated_conjecture,
    ( v4_relat_1(esk3_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_37])).

fof(c_0_83,plain,(
    ! [X49,X50,X51,X52,X53,X54] :
      ( ~ v1_funct_1(X53)
      | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X49,X50)))
      | ~ v1_funct_1(X54)
      | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))
      | k1_partfun1(X49,X50,X51,X52,X53,X54) = k5_relat_1(X53,X54) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).

cnf(c_0_84,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_85,negated_conjecture,
    ( esk2_0 = k2_relat_1(esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_37]),c_0_73])).

fof(c_0_86,plain,(
    ! [X7,X8] :
      ( ( r1_tarski(X7,X8)
        | X7 != X8 )
      & ( r1_tarski(X8,X7)
        | X7 != X8 )
      & ( ~ r1_tarski(X7,X8)
        | ~ r1_tarski(X8,X7)
        | X7 = X8 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_87,negated_conjecture,
    ( k5_relat_1(k6_relat_1(k1_relat_1(esk3_0)),k6_relat_1(k2_relat_1(k2_funct_1(esk3_0)))) = k5_relat_1(esk3_0,k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_59]),c_0_46])])).

cnf(c_0_88,plain,
    ( k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_89,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X1)) = k6_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_53]),c_0_57])).

cnf(c_0_90,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(k2_funct_1(X1),X2)),k2_relat_1(X2))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_42])).

cnf(c_0_91,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk3_0),k5_relat_1(esk3_0,X1)) = k5_relat_1(k6_relat_1(k2_relat_1(esk3_0)),X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_42]),c_0_59]),c_0_46])])).

cnf(c_0_92,negated_conjecture,
    ( k5_relat_1(k6_relat_1(k2_relat_1(esk3_0)),k2_funct_1(esk3_0)) = k2_funct_1(esk3_0)
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

fof(c_0_93,plain,(
    ! [X28] :
      ( ~ v1_relat_1(X28)
      | ~ v1_funct_1(X28)
      | ~ v2_funct_1(X28)
      | k2_funct_1(X28) = k4_relat_1(X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_1])])).

cnf(c_0_94,plain,
    ( k4_relat_1(k5_relat_1(X1,X2)) = k5_relat_1(k4_relat_1(X2),k4_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_95,plain,
    ( k4_relat_1(k6_relat_1(X1)) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_96,plain,
    ( v1_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_97,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk3_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_82]),c_0_46])])).

cnf(c_0_98,negated_conjecture,
    ( r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_partfun1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_99,plain,
    ( k1_partfun1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_100,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(esk3_0),esk1_0))) ),
    inference(rw,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_101,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_102,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_103,negated_conjecture,
    ( k5_relat_1(esk3_0,k2_funct_1(esk3_0)) = k6_relat_1(k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_89]),c_0_58]),c_0_59]),c_0_46])])).

cnf(c_0_104,negated_conjecture,
    ( r1_tarski(k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(esk3_0)),X1)),k2_relat_1(k5_relat_1(esk3_0,X1)))
    | ~ v1_relat_1(k5_relat_1(esk3_0,X1))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_59]),c_0_46])])).

cnf(c_0_105,negated_conjecture,
    ( k5_relat_1(k6_relat_1(k2_relat_1(esk3_0)),k2_funct_1(esk3_0)) = k2_funct_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_42]),c_0_59]),c_0_46])])).

cnf(c_0_106,plain,
    ( k2_funct_1(X1) = k4_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

cnf(c_0_107,plain,
    ( k4_relat_1(k5_relat_1(X1,k6_relat_1(X2))) = k5_relat_1(k6_relat_1(X2),k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_53]),c_0_95])).

cnf(c_0_108,plain,
    ( v1_relat_1(k5_relat_1(k4_relat_1(X1),k4_relat_1(X2)))
    | ~ v1_relat_1(k5_relat_1(X2,X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_96,c_0_94])).

cnf(c_0_109,negated_conjecture,
    ( k5_relat_1(k6_relat_1(esk1_0),esk3_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_97]),c_0_46])])).

cnf(c_0_110,plain,
    ( k4_relat_1(k5_relat_1(k6_relat_1(X1),X2)) = k5_relat_1(k4_relat_1(X2),k6_relat_1(X1))
    | ~ v1_relat_1(X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_53]),c_0_95])).

fof(c_0_111,plain,(
    ! [X38,X39,X40,X41] :
      ( ( ~ r2_relset_1(X38,X39,X40,X41)
        | X40 = X41
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) )
      & ( X40 != X41
        | r2_relset_1(X38,X39,X40,X41)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).

cnf(c_0_112,negated_conjecture,
    ( r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_relat_1(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_98,c_0_40])).

cnf(c_0_113,negated_conjecture,
    ( k1_partfun1(X1,X2,k2_relat_1(esk3_0),esk1_0,X3,esk4_0) = k5_relat_1(X3,esk4_0)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100]),c_0_101])])).

cnf(c_0_114,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,k2_relat_1(esk3_0)))) ),
    inference(rw,[status(thm)],[c_0_37,c_0_85])).

fof(c_0_115,plain,(
    ! [X42,X43,X44,X45,X46,X47] :
      ( ( v1_funct_1(k1_partfun1(X42,X43,X44,X45,X46,X47))
        | ~ v1_funct_1(X46)
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))
        | ~ v1_funct_1(X47)
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X44,X45))) )
      & ( m1_subset_1(k1_partfun1(X42,X43,X44,X45,X46,X47),k1_zfmisc_1(k2_zfmisc_1(X42,X45)))
        | ~ v1_funct_1(X46)
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))
        | ~ v1_funct_1(X47)
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X44,X45))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).

cnf(c_0_116,negated_conjecture,
    ( v4_relat_1(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_84])).

cnf(c_0_117,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_84]),c_0_38])])).

cnf(c_0_118,plain,
    ( k2_relat_1(k5_relat_1(X1,X2)) = k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X2),k2_relat_1(k5_relat_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_102,c_0_49])).

cnf(c_0_119,negated_conjecture,
    ( k5_relat_1(k6_relat_1(k1_relat_1(esk3_0)),k6_relat_1(k2_relat_1(k2_funct_1(esk3_0)))) = k6_relat_1(k1_relat_1(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_87,c_0_103])).

cnf(c_0_120,negated_conjecture,
    ( r1_tarski(k2_relat_1(k2_funct_1(esk3_0)),k1_relat_1(esk3_0))
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_61]),c_0_105]),c_0_57]),c_0_53]),c_0_58]),c_0_59]),c_0_46])])).

cnf(c_0_121,plain,
    ( k5_relat_1(X1,k4_relat_1(X1)) = k6_relat_1(k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_106])).

cnf(c_0_122,negated_conjecture,
    ( k4_relat_1(k5_relat_1(esk3_0,k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k4_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_107,c_0_46])).

cnf(c_0_123,negated_conjecture,
    ( v1_relat_1(k5_relat_1(k4_relat_1(esk3_0),k6_relat_1(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_109]),c_0_95]),c_0_46]),c_0_53])])).

cnf(c_0_124,negated_conjecture,
    ( k5_relat_1(k4_relat_1(esk3_0),k6_relat_1(esk1_0)) = k4_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_109]),c_0_46])])).

cnf(c_0_125,plain,
    ( X3 = X4
    | ~ r2_relset_1(X1,X2,X3,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_111])).

cnf(c_0_126,negated_conjecture,
    ( r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,k2_relat_1(esk3_0),k2_relat_1(esk3_0),esk1_0,esk3_0,esk4_0),k6_relat_1(esk1_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_112,c_0_85]),c_0_85])).

cnf(c_0_127,negated_conjecture,
    ( k1_partfun1(esk1_0,k2_relat_1(esk3_0),k2_relat_1(esk3_0),esk1_0,esk3_0,esk4_0) = k5_relat_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_114]),c_0_59])])).

cnf(c_0_128,plain,
    ( m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X6)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_115])).

cnf(c_0_129,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk4_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_116]),c_0_117])])).

cnf(c_0_130,negated_conjecture,
    ( k2_relat_1(k2_funct_1(esk3_0)) = k1_relat_1(esk3_0)
    | ~ r1_tarski(k2_relat_1(k2_funct_1(esk3_0)),k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_119]),c_0_57]),c_0_57]),c_0_53]),c_0_53]),c_0_57]),c_0_57])])).

cnf(c_0_131,negated_conjecture,
    ( r1_tarski(k2_relat_1(k2_funct_1(esk3_0)),k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_42]),c_0_59]),c_0_46])])).

cnf(c_0_132,negated_conjecture,
    ( k5_relat_1(esk3_0,k4_relat_1(esk3_0)) = k6_relat_1(k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_46]),c_0_58]),c_0_59])])).

cnf(c_0_133,negated_conjecture,
    ( k5_relat_1(k6_relat_1(k2_relat_1(esk3_0)),k4_relat_1(esk3_0)) = k4_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_122,c_0_56])).

cnf(c_0_134,negated_conjecture,
    ( v1_relat_1(k4_relat_1(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_123,c_0_124])).

cnf(c_0_135,plain,
    ( X1 = k6_relat_1(X2)
    | ~ r2_relset_1(X2,X2,X1,k6_relat_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(spm,[status(thm)],[c_0_125,c_0_47])).

cnf(c_0_136,negated_conjecture,
    ( r2_relset_1(esk1_0,esk1_0,k5_relat_1(esk3_0,esk4_0),k6_relat_1(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_126,c_0_127])).

cnf(c_0_137,negated_conjecture,
    ( m1_subset_1(k1_partfun1(X1,X2,k2_relat_1(esk3_0),esk1_0,X3,esk4_0),k1_zfmisc_1(k2_zfmisc_1(X1,esk1_0)))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_100]),c_0_101])])).

cnf(c_0_138,plain,
    ( k5_relat_1(k4_relat_1(X1),X1) = k6_relat_1(k2_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_68,c_0_106])).

cnf(c_0_139,negated_conjecture,
    ( k5_relat_1(k6_relat_1(esk2_0),esk4_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_129]),c_0_117])])).

cnf(c_0_140,negated_conjecture,
    ( k2_relat_1(k2_funct_1(esk3_0)) = k1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_130,c_0_131])])).

cnf(c_0_141,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk3_0),k6_relat_1(k1_relat_1(esk3_0))) = k4_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_132]),c_0_133]),c_0_134])])).

cnf(c_0_142,negated_conjecture,
    ( k6_relat_1(esk1_0) = k5_relat_1(esk3_0,esk4_0)
    | ~ m1_subset_1(k5_relat_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(spm,[status(thm)],[c_0_135,c_0_136])).

cnf(c_0_143,negated_conjecture,
    ( m1_subset_1(k5_relat_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137,c_0_114]),c_0_127]),c_0_59])])).

cnf(c_0_144,negated_conjecture,
    ( k5_relat_1(k5_relat_1(X1,esk3_0),esk4_0) = k5_relat_1(X1,k5_relat_1(esk3_0,esk4_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_67,c_0_117])).

cnf(c_0_145,negated_conjecture,
    ( k5_relat_1(k4_relat_1(esk3_0),esk3_0) = k6_relat_1(k2_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_46]),c_0_58]),c_0_59])])).

cnf(c_0_146,negated_conjecture,
    ( k5_relat_1(k6_relat_1(k2_relat_1(esk3_0)),esk4_0) = esk4_0 ),
    inference(rw,[status(thm)],[c_0_139,c_0_85])).

cnf(c_0_147,negated_conjecture,
    ( esk4_0 != k2_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_148,negated_conjecture,
    ( k2_funct_1(esk3_0) = k4_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_140]),c_0_141]),c_0_59]),c_0_46])])).

cnf(c_0_149,negated_conjecture,
    ( k6_relat_1(esk1_0) = k5_relat_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_142,c_0_143])])).

cnf(c_0_150,negated_conjecture,
    ( k5_relat_1(k4_relat_1(esk3_0),k5_relat_1(esk3_0,esk4_0)) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_144,c_0_145]),c_0_146]),c_0_134])])).

cnf(c_0_151,negated_conjecture,
    ( esk4_0 != k4_relat_1(esk3_0) ),
    inference(rw,[status(thm)],[c_0_147,c_0_148])).

cnf(c_0_152,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_124,c_0_149]),c_0_150]),c_0_151]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:12:05 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 2.81/2.98  # AutoSched0-Mode selected heuristic H_____042_B03_F1_AE_Q4_SP_S2S
% 2.81/2.98  # and selection function SelectNewComplexAHP.
% 2.81/2.98  #
% 2.81/2.98  # Preprocessing time       : 0.028 s
% 2.81/2.98  
% 2.81/2.98  # Proof found!
% 2.81/2.98  # SZS status Theorem
% 2.81/2.98  # SZS output start CNFRefutation
% 2.81/2.98  fof(t36_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(((k2_relset_1(X1,X2,X3)=X2&r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1)))&v2_funct_1(X3))=>(X1=k1_xboole_0|X2=k1_xboole_0|X4=k2_funct_1(X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 2.81/2.98  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.81/2.98  fof(t55_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))&k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 2.81/2.98  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.81/2.98  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.81/2.98  fof(dt_k6_partfun1, axiom, ![X1]:(v1_partfun1(k6_partfun1(X1),X1)&m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 2.81/2.98  fof(redefinition_k6_partfun1, axiom, ![X1]:k6_partfun1(X1)=k6_relat_1(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.81/2.98  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 2.81/2.98  fof(t55_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>k5_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(X1,k5_relat_1(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 2.81/2.98  fof(t45_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k2_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 2.81/2.98  fof(t80_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k5_relat_1(X1,k6_relat_1(k2_relat_1(X1)))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 2.81/2.98  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.81/2.98  fof(t61_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(k1_relat_1(X1))&k5_relat_1(k2_funct_1(X1),X1)=k6_relat_1(k2_relat_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 2.81/2.98  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.81/2.98  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.81/2.98  fof(t77_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X2),X1)=>k5_relat_1(k6_relat_1(X1),X2)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 2.81/2.98  fof(t54_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k4_relat_1(k5_relat_1(X1,X2))=k5_relat_1(k4_relat_1(X2),k4_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_relat_1)).
% 2.81/2.98  fof(t72_relat_1, axiom, ![X1]:k4_relat_1(k6_relat_1(X1))=k6_relat_1(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_relat_1)).
% 2.81/2.98  fof(dt_k4_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>v1_relat_1(k4_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 2.81/2.98  fof(redefinition_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>k1_partfun1(X1,X2,X3,X4,X5,X6)=k5_relat_1(X5,X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 2.81/2.98  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.81/2.98  fof(d9_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>k2_funct_1(X1)=k4_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 2.81/2.98  fof(redefinition_r2_relset_1, axiom, ![X1, X2, X3, X4]:((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_relset_1(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 2.81/2.98  fof(dt_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>(v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))&m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 2.81/2.98  fof(c_0_24, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(((k2_relset_1(X1,X2,X3)=X2&r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1)))&v2_funct_1(X3))=>(X1=k1_xboole_0|X2=k1_xboole_0|X4=k2_funct_1(X3)))))), inference(assume_negation,[status(cth)],[t36_funct_2])).
% 2.81/2.98  fof(c_0_25, plain, ![X11, X12]:((~v4_relat_1(X12,X11)|r1_tarski(k1_relat_1(X12),X11)|~v1_relat_1(X12))&(~r1_tarski(k1_relat_1(X12),X11)|v4_relat_1(X12,X11)|~v1_relat_1(X12))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 2.81/2.98  fof(c_0_26, plain, ![X30]:((k2_relat_1(X30)=k1_relat_1(k2_funct_1(X30))|~v2_funct_1(X30)|(~v1_relat_1(X30)|~v1_funct_1(X30)))&(k1_relat_1(X30)=k2_relat_1(k2_funct_1(X30))|~v2_funct_1(X30)|(~v1_relat_1(X30)|~v1_funct_1(X30)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).
% 2.81/2.98  fof(c_0_27, plain, ![X9, X10]:(~v1_relat_1(X9)|(~m1_subset_1(X10,k1_zfmisc_1(X9))|v1_relat_1(X10))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 2.81/2.98  fof(c_0_28, negated_conjecture, (((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,esk1_0,esk2_0))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))))&(((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,esk2_0,esk1_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))))&(((k2_relset_1(esk1_0,esk2_0,esk3_0)=esk2_0&r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_partfun1(esk1_0)))&v2_funct_1(esk3_0))&((esk1_0!=k1_xboole_0&esk2_0!=k1_xboole_0)&esk4_0!=k2_funct_1(esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).
% 2.81/2.98  fof(c_0_29, plain, ![X14, X15]:v1_relat_1(k2_zfmisc_1(X14,X15)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 2.81/2.98  fof(c_0_30, plain, ![X48]:(v1_partfun1(k6_partfun1(X48),X48)&m1_subset_1(k6_partfun1(X48),k1_zfmisc_1(k2_zfmisc_1(X48,X48)))), inference(variable_rename,[status(thm)],[dt_k6_partfun1])).
% 2.81/2.98  fof(c_0_31, plain, ![X55]:k6_partfun1(X55)=k6_relat_1(X55), inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).
% 2.81/2.98  cnf(c_0_32, plain, (v4_relat_1(X1,X2)|~r1_tarski(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 2.81/2.98  cnf(c_0_33, plain, (k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 2.81/2.98  fof(c_0_34, plain, ![X29]:((v1_relat_1(k2_funct_1(X29))|(~v1_relat_1(X29)|~v1_funct_1(X29)))&(v1_funct_1(k2_funct_1(X29))|(~v1_relat_1(X29)|~v1_funct_1(X29)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 2.81/2.98  fof(c_0_35, plain, ![X20, X21, X22]:(~v1_relat_1(X20)|(~v1_relat_1(X21)|(~v1_relat_1(X22)|k5_relat_1(k5_relat_1(X20,X21),X22)=k5_relat_1(X20,k5_relat_1(X21,X22))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_relat_1])])])).
% 2.81/2.98  cnf(c_0_36, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 2.81/2.98  cnf(c_0_37, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 2.81/2.98  cnf(c_0_38, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 2.81/2.98  cnf(c_0_39, plain, (m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 2.81/2.98  cnf(c_0_40, plain, (k6_partfun1(X1)=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 2.81/2.98  cnf(c_0_41, plain, (v4_relat_1(k2_funct_1(X1),X2)|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 2.81/2.98  cnf(c_0_42, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 2.81/2.98  fof(c_0_43, plain, ![X16, X17]:(~v1_relat_1(X16)|(~v1_relat_1(X17)|r1_tarski(k2_relat_1(k5_relat_1(X16,X17)),k2_relat_1(X17)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_relat_1])])])).
% 2.81/2.98  fof(c_0_44, plain, ![X27]:(~v1_relat_1(X27)|k5_relat_1(X27,k6_relat_1(k2_relat_1(X27)))=X27), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_relat_1])])).
% 2.81/2.98  cnf(c_0_45, plain, (k5_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(X1,k5_relat_1(X2,X3))|~v1_relat_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 2.81/2.98  cnf(c_0_46, negated_conjecture, (v1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38])])).
% 2.81/2.98  cnf(c_0_47, plain, (m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(rw,[status(thm)],[c_0_39, c_0_40])).
% 2.81/2.98  cnf(c_0_48, plain, (v4_relat_1(k2_funct_1(X1),X2)|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 2.81/2.98  cnf(c_0_49, plain, (r1_tarski(k2_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 2.81/2.98  cnf(c_0_50, plain, (k5_relat_1(X1,k6_relat_1(k2_relat_1(X1)))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 2.81/2.98  fof(c_0_51, plain, ![X23]:(k1_relat_1(k6_relat_1(X23))=X23&k2_relat_1(k6_relat_1(X23))=X23), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 2.81/2.98  cnf(c_0_52, negated_conjecture, (k5_relat_1(k5_relat_1(esk3_0,X1),X2)=k5_relat_1(esk3_0,k5_relat_1(X1,X2))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 2.81/2.98  cnf(c_0_53, plain, (v1_relat_1(k6_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_47]), c_0_38])])).
% 2.81/2.98  fof(c_0_54, plain, ![X31]:((k5_relat_1(X31,k2_funct_1(X31))=k6_relat_1(k1_relat_1(X31))|~v2_funct_1(X31)|(~v1_relat_1(X31)|~v1_funct_1(X31)))&(k5_relat_1(k2_funct_1(X31),X31)=k6_relat_1(k2_relat_1(X31))|~v2_funct_1(X31)|(~v1_relat_1(X31)|~v1_funct_1(X31)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_funct_1])])])).
% 2.81/2.98  cnf(c_0_55, plain, (v4_relat_1(k2_funct_1(k5_relat_1(X1,X2)),k2_relat_1(X2))|~v2_funct_1(k5_relat_1(X1,X2))|~v1_funct_1(k5_relat_1(X1,X2))|~v1_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 2.81/2.98  cnf(c_0_56, negated_conjecture, (k5_relat_1(esk3_0,k6_relat_1(k2_relat_1(esk3_0)))=esk3_0), inference(spm,[status(thm)],[c_0_50, c_0_46])).
% 2.81/2.98  cnf(c_0_57, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_51])).
% 2.81/2.98  cnf(c_0_58, negated_conjecture, (v2_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 2.81/2.98  cnf(c_0_59, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 2.81/2.98  cnf(c_0_60, negated_conjecture, (k5_relat_1(k5_relat_1(esk3_0,X1),k6_relat_1(X2))=k5_relat_1(esk3_0,k5_relat_1(X1,k6_relat_1(X2)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 2.81/2.98  cnf(c_0_61, plain, (k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(k1_relat_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 2.81/2.98  cnf(c_0_62, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 2.81/2.98  cnf(c_0_63, negated_conjecture, (v4_relat_1(k2_funct_1(esk3_0),k2_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57]), c_0_58]), c_0_59]), c_0_46]), c_0_53])])).
% 2.81/2.98  fof(c_0_64, plain, ![X32, X33, X34]:((v4_relat_1(X34,X32)|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))))&(v5_relat_1(X34,X33)|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 2.81/2.98  fof(c_0_65, plain, ![X35, X36, X37]:(~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))|k2_relset_1(X35,X36,X37)=k2_relat_1(X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 2.81/2.98  cnf(c_0_66, negated_conjecture, (k5_relat_1(esk3_0,k5_relat_1(k2_funct_1(esk3_0),k6_relat_1(X1)))=k5_relat_1(k6_relat_1(k1_relat_1(esk3_0)),k6_relat_1(X1))|~v1_relat_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_58]), c_0_59]), c_0_46])])).
% 2.81/2.98  cnf(c_0_67, negated_conjecture, (k5_relat_1(k5_relat_1(X1,esk3_0),X2)=k5_relat_1(X1,k5_relat_1(esk3_0,X2))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 2.81/2.98  cnf(c_0_68, plain, (k5_relat_1(k2_funct_1(X1),X1)=k6_relat_1(k2_relat_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 2.81/2.98  fof(c_0_69, plain, ![X25, X26]:(~v1_relat_1(X26)|(~r1_tarski(k1_relat_1(X26),X25)|k5_relat_1(k6_relat_1(X25),X26)=X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t77_relat_1])])).
% 2.81/2.98  cnf(c_0_70, negated_conjecture, (r1_tarski(k1_relat_1(k2_funct_1(esk3_0)),k2_relat_1(esk3_0))|~v1_relat_1(k2_funct_1(esk3_0))), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 2.81/2.98  cnf(c_0_71, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_64])).
% 2.81/2.98  cnf(c_0_72, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_65])).
% 2.81/2.98  cnf(c_0_73, negated_conjecture, (k2_relset_1(esk1_0,esk2_0,esk3_0)=esk2_0), inference(split_conjunct,[status(thm)],[c_0_28])).
% 2.81/2.98  cnf(c_0_74, negated_conjecture, (k5_relat_1(esk3_0,k5_relat_1(k2_funct_1(esk3_0),k6_relat_1(X1)))=k5_relat_1(k6_relat_1(k1_relat_1(esk3_0)),k6_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_42]), c_0_59]), c_0_46])])).
% 2.81/2.98  cnf(c_0_75, plain, (k5_relat_1(k2_funct_1(X1),k6_relat_1(k2_relat_1(k2_funct_1(X1))))=k2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_50, c_0_42])).
% 2.81/2.98  cnf(c_0_76, negated_conjecture, (k5_relat_1(k2_funct_1(esk3_0),k5_relat_1(esk3_0,X1))=k5_relat_1(k6_relat_1(k2_relat_1(esk3_0)),X1)|~v1_relat_1(k2_funct_1(esk3_0))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_58]), c_0_59]), c_0_46])])).
% 2.81/2.98  cnf(c_0_77, plain, (k5_relat_1(k6_relat_1(X2),X1)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 2.81/2.98  cnf(c_0_78, negated_conjecture, (r1_tarski(k1_relat_1(k2_funct_1(esk3_0)),k2_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_42]), c_0_59]), c_0_46])])).
% 2.81/2.98  fof(c_0_79, plain, ![X18, X19]:(~v1_relat_1(X18)|(~v1_relat_1(X19)|k4_relat_1(k5_relat_1(X18,X19))=k5_relat_1(k4_relat_1(X19),k4_relat_1(X18)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_relat_1])])])).
% 2.81/2.98  fof(c_0_80, plain, ![X24]:k4_relat_1(k6_relat_1(X24))=k6_relat_1(X24), inference(variable_rename,[status(thm)],[t72_relat_1])).
% 2.81/2.98  fof(c_0_81, plain, ![X13]:(~v1_relat_1(X13)|v1_relat_1(k4_relat_1(X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relat_1])])).
% 2.81/2.98  cnf(c_0_82, negated_conjecture, (v4_relat_1(esk3_0,esk1_0)), inference(spm,[status(thm)],[c_0_71, c_0_37])).
% 2.81/2.98  fof(c_0_83, plain, ![X49, X50, X51, X52, X53, X54]:(~v1_funct_1(X53)|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X49,X50)))|~v1_funct_1(X54)|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))|k1_partfun1(X49,X50,X51,X52,X53,X54)=k5_relat_1(X53,X54)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).
% 2.81/2.98  cnf(c_0_84, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 2.81/2.98  cnf(c_0_85, negated_conjecture, (esk2_0=k2_relat_1(esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_37]), c_0_73])).
% 2.81/2.98  fof(c_0_86, plain, ![X7, X8]:(((r1_tarski(X7,X8)|X7!=X8)&(r1_tarski(X8,X7)|X7!=X8))&(~r1_tarski(X7,X8)|~r1_tarski(X8,X7)|X7=X8)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 2.81/2.98  cnf(c_0_87, negated_conjecture, (k5_relat_1(k6_relat_1(k1_relat_1(esk3_0)),k6_relat_1(k2_relat_1(k2_funct_1(esk3_0))))=k5_relat_1(esk3_0,k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_59]), c_0_46])])).
% 2.81/2.98  cnf(c_0_88, plain, (k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 2.81/2.98  cnf(c_0_89, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X1))=k6_relat_1(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_53]), c_0_57])).
% 2.81/2.98  cnf(c_0_90, plain, (r1_tarski(k2_relat_1(k5_relat_1(k2_funct_1(X1),X2)),k2_relat_1(X2))|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_49, c_0_42])).
% 2.81/2.98  cnf(c_0_91, negated_conjecture, (k5_relat_1(k2_funct_1(esk3_0),k5_relat_1(esk3_0,X1))=k5_relat_1(k6_relat_1(k2_relat_1(esk3_0)),X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_42]), c_0_59]), c_0_46])])).
% 2.81/2.98  cnf(c_0_92, negated_conjecture, (k5_relat_1(k6_relat_1(k2_relat_1(esk3_0)),k2_funct_1(esk3_0))=k2_funct_1(esk3_0)|~v1_relat_1(k2_funct_1(esk3_0))), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 2.81/2.98  fof(c_0_93, plain, ![X28]:(~v1_relat_1(X28)|~v1_funct_1(X28)|(~v2_funct_1(X28)|k2_funct_1(X28)=k4_relat_1(X28))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_1])])).
% 2.81/2.98  cnf(c_0_94, plain, (k4_relat_1(k5_relat_1(X1,X2))=k5_relat_1(k4_relat_1(X2),k4_relat_1(X1))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_79])).
% 2.81/2.98  cnf(c_0_95, plain, (k4_relat_1(k6_relat_1(X1))=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_80])).
% 2.81/2.98  cnf(c_0_96, plain, (v1_relat_1(k4_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_81])).
% 2.81/2.98  cnf(c_0_97, negated_conjecture, (r1_tarski(k1_relat_1(esk3_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_82]), c_0_46])])).
% 2.81/2.98  cnf(c_0_98, negated_conjecture, (r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_partfun1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 2.81/2.98  cnf(c_0_99, plain, (k1_partfun1(X2,X3,X5,X6,X1,X4)=k5_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_83])).
% 2.81/2.98  cnf(c_0_100, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(esk3_0),esk1_0)))), inference(rw,[status(thm)],[c_0_84, c_0_85])).
% 2.81/2.98  cnf(c_0_101, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 2.81/2.98  cnf(c_0_102, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_86])).
% 2.81/2.98  cnf(c_0_103, negated_conjecture, (k5_relat_1(esk3_0,k2_funct_1(esk3_0))=k6_relat_1(k1_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_89]), c_0_58]), c_0_59]), c_0_46])])).
% 2.81/2.98  cnf(c_0_104, negated_conjecture, (r1_tarski(k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(esk3_0)),X1)),k2_relat_1(k5_relat_1(esk3_0,X1)))|~v1_relat_1(k5_relat_1(esk3_0,X1))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_91]), c_0_59]), c_0_46])])).
% 2.81/2.98  cnf(c_0_105, negated_conjecture, (k5_relat_1(k6_relat_1(k2_relat_1(esk3_0)),k2_funct_1(esk3_0))=k2_funct_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_42]), c_0_59]), c_0_46])])).
% 2.81/2.98  cnf(c_0_106, plain, (k2_funct_1(X1)=k4_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_93])).
% 2.81/2.98  cnf(c_0_107, plain, (k4_relat_1(k5_relat_1(X1,k6_relat_1(X2)))=k5_relat_1(k6_relat_1(X2),k4_relat_1(X1))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_53]), c_0_95])).
% 2.81/2.98  cnf(c_0_108, plain, (v1_relat_1(k5_relat_1(k4_relat_1(X1),k4_relat_1(X2)))|~v1_relat_1(k5_relat_1(X2,X1))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_96, c_0_94])).
% 2.81/2.98  cnf(c_0_109, negated_conjecture, (k5_relat_1(k6_relat_1(esk1_0),esk3_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_97]), c_0_46])])).
% 2.81/2.98  cnf(c_0_110, plain, (k4_relat_1(k5_relat_1(k6_relat_1(X1),X2))=k5_relat_1(k4_relat_1(X2),k6_relat_1(X1))|~v1_relat_1(X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_53]), c_0_95])).
% 2.81/2.98  fof(c_0_111, plain, ![X38, X39, X40, X41]:((~r2_relset_1(X38,X39,X40,X41)|X40=X41|(~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))))&(X40!=X41|r2_relset_1(X38,X39,X40,X41)|(~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).
% 2.81/2.98  cnf(c_0_112, negated_conjecture, (r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_relat_1(esk1_0))), inference(rw,[status(thm)],[c_0_98, c_0_40])).
% 2.81/2.98  cnf(c_0_113, negated_conjecture, (k1_partfun1(X1,X2,k2_relat_1(esk3_0),esk1_0,X3,esk4_0)=k5_relat_1(X3,esk4_0)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_100]), c_0_101])])).
% 2.81/2.98  cnf(c_0_114, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,k2_relat_1(esk3_0))))), inference(rw,[status(thm)],[c_0_37, c_0_85])).
% 2.81/2.98  fof(c_0_115, plain, ![X42, X43, X44, X45, X46, X47]:((v1_funct_1(k1_partfun1(X42,X43,X44,X45,X46,X47))|(~v1_funct_1(X46)|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))|~v1_funct_1(X47)|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))))&(m1_subset_1(k1_partfun1(X42,X43,X44,X45,X46,X47),k1_zfmisc_1(k2_zfmisc_1(X42,X45)))|(~v1_funct_1(X46)|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))|~v1_funct_1(X47)|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).
% 2.81/2.98  cnf(c_0_116, negated_conjecture, (v4_relat_1(esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_71, c_0_84])).
% 2.81/2.98  cnf(c_0_117, negated_conjecture, (v1_relat_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_84]), c_0_38])])).
% 2.81/2.98  cnf(c_0_118, plain, (k2_relat_1(k5_relat_1(X1,X2))=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X2),k2_relat_1(k5_relat_1(X1,X2)))), inference(spm,[status(thm)],[c_0_102, c_0_49])).
% 2.81/2.98  cnf(c_0_119, negated_conjecture, (k5_relat_1(k6_relat_1(k1_relat_1(esk3_0)),k6_relat_1(k2_relat_1(k2_funct_1(esk3_0))))=k6_relat_1(k1_relat_1(esk3_0))), inference(rw,[status(thm)],[c_0_87, c_0_103])).
% 2.81/2.98  cnf(c_0_120, negated_conjecture, (r1_tarski(k2_relat_1(k2_funct_1(esk3_0)),k1_relat_1(esk3_0))|~v1_relat_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_61]), c_0_105]), c_0_57]), c_0_53]), c_0_58]), c_0_59]), c_0_46])])).
% 2.81/2.98  cnf(c_0_121, plain, (k5_relat_1(X1,k4_relat_1(X1))=k6_relat_1(k1_relat_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_61, c_0_106])).
% 2.81/2.98  cnf(c_0_122, negated_conjecture, (k4_relat_1(k5_relat_1(esk3_0,k6_relat_1(X1)))=k5_relat_1(k6_relat_1(X1),k4_relat_1(esk3_0))), inference(spm,[status(thm)],[c_0_107, c_0_46])).
% 2.81/2.98  cnf(c_0_123, negated_conjecture, (v1_relat_1(k5_relat_1(k4_relat_1(esk3_0),k6_relat_1(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_109]), c_0_95]), c_0_46]), c_0_53])])).
% 2.81/2.98  cnf(c_0_124, negated_conjecture, (k5_relat_1(k4_relat_1(esk3_0),k6_relat_1(esk1_0))=k4_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_109]), c_0_46])])).
% 2.81/2.98  cnf(c_0_125, plain, (X3=X4|~r2_relset_1(X1,X2,X3,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_111])).
% 2.81/2.98  cnf(c_0_126, negated_conjecture, (r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,k2_relat_1(esk3_0),k2_relat_1(esk3_0),esk1_0,esk3_0,esk4_0),k6_relat_1(esk1_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_112, c_0_85]), c_0_85])).
% 2.81/2.98  cnf(c_0_127, negated_conjecture, (k1_partfun1(esk1_0,k2_relat_1(esk3_0),k2_relat_1(esk3_0),esk1_0,esk3_0,esk4_0)=k5_relat_1(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_114]), c_0_59])])).
% 2.81/2.98  cnf(c_0_128, plain, (m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X6)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_115])).
% 2.81/2.98  cnf(c_0_129, negated_conjecture, (r1_tarski(k1_relat_1(esk4_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_116]), c_0_117])])).
% 2.81/2.98  cnf(c_0_130, negated_conjecture, (k2_relat_1(k2_funct_1(esk3_0))=k1_relat_1(esk3_0)|~r1_tarski(k2_relat_1(k2_funct_1(esk3_0)),k1_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118, c_0_119]), c_0_57]), c_0_57]), c_0_53]), c_0_53]), c_0_57]), c_0_57])])).
% 2.81/2.98  cnf(c_0_131, negated_conjecture, (r1_tarski(k2_relat_1(k2_funct_1(esk3_0)),k1_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_42]), c_0_59]), c_0_46])])).
% 2.81/2.98  cnf(c_0_132, negated_conjecture, (k5_relat_1(esk3_0,k4_relat_1(esk3_0))=k6_relat_1(k1_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121, c_0_46]), c_0_58]), c_0_59])])).
% 2.81/2.98  cnf(c_0_133, negated_conjecture, (k5_relat_1(k6_relat_1(k2_relat_1(esk3_0)),k4_relat_1(esk3_0))=k4_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_122, c_0_56])).
% 2.81/2.98  cnf(c_0_134, negated_conjecture, (v1_relat_1(k4_relat_1(esk3_0))), inference(rw,[status(thm)],[c_0_123, c_0_124])).
% 2.81/2.98  cnf(c_0_135, plain, (X1=k6_relat_1(X2)|~r2_relset_1(X2,X2,X1,k6_relat_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))), inference(spm,[status(thm)],[c_0_125, c_0_47])).
% 2.81/2.98  cnf(c_0_136, negated_conjecture, (r2_relset_1(esk1_0,esk1_0,k5_relat_1(esk3_0,esk4_0),k6_relat_1(esk1_0))), inference(rw,[status(thm)],[c_0_126, c_0_127])).
% 2.81/2.98  cnf(c_0_137, negated_conjecture, (m1_subset_1(k1_partfun1(X1,X2,k2_relat_1(esk3_0),esk1_0,X3,esk4_0),k1_zfmisc_1(k2_zfmisc_1(X1,esk1_0)))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_100]), c_0_101])])).
% 2.81/2.98  cnf(c_0_138, plain, (k5_relat_1(k4_relat_1(X1),X1)=k6_relat_1(k2_relat_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_68, c_0_106])).
% 2.81/2.98  cnf(c_0_139, negated_conjecture, (k5_relat_1(k6_relat_1(esk2_0),esk4_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_129]), c_0_117])])).
% 2.81/2.98  cnf(c_0_140, negated_conjecture, (k2_relat_1(k2_funct_1(esk3_0))=k1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_130, c_0_131])])).
% 2.81/2.98  cnf(c_0_141, negated_conjecture, (k5_relat_1(k2_funct_1(esk3_0),k6_relat_1(k1_relat_1(esk3_0)))=k4_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_132]), c_0_133]), c_0_134])])).
% 2.81/2.98  cnf(c_0_142, negated_conjecture, (k6_relat_1(esk1_0)=k5_relat_1(esk3_0,esk4_0)|~m1_subset_1(k5_relat_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(spm,[status(thm)],[c_0_135, c_0_136])).
% 2.81/2.98  cnf(c_0_143, negated_conjecture, (m1_subset_1(k5_relat_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137, c_0_114]), c_0_127]), c_0_59])])).
% 2.81/2.98  cnf(c_0_144, negated_conjecture, (k5_relat_1(k5_relat_1(X1,esk3_0),esk4_0)=k5_relat_1(X1,k5_relat_1(esk3_0,esk4_0))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_67, c_0_117])).
% 2.81/2.98  cnf(c_0_145, negated_conjecture, (k5_relat_1(k4_relat_1(esk3_0),esk3_0)=k6_relat_1(k2_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_46]), c_0_58]), c_0_59])])).
% 2.81/2.98  cnf(c_0_146, negated_conjecture, (k5_relat_1(k6_relat_1(k2_relat_1(esk3_0)),esk4_0)=esk4_0), inference(rw,[status(thm)],[c_0_139, c_0_85])).
% 2.81/2.98  cnf(c_0_147, negated_conjecture, (esk4_0!=k2_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 2.81/2.98  cnf(c_0_148, negated_conjecture, (k2_funct_1(esk3_0)=k4_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_140]), c_0_141]), c_0_59]), c_0_46])])).
% 2.81/2.98  cnf(c_0_149, negated_conjecture, (k6_relat_1(esk1_0)=k5_relat_1(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_142, c_0_143])])).
% 2.81/2.98  cnf(c_0_150, negated_conjecture, (k5_relat_1(k4_relat_1(esk3_0),k5_relat_1(esk3_0,esk4_0))=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_144, c_0_145]), c_0_146]), c_0_134])])).
% 2.81/2.98  cnf(c_0_151, negated_conjecture, (esk4_0!=k4_relat_1(esk3_0)), inference(rw,[status(thm)],[c_0_147, c_0_148])).
% 2.81/2.98  cnf(c_0_152, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_124, c_0_149]), c_0_150]), c_0_151]), ['proof']).
% 2.81/2.98  # SZS output end CNFRefutation
% 2.81/2.98  # Proof object total steps             : 153
% 2.81/2.98  # Proof object clause steps            : 104
% 2.81/2.98  # Proof object formula steps           : 49
% 2.81/2.98  # Proof object conjectures             : 66
% 2.81/2.98  # Proof object clause conjectures      : 63
% 2.81/2.98  # Proof object formula conjectures     : 3
% 2.81/2.98  # Proof object initial clauses used    : 34
% 2.81/2.98  # Proof object initial formulas used   : 24
% 2.81/2.98  # Proof object generating inferences   : 57
% 2.81/2.98  # Proof object simplifying inferences  : 121
% 2.81/2.98  # Training examples: 0 positive, 0 negative
% 2.81/2.98  # Parsed axioms                        : 24
% 2.81/2.98  # Removed by relevancy pruning/SinE    : 0
% 2.81/2.98  # Initial clauses                      : 46
% 2.81/2.98  # Removed in clause preprocessing      : 1
% 2.81/2.98  # Initial clauses in saturation        : 45
% 2.81/2.98  # Processed clauses                    : 8296
% 2.81/2.98  # ...of these trivial                  : 1256
% 2.81/2.98  # ...subsumed                          : 3003
% 2.81/2.98  # ...remaining for further processing  : 4037
% 2.81/2.98  # Other redundant clauses eliminated   : 3
% 2.81/2.98  # Clauses deleted for lack of memory   : 0
% 2.81/2.98  # Backward-subsumed                    : 56
% 2.81/2.98  # Backward-rewritten                   : 758
% 2.81/2.98  # Generated clauses                    : 240911
% 2.81/2.98  # ...of the previous two non-trivial   : 226647
% 2.81/2.98  # Contextual simplify-reflections      : 0
% 2.81/2.98  # Paramodulations                      : 240908
% 2.81/2.98  # Factorizations                       : 0
% 2.81/2.98  # Equation resolutions                 : 3
% 2.81/2.98  # Propositional unsat checks           : 0
% 2.81/2.98  #    Propositional check models        : 0
% 2.81/2.98  #    Propositional check unsatisfiable : 0
% 2.81/2.98  #    Propositional clauses             : 0
% 2.81/2.98  #    Propositional clauses after purity: 0
% 2.81/2.98  #    Propositional unsat core size     : 0
% 2.81/2.98  #    Propositional preprocessing time  : 0.000
% 2.81/2.98  #    Propositional encoding time       : 0.000
% 2.81/2.98  #    Propositional solver time         : 0.000
% 2.81/2.98  #    Success case prop preproc time    : 0.000
% 2.81/2.98  #    Success case prop encoding time   : 0.000
% 2.81/2.98  #    Success case prop solver time     : 0.000
% 2.81/2.98  # Current number of processed clauses  : 3220
% 2.81/2.98  #    Positive orientable unit clauses  : 1217
% 2.81/2.98  #    Positive unorientable unit clauses: 0
% 2.81/2.98  #    Negative unit clauses             : 3
% 2.81/2.98  #    Non-unit-clauses                  : 2000
% 2.81/2.98  # Current number of unprocessed clauses: 216862
% 2.81/2.98  # ...number of literals in the above   : 743037
% 2.81/2.98  # Current number of archived formulas  : 0
% 2.81/2.98  # Current number of archived clauses   : 815
% 2.81/2.98  # Clause-clause subsumption calls (NU) : 104151
% 2.81/2.98  # Rec. Clause-clause subsumption calls : 86864
% 2.81/2.98  # Non-unit clause-clause subsumptions  : 3059
% 2.81/2.98  # Unit Clause-clause subsumption calls : 3218
% 2.81/2.98  # Rewrite failures with RHS unbound    : 0
% 2.81/2.98  # BW rewrite match attempts            : 20477
% 2.81/2.98  # BW rewrite match successes           : 285
% 2.81/2.98  # Condensation attempts                : 0
% 2.81/2.98  # Condensation successes               : 0
% 2.81/2.98  # Termbank termtop insertions          : 8050412
% 2.81/3.00  
% 2.81/3.00  # -------------------------------------------------
% 2.81/3.00  # User time                : 2.530 s
% 2.81/3.00  # System time              : 0.126 s
% 2.81/3.00  # Total time               : 2.656 s
% 2.81/3.00  # Maximum resident set size: 1604 pages
%------------------------------------------------------------------------------

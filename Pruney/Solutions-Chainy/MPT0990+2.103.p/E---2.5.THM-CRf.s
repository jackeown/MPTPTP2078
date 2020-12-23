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
% DateTime   : Thu Dec  3 11:03:14 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  140 (1779 expanded)
%              Number of clauses        :   81 ( 614 expanded)
%              Number of leaves         :   29 ( 455 expanded)
%              Depth                    :   14
%              Number of atoms          :  517 (11816 expanded)
%              Number of equality atoms :  147 (3758 expanded)
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

fof(redefinition_r2_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_relset_1(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

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

fof(dt_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => ( v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))
        & m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(t59_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k1_relat_1(k5_relat_1(k2_funct_1(X1),X1)) = k2_relat_1(X1)
          & k2_relat_1(k5_relat_1(k2_funct_1(X1),X1)) = k2_relat_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(t58_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k1_relat_1(k5_relat_1(X1,k2_funct_1(X1))) = k1_relat_1(X1)
          & k2_relat_1(k5_relat_1(X1,k2_funct_1(X1))) = k1_relat_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).

fof(redefinition_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k1_partfun1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(t29_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X2,X1)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) )
         => ( r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1))
           => ( v2_funct_1(X3)
              & v2_funct_2(X4,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t27_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( k1_relat_1(k5_relat_1(X2,X1)) = k1_relat_1(X2)
           => r1_tarski(k2_relat_1(X2),k1_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_funct_1)).

fof(fc4_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v2_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(d3_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v5_relat_1(X2,X1) )
     => ( v2_funct_2(X2,X1)
      <=> k2_relat_1(X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

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

fof(t80_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(X1,k6_relat_1(k2_relat_1(X1))) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

fof(t37_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k2_relat_1(X1) = k1_relat_1(k4_relat_1(X1))
        & k1_relat_1(X1) = k2_relat_1(k4_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

fof(dt_k4_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k4_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

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

fof(t54_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k4_relat_1(k5_relat_1(X1,X2)) = k5_relat_1(k4_relat_1(X2),k4_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).

fof(involutiveness_k4_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k4_relat_1(k4_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

fof(t78_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

fof(t72_relat_1,axiom,(
    ! [X1] : k4_relat_1(k6_relat_1(X1)) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_relat_1)).

fof(d9_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => k2_funct_1(X1) = k4_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

fof(c_0_29,negated_conjecture,(
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

fof(c_0_30,negated_conjecture,
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_29])])])).

fof(c_0_31,plain,(
    ! [X72] : k6_partfun1(X72) = k6_relat_1(X72) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

fof(c_0_32,plain,(
    ! [X65] :
      ( v1_partfun1(k6_partfun1(X65),X65)
      & m1_subset_1(k6_partfun1(X65),k1_zfmisc_1(k2_zfmisc_1(X65,X65))) ) ),
    inference(variable_rename,[status(thm)],[dt_k6_partfun1])).

fof(c_0_33,plain,(
    ! [X82,X83,X84] :
      ( ( k5_relat_1(X84,k2_funct_1(X84)) = k6_partfun1(X82)
        | X83 = k1_xboole_0
        | k2_relset_1(X82,X83,X84) != X83
        | ~ v2_funct_1(X84)
        | ~ v1_funct_1(X84)
        | ~ v1_funct_2(X84,X82,X83)
        | ~ m1_subset_1(X84,k1_zfmisc_1(k2_zfmisc_1(X82,X83))) )
      & ( k5_relat_1(k2_funct_1(X84),X84) = k6_partfun1(X83)
        | X83 = k1_xboole_0
        | k2_relset_1(X82,X83,X84) != X83
        | ~ v2_funct_1(X84)
        | ~ v1_funct_1(X84)
        | ~ v1_funct_2(X84,X82,X83)
        | ~ m1_subset_1(X84,k1_zfmisc_1(k2_zfmisc_1(X82,X83))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_funct_2])])])).

fof(c_0_34,plain,(
    ! [X53,X54,X55,X56] :
      ( ( ~ r2_relset_1(X53,X54,X55,X56)
        | X55 = X56
        | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X54)))
        | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X53,X54))) )
      & ( X55 != X56
        | r2_relset_1(X53,X54,X55,X56)
        | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X54)))
        | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X53,X54))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).

cnf(c_0_35,negated_conjecture,
    ( r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_partfun1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,plain,
    ( m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_38,plain,(
    ! [X50,X51,X52] :
      ( ( v4_relat_1(X52,X50)
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51))) )
      & ( v5_relat_1(X52,X51)
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_39,plain,(
    ! [X23,X24] :
      ( ~ v1_relat_1(X23)
      | ~ m1_subset_1(X24,k1_zfmisc_1(X23))
      | v1_relat_1(X24) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_40,plain,(
    ! [X28,X29] : v1_relat_1(k2_zfmisc_1(X28,X29)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_41,plain,
    ( k5_relat_1(k2_funct_1(X1),X1) = k6_partfun1(X2)
    | X2 = k1_xboole_0
    | k2_relset_1(X3,X2,X1) != X2
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,plain,
    ( k5_relat_1(X1,k2_funct_1(X1)) = k6_partfun1(X2)
    | X3 = k1_xboole_0
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_43,plain,
    ( X3 = X4
    | ~ r2_relset_1(X1,X2,X3,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_44,negated_conjecture,
    ( r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_relat_1(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_45,plain,
    ( m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(rw,[status(thm)],[c_0_37,c_0_36])).

fof(c_0_46,plain,(
    ! [X59,X60,X61,X62,X63,X64] :
      ( ( v1_funct_1(k1_partfun1(X59,X60,X61,X62,X63,X64))
        | ~ v1_funct_1(X63)
        | ~ m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X59,X60)))
        | ~ v1_funct_1(X64)
        | ~ m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X61,X62))) )
      & ( m1_subset_1(k1_partfun1(X59,X60,X61,X62,X63,X64),k1_zfmisc_1(k2_zfmisc_1(X59,X62)))
        | ~ v1_funct_1(X63)
        | ~ m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X59,X60)))
        | ~ v1_funct_1(X64)
        | ~ m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X61,X62))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).

fof(c_0_47,plain,(
    ! [X25,X26] :
      ( ( ~ v4_relat_1(X26,X25)
        | r1_tarski(k1_relat_1(X26),X25)
        | ~ v1_relat_1(X26) )
      & ( ~ r1_tarski(k1_relat_1(X26),X25)
        | v4_relat_1(X26,X25)
        | ~ v1_relat_1(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

cnf(c_0_48,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_50,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_51,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_52,plain,(
    ! [X47] :
      ( ( k1_relat_1(k5_relat_1(k2_funct_1(X47),X47)) = k2_relat_1(X47)
        | ~ v2_funct_1(X47)
        | ~ v1_relat_1(X47)
        | ~ v1_funct_1(X47) )
      & ( k2_relat_1(k5_relat_1(k2_funct_1(X47),X47)) = k2_relat_1(X47)
        | ~ v2_funct_1(X47)
        | ~ v1_relat_1(X47)
        | ~ v1_funct_1(X47) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t59_funct_1])])])).

cnf(c_0_53,plain,
    ( X2 = k1_xboole_0
    | k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(X2)
    | k2_relset_1(X3,X2,X1) != X2
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(rw,[status(thm)],[c_0_41,c_0_36])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_55,negated_conjecture,
    ( k2_relset_1(esk1_0,esk2_0,esk3_0) = esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_56,negated_conjecture,
    ( v1_funct_2(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_57,negated_conjecture,
    ( v2_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_58,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_59,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_60,plain,(
    ! [X38] :
      ( k1_relat_1(k6_relat_1(X38)) = X38
      & k2_relat_1(k6_relat_1(X38)) = X38 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_61,plain,(
    ! [X46] :
      ( ( k1_relat_1(k5_relat_1(X46,k2_funct_1(X46))) = k1_relat_1(X46)
        | ~ v2_funct_1(X46)
        | ~ v1_relat_1(X46)
        | ~ v1_funct_1(X46) )
      & ( k2_relat_1(k5_relat_1(X46,k2_funct_1(X46))) = k1_relat_1(X46)
        | ~ v2_funct_1(X46)
        | ~ v1_relat_1(X46)
        | ~ v1_funct_1(X46) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t58_funct_1])])])).

cnf(c_0_62,plain,
    ( X3 = k1_xboole_0
    | k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(X2)
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_42,c_0_36])).

fof(c_0_63,plain,(
    ! [X66,X67,X68,X69,X70,X71] :
      ( ~ v1_funct_1(X70)
      | ~ m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(X66,X67)))
      | ~ v1_funct_1(X71)
      | ~ m1_subset_1(X71,k1_zfmisc_1(k2_zfmisc_1(X68,X69)))
      | k1_partfun1(X66,X67,X68,X69,X70,X71) = k5_relat_1(X70,X71) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).

cnf(c_0_64,negated_conjecture,
    ( k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0) = k6_relat_1(esk1_0)
    | ~ m1_subset_1(k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])])).

cnf(c_0_65,plain,
    ( m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X6)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_66,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_67,plain,(
    ! [X73,X74,X75,X76] :
      ( ( v2_funct_1(X75)
        | ~ r2_relset_1(X73,X73,k1_partfun1(X73,X74,X74,X73,X75,X76),k6_partfun1(X73))
        | ~ v1_funct_1(X76)
        | ~ v1_funct_2(X76,X74,X73)
        | ~ m1_subset_1(X76,k1_zfmisc_1(k2_zfmisc_1(X74,X73)))
        | ~ v1_funct_1(X75)
        | ~ v1_funct_2(X75,X73,X74)
        | ~ m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(X73,X74))) )
      & ( v2_funct_2(X76,X73)
        | ~ r2_relset_1(X73,X73,k1_partfun1(X73,X74,X74,X73,X75,X76),k6_partfun1(X73))
        | ~ v1_funct_1(X76)
        | ~ v1_funct_2(X76,X74,X73)
        | ~ m1_subset_1(X76,k1_zfmisc_1(k2_zfmisc_1(X74,X73)))
        | ~ v1_funct_1(X75)
        | ~ v1_funct_2(X75,X73,X74)
        | ~ m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(X73,X74))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_funct_2])])])])).

fof(c_0_68,plain,(
    ! [X8,X9] :
      ( ( r1_tarski(X8,X9)
        | X8 != X9 )
      & ( r1_tarski(X9,X8)
        | X8 != X9 )
      & ( ~ r1_tarski(X8,X9)
        | ~ r1_tarski(X9,X8)
        | X8 = X9 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_69,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_70,negated_conjecture,
    ( v4_relat_1(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_71,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_49]),c_0_51])])).

fof(c_0_72,plain,(
    ! [X44,X45] :
      ( ~ v1_relat_1(X44)
      | ~ v1_funct_1(X44)
      | ~ v1_relat_1(X45)
      | ~ v1_funct_1(X45)
      | k1_relat_1(k5_relat_1(X45,X44)) != k1_relat_1(X45)
      | r1_tarski(k2_relat_1(X45),k1_relat_1(X44)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t27_funct_1])])])).

cnf(c_0_73,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1(X1),X1)) = k2_relat_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_74,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk3_0),esk3_0) = k6_relat_1(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55]),c_0_56]),c_0_57]),c_0_58])]),c_0_59])).

cnf(c_0_75,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_76,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_54]),c_0_51])])).

cnf(c_0_77,plain,
    ( k1_relat_1(k5_relat_1(X1,k2_funct_1(X1))) = k1_relat_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_78,negated_conjecture,
    ( k5_relat_1(esk3_0,k2_funct_1(esk3_0)) = k6_relat_1(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_54]),c_0_55]),c_0_56]),c_0_57]),c_0_58])]),c_0_59])).

cnf(c_0_79,plain,
    ( k1_partfun1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_80,negated_conjecture,
    ( k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0) = k6_relat_1(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_66]),c_0_58]),c_0_49]),c_0_54])])).

cnf(c_0_81,plain,
    ( v2_funct_2(X1,X2)
    | ~ r2_relset_1(X2,X2,k1_partfun1(X2,X3,X3,X2,X4,X1),k6_partfun1(X2))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_82,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_83,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk4_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71])])).

cnf(c_0_84,plain,
    ( r1_tarski(k2_relat_1(X2),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | k1_relat_1(k5_relat_1(X2,X1)) != k1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_85,negated_conjecture,
    ( k2_relat_1(esk3_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_75]),c_0_57]),c_0_58]),c_0_76])])).

cnf(c_0_86,negated_conjecture,
    ( k1_relat_1(esk3_0) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_75]),c_0_57]),c_0_58]),c_0_76])])).

cnf(c_0_87,negated_conjecture,
    ( k6_relat_1(esk1_0) = k5_relat_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_66]),c_0_58]),c_0_49]),c_0_54])])).

fof(c_0_88,plain,(
    ! [X43] :
      ( v1_relat_1(k6_relat_1(X43))
      & v2_funct_1(k6_relat_1(X43)) ) ),
    inference(variable_rename,[status(thm)],[fc4_funct_1])).

fof(c_0_89,plain,(
    ! [X57,X58] :
      ( ( ~ v2_funct_2(X58,X57)
        | k2_relat_1(X58) = X57
        | ~ v1_relat_1(X58)
        | ~ v5_relat_1(X58,X57) )
      & ( k2_relat_1(X58) != X57
        | v2_funct_2(X58,X57)
        | ~ v1_relat_1(X58)
        | ~ v5_relat_1(X58,X57) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_funct_2])])])).

cnf(c_0_90,plain,
    ( v2_funct_2(X1,X2)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X4,X2,X3)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ r2_relset_1(X2,X2,k1_partfun1(X2,X3,X3,X2,X4,X1),k6_relat_1(X2)) ),
    inference(rw,[status(thm)],[c_0_81,c_0_36])).

cnf(c_0_91,negated_conjecture,
    ( v1_funct_2(esk4_0,esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_92,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_93,negated_conjecture,
    ( k1_relat_1(esk4_0) = esk2_0
    | ~ r1_tarski(esk2_0,k1_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_94,negated_conjecture,
    ( r1_tarski(esk2_0,k1_relat_1(X1))
    | k1_relat_1(k5_relat_1(esk3_0,X1)) != esk1_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_86]),c_0_58]),c_0_76])])).

cnf(c_0_95,negated_conjecture,
    ( k5_relat_1(esk3_0,k2_funct_1(esk3_0)) = k5_relat_1(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_78,c_0_87])).

fof(c_0_96,plain,(
    ! [X77,X78,X79,X80,X81] :
      ( ( v2_funct_1(X80)
        | X79 = k1_xboole_0
        | ~ v2_funct_1(k1_partfun1(X77,X78,X78,X79,X80,X81))
        | k2_relset_1(X77,X78,X80) != X78
        | ~ v1_funct_1(X81)
        | ~ v1_funct_2(X81,X78,X79)
        | ~ m1_subset_1(X81,k1_zfmisc_1(k2_zfmisc_1(X78,X79)))
        | ~ v1_funct_1(X80)
        | ~ v1_funct_2(X80,X77,X78)
        | ~ m1_subset_1(X80,k1_zfmisc_1(k2_zfmisc_1(X77,X78))) )
      & ( v2_funct_1(X81)
        | X79 = k1_xboole_0
        | ~ v2_funct_1(k1_partfun1(X77,X78,X78,X79,X80,X81))
        | k2_relset_1(X77,X78,X80) != X78
        | ~ v1_funct_1(X81)
        | ~ v1_funct_2(X81,X78,X79)
        | ~ m1_subset_1(X81,k1_zfmisc_1(k2_zfmisc_1(X78,X79)))
        | ~ v1_funct_1(X80)
        | ~ v1_funct_2(X80,X77,X78)
        | ~ m1_subset_1(X80,k1_zfmisc_1(k2_zfmisc_1(X77,X78))) )
      & ( v2_funct_1(X80)
        | X78 != k1_xboole_0
        | ~ v2_funct_1(k1_partfun1(X77,X78,X78,X79,X80,X81))
        | k2_relset_1(X77,X78,X80) != X78
        | ~ v1_funct_1(X81)
        | ~ v1_funct_2(X81,X78,X79)
        | ~ m1_subset_1(X81,k1_zfmisc_1(k2_zfmisc_1(X78,X79)))
        | ~ v1_funct_1(X80)
        | ~ v1_funct_2(X80,X77,X78)
        | ~ m1_subset_1(X80,k1_zfmisc_1(k2_zfmisc_1(X77,X78))) )
      & ( v2_funct_1(X81)
        | X78 != k1_xboole_0
        | ~ v2_funct_1(k1_partfun1(X77,X78,X78,X79,X80,X81))
        | k2_relset_1(X77,X78,X80) != X78
        | ~ v1_funct_1(X81)
        | ~ v1_funct_2(X81,X78,X79)
        | ~ m1_subset_1(X81,k1_zfmisc_1(k2_zfmisc_1(X78,X79)))
        | ~ v1_funct_1(X80)
        | ~ v1_funct_2(X80,X77,X78)
        | ~ m1_subset_1(X80,k1_zfmisc_1(k2_zfmisc_1(X77,X78))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_funct_2])])])])).

cnf(c_0_97,plain,
    ( v2_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

fof(c_0_98,plain,(
    ! [X41] :
      ( ~ v1_relat_1(X41)
      | k5_relat_1(X41,k6_relat_1(k2_relat_1(X41))) = X41 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_relat_1])])).

fof(c_0_99,plain,(
    ! [X35] :
      ( ( k2_relat_1(X35) = k1_relat_1(k4_relat_1(X35))
        | ~ v1_relat_1(X35) )
      & ( k1_relat_1(X35) = k2_relat_1(k4_relat_1(X35))
        | ~ v1_relat_1(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_relat_1])])])).

fof(c_0_100,plain,(
    ! [X27] :
      ( ~ v1_relat_1(X27)
      | v1_relat_1(k4_relat_1(X27)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relat_1])])).

fof(c_0_101,plain,(
    ! [X48,X49] :
      ( ~ v1_relat_1(X48)
      | ~ v1_funct_1(X48)
      | ~ v1_relat_1(X49)
      | ~ v1_funct_1(X49)
      | ~ v2_funct_1(X48)
      | k2_relat_1(X49) != k1_relat_1(X48)
      | k5_relat_1(X49,X48) != k6_relat_1(k2_relat_1(X48))
      | X49 = k2_funct_1(X48) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_funct_1])])])).

cnf(c_0_102,plain,
    ( k2_relat_1(X1) = X2
    | ~ v2_funct_2(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_89])).

cnf(c_0_103,negated_conjecture,
    ( v2_funct_2(esk4_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_44]),c_0_56]),c_0_91]),c_0_58]),c_0_66]),c_0_54]),c_0_49])])).

cnf(c_0_104,negated_conjecture,
    ( v5_relat_1(esk4_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_92,c_0_49])).

cnf(c_0_105,negated_conjecture,
    ( k1_relat_1(esk4_0) = esk2_0
    | k1_relat_1(k5_relat_1(esk3_0,esk4_0)) != esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_66]),c_0_71])])).

cnf(c_0_106,negated_conjecture,
    ( k1_relat_1(k5_relat_1(esk3_0,esk4_0)) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_95]),c_0_86]),c_0_57]),c_0_58]),c_0_76])])).

cnf(c_0_107,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_96])).

cnf(c_0_108,negated_conjecture,
    ( k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0) = k5_relat_1(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_80,c_0_87])).

cnf(c_0_109,negated_conjecture,
    ( v2_funct_1(k5_relat_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_97,c_0_87])).

cnf(c_0_110,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_111,plain,(
    ! [X36,X37] :
      ( ~ v1_relat_1(X36)
      | ~ v1_relat_1(X37)
      | k4_relat_1(k5_relat_1(X36,X37)) = k5_relat_1(k4_relat_1(X37),k4_relat_1(X36)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_relat_1])])])).

fof(c_0_112,plain,(
    ! [X30] :
      ( ~ v1_relat_1(X30)
      | k4_relat_1(k4_relat_1(X30)) = X30 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k4_relat_1])])).

cnf(c_0_113,plain,
    ( k5_relat_1(X1,k6_relat_1(k2_relat_1(X1))) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_98])).

cnf(c_0_114,plain,
    ( k1_relat_1(X1) = k2_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_99])).

cnf(c_0_115,plain,
    ( v1_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_100])).

fof(c_0_116,plain,(
    ! [X40] :
      ( ~ v1_relat_1(X40)
      | k5_relat_1(k6_relat_1(k1_relat_1(X40)),X40) = X40 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_relat_1])])).

cnf(c_0_117,plain,
    ( X2 = k2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X1)
    | k2_relat_1(X2) != k1_relat_1(X1)
    | k5_relat_1(X2,X1) != k6_relat_1(k2_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_101])).

cnf(c_0_118,negated_conjecture,
    ( k2_relat_1(esk4_0) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_103]),c_0_104]),c_0_71])])).

cnf(c_0_119,negated_conjecture,
    ( k1_relat_1(esk4_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_105,c_0_106])])).

cnf(c_0_120,negated_conjecture,
    ( v2_funct_1(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_108]),c_0_55]),c_0_56]),c_0_91]),c_0_109]),c_0_58]),c_0_66]),c_0_54]),c_0_49])]),c_0_110])).

cnf(c_0_121,plain,
    ( k4_relat_1(k5_relat_1(X1,X2)) = k5_relat_1(k4_relat_1(X2),k4_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_111])).

cnf(c_0_122,plain,
    ( k4_relat_1(k4_relat_1(X1)) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_112])).

cnf(c_0_123,plain,
    ( k5_relat_1(k4_relat_1(X1),k6_relat_1(k1_relat_1(X1))) = k4_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_114]),c_0_115])).

fof(c_0_124,plain,(
    ! [X39] : k4_relat_1(k6_relat_1(X39)) = k6_relat_1(X39) ),
    inference(variable_rename,[status(thm)],[t72_relat_1])).

cnf(c_0_125,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_116])).

fof(c_0_126,plain,(
    ! [X42] :
      ( ~ v1_relat_1(X42)
      | ~ v1_funct_1(X42)
      | ~ v2_funct_1(X42)
      | k2_funct_1(X42) = k4_relat_1(X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_1])])).

cnf(c_0_127,negated_conjecture,
    ( X1 = k2_funct_1(esk4_0)
    | k5_relat_1(X1,esk4_0) != k5_relat_1(esk3_0,esk4_0)
    | k2_relat_1(X1) != esk2_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_118]),c_0_66]),c_0_71])]),c_0_87]),c_0_119]),c_0_120])])).

cnf(c_0_128,plain,
    ( k4_relat_1(k5_relat_1(k4_relat_1(X1),X2)) = k5_relat_1(k4_relat_1(X2),X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_122]),c_0_115])).

cnf(c_0_129,negated_conjecture,
    ( k5_relat_1(k4_relat_1(esk4_0),k6_relat_1(esk2_0)) = k4_relat_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_119]),c_0_71])])).

cnf(c_0_130,plain,
    ( k4_relat_1(k6_relat_1(X1)) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_124])).

cnf(c_0_131,negated_conjecture,
    ( k5_relat_1(k6_relat_1(esk2_0),esk4_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_119]),c_0_71])])).

cnf(c_0_132,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

cnf(c_0_133,plain,
    ( k2_funct_1(X1) = k4_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_126])).

cnf(c_0_134,negated_conjecture,
    ( k2_funct_1(esk4_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_127]),c_0_85]),c_0_58]),c_0_76])])).

cnf(c_0_135,negated_conjecture,
    ( esk4_0 != k2_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_136,negated_conjecture,
    ( k4_relat_1(k4_relat_1(esk4_0)) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_129]),c_0_130]),c_0_131]),c_0_132]),c_0_71])])).

cnf(c_0_137,negated_conjecture,
    ( k4_relat_1(esk4_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_133,c_0_134]),c_0_120]),c_0_66]),c_0_71])])).

cnf(c_0_138,negated_conjecture,
    ( k4_relat_1(esk3_0) != esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_133]),c_0_57]),c_0_58]),c_0_76])])).

cnf(c_0_139,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_136,c_0_137]),c_0_138]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:57:45 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.48  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.19/0.48  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.19/0.48  #
% 0.19/0.48  # Preprocessing time       : 0.030 s
% 0.19/0.48  # Presaturation interreduction done
% 0.19/0.48  
% 0.19/0.48  # Proof found!
% 0.19/0.48  # SZS status Theorem
% 0.19/0.48  # SZS output start CNFRefutation
% 0.19/0.48  fof(t36_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(((k2_relset_1(X1,X2,X3)=X2&r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1)))&v2_funct_1(X3))=>(X1=k1_xboole_0|X2=k1_xboole_0|X4=k2_funct_1(X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 0.19/0.48  fof(redefinition_k6_partfun1, axiom, ![X1]:k6_partfun1(X1)=k6_relat_1(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 0.19/0.48  fof(dt_k6_partfun1, axiom, ![X1]:(v1_partfun1(k6_partfun1(X1),X1)&m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 0.19/0.48  fof(t35_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((k2_relset_1(X1,X2,X3)=X2&v2_funct_1(X3))=>(X2=k1_xboole_0|(k5_relat_1(X3,k2_funct_1(X3))=k6_partfun1(X1)&k5_relat_1(k2_funct_1(X3),X3)=k6_partfun1(X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 0.19/0.48  fof(redefinition_r2_relset_1, axiom, ![X1, X2, X3, X4]:((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_relset_1(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 0.19/0.48  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.19/0.48  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.19/0.48  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.19/0.48  fof(dt_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>(v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))&m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 0.19/0.48  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 0.19/0.48  fof(t59_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k1_relat_1(k5_relat_1(k2_funct_1(X1),X1))=k2_relat_1(X1)&k2_relat_1(k5_relat_1(k2_funct_1(X1),X1))=k2_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_funct_1)).
% 0.19/0.48  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 0.19/0.48  fof(t58_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k1_relat_1(k5_relat_1(X1,k2_funct_1(X1)))=k1_relat_1(X1)&k2_relat_1(k5_relat_1(X1,k2_funct_1(X1)))=k1_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_funct_1)).
% 0.19/0.48  fof(redefinition_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>k1_partfun1(X1,X2,X3,X4,X5,X6)=k5_relat_1(X5,X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 0.19/0.48  fof(t29_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1))=>(v2_funct_1(X3)&v2_funct_2(X4,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 0.19/0.48  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.48  fof(t27_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(k1_relat_1(k5_relat_1(X2,X1))=k1_relat_1(X2)=>r1_tarski(k2_relat_1(X2),k1_relat_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_funct_1)).
% 0.19/0.48  fof(fc4_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v2_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 0.19/0.48  fof(d3_funct_2, axiom, ![X1, X2]:((v1_relat_1(X2)&v5_relat_1(X2,X1))=>(v2_funct_2(X2,X1)<=>k2_relat_1(X2)=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 0.19/0.48  fof(t30_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X2,X3))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>((v2_funct_1(k1_partfun1(X1,X2,X2,X3,X4,X5))&k2_relset_1(X1,X2,X4)=X2)=>((X3=k1_xboole_0&X2!=k1_xboole_0)|(v2_funct_1(X4)&v2_funct_1(X5)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_funct_2)).
% 0.19/0.48  fof(t80_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k5_relat_1(X1,k6_relat_1(k2_relat_1(X1)))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 0.19/0.48  fof(t37_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k4_relat_1(X1))&k1_relat_1(X1)=k2_relat_1(k4_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 0.19/0.48  fof(dt_k4_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>v1_relat_1(k4_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 0.19/0.48  fof(t64_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(((v2_funct_1(X1)&k2_relat_1(X2)=k1_relat_1(X1))&k5_relat_1(X2,X1)=k6_relat_1(k2_relat_1(X1)))=>X2=k2_funct_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_1)).
% 0.19/0.48  fof(t54_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k4_relat_1(k5_relat_1(X1,X2))=k5_relat_1(k4_relat_1(X2),k4_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_relat_1)).
% 0.19/0.48  fof(involutiveness_k4_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k4_relat_1(k4_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k4_relat_1)).
% 0.19/0.48  fof(t78_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_relat_1)).
% 0.19/0.48  fof(t72_relat_1, axiom, ![X1]:k4_relat_1(k6_relat_1(X1))=k6_relat_1(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_relat_1)).
% 0.19/0.48  fof(d9_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>k2_funct_1(X1)=k4_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 0.19/0.48  fof(c_0_29, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(((k2_relset_1(X1,X2,X3)=X2&r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1)))&v2_funct_1(X3))=>(X1=k1_xboole_0|X2=k1_xboole_0|X4=k2_funct_1(X3)))))), inference(assume_negation,[status(cth)],[t36_funct_2])).
% 0.19/0.48  fof(c_0_30, negated_conjecture, (((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,esk1_0,esk2_0))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))))&(((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,esk2_0,esk1_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))))&(((k2_relset_1(esk1_0,esk2_0,esk3_0)=esk2_0&r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_partfun1(esk1_0)))&v2_funct_1(esk3_0))&((esk1_0!=k1_xboole_0&esk2_0!=k1_xboole_0)&esk4_0!=k2_funct_1(esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_29])])])).
% 0.19/0.48  fof(c_0_31, plain, ![X72]:k6_partfun1(X72)=k6_relat_1(X72), inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).
% 0.19/0.48  fof(c_0_32, plain, ![X65]:(v1_partfun1(k6_partfun1(X65),X65)&m1_subset_1(k6_partfun1(X65),k1_zfmisc_1(k2_zfmisc_1(X65,X65)))), inference(variable_rename,[status(thm)],[dt_k6_partfun1])).
% 0.19/0.48  fof(c_0_33, plain, ![X82, X83, X84]:((k5_relat_1(X84,k2_funct_1(X84))=k6_partfun1(X82)|X83=k1_xboole_0|(k2_relset_1(X82,X83,X84)!=X83|~v2_funct_1(X84))|(~v1_funct_1(X84)|~v1_funct_2(X84,X82,X83)|~m1_subset_1(X84,k1_zfmisc_1(k2_zfmisc_1(X82,X83)))))&(k5_relat_1(k2_funct_1(X84),X84)=k6_partfun1(X83)|X83=k1_xboole_0|(k2_relset_1(X82,X83,X84)!=X83|~v2_funct_1(X84))|(~v1_funct_1(X84)|~v1_funct_2(X84,X82,X83)|~m1_subset_1(X84,k1_zfmisc_1(k2_zfmisc_1(X82,X83)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_funct_2])])])).
% 0.19/0.48  fof(c_0_34, plain, ![X53, X54, X55, X56]:((~r2_relset_1(X53,X54,X55,X56)|X55=X56|(~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X54)))|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X53,X54)))))&(X55!=X56|r2_relset_1(X53,X54,X55,X56)|(~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X54)))|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X53,X54)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).
% 0.19/0.48  cnf(c_0_35, negated_conjecture, (r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_partfun1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.48  cnf(c_0_36, plain, (k6_partfun1(X1)=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.48  cnf(c_0_37, plain, (m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.48  fof(c_0_38, plain, ![X50, X51, X52]:((v4_relat_1(X52,X50)|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51))))&(v5_relat_1(X52,X51)|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.19/0.48  fof(c_0_39, plain, ![X23, X24]:(~v1_relat_1(X23)|(~m1_subset_1(X24,k1_zfmisc_1(X23))|v1_relat_1(X24))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.19/0.48  fof(c_0_40, plain, ![X28, X29]:v1_relat_1(k2_zfmisc_1(X28,X29)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.19/0.48  cnf(c_0_41, plain, (k5_relat_1(k2_funct_1(X1),X1)=k6_partfun1(X2)|X2=k1_xboole_0|k2_relset_1(X3,X2,X1)!=X2|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.48  cnf(c_0_42, plain, (k5_relat_1(X1,k2_funct_1(X1))=k6_partfun1(X2)|X3=k1_xboole_0|k2_relset_1(X2,X3,X1)!=X3|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.48  cnf(c_0_43, plain, (X3=X4|~r2_relset_1(X1,X2,X3,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.48  cnf(c_0_44, negated_conjecture, (r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_relat_1(esk1_0))), inference(rw,[status(thm)],[c_0_35, c_0_36])).
% 0.19/0.48  cnf(c_0_45, plain, (m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(rw,[status(thm)],[c_0_37, c_0_36])).
% 0.19/0.48  fof(c_0_46, plain, ![X59, X60, X61, X62, X63, X64]:((v1_funct_1(k1_partfun1(X59,X60,X61,X62,X63,X64))|(~v1_funct_1(X63)|~m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X59,X60)))|~v1_funct_1(X64)|~m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X61,X62)))))&(m1_subset_1(k1_partfun1(X59,X60,X61,X62,X63,X64),k1_zfmisc_1(k2_zfmisc_1(X59,X62)))|(~v1_funct_1(X63)|~m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X59,X60)))|~v1_funct_1(X64)|~m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X61,X62)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).
% 0.19/0.48  fof(c_0_47, plain, ![X25, X26]:((~v4_relat_1(X26,X25)|r1_tarski(k1_relat_1(X26),X25)|~v1_relat_1(X26))&(~r1_tarski(k1_relat_1(X26),X25)|v4_relat_1(X26,X25)|~v1_relat_1(X26))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.19/0.48  cnf(c_0_48, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.48  cnf(c_0_49, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.48  cnf(c_0_50, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.48  cnf(c_0_51, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.48  fof(c_0_52, plain, ![X47]:((k1_relat_1(k5_relat_1(k2_funct_1(X47),X47))=k2_relat_1(X47)|~v2_funct_1(X47)|(~v1_relat_1(X47)|~v1_funct_1(X47)))&(k2_relat_1(k5_relat_1(k2_funct_1(X47),X47))=k2_relat_1(X47)|~v2_funct_1(X47)|(~v1_relat_1(X47)|~v1_funct_1(X47)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t59_funct_1])])])).
% 0.19/0.48  cnf(c_0_53, plain, (X2=k1_xboole_0|k5_relat_1(k2_funct_1(X1),X1)=k6_relat_1(X2)|k2_relset_1(X3,X2,X1)!=X2|~v1_funct_1(X1)|~v2_funct_1(X1)|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(rw,[status(thm)],[c_0_41, c_0_36])).
% 0.19/0.48  cnf(c_0_54, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.48  cnf(c_0_55, negated_conjecture, (k2_relset_1(esk1_0,esk2_0,esk3_0)=esk2_0), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.48  cnf(c_0_56, negated_conjecture, (v1_funct_2(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.48  cnf(c_0_57, negated_conjecture, (v2_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.48  cnf(c_0_58, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.48  cnf(c_0_59, negated_conjecture, (esk2_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.48  fof(c_0_60, plain, ![X38]:(k1_relat_1(k6_relat_1(X38))=X38&k2_relat_1(k6_relat_1(X38))=X38), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.19/0.48  fof(c_0_61, plain, ![X46]:((k1_relat_1(k5_relat_1(X46,k2_funct_1(X46)))=k1_relat_1(X46)|~v2_funct_1(X46)|(~v1_relat_1(X46)|~v1_funct_1(X46)))&(k2_relat_1(k5_relat_1(X46,k2_funct_1(X46)))=k1_relat_1(X46)|~v2_funct_1(X46)|(~v1_relat_1(X46)|~v1_funct_1(X46)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t58_funct_1])])])).
% 0.19/0.48  cnf(c_0_62, plain, (X3=k1_xboole_0|k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(X2)|k2_relset_1(X2,X3,X1)!=X3|~v1_funct_1(X1)|~v2_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(rw,[status(thm)],[c_0_42, c_0_36])).
% 0.19/0.48  fof(c_0_63, plain, ![X66, X67, X68, X69, X70, X71]:(~v1_funct_1(X70)|~m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(X66,X67)))|~v1_funct_1(X71)|~m1_subset_1(X71,k1_zfmisc_1(k2_zfmisc_1(X68,X69)))|k1_partfun1(X66,X67,X68,X69,X70,X71)=k5_relat_1(X70,X71)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).
% 0.19/0.48  cnf(c_0_64, negated_conjecture, (k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0)=k6_relat_1(esk1_0)|~m1_subset_1(k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45])])).
% 0.19/0.48  cnf(c_0_65, plain, (m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X6)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.19/0.48  cnf(c_0_66, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.48  fof(c_0_67, plain, ![X73, X74, X75, X76]:((v2_funct_1(X75)|~r2_relset_1(X73,X73,k1_partfun1(X73,X74,X74,X73,X75,X76),k6_partfun1(X73))|(~v1_funct_1(X76)|~v1_funct_2(X76,X74,X73)|~m1_subset_1(X76,k1_zfmisc_1(k2_zfmisc_1(X74,X73))))|(~v1_funct_1(X75)|~v1_funct_2(X75,X73,X74)|~m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(X73,X74)))))&(v2_funct_2(X76,X73)|~r2_relset_1(X73,X73,k1_partfun1(X73,X74,X74,X73,X75,X76),k6_partfun1(X73))|(~v1_funct_1(X76)|~v1_funct_2(X76,X74,X73)|~m1_subset_1(X76,k1_zfmisc_1(k2_zfmisc_1(X74,X73))))|(~v1_funct_1(X75)|~v1_funct_2(X75,X73,X74)|~m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(X73,X74)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_funct_2])])])])).
% 0.19/0.48  fof(c_0_68, plain, ![X8, X9]:(((r1_tarski(X8,X9)|X8!=X9)&(r1_tarski(X9,X8)|X8!=X9))&(~r1_tarski(X8,X9)|~r1_tarski(X9,X8)|X8=X9)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.48  cnf(c_0_69, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.48  cnf(c_0_70, negated_conjecture, (v4_relat_1(esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.19/0.48  cnf(c_0_71, negated_conjecture, (v1_relat_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_49]), c_0_51])])).
% 0.19/0.48  fof(c_0_72, plain, ![X44, X45]:(~v1_relat_1(X44)|~v1_funct_1(X44)|(~v1_relat_1(X45)|~v1_funct_1(X45)|(k1_relat_1(k5_relat_1(X45,X44))!=k1_relat_1(X45)|r1_tarski(k2_relat_1(X45),k1_relat_1(X44))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t27_funct_1])])])).
% 0.19/0.48  cnf(c_0_73, plain, (k1_relat_1(k5_relat_1(k2_funct_1(X1),X1))=k2_relat_1(X1)|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.19/0.48  cnf(c_0_74, negated_conjecture, (k5_relat_1(k2_funct_1(esk3_0),esk3_0)=k6_relat_1(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55]), c_0_56]), c_0_57]), c_0_58])]), c_0_59])).
% 0.19/0.48  cnf(c_0_75, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.19/0.48  cnf(c_0_76, negated_conjecture, (v1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_54]), c_0_51])])).
% 0.19/0.48  cnf(c_0_77, plain, (k1_relat_1(k5_relat_1(X1,k2_funct_1(X1)))=k1_relat_1(X1)|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.19/0.48  cnf(c_0_78, negated_conjecture, (k5_relat_1(esk3_0,k2_funct_1(esk3_0))=k6_relat_1(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_54]), c_0_55]), c_0_56]), c_0_57]), c_0_58])]), c_0_59])).
% 0.19/0.48  cnf(c_0_79, plain, (k1_partfun1(X2,X3,X5,X6,X1,X4)=k5_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.19/0.48  cnf(c_0_80, negated_conjecture, (k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0)=k6_relat_1(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_66]), c_0_58]), c_0_49]), c_0_54])])).
% 0.19/0.48  cnf(c_0_81, plain, (v2_funct_2(X1,X2)|~r2_relset_1(X2,X2,k1_partfun1(X2,X3,X3,X2,X4,X1),k6_partfun1(X2))|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_1(X4)|~v1_funct_2(X4,X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.19/0.48  cnf(c_0_82, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.19/0.48  cnf(c_0_83, negated_conjecture, (r1_tarski(k1_relat_1(esk4_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_71])])).
% 0.19/0.48  cnf(c_0_84, plain, (r1_tarski(k2_relat_1(X2),k1_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|k1_relat_1(k5_relat_1(X2,X1))!=k1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.19/0.48  cnf(c_0_85, negated_conjecture, (k2_relat_1(esk3_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_75]), c_0_57]), c_0_58]), c_0_76])])).
% 0.19/0.48  cnf(c_0_86, negated_conjecture, (k1_relat_1(esk3_0)=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_75]), c_0_57]), c_0_58]), c_0_76])])).
% 0.19/0.48  cnf(c_0_87, negated_conjecture, (k6_relat_1(esk1_0)=k5_relat_1(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_66]), c_0_58]), c_0_49]), c_0_54])])).
% 0.19/0.48  fof(c_0_88, plain, ![X43]:(v1_relat_1(k6_relat_1(X43))&v2_funct_1(k6_relat_1(X43))), inference(variable_rename,[status(thm)],[fc4_funct_1])).
% 0.19/0.48  fof(c_0_89, plain, ![X57, X58]:((~v2_funct_2(X58,X57)|k2_relat_1(X58)=X57|(~v1_relat_1(X58)|~v5_relat_1(X58,X57)))&(k2_relat_1(X58)!=X57|v2_funct_2(X58,X57)|(~v1_relat_1(X58)|~v5_relat_1(X58,X57)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_funct_2])])])).
% 0.19/0.48  cnf(c_0_90, plain, (v2_funct_2(X1,X2)|~v1_funct_1(X4)|~v1_funct_1(X1)|~v1_funct_2(X4,X2,X3)|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~r2_relset_1(X2,X2,k1_partfun1(X2,X3,X3,X2,X4,X1),k6_relat_1(X2))), inference(rw,[status(thm)],[c_0_81, c_0_36])).
% 0.19/0.48  cnf(c_0_91, negated_conjecture, (v1_funct_2(esk4_0,esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.48  cnf(c_0_92, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.48  cnf(c_0_93, negated_conjecture, (k1_relat_1(esk4_0)=esk2_0|~r1_tarski(esk2_0,k1_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 0.19/0.48  cnf(c_0_94, negated_conjecture, (r1_tarski(esk2_0,k1_relat_1(X1))|k1_relat_1(k5_relat_1(esk3_0,X1))!=esk1_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_86]), c_0_58]), c_0_76])])).
% 0.19/0.48  cnf(c_0_95, negated_conjecture, (k5_relat_1(esk3_0,k2_funct_1(esk3_0))=k5_relat_1(esk3_0,esk4_0)), inference(rw,[status(thm)],[c_0_78, c_0_87])).
% 0.19/0.48  fof(c_0_96, plain, ![X77, X78, X79, X80, X81]:(((v2_funct_1(X80)|X79=k1_xboole_0|(~v2_funct_1(k1_partfun1(X77,X78,X78,X79,X80,X81))|k2_relset_1(X77,X78,X80)!=X78)|(~v1_funct_1(X81)|~v1_funct_2(X81,X78,X79)|~m1_subset_1(X81,k1_zfmisc_1(k2_zfmisc_1(X78,X79))))|(~v1_funct_1(X80)|~v1_funct_2(X80,X77,X78)|~m1_subset_1(X80,k1_zfmisc_1(k2_zfmisc_1(X77,X78)))))&(v2_funct_1(X81)|X79=k1_xboole_0|(~v2_funct_1(k1_partfun1(X77,X78,X78,X79,X80,X81))|k2_relset_1(X77,X78,X80)!=X78)|(~v1_funct_1(X81)|~v1_funct_2(X81,X78,X79)|~m1_subset_1(X81,k1_zfmisc_1(k2_zfmisc_1(X78,X79))))|(~v1_funct_1(X80)|~v1_funct_2(X80,X77,X78)|~m1_subset_1(X80,k1_zfmisc_1(k2_zfmisc_1(X77,X78))))))&((v2_funct_1(X80)|X78!=k1_xboole_0|(~v2_funct_1(k1_partfun1(X77,X78,X78,X79,X80,X81))|k2_relset_1(X77,X78,X80)!=X78)|(~v1_funct_1(X81)|~v1_funct_2(X81,X78,X79)|~m1_subset_1(X81,k1_zfmisc_1(k2_zfmisc_1(X78,X79))))|(~v1_funct_1(X80)|~v1_funct_2(X80,X77,X78)|~m1_subset_1(X80,k1_zfmisc_1(k2_zfmisc_1(X77,X78)))))&(v2_funct_1(X81)|X78!=k1_xboole_0|(~v2_funct_1(k1_partfun1(X77,X78,X78,X79,X80,X81))|k2_relset_1(X77,X78,X80)!=X78)|(~v1_funct_1(X81)|~v1_funct_2(X81,X78,X79)|~m1_subset_1(X81,k1_zfmisc_1(k2_zfmisc_1(X78,X79))))|(~v1_funct_1(X80)|~v1_funct_2(X80,X77,X78)|~m1_subset_1(X80,k1_zfmisc_1(k2_zfmisc_1(X77,X78))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_funct_2])])])])).
% 0.19/0.48  cnf(c_0_97, plain, (v2_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_88])).
% 0.19/0.48  fof(c_0_98, plain, ![X41]:(~v1_relat_1(X41)|k5_relat_1(X41,k6_relat_1(k2_relat_1(X41)))=X41), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_relat_1])])).
% 0.19/0.48  fof(c_0_99, plain, ![X35]:((k2_relat_1(X35)=k1_relat_1(k4_relat_1(X35))|~v1_relat_1(X35))&(k1_relat_1(X35)=k2_relat_1(k4_relat_1(X35))|~v1_relat_1(X35))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_relat_1])])])).
% 0.19/0.48  fof(c_0_100, plain, ![X27]:(~v1_relat_1(X27)|v1_relat_1(k4_relat_1(X27))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relat_1])])).
% 0.19/0.48  fof(c_0_101, plain, ![X48, X49]:(~v1_relat_1(X48)|~v1_funct_1(X48)|(~v1_relat_1(X49)|~v1_funct_1(X49)|(~v2_funct_1(X48)|k2_relat_1(X49)!=k1_relat_1(X48)|k5_relat_1(X49,X48)!=k6_relat_1(k2_relat_1(X48))|X49=k2_funct_1(X48)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_funct_1])])])).
% 0.19/0.48  cnf(c_0_102, plain, (k2_relat_1(X1)=X2|~v2_funct_2(X1,X2)|~v1_relat_1(X1)|~v5_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_89])).
% 0.19/0.48  cnf(c_0_103, negated_conjecture, (v2_funct_2(esk4_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_44]), c_0_56]), c_0_91]), c_0_58]), c_0_66]), c_0_54]), c_0_49])])).
% 0.19/0.48  cnf(c_0_104, negated_conjecture, (v5_relat_1(esk4_0,esk1_0)), inference(spm,[status(thm)],[c_0_92, c_0_49])).
% 0.19/0.48  cnf(c_0_105, negated_conjecture, (k1_relat_1(esk4_0)=esk2_0|k1_relat_1(k5_relat_1(esk3_0,esk4_0))!=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_66]), c_0_71])])).
% 0.19/0.48  cnf(c_0_106, negated_conjecture, (k1_relat_1(k5_relat_1(esk3_0,esk4_0))=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_95]), c_0_86]), c_0_57]), c_0_58]), c_0_76])])).
% 0.19/0.48  cnf(c_0_107, plain, (v2_funct_1(X1)|X2=k1_xboole_0|~v2_funct_1(k1_partfun1(X3,X4,X4,X2,X5,X1))|k2_relset_1(X3,X4,X5)!=X4|~v1_funct_1(X1)|~v1_funct_2(X1,X4,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|~v1_funct_1(X5)|~v1_funct_2(X5,X3,X4)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_96])).
% 0.19/0.48  cnf(c_0_108, negated_conjecture, (k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0)=k5_relat_1(esk3_0,esk4_0)), inference(rw,[status(thm)],[c_0_80, c_0_87])).
% 0.19/0.48  cnf(c_0_109, negated_conjecture, (v2_funct_1(k5_relat_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_97, c_0_87])).
% 0.19/0.48  cnf(c_0_110, negated_conjecture, (esk1_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.48  fof(c_0_111, plain, ![X36, X37]:(~v1_relat_1(X36)|(~v1_relat_1(X37)|k4_relat_1(k5_relat_1(X36,X37))=k5_relat_1(k4_relat_1(X37),k4_relat_1(X36)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_relat_1])])])).
% 0.19/0.48  fof(c_0_112, plain, ![X30]:(~v1_relat_1(X30)|k4_relat_1(k4_relat_1(X30))=X30), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k4_relat_1])])).
% 0.19/0.48  cnf(c_0_113, plain, (k5_relat_1(X1,k6_relat_1(k2_relat_1(X1)))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_98])).
% 0.19/0.48  cnf(c_0_114, plain, (k1_relat_1(X1)=k2_relat_1(k4_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_99])).
% 0.19/0.48  cnf(c_0_115, plain, (v1_relat_1(k4_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_100])).
% 0.19/0.48  fof(c_0_116, plain, ![X40]:(~v1_relat_1(X40)|k5_relat_1(k6_relat_1(k1_relat_1(X40)),X40)=X40), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_relat_1])])).
% 0.19/0.48  cnf(c_0_117, plain, (X2=k2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v2_funct_1(X1)|k2_relat_1(X2)!=k1_relat_1(X1)|k5_relat_1(X2,X1)!=k6_relat_1(k2_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_101])).
% 0.19/0.48  cnf(c_0_118, negated_conjecture, (k2_relat_1(esk4_0)=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_103]), c_0_104]), c_0_71])])).
% 0.19/0.48  cnf(c_0_119, negated_conjecture, (k1_relat_1(esk4_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_105, c_0_106])])).
% 0.19/0.48  cnf(c_0_120, negated_conjecture, (v2_funct_1(esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_108]), c_0_55]), c_0_56]), c_0_91]), c_0_109]), c_0_58]), c_0_66]), c_0_54]), c_0_49])]), c_0_110])).
% 0.19/0.48  cnf(c_0_121, plain, (k4_relat_1(k5_relat_1(X1,X2))=k5_relat_1(k4_relat_1(X2),k4_relat_1(X1))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_111])).
% 0.19/0.48  cnf(c_0_122, plain, (k4_relat_1(k4_relat_1(X1))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_112])).
% 0.19/0.48  cnf(c_0_123, plain, (k5_relat_1(k4_relat_1(X1),k6_relat_1(k1_relat_1(X1)))=k4_relat_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_114]), c_0_115])).
% 0.19/0.48  fof(c_0_124, plain, ![X39]:k4_relat_1(k6_relat_1(X39))=k6_relat_1(X39), inference(variable_rename,[status(thm)],[t72_relat_1])).
% 0.19/0.48  cnf(c_0_125, plain, (k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1)=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_116])).
% 0.19/0.48  fof(c_0_126, plain, ![X42]:(~v1_relat_1(X42)|~v1_funct_1(X42)|(~v2_funct_1(X42)|k2_funct_1(X42)=k4_relat_1(X42))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_1])])).
% 0.19/0.48  cnf(c_0_127, negated_conjecture, (X1=k2_funct_1(esk4_0)|k5_relat_1(X1,esk4_0)!=k5_relat_1(esk3_0,esk4_0)|k2_relat_1(X1)!=esk2_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_118]), c_0_66]), c_0_71])]), c_0_87]), c_0_119]), c_0_120])])).
% 0.19/0.48  cnf(c_0_128, plain, (k4_relat_1(k5_relat_1(k4_relat_1(X1),X2))=k5_relat_1(k4_relat_1(X2),X1)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_121, c_0_122]), c_0_115])).
% 0.19/0.48  cnf(c_0_129, negated_conjecture, (k5_relat_1(k4_relat_1(esk4_0),k6_relat_1(esk2_0))=k4_relat_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123, c_0_119]), c_0_71])])).
% 0.19/0.48  cnf(c_0_130, plain, (k4_relat_1(k6_relat_1(X1))=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_124])).
% 0.19/0.48  cnf(c_0_131, negated_conjecture, (k5_relat_1(k6_relat_1(esk2_0),esk4_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125, c_0_119]), c_0_71])])).
% 0.19/0.48  cnf(c_0_132, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_88])).
% 0.19/0.48  cnf(c_0_133, plain, (k2_funct_1(X1)=k4_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_126])).
% 0.19/0.48  cnf(c_0_134, negated_conjecture, (k2_funct_1(esk4_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_127]), c_0_85]), c_0_58]), c_0_76])])).
% 0.19/0.48  cnf(c_0_135, negated_conjecture, (esk4_0!=k2_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.48  cnf(c_0_136, negated_conjecture, (k4_relat_1(k4_relat_1(esk4_0))=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_129]), c_0_130]), c_0_131]), c_0_132]), c_0_71])])).
% 0.19/0.48  cnf(c_0_137, negated_conjecture, (k4_relat_1(esk4_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_133, c_0_134]), c_0_120]), c_0_66]), c_0_71])])).
% 0.19/0.48  cnf(c_0_138, negated_conjecture, (k4_relat_1(esk3_0)!=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135, c_0_133]), c_0_57]), c_0_58]), c_0_76])])).
% 0.19/0.48  cnf(c_0_139, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_136, c_0_137]), c_0_138]), ['proof']).
% 0.19/0.48  # SZS output end CNFRefutation
% 0.19/0.48  # Proof object total steps             : 140
% 0.19/0.48  # Proof object clause steps            : 81
% 0.19/0.48  # Proof object formula steps           : 59
% 0.19/0.48  # Proof object conjectures             : 47
% 0.19/0.48  # Proof object clause conjectures      : 44
% 0.19/0.48  # Proof object formula conjectures     : 3
% 0.19/0.48  # Proof object initial clauses used    : 43
% 0.19/0.48  # Proof object initial formulas used   : 29
% 0.19/0.48  # Proof object generating inferences   : 29
% 0.19/0.48  # Proof object simplifying inferences  : 113
% 0.19/0.48  # Training examples: 0 positive, 0 negative
% 0.19/0.48  # Parsed axioms                        : 38
% 0.19/0.48  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.48  # Initial clauses                      : 68
% 0.19/0.48  # Removed in clause preprocessing      : 5
% 0.19/0.48  # Initial clauses in saturation        : 63
% 0.19/0.48  # Processed clauses                    : 987
% 0.19/0.48  # ...of these trivial                  : 60
% 0.19/0.48  # ...subsumed                          : 305
% 0.19/0.48  # ...remaining for further processing  : 622
% 0.19/0.48  # Other redundant clauses eliminated   : 20
% 0.19/0.48  # Clauses deleted for lack of memory   : 0
% 0.19/0.48  # Backward-subsumed                    : 6
% 0.19/0.48  # Backward-rewritten                   : 222
% 0.19/0.48  # Generated clauses                    : 3843
% 0.19/0.48  # ...of the previous two non-trivial   : 3018
% 0.19/0.48  # Contextual simplify-reflections      : 25
% 0.19/0.48  # Paramodulations                      : 3818
% 0.19/0.48  # Factorizations                       : 4
% 0.19/0.48  # Equation resolutions                 : 21
% 0.19/0.48  # Propositional unsat checks           : 0
% 0.19/0.48  #    Propositional check models        : 0
% 0.19/0.48  #    Propositional check unsatisfiable : 0
% 0.19/0.48  #    Propositional clauses             : 0
% 0.19/0.48  #    Propositional clauses after purity: 0
% 0.19/0.48  #    Propositional unsat core size     : 0
% 0.19/0.48  #    Propositional preprocessing time  : 0.000
% 0.19/0.48  #    Propositional encoding time       : 0.000
% 0.19/0.48  #    Propositional solver time         : 0.000
% 0.19/0.48  #    Success case prop preproc time    : 0.000
% 0.19/0.48  #    Success case prop encoding time   : 0.000
% 0.19/0.48  #    Success case prop solver time     : 0.000
% 0.19/0.48  # Current number of processed clauses  : 326
% 0.19/0.48  #    Positive orientable unit clauses  : 94
% 0.19/0.48  #    Positive unorientable unit clauses: 0
% 0.19/0.48  #    Negative unit clauses             : 4
% 0.19/0.48  #    Non-unit-clauses                  : 228
% 0.19/0.48  # Current number of unprocessed clauses: 2075
% 0.19/0.48  # ...number of literals in the above   : 11511
% 0.19/0.48  # Current number of archived formulas  : 0
% 0.19/0.48  # Current number of archived clauses   : 295
% 0.19/0.48  # Clause-clause subsumption calls (NU) : 12782
% 0.19/0.48  # Rec. Clause-clause subsumption calls : 3036
% 0.19/0.48  # Non-unit clause-clause subsumptions  : 334
% 0.19/0.48  # Unit Clause-clause subsumption calls : 335
% 0.19/0.48  # Rewrite failures with RHS unbound    : 0
% 0.19/0.48  # BW rewrite match attempts            : 54
% 0.19/0.48  # BW rewrite match successes           : 30
% 0.19/0.48  # Condensation attempts                : 0
% 0.19/0.48  # Condensation successes               : 0
% 0.19/0.48  # Termbank termtop insertions          : 102440
% 0.19/0.48  
% 0.19/0.48  # -------------------------------------------------
% 0.19/0.48  # User time                : 0.132 s
% 0.19/0.48  # System time              : 0.007 s
% 0.19/0.48  # Total time               : 0.139 s
% 0.19/0.48  # Maximum resident set size: 1628 pages
%------------------------------------------------------------------------------

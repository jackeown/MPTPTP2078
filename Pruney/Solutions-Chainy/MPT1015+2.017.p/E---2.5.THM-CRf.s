%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:05:47 EST 2020

% Result     : Theorem 1.30s
% Output     : CNFRefutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :  192 (57208 expanded)
%              Number of clauses        :  145 (19973 expanded)
%              Number of leaves         :   23 (14438 expanded)
%              Depth                    :   33
%              Number of atoms          :  704 (313021 expanded)
%              Number of equality atoms :  133 (12894 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   48 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t76_funct_2,conjecture,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => ! [X3] :
          ( ( v1_funct_1(X3)
            & v1_funct_2(X3,X1,X1)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
         => ( ( r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X3,X2),X2)
              & v2_funct_1(X2) )
           => r2_relset_1(X1,X1,X3,k6_partfun1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_funct_2)).

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

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t67_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => k1_relset_1(X1,X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

fof(redefinition_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k1_partfun1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(t48_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( ( v2_funct_1(k5_relat_1(X2,X1))
              & k2_relat_1(X2) = k1_relat_1(X1) )
           => ( v2_funct_1(X2)
              & v2_funct_1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t51_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( ( k2_relat_1(k5_relat_1(X2,X1)) = k2_relat_1(X1)
              & v2_funct_1(X1) )
           => r1_tarski(k1_relat_1(X1),k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_funct_1)).

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

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(t61_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(k1_relat_1(X1))
          & k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(k2_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(t3_funct_2,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_funct_1(X1)
        & v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(dt_k6_partfun1,axiom,(
    ! [X1] :
      ( v1_partfun1(k6_partfun1(X1),X1)
      & m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(t23_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( r2_relset_1(X1,X2,k4_relset_1(X1,X1,X1,X2,k6_partfun1(X1),X3),X3)
        & r2_relset_1(X1,X2,k4_relset_1(X1,X2,X2,X2,X3,k6_partfun1(X2)),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_2)).

fof(redefinition_k4_relset_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k4_relset_1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

fof(t49_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
      <=> ! [X2] :
            ( ( v1_relat_1(X2)
              & v1_funct_1(X2) )
           => ! [X3] :
                ( ( v1_relat_1(X3)
                  & v1_funct_1(X3) )
               => ( ( r1_tarski(k2_relat_1(X2),k1_relat_1(X1))
                    & r1_tarski(k2_relat_1(X3),k1_relat_1(X1))
                    & k1_relat_1(X2) = k1_relat_1(X3)
                    & k5_relat_1(X2,X1) = k5_relat_1(X3,X1) )
                 => X2 = X3 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_funct_1)).

fof(c_0_23,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_funct_2(X2,X1,X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
       => ! [X3] :
            ( ( v1_funct_1(X3)
              & v1_funct_2(X3,X1,X1)
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
           => ( ( r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X3,X2),X2)
                & v2_funct_1(X2) )
             => r2_relset_1(X1,X1,X3,k6_partfun1(X1)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t76_funct_2])).

fof(c_0_24,plain,(
    ! [X41,X42,X43,X44] :
      ( ( ~ r2_relset_1(X41,X42,X43,X44)
        | X43 = X44
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X41,X42))) )
      & ( X43 != X44
        | r2_relset_1(X41,X42,X43,X44)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X41,X42))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).

fof(c_0_25,negated_conjecture,
    ( v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,esk3_0,esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))
    & v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,esk3_0,esk3_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))
    & r2_relset_1(esk3_0,esk3_0,k1_partfun1(esk3_0,esk3_0,esk3_0,esk3_0,esk5_0,esk4_0),esk4_0)
    & v2_funct_1(esk4_0)
    & ~ r2_relset_1(esk3_0,esk3_0,esk5_0,k6_partfun1(esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).

cnf(c_0_26,plain,
    ( X3 = X4
    | ~ r2_relset_1(X1,X2,X3,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_27,negated_conjecture,
    ( r2_relset_1(esk3_0,esk3_0,k1_partfun1(esk3_0,esk3_0,esk3_0,esk3_0,esk5_0,esk4_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_29,plain,(
    ! [X45,X46,X47,X48,X49,X50] :
      ( ( v1_funct_1(k1_partfun1(X45,X46,X47,X48,X49,X50))
        | ~ v1_funct_1(X49)
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))
        | ~ v1_funct_1(X50)
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X47,X48))) )
      & ( m1_subset_1(k1_partfun1(X45,X46,X47,X48,X49,X50),k1_zfmisc_1(k2_zfmisc_1(X45,X48)))
        | ~ v1_funct_1(X49)
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))
        | ~ v1_funct_1(X50)
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X47,X48))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).

fof(c_0_30,plain,(
    ! [X26,X27,X28] :
      ( ( v4_relat_1(X28,X26)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) )
      & ( v5_relat_1(X28,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_31,plain,(
    ! [X9,X10] :
      ( ~ v1_relat_1(X9)
      | ~ m1_subset_1(X10,k1_zfmisc_1(X9))
      | v1_relat_1(X10) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_32,plain,(
    ! [X13,X14] : v1_relat_1(k2_zfmisc_1(X13,X14)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_33,plain,(
    ! [X29,X30,X31] :
      ( ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))
      | k1_relset_1(X29,X30,X31) = k1_relat_1(X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_34,plain,(
    ! [X66,X67] :
      ( ~ v1_funct_1(X67)
      | ~ v1_funct_2(X67,X66,X66)
      | ~ m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(X66,X66)))
      | k1_relset_1(X66,X66,X67) = X66 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_funct_2])])).

fof(c_0_35,plain,(
    ! [X52,X53,X54,X55,X56,X57] :
      ( ~ v1_funct_1(X56)
      | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))
      | ~ v1_funct_1(X57)
      | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X54,X55)))
      | k1_partfun1(X52,X53,X54,X55,X56,X57) = k5_relat_1(X56,X57) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).

cnf(c_0_36,negated_conjecture,
    ( k1_partfun1(esk3_0,esk3_0,esk3_0,esk3_0,esk5_0,esk4_0) = esk4_0
    | ~ m1_subset_1(k1_partfun1(esk3_0,esk3_0,esk3_0,esk3_0,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])])).

cnf(c_0_37,plain,
    ( m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X6)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_39,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_41,plain,(
    ! [X11,X12] :
      ( ( ~ v5_relat_1(X12,X11)
        | r1_tarski(k2_relat_1(X12),X11)
        | ~ v1_relat_1(X12) )
      & ( ~ r1_tarski(k2_relat_1(X12),X11)
        | v5_relat_1(X12,X11)
        | ~ v1_relat_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

cnf(c_0_42,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_43,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_44,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_45,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_46,plain,
    ( k1_relset_1(X2,X2,X1) = X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_47,plain,(
    ! [X16,X17] :
      ( ( v2_funct_1(X17)
        | ~ v2_funct_1(k5_relat_1(X17,X16))
        | k2_relat_1(X17) != k1_relat_1(X16)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( v2_funct_1(X16)
        | ~ v2_funct_1(k5_relat_1(X17,X16))
        | k2_relat_1(X17) != k1_relat_1(X16)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_funct_1])])])])).

cnf(c_0_48,plain,
    ( k1_partfun1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_49,negated_conjecture,
    ( k1_partfun1(esk3_0,esk3_0,esk3_0,esk3_0,esk5_0,esk4_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38]),c_0_39]),c_0_28]),c_0_40])])).

fof(c_0_50,plain,(
    ! [X7,X8] :
      ( ( r1_tarski(X7,X8)
        | X7 != X8 )
      & ( r1_tarski(X8,X7)
        | X7 != X8 )
      & ( ~ r1_tarski(X7,X8)
        | ~ r1_tarski(X8,X7)
        | X7 = X8 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_51,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_52,negated_conjecture,
    ( v5_relat_1(esk5_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_40])).

cnf(c_0_53,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_40]),c_0_44])])).

fof(c_0_54,plain,(
    ! [X23,X24] :
      ( ~ v1_relat_1(X23)
      | ~ v1_funct_1(X23)
      | ~ v1_relat_1(X24)
      | ~ v1_funct_1(X24)
      | k2_relat_1(k5_relat_1(X24,X23)) != k2_relat_1(X23)
      | ~ v2_funct_1(X23)
      | r1_tarski(k1_relat_1(X23),k2_relat_1(X24)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t51_funct_1])])])).

cnf(c_0_55,plain,
    ( X1 = k1_relat_1(X2)
    | ~ v1_funct_2(X2,X1,X1)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_56,negated_conjecture,
    ( v1_funct_2(esk4_0,esk3_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_57,plain,(
    ! [X62,X63,X64] :
      ( ( v1_funct_1(k2_funct_1(X64))
        | ~ v2_funct_1(X64)
        | k2_relset_1(X62,X63,X64) != X63
        | ~ v1_funct_1(X64)
        | ~ v1_funct_2(X64,X62,X63)
        | ~ m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X62,X63))) )
      & ( v1_funct_2(k2_funct_1(X64),X63,X62)
        | ~ v2_funct_1(X64)
        | k2_relset_1(X62,X63,X64) != X63
        | ~ v1_funct_1(X64)
        | ~ v1_funct_2(X64,X62,X63)
        | ~ m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X62,X63))) )
      & ( m1_subset_1(k2_funct_1(X64),k1_zfmisc_1(k2_zfmisc_1(X63,X62)))
        | ~ v2_funct_1(X64)
        | k2_relset_1(X62,X63,X64) != X63
        | ~ v1_funct_1(X64)
        | ~ v1_funct_2(X64,X62,X63)
        | ~ m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X62,X63))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_funct_2])])])).

cnf(c_0_58,plain,
    ( v2_funct_1(X1)
    | ~ v2_funct_1(k5_relat_1(X1,X2))
    | k2_relat_1(X1) != k1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_59,negated_conjecture,
    ( k5_relat_1(esk5_0,esk4_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_38]),c_0_39]),c_0_28]),c_0_40])])).

cnf(c_0_60,negated_conjecture,
    ( v2_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_61,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_28]),c_0_44])])).

cnf(c_0_62,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_63,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk5_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53])])).

cnf(c_0_64,plain,
    ( r1_tarski(k1_relat_1(X1),k2_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | k2_relat_1(k5_relat_1(X2,X1)) != k2_relat_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_65,negated_conjecture,
    ( k1_relat_1(esk4_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_38]),c_0_28])])).

cnf(c_0_66,plain,
    ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v2_funct_1(X1)
    | k2_relset_1(X3,X2,X1) != X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

fof(c_0_67,plain,(
    ! [X32,X33,X34] :
      ( ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))
      | k2_relset_1(X32,X33,X34) = k2_relat_1(X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_68,negated_conjecture,
    ( v2_funct_1(esk5_0)
    | k1_relat_1(esk4_0) != k2_relat_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60]),c_0_38]),c_0_39]),c_0_61]),c_0_53])])).

cnf(c_0_69,negated_conjecture,
    ( k2_relat_1(esk5_0) = esk3_0
    | ~ r1_tarski(esk3_0,k2_relat_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(esk3_0,k2_relat_1(X1))
    | k2_relat_1(k5_relat_1(X1,esk4_0)) != k2_relat_1(esk4_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_60]),c_0_38]),c_0_61])])).

cnf(c_0_71,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v1_funct_2(X1,X2,X3)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_66]),c_0_44])])).

cnf(c_0_72,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_73,negated_conjecture,
    ( v2_funct_1(esk5_0)
    | k2_relat_1(esk5_0) != esk3_0 ),
    inference(rw,[status(thm)],[c_0_68,c_0_65])).

cnf(c_0_74,negated_conjecture,
    ( k2_relat_1(esk5_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_59]),c_0_39]),c_0_53])])).

cnf(c_0_75,negated_conjecture,
    ( v1_funct_2(esk5_0,esk3_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_76,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_funct_2(X1,X2,k2_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k2_relat_1(X1)))) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72])])).

cnf(c_0_77,negated_conjecture,
    ( v2_funct_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_74])])).

cnf(c_0_78,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_79,negated_conjecture,
    ( k1_relat_1(esk5_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_75]),c_0_39]),c_0_40])])).

cnf(c_0_80,plain,
    ( v5_relat_1(k2_funct_1(X1),X2)
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v1_funct_2(X1,X2,X3)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_66])).

cnf(c_0_81,negated_conjecture,
    ( v1_relat_1(k2_funct_1(esk5_0))
    | ~ v1_funct_2(esk5_0,X1,esk3_0)
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_74]),c_0_77]),c_0_39])])).

cnf(c_0_82,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_funct_2(X1,X2,k2_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k2_relat_1(X1)))) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_72])])).

cnf(c_0_83,negated_conjecture,
    ( r1_tarski(esk3_0,k2_relat_1(X1))
    | k2_relat_1(k5_relat_1(X1,esk5_0)) != esk3_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_79]),c_0_39]),c_0_53])]),c_0_74]),c_0_77])])).

cnf(c_0_84,negated_conjecture,
    ( v5_relat_1(k2_funct_1(esk5_0),esk3_0)
    | k2_relset_1(esk3_0,esk3_0,esk5_0) != esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_40]),c_0_75]),c_0_77]),c_0_39])])).

cnf(c_0_85,negated_conjecture,
    ( v1_relat_1(k2_funct_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_40]),c_0_75])])).

cnf(c_0_86,negated_conjecture,
    ( v1_funct_1(k2_funct_1(esk5_0))
    | ~ v1_funct_2(esk5_0,X1,esk3_0)
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_74]),c_0_77]),c_0_39])])).

cnf(c_0_87,negated_conjecture,
    ( k2_relat_1(X1) = esk3_0
    | k2_relat_1(k5_relat_1(X1,esk5_0)) != esk3_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),esk3_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_83])).

cnf(c_0_88,negated_conjecture,
    ( r1_tarski(k2_relat_1(k2_funct_1(esk5_0)),esk3_0)
    | k2_relset_1(esk3_0,esk3_0,esk5_0) != esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_84]),c_0_85])])).

cnf(c_0_89,negated_conjecture,
    ( v1_funct_1(k2_funct_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_40]),c_0_75])])).

fof(c_0_90,plain,(
    ! [X25] :
      ( ( k5_relat_1(X25,k2_funct_1(X25)) = k6_relat_1(k1_relat_1(X25))
        | ~ v2_funct_1(X25)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) )
      & ( k5_relat_1(k2_funct_1(X25),X25) = k6_relat_1(k2_relat_1(X25))
        | ~ v2_funct_1(X25)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_funct_1])])])).

fof(c_0_91,plain,(
    ! [X15] :
      ( k1_relat_1(k6_relat_1(X15)) = X15
      & k2_relat_1(k6_relat_1(X15)) = X15 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_92,plain,(
    ! [X65] :
      ( ( v1_funct_1(X65)
        | ~ v1_relat_1(X65)
        | ~ v1_funct_1(X65) )
      & ( v1_funct_2(X65,k1_relat_1(X65),k2_relat_1(X65))
        | ~ v1_relat_1(X65)
        | ~ v1_funct_1(X65) )
      & ( m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X65),k2_relat_1(X65))))
        | ~ v1_relat_1(X65)
        | ~ v1_funct_1(X65) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).

cnf(c_0_93,negated_conjecture,
    ( k2_relat_1(k2_funct_1(esk5_0)) = esk3_0
    | k2_relat_1(k5_relat_1(k2_funct_1(esk5_0),esk5_0)) != esk3_0
    | k2_relset_1(esk3_0,esk3_0,esk5_0) != esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_89]),c_0_85])])).

cnf(c_0_94,plain,
    ( k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(k2_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_95,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_91])).

cnf(c_0_96,plain,
    ( v5_relat_1(k1_partfun1(X1,X2,X3,X4,X5,X6),X4)
    | ~ v1_funct_1(X6)
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_37])).

cnf(c_0_97,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_92])).

cnf(c_0_98,negated_conjecture,
    ( k2_relat_1(k2_funct_1(esk5_0)) = esk3_0
    | k2_relset_1(esk3_0,esk3_0,esk5_0) != esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_74]),c_0_95]),c_0_77]),c_0_39]),c_0_53])])).

cnf(c_0_99,plain,
    ( v1_relat_1(k1_partfun1(X1,X2,X3,X4,X5,X6))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_37]),c_0_44])])).

cnf(c_0_100,plain,
    ( v5_relat_1(k5_relat_1(X1,X2),X3)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X4,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(spm,[status(thm)],[c_0_96,c_0_48])).

cnf(c_0_101,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(esk5_0)),esk3_0)))
    | k2_relset_1(esk3_0,esk3_0,esk5_0) != esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_89]),c_0_85])])).

cnf(c_0_102,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(spm,[status(thm)],[c_0_99,c_0_48])).

cnf(c_0_103,negated_conjecture,
    ( v5_relat_1(k5_relat_1(X1,k2_funct_1(esk5_0)),esk3_0)
    | k2_relset_1(esk3_0,esk3_0,esk5_0) != esk3_0
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_89])])).

cnf(c_0_104,negated_conjecture,
    ( v1_relat_1(k5_relat_1(X1,k2_funct_1(esk5_0)))
    | k2_relset_1(esk3_0,esk3_0,esk5_0) != esk3_0
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_101]),c_0_89])])).

fof(c_0_105,plain,(
    ! [X51] :
      ( v1_partfun1(k6_partfun1(X51),X51)
      & m1_subset_1(k6_partfun1(X51),k1_zfmisc_1(k2_zfmisc_1(X51,X51))) ) ),
    inference(variable_rename,[status(thm)],[dt_k6_partfun1])).

fof(c_0_106,plain,(
    ! [X58] : k6_partfun1(X58) = k6_relat_1(X58) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

cnf(c_0_107,negated_conjecture,
    ( v5_relat_1(k5_relat_1(X1,k2_funct_1(esk5_0)),esk3_0)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_72]),c_0_74]),c_0_40])])).

cnf(c_0_108,negated_conjecture,
    ( v1_relat_1(k5_relat_1(X1,k2_funct_1(esk5_0)))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_72]),c_0_74]),c_0_40])])).

cnf(c_0_109,plain,
    ( v5_relat_1(k5_relat_1(X1,X2),k2_relat_1(X2))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_100,c_0_97])).

cnf(c_0_110,plain,
    ( m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_105])).

cnf(c_0_111,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_106])).

cnf(c_0_112,plain,
    ( v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X6)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_113,negated_conjecture,
    ( v5_relat_1(k5_relat_1(X1,k2_funct_1(esk5_0)),esk3_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_107,c_0_97])).

cnf(c_0_114,negated_conjecture,
    ( v1_relat_1(k5_relat_1(X1,k2_funct_1(esk5_0)))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_108,c_0_97])).

cnf(c_0_115,negated_conjecture,
    ( v5_relat_1(k5_relat_1(esk5_0,X1),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_40]),c_0_39])])).

cnf(c_0_116,plain,
    ( k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_117,plain,
    ( m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(rw,[status(thm)],[c_0_110,c_0_111])).

cnf(c_0_118,plain,
    ( m1_subset_1(k5_relat_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X5,X4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X6))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_48])).

cnf(c_0_119,plain,
    ( v1_funct_1(k5_relat_1(X1,X2))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(spm,[status(thm)],[c_0_112,c_0_48])).

cnf(c_0_120,negated_conjecture,
    ( r1_tarski(k2_relat_1(k5_relat_1(X1,k2_funct_1(esk5_0))),esk3_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_113]),c_0_114])).

cnf(c_0_121,negated_conjecture,
    ( v5_relat_1(k6_relat_1(esk3_0),k2_relat_1(k2_funct_1(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_116]),c_0_79]),c_0_89]),c_0_85]),c_0_77]),c_0_39]),c_0_53])])).

cnf(c_0_122,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_117]),c_0_44])])).

fof(c_0_123,plain,(
    ! [X59,X60,X61] :
      ( ( r2_relset_1(X59,X60,k4_relset_1(X59,X59,X59,X60,k6_partfun1(X59),X61),X61)
        | ~ m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X59,X60))) )
      & ( r2_relset_1(X59,X60,k4_relset_1(X59,X60,X60,X60,X61,k6_partfun1(X60)),X61)
        | ~ m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X59,X60))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_funct_2])])])).

cnf(c_0_124,negated_conjecture,
    ( m1_subset_1(k5_relat_1(X1,esk5_0),k1_zfmisc_1(k2_zfmisc_1(X2,esk3_0)))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_40]),c_0_39])])).

cnf(c_0_125,negated_conjecture,
    ( v1_funct_1(k5_relat_1(X1,esk5_0))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_40]),c_0_39])])).

cnf(c_0_126,negated_conjecture,
    ( k2_relat_1(k5_relat_1(X1,k2_funct_1(esk5_0))) = esk3_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(esk3_0,k2_relat_1(k5_relat_1(X1,k2_funct_1(esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_62,c_0_120])).

cnf(c_0_127,negated_conjecture,
    ( r1_tarski(esk3_0,k2_relat_1(k2_funct_1(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_121]),c_0_95]),c_0_122])])).

cnf(c_0_128,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_92])).

cnf(c_0_129,plain,
    ( r2_relset_1(X1,X2,k4_relset_1(X1,X1,X1,X2,k6_partfun1(X1),X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_123])).

fof(c_0_130,plain,(
    ! [X35,X36,X37,X38,X39,X40] :
      ( ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))
      | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))
      | k4_relset_1(X35,X36,X37,X38,X39,X40) = k5_relat_1(X39,X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_relset_1])])).

cnf(c_0_131,negated_conjecture,
    ( m1_subset_1(k6_relat_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(X1,esk3_0)))
    | ~ m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_94]),c_0_74]),c_0_89]),c_0_77]),c_0_39]),c_0_53])])).

cnf(c_0_132,negated_conjecture,
    ( v1_funct_1(k5_relat_1(X1,esk5_0))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_125,c_0_97])).

cnf(c_0_133,plain,
    ( v1_funct_2(k2_funct_1(X1),X2,X3)
    | ~ v2_funct_1(X1)
    | k2_relset_1(X3,X2,X1) != X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_134,negated_conjecture,
    ( k2_relat_1(k2_funct_1(esk5_0)) = esk3_0
    | ~ v2_funct_1(k2_funct_1(esk5_0))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(esk5_0)))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_94]),c_0_95]),c_0_95]),c_0_127]),c_0_89]),c_0_85])])).

cnf(c_0_135,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_128]),c_0_97])).

cnf(c_0_136,plain,
    ( v2_funct_1(k2_funct_1(X1))
    | k2_relat_1(k2_funct_1(X1)) != k1_relat_1(X1)
    | ~ v2_funct_1(k6_relat_1(k2_relat_1(X1)))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_94])).

cnf(c_0_137,plain,
    ( r2_relset_1(X1,X2,k4_relset_1(X1,X1,X1,X2,k6_relat_1(X1),X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_129,c_0_111])).

cnf(c_0_138,plain,
    ( k4_relset_1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_130])).

cnf(c_0_139,negated_conjecture,
    ( m1_subset_1(k6_relat_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(esk5_0)),esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_97]),c_0_89]),c_0_85])])).

cnf(c_0_140,negated_conjecture,
    ( v1_funct_1(k6_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132,c_0_94]),c_0_74]),c_0_89]),c_0_85]),c_0_77]),c_0_39]),c_0_53])])).

cnf(c_0_141,plain,
    ( X1 = k1_relat_1(k2_funct_1(X2))
    | k2_relset_1(X1,X1,X2) != X1
    | ~ v1_funct_2(X2,X1,X1)
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_133]),c_0_66]),c_0_78])).

cnf(c_0_142,negated_conjecture,
    ( k2_relat_1(k2_funct_1(esk5_0)) = esk3_0
    | ~ v2_funct_1(k2_funct_1(esk5_0))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134,c_0_135]),c_0_89]),c_0_85])])).

cnf(c_0_143,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_128]),c_0_97])).

cnf(c_0_144,negated_conjecture,
    ( v2_funct_1(k2_funct_1(esk5_0))
    | k2_relat_1(k2_funct_1(esk5_0)) != esk3_0
    | ~ v2_funct_1(k6_relat_1(esk3_0))
    | ~ v1_relat_1(k2_funct_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136,c_0_74]),c_0_79]),c_0_77]),c_0_89]),c_0_39]),c_0_53])])).

cnf(c_0_145,plain,
    ( r2_relset_1(X1,X2,k5_relat_1(k6_relat_1(X1),X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137,c_0_138]),c_0_117])])).

cnf(c_0_146,negated_conjecture,
    ( m1_subset_1(k5_relat_1(k6_relat_1(esk3_0),esk5_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(esk5_0)),esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_139]),c_0_140])])).

cnf(c_0_147,negated_conjecture,
    ( k1_relat_1(k2_funct_1(esk5_0)) = esk3_0
    | k2_relset_1(esk3_0,esk3_0,esk5_0) != esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_141,c_0_40]),c_0_75]),c_0_77]),c_0_39])])).

cnf(c_0_148,negated_conjecture,
    ( k2_relat_1(k2_funct_1(esk5_0)) = esk3_0
    | ~ v2_funct_1(k2_funct_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_142,c_0_143]),c_0_89]),c_0_85])])).

cnf(c_0_149,negated_conjecture,
    ( v2_funct_1(k2_funct_1(esk5_0))
    | k2_relat_1(k2_funct_1(esk5_0)) != esk3_0
    | ~ v2_funct_1(k6_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_144,c_0_85])])).

cnf(c_0_150,plain,
    ( k5_relat_1(k6_relat_1(X1),X2) = X2
    | ~ m1_subset_1(k5_relat_1(k6_relat_1(X1),X2),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_145])).

cnf(c_0_151,negated_conjecture,
    ( m1_subset_1(k5_relat_1(k6_relat_1(esk3_0),esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))
    | k2_relset_1(esk3_0,esk3_0,esk5_0) != esk3_0 ),
    inference(spm,[status(thm)],[c_0_146,c_0_147])).

cnf(c_0_152,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(esk5_0)),esk3_0)))
    | ~ v2_funct_1(k2_funct_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_148]),c_0_89]),c_0_85])])).

cnf(c_0_153,negated_conjecture,
    ( v2_funct_1(k2_funct_1(esk5_0))
    | k2_relset_1(esk3_0,esk3_0,esk5_0) != esk3_0
    | ~ v2_funct_1(k6_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_149,c_0_98])).

cnf(c_0_154,negated_conjecture,
    ( k5_relat_1(k6_relat_1(esk3_0),esk5_0) = esk5_0
    | k2_relset_1(esk3_0,esk3_0,esk5_0) != esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_150,c_0_151]),c_0_40])])).

cnf(c_0_155,negated_conjecture,
    ( m1_subset_1(k5_relat_1(X1,k2_funct_1(esk5_0)),k1_zfmisc_1(k2_zfmisc_1(X2,esk3_0)))
    | ~ v2_funct_1(k2_funct_1(esk5_0))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_152]),c_0_89])])).

cnf(c_0_156,negated_conjecture,
    ( v2_funct_1(k2_funct_1(esk5_0))
    | ~ v2_funct_1(k6_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_153,c_0_72]),c_0_74]),c_0_40])])).

cnf(c_0_157,negated_conjecture,
    ( v2_funct_1(k6_relat_1(esk3_0))
    | k2_relset_1(esk3_0,esk3_0,esk5_0) != esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_154]),c_0_79]),c_0_95]),c_0_77]),c_0_39]),c_0_140]),c_0_53]),c_0_122])])).

fof(c_0_158,plain,(
    ! [X18,X19,X20] :
      ( ( ~ v2_funct_1(X18)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19)
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20)
        | ~ r1_tarski(k2_relat_1(X19),k1_relat_1(X18))
        | ~ r1_tarski(k2_relat_1(X20),k1_relat_1(X18))
        | k1_relat_1(X19) != k1_relat_1(X20)
        | k5_relat_1(X19,X18) != k5_relat_1(X20,X18)
        | X19 = X20
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) )
      & ( v1_relat_1(esk1_1(X18))
        | v2_funct_1(X18)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) )
      & ( v1_funct_1(esk1_1(X18))
        | v2_funct_1(X18)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) )
      & ( v1_relat_1(esk2_1(X18))
        | v2_funct_1(X18)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) )
      & ( v1_funct_1(esk2_1(X18))
        | v2_funct_1(X18)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) )
      & ( r1_tarski(k2_relat_1(esk1_1(X18)),k1_relat_1(X18))
        | v2_funct_1(X18)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) )
      & ( r1_tarski(k2_relat_1(esk2_1(X18)),k1_relat_1(X18))
        | v2_funct_1(X18)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) )
      & ( k1_relat_1(esk1_1(X18)) = k1_relat_1(esk2_1(X18))
        | v2_funct_1(X18)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) )
      & ( k5_relat_1(esk1_1(X18),X18) = k5_relat_1(esk2_1(X18),X18)
        | v2_funct_1(X18)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) )
      & ( esk1_1(X18) != esk2_1(X18)
        | v2_funct_1(X18)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t49_funct_1])])])])])).

cnf(c_0_159,negated_conjecture,
    ( m1_subset_1(k5_relat_1(X1,k2_funct_1(esk5_0)),k1_zfmisc_1(k2_zfmisc_1(X2,esk3_0)))
    | ~ v2_funct_1(k6_relat_1(esk3_0))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_155,c_0_156])).

cnf(c_0_160,negated_conjecture,
    ( v2_funct_1(k6_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_157,c_0_72]),c_0_74]),c_0_40])])).

cnf(c_0_161,negated_conjecture,
    ( v1_funct_1(k5_relat_1(X1,k2_funct_1(esk5_0)))
    | k2_relset_1(esk3_0,esk3_0,esk5_0) != esk3_0
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_101]),c_0_89])])).

cnf(c_0_162,plain,
    ( X2 = X3
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3)
    | ~ r1_tarski(k2_relat_1(X2),k1_relat_1(X1))
    | ~ r1_tarski(k2_relat_1(X3),k1_relat_1(X1))
    | k1_relat_1(X2) != k1_relat_1(X3)
    | k5_relat_1(X2,X1) != k5_relat_1(X3,X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_158])).

cnf(c_0_163,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_91])).

cnf(c_0_164,negated_conjecture,
    ( m1_subset_1(k5_relat_1(X1,k2_funct_1(esk5_0)),k1_zfmisc_1(k2_zfmisc_1(X2,esk3_0)))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_159,c_0_160])])).

cnf(c_0_165,negated_conjecture,
    ( v1_funct_1(k5_relat_1(X1,k2_funct_1(esk5_0)))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_161,c_0_72]),c_0_74]),c_0_40])])).

cnf(c_0_166,plain,
    ( k6_relat_1(k1_relat_1(X1)) = X1
    | k5_relat_1(k6_relat_1(k1_relat_1(X1)),X2) != k5_relat_1(X1,X2)
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(k6_relat_1(k1_relat_1(X1)))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X2)) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_162,c_0_95]),c_0_163]),c_0_122])])])).

cnf(c_0_167,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_168,negated_conjecture,
    ( m1_subset_1(k5_relat_1(X1,esk4_0),k1_zfmisc_1(k2_zfmisc_1(X2,esk3_0)))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_28]),c_0_38])])).

cnf(c_0_169,negated_conjecture,
    ( m1_subset_1(k5_relat_1(esk5_0,k2_funct_1(esk5_0)),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_164,c_0_40]),c_0_39])])).

cnf(c_0_170,negated_conjecture,
    ( v1_funct_1(k5_relat_1(esk5_0,k2_funct_1(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_165,c_0_40]),c_0_39])])).

cnf(c_0_171,negated_conjecture,
    ( k6_relat_1(esk3_0) = esk5_0
    | k5_relat_1(k6_relat_1(esk3_0),X1) != k5_relat_1(esk5_0,X1)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(esk3_0,k1_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_166,c_0_79]),c_0_140]),c_0_39]),c_0_53]),c_0_74])])).

cnf(c_0_172,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_167])).

cnf(c_0_173,negated_conjecture,
    ( X1 = X2
    | k5_relat_1(X1,esk4_0) != k5_relat_1(X2,esk4_0)
    | k1_relat_1(X1) != k1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X2),esk3_0)
    | ~ r1_tarski(k2_relat_1(X1),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_162,c_0_65]),c_0_60]),c_0_38]),c_0_61])])).

cnf(c_0_174,negated_conjecture,
    ( m1_subset_1(k5_relat_1(k5_relat_1(esk5_0,k2_funct_1(esk5_0)),esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_168,c_0_169]),c_0_170])])).

cnf(c_0_175,negated_conjecture,
    ( ~ r2_relset_1(esk3_0,esk3_0,esk5_0,k6_partfun1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_176,negated_conjecture,
    ( k6_relat_1(esk3_0) = esk5_0
    | k2_relset_1(esk3_0,esk3_0,esk5_0) != esk3_0
    | k5_relat_1(esk5_0,esk5_0) != esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_171,c_0_154]),c_0_77]),c_0_39]),c_0_53]),c_0_79]),c_0_172])])).

cnf(c_0_177,negated_conjecture,
    ( m1_subset_1(k5_relat_1(k5_relat_1(esk5_0,k2_funct_1(esk5_0)),esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_169]),c_0_170])])).

cnf(c_0_178,negated_conjecture,
    ( X1 = esk5_0
    | k5_relat_1(X1,esk4_0) != esk4_0
    | k1_relat_1(X1) != esk3_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_173,c_0_74]),c_0_59]),c_0_79]),c_0_39]),c_0_53]),c_0_172])])).

cnf(c_0_179,negated_conjecture,
    ( m1_subset_1(k5_relat_1(k6_relat_1(esk3_0),esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_174,c_0_116]),c_0_79]),c_0_77]),c_0_39]),c_0_53])])).

cnf(c_0_180,negated_conjecture,
    ( ~ r2_relset_1(esk3_0,esk3_0,esk5_0,k6_relat_1(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_175,c_0_111])).

cnf(c_0_181,negated_conjecture,
    ( k6_relat_1(esk3_0) = esk5_0
    | k5_relat_1(esk5_0,esk5_0) != esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_176,c_0_72]),c_0_74]),c_0_40])])).

cnf(c_0_182,plain,
    ( r2_relset_1(X3,X4,X1,X2)
    | X1 != X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_183,negated_conjecture,
    ( m1_subset_1(k5_relat_1(k6_relat_1(esk3_0),esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_177,c_0_116]),c_0_79]),c_0_77]),c_0_39]),c_0_53])])).

cnf(c_0_184,negated_conjecture,
    ( k6_relat_1(esk3_0) = esk5_0
    | k5_relat_1(k6_relat_1(esk3_0),esk4_0) != esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_178,c_0_95]),c_0_163]),c_0_122])])]),c_0_140]),c_0_172])])).

cnf(c_0_185,negated_conjecture,
    ( k5_relat_1(k6_relat_1(esk3_0),esk4_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_150,c_0_179]),c_0_28])])).

cnf(c_0_186,negated_conjecture,
    ( k5_relat_1(esk5_0,esk5_0) != esk5_0
    | ~ r2_relset_1(esk3_0,esk3_0,esk5_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_180,c_0_181])).

cnf(c_0_187,plain,
    ( r2_relset_1(X1,X2,X3,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(er,[status(thm)],[c_0_182])).

cnf(c_0_188,negated_conjecture,
    ( k5_relat_1(k6_relat_1(esk3_0),esk5_0) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_150,c_0_183]),c_0_40])])).

cnf(c_0_189,negated_conjecture,
    ( k6_relat_1(esk3_0) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_184,c_0_185])])).

cnf(c_0_190,negated_conjecture,
    ( k5_relat_1(esk5_0,esk5_0) != esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_186,c_0_187]),c_0_40])])).

cnf(c_0_191,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_188,c_0_189]),c_0_190]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:35:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 1.30/1.49  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 1.30/1.49  # and selection function PSelectComplexExceptUniqMaxHorn.
% 1.30/1.49  #
% 1.30/1.49  # Preprocessing time       : 0.031 s
% 1.30/1.49  # Presaturation interreduction done
% 1.30/1.49  
% 1.30/1.49  # Proof found!
% 1.30/1.49  # SZS status Theorem
% 1.30/1.49  # SZS output start CNFRefutation
% 1.30/1.49  fof(t76_funct_2, conjecture, ![X1, X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X1))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>((r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X3,X2),X2)&v2_funct_1(X2))=>r2_relset_1(X1,X1,X3,k6_partfun1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_funct_2)).
% 1.30/1.49  fof(redefinition_r2_relset_1, axiom, ![X1, X2, X3, X4]:((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_relset_1(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 1.30/1.49  fof(dt_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>(v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))&m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 1.30/1.49  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 1.30/1.49  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 1.30/1.49  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.30/1.49  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 1.30/1.49  fof(t67_funct_2, axiom, ![X1, X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>k1_relset_1(X1,X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_2)).
% 1.30/1.49  fof(redefinition_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>k1_partfun1(X1,X2,X3,X4,X5,X6)=k5_relat_1(X5,X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 1.30/1.49  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 1.30/1.49  fof(t48_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((v2_funct_1(k5_relat_1(X2,X1))&k2_relat_1(X2)=k1_relat_1(X1))=>(v2_funct_1(X2)&v2_funct_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_funct_1)).
% 1.30/1.49  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.30/1.49  fof(t51_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((k2_relat_1(k5_relat_1(X2,X1))=k2_relat_1(X1)&v2_funct_1(X1))=>r1_tarski(k1_relat_1(X1),k2_relat_1(X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_funct_1)).
% 1.30/1.49  fof(t31_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 1.30/1.49  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 1.30/1.49  fof(t61_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(k1_relat_1(X1))&k5_relat_1(k2_funct_1(X1),X1)=k6_relat_1(k2_relat_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 1.30/1.49  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 1.30/1.49  fof(t3_funct_2, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 1.30/1.49  fof(dt_k6_partfun1, axiom, ![X1]:(v1_partfun1(k6_partfun1(X1),X1)&m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 1.30/1.49  fof(redefinition_k6_partfun1, axiom, ![X1]:k6_partfun1(X1)=k6_relat_1(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 1.30/1.49  fof(t23_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(r2_relset_1(X1,X2,k4_relset_1(X1,X1,X1,X2,k6_partfun1(X1),X3),X3)&r2_relset_1(X1,X2,k4_relset_1(X1,X2,X2,X2,X3,k6_partfun1(X2)),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_funct_2)).
% 1.30/1.49  fof(redefinition_k4_relset_1, axiom, ![X1, X2, X3, X4, X5, X6]:((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>k4_relset_1(X1,X2,X3,X4,X5,X6)=k5_relat_1(X5,X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 1.30/1.49  fof(t49_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)<=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((((r1_tarski(k2_relat_1(X2),k1_relat_1(X1))&r1_tarski(k2_relat_1(X3),k1_relat_1(X1)))&k1_relat_1(X2)=k1_relat_1(X3))&k5_relat_1(X2,X1)=k5_relat_1(X3,X1))=>X2=X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_funct_1)).
% 1.30/1.49  fof(c_0_23, negated_conjecture, ~(![X1, X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X1))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>((r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X3,X2),X2)&v2_funct_1(X2))=>r2_relset_1(X1,X1,X3,k6_partfun1(X1)))))), inference(assume_negation,[status(cth)],[t76_funct_2])).
% 1.30/1.49  fof(c_0_24, plain, ![X41, X42, X43, X44]:((~r2_relset_1(X41,X42,X43,X44)|X43=X44|(~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))))&(X43!=X44|r2_relset_1(X41,X42,X43,X44)|(~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).
% 1.30/1.49  fof(c_0_25, negated_conjecture, (((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,esk3_0,esk3_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0))))&(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,esk3_0,esk3_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0))))&((r2_relset_1(esk3_0,esk3_0,k1_partfun1(esk3_0,esk3_0,esk3_0,esk3_0,esk5_0,esk4_0),esk4_0)&v2_funct_1(esk4_0))&~r2_relset_1(esk3_0,esk3_0,esk5_0,k6_partfun1(esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).
% 1.30/1.49  cnf(c_0_26, plain, (X3=X4|~r2_relset_1(X1,X2,X3,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.30/1.49  cnf(c_0_27, negated_conjecture, (r2_relset_1(esk3_0,esk3_0,k1_partfun1(esk3_0,esk3_0,esk3_0,esk3_0,esk5_0,esk4_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 1.30/1.49  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 1.30/1.49  fof(c_0_29, plain, ![X45, X46, X47, X48, X49, X50]:((v1_funct_1(k1_partfun1(X45,X46,X47,X48,X49,X50))|(~v1_funct_1(X49)|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))|~v1_funct_1(X50)|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))))&(m1_subset_1(k1_partfun1(X45,X46,X47,X48,X49,X50),k1_zfmisc_1(k2_zfmisc_1(X45,X48)))|(~v1_funct_1(X49)|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))|~v1_funct_1(X50)|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).
% 1.30/1.49  fof(c_0_30, plain, ![X26, X27, X28]:((v4_relat_1(X28,X26)|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))))&(v5_relat_1(X28,X27)|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 1.30/1.49  fof(c_0_31, plain, ![X9, X10]:(~v1_relat_1(X9)|(~m1_subset_1(X10,k1_zfmisc_1(X9))|v1_relat_1(X10))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 1.30/1.49  fof(c_0_32, plain, ![X13, X14]:v1_relat_1(k2_zfmisc_1(X13,X14)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 1.30/1.49  fof(c_0_33, plain, ![X29, X30, X31]:(~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))|k1_relset_1(X29,X30,X31)=k1_relat_1(X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 1.30/1.49  fof(c_0_34, plain, ![X66, X67]:(~v1_funct_1(X67)|~v1_funct_2(X67,X66,X66)|~m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(X66,X66)))|k1_relset_1(X66,X66,X67)=X66), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_funct_2])])).
% 1.30/1.49  fof(c_0_35, plain, ![X52, X53, X54, X55, X56, X57]:(~v1_funct_1(X56)|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))|~v1_funct_1(X57)|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X54,X55)))|k1_partfun1(X52,X53,X54,X55,X56,X57)=k5_relat_1(X56,X57)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).
% 1.30/1.49  cnf(c_0_36, negated_conjecture, (k1_partfun1(esk3_0,esk3_0,esk3_0,esk3_0,esk5_0,esk4_0)=esk4_0|~m1_subset_1(k1_partfun1(esk3_0,esk3_0,esk3_0,esk3_0,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])])).
% 1.30/1.49  cnf(c_0_37, plain, (m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X6)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 1.30/1.49  cnf(c_0_38, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 1.30/1.49  cnf(c_0_39, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 1.30/1.49  cnf(c_0_40, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 1.30/1.49  fof(c_0_41, plain, ![X11, X12]:((~v5_relat_1(X12,X11)|r1_tarski(k2_relat_1(X12),X11)|~v1_relat_1(X12))&(~r1_tarski(k2_relat_1(X12),X11)|v5_relat_1(X12,X11)|~v1_relat_1(X12))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 1.30/1.49  cnf(c_0_42, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 1.30/1.49  cnf(c_0_43, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 1.30/1.49  cnf(c_0_44, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 1.30/1.49  cnf(c_0_45, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 1.30/1.49  cnf(c_0_46, plain, (k1_relset_1(X2,X2,X1)=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 1.30/1.49  fof(c_0_47, plain, ![X16, X17]:((v2_funct_1(X17)|(~v2_funct_1(k5_relat_1(X17,X16))|k2_relat_1(X17)!=k1_relat_1(X16))|(~v1_relat_1(X17)|~v1_funct_1(X17))|(~v1_relat_1(X16)|~v1_funct_1(X16)))&(v2_funct_1(X16)|(~v2_funct_1(k5_relat_1(X17,X16))|k2_relat_1(X17)!=k1_relat_1(X16))|(~v1_relat_1(X17)|~v1_funct_1(X17))|(~v1_relat_1(X16)|~v1_funct_1(X16)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_funct_1])])])])).
% 1.30/1.49  cnf(c_0_48, plain, (k1_partfun1(X2,X3,X5,X6,X1,X4)=k5_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 1.30/1.49  cnf(c_0_49, negated_conjecture, (k1_partfun1(esk3_0,esk3_0,esk3_0,esk3_0,esk5_0,esk4_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38]), c_0_39]), c_0_28]), c_0_40])])).
% 1.30/1.49  fof(c_0_50, plain, ![X7, X8]:(((r1_tarski(X7,X8)|X7!=X8)&(r1_tarski(X8,X7)|X7!=X8))&(~r1_tarski(X7,X8)|~r1_tarski(X8,X7)|X7=X8)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 1.30/1.49  cnf(c_0_51, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 1.30/1.49  cnf(c_0_52, negated_conjecture, (v5_relat_1(esk5_0,esk3_0)), inference(spm,[status(thm)],[c_0_42, c_0_40])).
% 1.30/1.49  cnf(c_0_53, negated_conjecture, (v1_relat_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_40]), c_0_44])])).
% 1.30/1.49  fof(c_0_54, plain, ![X23, X24]:(~v1_relat_1(X23)|~v1_funct_1(X23)|(~v1_relat_1(X24)|~v1_funct_1(X24)|(k2_relat_1(k5_relat_1(X24,X23))!=k2_relat_1(X23)|~v2_funct_1(X23)|r1_tarski(k1_relat_1(X23),k2_relat_1(X24))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t51_funct_1])])])).
% 1.30/1.49  cnf(c_0_55, plain, (X1=k1_relat_1(X2)|~v1_funct_2(X2,X1,X1)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 1.30/1.49  cnf(c_0_56, negated_conjecture, (v1_funct_2(esk4_0,esk3_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 1.30/1.49  fof(c_0_57, plain, ![X62, X63, X64]:(((v1_funct_1(k2_funct_1(X64))|(~v2_funct_1(X64)|k2_relset_1(X62,X63,X64)!=X63)|(~v1_funct_1(X64)|~v1_funct_2(X64,X62,X63)|~m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X62,X63)))))&(v1_funct_2(k2_funct_1(X64),X63,X62)|(~v2_funct_1(X64)|k2_relset_1(X62,X63,X64)!=X63)|(~v1_funct_1(X64)|~v1_funct_2(X64,X62,X63)|~m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X62,X63))))))&(m1_subset_1(k2_funct_1(X64),k1_zfmisc_1(k2_zfmisc_1(X63,X62)))|(~v2_funct_1(X64)|k2_relset_1(X62,X63,X64)!=X63)|(~v1_funct_1(X64)|~v1_funct_2(X64,X62,X63)|~m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X62,X63)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_funct_2])])])).
% 1.30/1.49  cnf(c_0_58, plain, (v2_funct_1(X1)|~v2_funct_1(k5_relat_1(X1,X2))|k2_relat_1(X1)!=k1_relat_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 1.30/1.49  cnf(c_0_59, negated_conjecture, (k5_relat_1(esk5_0,esk4_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_38]), c_0_39]), c_0_28]), c_0_40])])).
% 1.30/1.49  cnf(c_0_60, negated_conjecture, (v2_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 1.30/1.49  cnf(c_0_61, negated_conjecture, (v1_relat_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_28]), c_0_44])])).
% 1.30/1.49  cnf(c_0_62, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 1.30/1.49  cnf(c_0_63, negated_conjecture, (r1_tarski(k2_relat_1(esk5_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53])])).
% 1.30/1.49  cnf(c_0_64, plain, (r1_tarski(k1_relat_1(X1),k2_relat_1(X2))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|k2_relat_1(k5_relat_1(X2,X1))!=k2_relat_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 1.30/1.49  cnf(c_0_65, negated_conjecture, (k1_relat_1(esk4_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_38]), c_0_28])])).
% 1.30/1.49  cnf(c_0_66, plain, (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v2_funct_1(X1)|k2_relset_1(X3,X2,X1)!=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 1.30/1.49  fof(c_0_67, plain, ![X32, X33, X34]:(~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))|k2_relset_1(X32,X33,X34)=k2_relat_1(X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 1.30/1.49  cnf(c_0_68, negated_conjecture, (v2_funct_1(esk5_0)|k1_relat_1(esk4_0)!=k2_relat_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_60]), c_0_38]), c_0_39]), c_0_61]), c_0_53])])).
% 1.30/1.49  cnf(c_0_69, negated_conjecture, (k2_relat_1(esk5_0)=esk3_0|~r1_tarski(esk3_0,k2_relat_1(esk5_0))), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 1.30/1.49  cnf(c_0_70, negated_conjecture, (r1_tarski(esk3_0,k2_relat_1(X1))|k2_relat_1(k5_relat_1(X1,esk4_0))!=k2_relat_1(esk4_0)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_60]), c_0_38]), c_0_61])])).
% 1.30/1.49  cnf(c_0_71, plain, (v1_relat_1(k2_funct_1(X1))|k2_relset_1(X2,X3,X1)!=X3|~v1_funct_2(X1,X2,X3)|~v2_funct_1(X1)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_66]), c_0_44])])).
% 1.30/1.49  cnf(c_0_72, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_67])).
% 1.30/1.49  cnf(c_0_73, negated_conjecture, (v2_funct_1(esk5_0)|k2_relat_1(esk5_0)!=esk3_0), inference(rw,[status(thm)],[c_0_68, c_0_65])).
% 1.30/1.49  cnf(c_0_74, negated_conjecture, (k2_relat_1(esk5_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_59]), c_0_39]), c_0_53])])).
% 1.30/1.49  cnf(c_0_75, negated_conjecture, (v1_funct_2(esk5_0,esk3_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 1.30/1.49  cnf(c_0_76, plain, (v1_relat_1(k2_funct_1(X1))|~v1_funct_2(X1,X2,k2_relat_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k2_relat_1(X1))))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72])])).
% 1.30/1.49  cnf(c_0_77, negated_conjecture, (v2_funct_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_73, c_0_74])])).
% 1.30/1.49  cnf(c_0_78, plain, (v1_funct_1(k2_funct_1(X1))|~v2_funct_1(X1)|k2_relset_1(X2,X3,X1)!=X3|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 1.30/1.49  cnf(c_0_79, negated_conjecture, (k1_relat_1(esk5_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_75]), c_0_39]), c_0_40])])).
% 1.30/1.49  cnf(c_0_80, plain, (v5_relat_1(k2_funct_1(X1),X2)|k2_relset_1(X2,X3,X1)!=X3|~v1_funct_2(X1,X2,X3)|~v2_funct_1(X1)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(spm,[status(thm)],[c_0_42, c_0_66])).
% 1.30/1.49  cnf(c_0_81, negated_conjecture, (v1_relat_1(k2_funct_1(esk5_0))|~v1_funct_2(esk5_0,X1,esk3_0)|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_74]), c_0_77]), c_0_39])])).
% 1.30/1.49  cnf(c_0_82, plain, (v1_funct_1(k2_funct_1(X1))|~v1_funct_2(X1,X2,k2_relat_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k2_relat_1(X1))))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_72])])).
% 1.30/1.49  cnf(c_0_83, negated_conjecture, (r1_tarski(esk3_0,k2_relat_1(X1))|k2_relat_1(k5_relat_1(X1,esk5_0))!=esk3_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_79]), c_0_39]), c_0_53])]), c_0_74]), c_0_77])])).
% 1.30/1.49  cnf(c_0_84, negated_conjecture, (v5_relat_1(k2_funct_1(esk5_0),esk3_0)|k2_relset_1(esk3_0,esk3_0,esk5_0)!=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_40]), c_0_75]), c_0_77]), c_0_39])])).
% 1.30/1.49  cnf(c_0_85, negated_conjecture, (v1_relat_1(k2_funct_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_40]), c_0_75])])).
% 1.30/1.49  cnf(c_0_86, negated_conjecture, (v1_funct_1(k2_funct_1(esk5_0))|~v1_funct_2(esk5_0,X1,esk3_0)|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_74]), c_0_77]), c_0_39])])).
% 1.30/1.49  cnf(c_0_87, negated_conjecture, (k2_relat_1(X1)=esk3_0|k2_relat_1(k5_relat_1(X1,esk5_0))!=esk3_0|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),esk3_0)), inference(spm,[status(thm)],[c_0_62, c_0_83])).
% 1.30/1.49  cnf(c_0_88, negated_conjecture, (r1_tarski(k2_relat_1(k2_funct_1(esk5_0)),esk3_0)|k2_relset_1(esk3_0,esk3_0,esk5_0)!=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_84]), c_0_85])])).
% 1.30/1.49  cnf(c_0_89, negated_conjecture, (v1_funct_1(k2_funct_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_40]), c_0_75])])).
% 1.30/1.49  fof(c_0_90, plain, ![X25]:((k5_relat_1(X25,k2_funct_1(X25))=k6_relat_1(k1_relat_1(X25))|~v2_funct_1(X25)|(~v1_relat_1(X25)|~v1_funct_1(X25)))&(k5_relat_1(k2_funct_1(X25),X25)=k6_relat_1(k2_relat_1(X25))|~v2_funct_1(X25)|(~v1_relat_1(X25)|~v1_funct_1(X25)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_funct_1])])])).
% 1.30/1.49  fof(c_0_91, plain, ![X15]:(k1_relat_1(k6_relat_1(X15))=X15&k2_relat_1(k6_relat_1(X15))=X15), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 1.30/1.49  fof(c_0_92, plain, ![X65]:(((v1_funct_1(X65)|(~v1_relat_1(X65)|~v1_funct_1(X65)))&(v1_funct_2(X65,k1_relat_1(X65),k2_relat_1(X65))|(~v1_relat_1(X65)|~v1_funct_1(X65))))&(m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X65),k2_relat_1(X65))))|(~v1_relat_1(X65)|~v1_funct_1(X65)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).
% 1.30/1.49  cnf(c_0_93, negated_conjecture, (k2_relat_1(k2_funct_1(esk5_0))=esk3_0|k2_relat_1(k5_relat_1(k2_funct_1(esk5_0),esk5_0))!=esk3_0|k2_relset_1(esk3_0,esk3_0,esk5_0)!=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_89]), c_0_85])])).
% 1.30/1.49  cnf(c_0_94, plain, (k5_relat_1(k2_funct_1(X1),X1)=k6_relat_1(k2_relat_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_90])).
% 1.30/1.49  cnf(c_0_95, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_91])).
% 1.30/1.49  cnf(c_0_96, plain, (v5_relat_1(k1_partfun1(X1,X2,X3,X4,X5,X6),X4)|~v1_funct_1(X6)|~v1_funct_1(X5)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_42, c_0_37])).
% 1.30/1.49  cnf(c_0_97, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_92])).
% 1.30/1.49  cnf(c_0_98, negated_conjecture, (k2_relat_1(k2_funct_1(esk5_0))=esk3_0|k2_relset_1(esk3_0,esk3_0,esk5_0)!=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_74]), c_0_95]), c_0_77]), c_0_39]), c_0_53])])).
% 1.30/1.49  cnf(c_0_99, plain, (v1_relat_1(k1_partfun1(X1,X2,X3,X4,X5,X6))|~v1_funct_1(X6)|~v1_funct_1(X5)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_37]), c_0_44])])).
% 1.30/1.49  cnf(c_0_100, plain, (v5_relat_1(k5_relat_1(X1,X2),X3)|~v1_funct_1(X2)|~v1_funct_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X4,X3)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(spm,[status(thm)],[c_0_96, c_0_48])).
% 1.30/1.49  cnf(c_0_101, negated_conjecture, (m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(esk5_0)),esk3_0)))|k2_relset_1(esk3_0,esk3_0,esk5_0)!=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_98]), c_0_89]), c_0_85])])).
% 1.30/1.49  cnf(c_0_102, plain, (v1_relat_1(k5_relat_1(X1,X2))|~v1_funct_1(X2)|~v1_funct_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(spm,[status(thm)],[c_0_99, c_0_48])).
% 1.30/1.49  cnf(c_0_103, negated_conjecture, (v5_relat_1(k5_relat_1(X1,k2_funct_1(esk5_0)),esk3_0)|k2_relset_1(esk3_0,esk3_0,esk5_0)!=esk3_0|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_101]), c_0_89])])).
% 1.30/1.49  cnf(c_0_104, negated_conjecture, (v1_relat_1(k5_relat_1(X1,k2_funct_1(esk5_0)))|k2_relset_1(esk3_0,esk3_0,esk5_0)!=esk3_0|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_101]), c_0_89])])).
% 1.30/1.49  fof(c_0_105, plain, ![X51]:(v1_partfun1(k6_partfun1(X51),X51)&m1_subset_1(k6_partfun1(X51),k1_zfmisc_1(k2_zfmisc_1(X51,X51)))), inference(variable_rename,[status(thm)],[dt_k6_partfun1])).
% 1.30/1.49  fof(c_0_106, plain, ![X58]:k6_partfun1(X58)=k6_relat_1(X58), inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).
% 1.30/1.49  cnf(c_0_107, negated_conjecture, (v5_relat_1(k5_relat_1(X1,k2_funct_1(esk5_0)),esk3_0)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_72]), c_0_74]), c_0_40])])).
% 1.30/1.49  cnf(c_0_108, negated_conjecture, (v1_relat_1(k5_relat_1(X1,k2_funct_1(esk5_0)))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_72]), c_0_74]), c_0_40])])).
% 1.30/1.49  cnf(c_0_109, plain, (v5_relat_1(k5_relat_1(X1,X2),k2_relat_1(X2))|~v1_funct_1(X2)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_100, c_0_97])).
% 1.30/1.49  cnf(c_0_110, plain, (m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_105])).
% 1.30/1.49  cnf(c_0_111, plain, (k6_partfun1(X1)=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_106])).
% 1.30/1.49  cnf(c_0_112, plain, (v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X6)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 1.30/1.49  cnf(c_0_113, negated_conjecture, (v5_relat_1(k5_relat_1(X1,k2_funct_1(esk5_0)),esk3_0)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_107, c_0_97])).
% 1.30/1.49  cnf(c_0_114, negated_conjecture, (v1_relat_1(k5_relat_1(X1,k2_funct_1(esk5_0)))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_108, c_0_97])).
% 1.30/1.49  cnf(c_0_115, negated_conjecture, (v5_relat_1(k5_relat_1(esk5_0,X1),k2_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_40]), c_0_39])])).
% 1.30/1.49  cnf(c_0_116, plain, (k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(k1_relat_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_90])).
% 1.30/1.49  cnf(c_0_117, plain, (m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(rw,[status(thm)],[c_0_110, c_0_111])).
% 1.30/1.49  cnf(c_0_118, plain, (m1_subset_1(k5_relat_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_1(X2)|~v1_funct_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X5,X4)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X6)))), inference(spm,[status(thm)],[c_0_37, c_0_48])).
% 1.30/1.49  cnf(c_0_119, plain, (v1_funct_1(k5_relat_1(X1,X2))|~v1_funct_1(X2)|~v1_funct_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(spm,[status(thm)],[c_0_112, c_0_48])).
% 1.30/1.49  cnf(c_0_120, negated_conjecture, (r1_tarski(k2_relat_1(k5_relat_1(X1,k2_funct_1(esk5_0))),esk3_0)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_113]), c_0_114])).
% 1.30/1.49  cnf(c_0_121, negated_conjecture, (v5_relat_1(k6_relat_1(esk3_0),k2_relat_1(k2_funct_1(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_116]), c_0_79]), c_0_89]), c_0_85]), c_0_77]), c_0_39]), c_0_53])])).
% 1.30/1.49  cnf(c_0_122, plain, (v1_relat_1(k6_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_117]), c_0_44])])).
% 1.30/1.49  fof(c_0_123, plain, ![X59, X60, X61]:((r2_relset_1(X59,X60,k4_relset_1(X59,X59,X59,X60,k6_partfun1(X59),X61),X61)|~m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X59,X60))))&(r2_relset_1(X59,X60,k4_relset_1(X59,X60,X60,X60,X61,k6_partfun1(X60)),X61)|~m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X59,X60))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_funct_2])])])).
% 1.30/1.49  cnf(c_0_124, negated_conjecture, (m1_subset_1(k5_relat_1(X1,esk5_0),k1_zfmisc_1(k2_zfmisc_1(X2,esk3_0)))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118, c_0_40]), c_0_39])])).
% 1.30/1.49  cnf(c_0_125, negated_conjecture, (v1_funct_1(k5_relat_1(X1,esk5_0))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_40]), c_0_39])])).
% 1.30/1.49  cnf(c_0_126, negated_conjecture, (k2_relat_1(k5_relat_1(X1,k2_funct_1(esk5_0)))=esk3_0|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(esk3_0,k2_relat_1(k5_relat_1(X1,k2_funct_1(esk5_0))))), inference(spm,[status(thm)],[c_0_62, c_0_120])).
% 1.30/1.49  cnf(c_0_127, negated_conjecture, (r1_tarski(esk3_0,k2_relat_1(k2_funct_1(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_121]), c_0_95]), c_0_122])])).
% 1.30/1.49  cnf(c_0_128, plain, (v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_92])).
% 1.30/1.49  cnf(c_0_129, plain, (r2_relset_1(X1,X2,k4_relset_1(X1,X1,X1,X2,k6_partfun1(X1),X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_123])).
% 1.30/1.49  fof(c_0_130, plain, ![X35, X36, X37, X38, X39, X40]:(~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))|k4_relset_1(X35,X36,X37,X38,X39,X40)=k5_relat_1(X39,X40)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_relset_1])])).
% 1.30/1.49  cnf(c_0_131, negated_conjecture, (m1_subset_1(k6_relat_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(X1,esk3_0)))|~m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124, c_0_94]), c_0_74]), c_0_89]), c_0_77]), c_0_39]), c_0_53])])).
% 1.30/1.49  cnf(c_0_132, negated_conjecture, (v1_funct_1(k5_relat_1(X1,esk5_0))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_125, c_0_97])).
% 1.30/1.49  cnf(c_0_133, plain, (v1_funct_2(k2_funct_1(X1),X2,X3)|~v2_funct_1(X1)|k2_relset_1(X3,X2,X1)!=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 1.30/1.49  cnf(c_0_134, negated_conjecture, (k2_relat_1(k2_funct_1(esk5_0))=esk3_0|~v2_funct_1(k2_funct_1(esk5_0))|~v1_funct_1(k2_funct_1(k2_funct_1(esk5_0)))|~v1_relat_1(k2_funct_1(k2_funct_1(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126, c_0_94]), c_0_95]), c_0_95]), c_0_127]), c_0_89]), c_0_85])])).
% 1.30/1.49  cnf(c_0_135, plain, (v1_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_128]), c_0_97])).
% 1.30/1.49  cnf(c_0_136, plain, (v2_funct_1(k2_funct_1(X1))|k2_relat_1(k2_funct_1(X1))!=k1_relat_1(X1)|~v2_funct_1(k6_relat_1(k2_relat_1(X1)))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(X1))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_58, c_0_94])).
% 1.30/1.49  cnf(c_0_137, plain, (r2_relset_1(X1,X2,k4_relset_1(X1,X1,X1,X2,k6_relat_1(X1),X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(rw,[status(thm)],[c_0_129, c_0_111])).
% 1.30/1.49  cnf(c_0_138, plain, (k4_relset_1(X2,X3,X5,X6,X1,X4)=k5_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_130])).
% 1.30/1.49  cnf(c_0_139, negated_conjecture, (m1_subset_1(k6_relat_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(esk5_0)),esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131, c_0_97]), c_0_89]), c_0_85])])).
% 1.30/1.49  cnf(c_0_140, negated_conjecture, (v1_funct_1(k6_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132, c_0_94]), c_0_74]), c_0_89]), c_0_85]), c_0_77]), c_0_39]), c_0_53])])).
% 1.30/1.49  cnf(c_0_141, plain, (X1=k1_relat_1(k2_funct_1(X2))|k2_relset_1(X1,X1,X2)!=X1|~v1_funct_2(X2,X1,X1)|~v2_funct_1(X2)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_133]), c_0_66]), c_0_78])).
% 1.30/1.49  cnf(c_0_142, negated_conjecture, (k2_relat_1(k2_funct_1(esk5_0))=esk3_0|~v2_funct_1(k2_funct_1(esk5_0))|~v1_funct_1(k2_funct_1(k2_funct_1(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134, c_0_135]), c_0_89]), c_0_85])])).
% 1.30/1.49  cnf(c_0_143, plain, (v1_funct_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_128]), c_0_97])).
% 1.30/1.49  cnf(c_0_144, negated_conjecture, (v2_funct_1(k2_funct_1(esk5_0))|k2_relat_1(k2_funct_1(esk5_0))!=esk3_0|~v2_funct_1(k6_relat_1(esk3_0))|~v1_relat_1(k2_funct_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136, c_0_74]), c_0_79]), c_0_77]), c_0_89]), c_0_39]), c_0_53])])).
% 1.30/1.49  cnf(c_0_145, plain, (r2_relset_1(X1,X2,k5_relat_1(k6_relat_1(X1),X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137, c_0_138]), c_0_117])])).
% 1.30/1.49  cnf(c_0_146, negated_conjecture, (m1_subset_1(k5_relat_1(k6_relat_1(esk3_0),esk5_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(esk5_0)),esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124, c_0_139]), c_0_140])])).
% 1.30/1.49  cnf(c_0_147, negated_conjecture, (k1_relat_1(k2_funct_1(esk5_0))=esk3_0|k2_relset_1(esk3_0,esk3_0,esk5_0)!=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_141, c_0_40]), c_0_75]), c_0_77]), c_0_39])])).
% 1.30/1.49  cnf(c_0_148, negated_conjecture, (k2_relat_1(k2_funct_1(esk5_0))=esk3_0|~v2_funct_1(k2_funct_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_142, c_0_143]), c_0_89]), c_0_85])])).
% 1.30/1.49  cnf(c_0_149, negated_conjecture, (v2_funct_1(k2_funct_1(esk5_0))|k2_relat_1(k2_funct_1(esk5_0))!=esk3_0|~v2_funct_1(k6_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_144, c_0_85])])).
% 1.30/1.49  cnf(c_0_150, plain, (k5_relat_1(k6_relat_1(X1),X2)=X2|~m1_subset_1(k5_relat_1(k6_relat_1(X1),X2),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(spm,[status(thm)],[c_0_26, c_0_145])).
% 1.30/1.49  cnf(c_0_151, negated_conjecture, (m1_subset_1(k5_relat_1(k6_relat_1(esk3_0),esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))|k2_relset_1(esk3_0,esk3_0,esk5_0)!=esk3_0), inference(spm,[status(thm)],[c_0_146, c_0_147])).
% 1.30/1.49  cnf(c_0_152, negated_conjecture, (m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(esk5_0)),esk3_0)))|~v2_funct_1(k2_funct_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_148]), c_0_89]), c_0_85])])).
% 1.30/1.49  cnf(c_0_153, negated_conjecture, (v2_funct_1(k2_funct_1(esk5_0))|k2_relset_1(esk3_0,esk3_0,esk5_0)!=esk3_0|~v2_funct_1(k6_relat_1(esk3_0))), inference(spm,[status(thm)],[c_0_149, c_0_98])).
% 1.30/1.49  cnf(c_0_154, negated_conjecture, (k5_relat_1(k6_relat_1(esk3_0),esk5_0)=esk5_0|k2_relset_1(esk3_0,esk3_0,esk5_0)!=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_150, c_0_151]), c_0_40])])).
% 1.30/1.49  cnf(c_0_155, negated_conjecture, (m1_subset_1(k5_relat_1(X1,k2_funct_1(esk5_0)),k1_zfmisc_1(k2_zfmisc_1(X2,esk3_0)))|~v2_funct_1(k2_funct_1(esk5_0))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118, c_0_152]), c_0_89])])).
% 1.30/1.49  cnf(c_0_156, negated_conjecture, (v2_funct_1(k2_funct_1(esk5_0))|~v2_funct_1(k6_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_153, c_0_72]), c_0_74]), c_0_40])])).
% 1.30/1.49  cnf(c_0_157, negated_conjecture, (v2_funct_1(k6_relat_1(esk3_0))|k2_relset_1(esk3_0,esk3_0,esk5_0)!=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_154]), c_0_79]), c_0_95]), c_0_77]), c_0_39]), c_0_140]), c_0_53]), c_0_122])])).
% 1.30/1.49  fof(c_0_158, plain, ![X18, X19, X20]:((~v2_funct_1(X18)|(~v1_relat_1(X19)|~v1_funct_1(X19)|(~v1_relat_1(X20)|~v1_funct_1(X20)|(~r1_tarski(k2_relat_1(X19),k1_relat_1(X18))|~r1_tarski(k2_relat_1(X20),k1_relat_1(X18))|k1_relat_1(X19)!=k1_relat_1(X20)|k5_relat_1(X19,X18)!=k5_relat_1(X20,X18)|X19=X20)))|(~v1_relat_1(X18)|~v1_funct_1(X18)))&(((v1_relat_1(esk1_1(X18))|v2_funct_1(X18)|(~v1_relat_1(X18)|~v1_funct_1(X18)))&(v1_funct_1(esk1_1(X18))|v2_funct_1(X18)|(~v1_relat_1(X18)|~v1_funct_1(X18))))&(((v1_relat_1(esk2_1(X18))|v2_funct_1(X18)|(~v1_relat_1(X18)|~v1_funct_1(X18)))&(v1_funct_1(esk2_1(X18))|v2_funct_1(X18)|(~v1_relat_1(X18)|~v1_funct_1(X18))))&(((((r1_tarski(k2_relat_1(esk1_1(X18)),k1_relat_1(X18))|v2_funct_1(X18)|(~v1_relat_1(X18)|~v1_funct_1(X18)))&(r1_tarski(k2_relat_1(esk2_1(X18)),k1_relat_1(X18))|v2_funct_1(X18)|(~v1_relat_1(X18)|~v1_funct_1(X18))))&(k1_relat_1(esk1_1(X18))=k1_relat_1(esk2_1(X18))|v2_funct_1(X18)|(~v1_relat_1(X18)|~v1_funct_1(X18))))&(k5_relat_1(esk1_1(X18),X18)=k5_relat_1(esk2_1(X18),X18)|v2_funct_1(X18)|(~v1_relat_1(X18)|~v1_funct_1(X18))))&(esk1_1(X18)!=esk2_1(X18)|v2_funct_1(X18)|(~v1_relat_1(X18)|~v1_funct_1(X18))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t49_funct_1])])])])])).
% 1.30/1.49  cnf(c_0_159, negated_conjecture, (m1_subset_1(k5_relat_1(X1,k2_funct_1(esk5_0)),k1_zfmisc_1(k2_zfmisc_1(X2,esk3_0)))|~v2_funct_1(k6_relat_1(esk3_0))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(spm,[status(thm)],[c_0_155, c_0_156])).
% 1.30/1.49  cnf(c_0_160, negated_conjecture, (v2_funct_1(k6_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_157, c_0_72]), c_0_74]), c_0_40])])).
% 1.30/1.49  cnf(c_0_161, negated_conjecture, (v1_funct_1(k5_relat_1(X1,k2_funct_1(esk5_0)))|k2_relset_1(esk3_0,esk3_0,esk5_0)!=esk3_0|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_101]), c_0_89])])).
% 1.30/1.49  cnf(c_0_162, plain, (X2=X3|~v2_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X3)|~v1_funct_1(X3)|~r1_tarski(k2_relat_1(X2),k1_relat_1(X1))|~r1_tarski(k2_relat_1(X3),k1_relat_1(X1))|k1_relat_1(X2)!=k1_relat_1(X3)|k5_relat_1(X2,X1)!=k5_relat_1(X3,X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_158])).
% 1.30/1.49  cnf(c_0_163, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_91])).
% 1.30/1.49  cnf(c_0_164, negated_conjecture, (m1_subset_1(k5_relat_1(X1,k2_funct_1(esk5_0)),k1_zfmisc_1(k2_zfmisc_1(X2,esk3_0)))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_159, c_0_160])])).
% 1.30/1.49  cnf(c_0_165, negated_conjecture, (v1_funct_1(k5_relat_1(X1,k2_funct_1(esk5_0)))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_161, c_0_72]), c_0_74]), c_0_40])])).
% 1.30/1.49  cnf(c_0_166, plain, (k6_relat_1(k1_relat_1(X1))=X1|k5_relat_1(k6_relat_1(k1_relat_1(X1)),X2)!=k5_relat_1(X1,X2)|~v2_funct_1(X2)|~v1_funct_1(k6_relat_1(k1_relat_1(X1)))|~v1_funct_1(X1)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(k1_relat_1(X1),k1_relat_1(X2))|~r1_tarski(k2_relat_1(X1),k1_relat_1(X2))), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_162, c_0_95]), c_0_163]), c_0_122])])])).
% 1.30/1.49  cnf(c_0_167, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_50])).
% 1.30/1.49  cnf(c_0_168, negated_conjecture, (m1_subset_1(k5_relat_1(X1,esk4_0),k1_zfmisc_1(k2_zfmisc_1(X2,esk3_0)))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118, c_0_28]), c_0_38])])).
% 1.30/1.49  cnf(c_0_169, negated_conjecture, (m1_subset_1(k5_relat_1(esk5_0,k2_funct_1(esk5_0)),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_164, c_0_40]), c_0_39])])).
% 1.30/1.49  cnf(c_0_170, negated_conjecture, (v1_funct_1(k5_relat_1(esk5_0,k2_funct_1(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_165, c_0_40]), c_0_39])])).
% 1.30/1.49  cnf(c_0_171, negated_conjecture, (k6_relat_1(esk3_0)=esk5_0|k5_relat_1(k6_relat_1(esk3_0),X1)!=k5_relat_1(esk5_0,X1)|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(esk3_0,k1_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_166, c_0_79]), c_0_140]), c_0_39]), c_0_53]), c_0_74])])).
% 1.30/1.49  cnf(c_0_172, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_167])).
% 1.30/1.49  cnf(c_0_173, negated_conjecture, (X1=X2|k5_relat_1(X1,esk4_0)!=k5_relat_1(X2,esk4_0)|k1_relat_1(X1)!=k1_relat_1(X2)|~v1_funct_1(X2)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X2),esk3_0)|~r1_tarski(k2_relat_1(X1),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_162, c_0_65]), c_0_60]), c_0_38]), c_0_61])])).
% 1.30/1.49  cnf(c_0_174, negated_conjecture, (m1_subset_1(k5_relat_1(k5_relat_1(esk5_0,k2_funct_1(esk5_0)),esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_168, c_0_169]), c_0_170])])).
% 1.30/1.49  cnf(c_0_175, negated_conjecture, (~r2_relset_1(esk3_0,esk3_0,esk5_0,k6_partfun1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 1.30/1.49  cnf(c_0_176, negated_conjecture, (k6_relat_1(esk3_0)=esk5_0|k2_relset_1(esk3_0,esk3_0,esk5_0)!=esk3_0|k5_relat_1(esk5_0,esk5_0)!=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_171, c_0_154]), c_0_77]), c_0_39]), c_0_53]), c_0_79]), c_0_172])])).
% 1.30/1.49  cnf(c_0_177, negated_conjecture, (m1_subset_1(k5_relat_1(k5_relat_1(esk5_0,k2_funct_1(esk5_0)),esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124, c_0_169]), c_0_170])])).
% 1.30/1.49  cnf(c_0_178, negated_conjecture, (X1=esk5_0|k5_relat_1(X1,esk4_0)!=esk4_0|k1_relat_1(X1)!=esk3_0|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_173, c_0_74]), c_0_59]), c_0_79]), c_0_39]), c_0_53]), c_0_172])])).
% 1.30/1.49  cnf(c_0_179, negated_conjecture, (m1_subset_1(k5_relat_1(k6_relat_1(esk3_0),esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_174, c_0_116]), c_0_79]), c_0_77]), c_0_39]), c_0_53])])).
% 1.30/1.49  cnf(c_0_180, negated_conjecture, (~r2_relset_1(esk3_0,esk3_0,esk5_0,k6_relat_1(esk3_0))), inference(rw,[status(thm)],[c_0_175, c_0_111])).
% 1.30/1.49  cnf(c_0_181, negated_conjecture, (k6_relat_1(esk3_0)=esk5_0|k5_relat_1(esk5_0,esk5_0)!=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_176, c_0_72]), c_0_74]), c_0_40])])).
% 1.30/1.49  cnf(c_0_182, plain, (r2_relset_1(X3,X4,X1,X2)|X1!=X2|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.30/1.49  cnf(c_0_183, negated_conjecture, (m1_subset_1(k5_relat_1(k6_relat_1(esk3_0),esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_177, c_0_116]), c_0_79]), c_0_77]), c_0_39]), c_0_53])])).
% 1.30/1.49  cnf(c_0_184, negated_conjecture, (k6_relat_1(esk3_0)=esk5_0|k5_relat_1(k6_relat_1(esk3_0),esk4_0)!=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_178, c_0_95]), c_0_163]), c_0_122])])]), c_0_140]), c_0_172])])).
% 1.30/1.49  cnf(c_0_185, negated_conjecture, (k5_relat_1(k6_relat_1(esk3_0),esk4_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_150, c_0_179]), c_0_28])])).
% 1.30/1.49  cnf(c_0_186, negated_conjecture, (k5_relat_1(esk5_0,esk5_0)!=esk5_0|~r2_relset_1(esk3_0,esk3_0,esk5_0,esk5_0)), inference(spm,[status(thm)],[c_0_180, c_0_181])).
% 1.30/1.49  cnf(c_0_187, plain, (r2_relset_1(X1,X2,X3,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(er,[status(thm)],[c_0_182])).
% 1.30/1.49  cnf(c_0_188, negated_conjecture, (k5_relat_1(k6_relat_1(esk3_0),esk5_0)=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_150, c_0_183]), c_0_40])])).
% 1.30/1.49  cnf(c_0_189, negated_conjecture, (k6_relat_1(esk3_0)=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_184, c_0_185])])).
% 1.30/1.49  cnf(c_0_190, negated_conjecture, (k5_relat_1(esk5_0,esk5_0)!=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_186, c_0_187]), c_0_40])])).
% 1.30/1.49  cnf(c_0_191, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_188, c_0_189]), c_0_190]), ['proof']).
% 1.30/1.49  # SZS output end CNFRefutation
% 1.30/1.49  # Proof object total steps             : 192
% 1.30/1.49  # Proof object clause steps            : 145
% 1.30/1.49  # Proof object formula steps           : 47
% 1.30/1.49  # Proof object conjectures             : 94
% 1.30/1.49  # Proof object clause conjectures      : 91
% 1.30/1.49  # Proof object formula conjectures     : 3
% 1.30/1.49  # Proof object initial clauses used    : 39
% 1.30/1.49  # Proof object initial formulas used   : 23
% 1.30/1.49  # Proof object generating inferences   : 95
% 1.30/1.49  # Proof object simplifying inferences  : 256
% 1.30/1.49  # Training examples: 0 positive, 0 negative
% 1.30/1.49  # Parsed axioms                        : 23
% 1.30/1.49  # Removed by relevancy pruning/SinE    : 0
% 1.30/1.49  # Initial clauses                      : 55
% 1.30/1.49  # Removed in clause preprocessing      : 2
% 1.30/1.49  # Initial clauses in saturation        : 53
% 1.30/1.49  # Processed clauses                    : 7290
% 1.30/1.49  # ...of these trivial                  : 205
% 1.30/1.49  # ...subsumed                          : 3826
% 1.30/1.49  # ...remaining for further processing  : 3259
% 1.30/1.49  # Other redundant clauses eliminated   : 35
% 1.30/1.49  # Clauses deleted for lack of memory   : 0
% 1.30/1.49  # Backward-subsumed                    : 360
% 1.30/1.49  # Backward-rewritten                   : 1164
% 1.30/1.49  # Generated clauses                    : 84870
% 1.30/1.49  # ...of the previous two non-trivial   : 75471
% 1.30/1.49  # Contextual simplify-reflections      : 850
% 1.30/1.49  # Paramodulations                      : 84828
% 1.30/1.49  # Factorizations                       : 0
% 1.30/1.49  # Equation resolutions                 : 42
% 1.30/1.49  # Propositional unsat checks           : 0
% 1.30/1.49  #    Propositional check models        : 0
% 1.30/1.49  #    Propositional check unsatisfiable : 0
% 1.30/1.49  #    Propositional clauses             : 0
% 1.30/1.49  #    Propositional clauses after purity: 0
% 1.30/1.49  #    Propositional unsat core size     : 0
% 1.30/1.49  #    Propositional preprocessing time  : 0.000
% 1.30/1.49  #    Propositional encoding time       : 0.000
% 1.30/1.49  #    Propositional solver time         : 0.000
% 1.30/1.49  #    Success case prop preproc time    : 0.000
% 1.30/1.49  #    Success case prop encoding time   : 0.000
% 1.30/1.49  #    Success case prop solver time     : 0.000
% 1.30/1.49  # Current number of processed clauses  : 1680
% 1.30/1.49  #    Positive orientable unit clauses  : 331
% 1.30/1.49  #    Positive unorientable unit clauses: 0
% 1.30/1.49  #    Negative unit clauses             : 1
% 1.30/1.49  #    Non-unit-clauses                  : 1348
% 1.30/1.49  # Current number of unprocessed clauses: 67488
% 1.30/1.49  # ...number of literals in the above   : 295727
% 1.30/1.49  # Current number of archived formulas  : 0
% 1.30/1.49  # Current number of archived clauses   : 1577
% 1.30/1.49  # Clause-clause subsumption calls (NU) : 185526
% 1.30/1.49  # Rec. Clause-clause subsumption calls : 92117
% 1.30/1.49  # Non-unit clause-clause subsumptions  : 4714
% 1.30/1.49  # Unit Clause-clause subsumption calls : 23698
% 1.30/1.49  # Rewrite failures with RHS unbound    : 0
% 1.30/1.49  # BW rewrite match attempts            : 2704
% 1.30/1.49  # BW rewrite match successes           : 86
% 1.30/1.49  # Condensation attempts                : 0
% 1.30/1.49  # Condensation successes               : 0
% 1.30/1.49  # Termbank termtop insertions          : 2506465
% 1.30/1.50  
% 1.30/1.50  # -------------------------------------------------
% 1.30/1.50  # User time                : 1.103 s
% 1.30/1.50  # System time              : 0.058 s
% 1.30/1.50  # Total time               : 1.161 s
% 1.30/1.50  # Maximum resident set size: 1612 pages
%------------------------------------------------------------------------------

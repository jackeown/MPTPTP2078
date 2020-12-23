%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:05:46 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  130 (4595 expanded)
%              Number of clauses        :   83 (1684 expanded)
%              Number of leaves         :   23 (1155 expanded)
%              Depth                    :   12
%              Number of atoms          :  486 (24365 expanded)
%              Number of equality atoms :  105 (1479 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   70 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t67_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => k1_relset_1(X1,X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_funct_2)).

fof(t23_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( r2_relset_1(X1,X2,k4_relset_1(X1,X1,X1,X2,k6_partfun1(X1),X3),X3)
        & r2_relset_1(X1,X2,k4_relset_1(X1,X2,X2,X2,X3,k6_partfun1(X2)),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_2)).

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(redefinition_r2_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_relset_1(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(dt_k6_partfun1,axiom,(
    ! [X1] :
      ( v1_partfun1(k6_partfun1(X1),X1)
      & m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

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

fof(t3_funct_2,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_funct_1(X1)
        & v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

fof(dt_k4_relset_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => m1_subset_1(k4_relset_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relset_1)).

fof(t27_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ~ ( X1 != k1_xboole_0
          & X2 != k1_xboole_0
          & ~ ( v2_funct_1(X3)
            <=> ! [X4,X5] :
                  ( ( v1_funct_1(X5)
                    & v1_funct_2(X5,X4,X1)
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) )
                 => ! [X6] :
                      ( ( v1_funct_1(X6)
                        & v1_funct_2(X6,X4,X1)
                        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) )
                     => ( r2_relset_1(X4,X2,k1_partfun1(X4,X1,X1,X2,X5,X3),k1_partfun1(X4,X1,X1,X2,X6,X3))
                       => r2_relset_1(X4,X1,X5,X6) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_funct_2)).

fof(redefinition_k4_relset_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k4_relset_1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t61_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(k1_relat_1(X1))
          & k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(k2_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(fc4_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v2_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(c_0_23,plain,(
    ! [X29,X30,X31] :
      ( ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))
      | k1_relset_1(X29,X30,X31) = k1_relat_1(X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_24,plain,(
    ! [X75,X76] :
      ( ~ v1_funct_1(X76)
      | ~ v1_funct_2(X76,X75,X75)
      | ~ m1_subset_1(X76,k1_zfmisc_1(k2_zfmisc_1(X75,X75)))
      | k1_relset_1(X75,X75,X76) = X75 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_funct_2])])).

fof(c_0_25,negated_conjecture,(
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

fof(c_0_26,plain,(
    ! [X59,X60,X61] :
      ( ( r2_relset_1(X59,X60,k4_relset_1(X59,X59,X59,X60,k6_partfun1(X59),X61),X61)
        | ~ m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X59,X60))) )
      & ( r2_relset_1(X59,X60,k4_relset_1(X59,X60,X60,X60,X61,k6_partfun1(X60)),X61)
        | ~ m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X59,X60))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_funct_2])])])).

fof(c_0_27,plain,(
    ! [X58] : k6_partfun1(X58) = k6_relat_1(X58) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

cnf(c_0_28,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( k1_relset_1(X2,X2,X1) = X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_30,negated_conjecture,
    ( v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,esk4_0,esk4_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0)))
    & v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,esk4_0,esk4_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0)))
    & r2_relset_1(esk4_0,esk4_0,k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,esk6_0,esk5_0),esk5_0)
    & v2_funct_1(esk5_0)
    & ~ r2_relset_1(esk4_0,esk4_0,esk6_0,k6_partfun1(esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).

fof(c_0_31,plain,(
    ! [X20,X21,X22] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
      | v1_relat_1(X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_32,plain,(
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

cnf(c_0_33,plain,
    ( r2_relset_1(X1,X2,k4_relset_1(X1,X1,X1,X2,k6_partfun1(X1),X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_35,plain,(
    ! [X51] :
      ( v1_partfun1(k6_partfun1(X51),X51)
      & m1_subset_1(k6_partfun1(X51),k1_zfmisc_1(k2_zfmisc_1(X51,X51))) ) ),
    inference(variable_rename,[status(thm)],[dt_k6_partfun1])).

fof(c_0_36,plain,(
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

fof(c_0_37,plain,(
    ! [X52,X53,X54,X55,X56,X57] :
      ( ~ v1_funct_1(X56)
      | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))
      | ~ v1_funct_1(X57)
      | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X54,X55)))
      | k1_partfun1(X52,X53,X54,X55,X56,X57) = k5_relat_1(X56,X57) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).

fof(c_0_38,plain,(
    ! [X74] :
      ( ( v1_funct_1(X74)
        | ~ v1_relat_1(X74)
        | ~ v1_funct_1(X74) )
      & ( v1_funct_2(X74,k1_relat_1(X74),k2_relat_1(X74))
        | ~ v1_relat_1(X74)
        | ~ v1_funct_1(X74) )
      & ( m1_subset_1(X74,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X74),k2_relat_1(X74))))
        | ~ v1_relat_1(X74)
        | ~ v1_funct_1(X74) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).

cnf(c_0_39,plain,
    ( X1 = k1_relat_1(X2)
    | ~ v1_funct_2(X2,X1,X1)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_41,negated_conjecture,
    ( v1_funct_2(esk5_0,esk4_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_42,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_43,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_44,plain,(
    ! [X71,X72,X73] :
      ( ( v1_funct_1(k2_funct_1(X73))
        | ~ v2_funct_1(X73)
        | k2_relset_1(X71,X72,X73) != X72
        | ~ v1_funct_1(X73)
        | ~ v1_funct_2(X73,X71,X72)
        | ~ m1_subset_1(X73,k1_zfmisc_1(k2_zfmisc_1(X71,X72))) )
      & ( v1_funct_2(k2_funct_1(X73),X72,X71)
        | ~ v2_funct_1(X73)
        | k2_relset_1(X71,X72,X73) != X72
        | ~ v1_funct_1(X73)
        | ~ v1_funct_2(X73,X71,X72)
        | ~ m1_subset_1(X73,k1_zfmisc_1(k2_zfmisc_1(X71,X72))) )
      & ( m1_subset_1(k2_funct_1(X73),k1_zfmisc_1(k2_zfmisc_1(X72,X71)))
        | ~ v2_funct_1(X73)
        | k2_relset_1(X71,X72,X73) != X72
        | ~ v1_funct_1(X73)
        | ~ v1_funct_2(X73,X71,X72)
        | ~ m1_subset_1(X73,k1_zfmisc_1(k2_zfmisc_1(X71,X72))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_funct_2])])])).

cnf(c_0_45,plain,
    ( X3 = X4
    | ~ r2_relset_1(X1,X2,X3,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_46,plain,
    ( r2_relset_1(X1,X2,k4_relset_1(X1,X1,X1,X2,k6_relat_1(X1),X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_33,c_0_34])).

fof(c_0_47,plain,(
    ! [X23,X24,X25,X26,X27,X28] :
      ( ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))
      | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
      | m1_subset_1(k4_relset_1(X23,X24,X25,X26,X27,X28),k1_zfmisc_1(k2_zfmisc_1(X23,X26))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relset_1])])).

cnf(c_0_48,plain,
    ( m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_49,plain,
    ( v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X6)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_50,plain,
    ( k1_partfun1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_51,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_52,negated_conjecture,
    ( k1_relat_1(esk5_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41]),c_0_42])])).

cnf(c_0_53,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_40])).

cnf(c_0_54,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_55,plain,
    ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v2_funct_1(X1)
    | k2_relset_1(X3,X2,X1) != X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_56,plain,(
    ! [X62,X63,X64,X65,X66,X67] :
      ( ( ~ v2_funct_1(X64)
        | ~ v1_funct_1(X66)
        | ~ v1_funct_2(X66,X65,X62)
        | ~ m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(X65,X62)))
        | ~ v1_funct_1(X67)
        | ~ v1_funct_2(X67,X65,X62)
        | ~ m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(X65,X62)))
        | ~ r2_relset_1(X65,X63,k1_partfun1(X65,X62,X62,X63,X66,X64),k1_partfun1(X65,X62,X62,X63,X67,X64))
        | r2_relset_1(X65,X62,X66,X67)
        | X62 = k1_xboole_0
        | X63 = k1_xboole_0
        | ~ v1_funct_1(X64)
        | ~ v1_funct_2(X64,X62,X63)
        | ~ m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X62,X63))) )
      & ( v1_funct_1(esk2_3(X62,X63,X64))
        | v2_funct_1(X64)
        | X62 = k1_xboole_0
        | X63 = k1_xboole_0
        | ~ v1_funct_1(X64)
        | ~ v1_funct_2(X64,X62,X63)
        | ~ m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X62,X63))) )
      & ( v1_funct_2(esk2_3(X62,X63,X64),esk1_3(X62,X63,X64),X62)
        | v2_funct_1(X64)
        | X62 = k1_xboole_0
        | X63 = k1_xboole_0
        | ~ v1_funct_1(X64)
        | ~ v1_funct_2(X64,X62,X63)
        | ~ m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X62,X63))) )
      & ( m1_subset_1(esk2_3(X62,X63,X64),k1_zfmisc_1(k2_zfmisc_1(esk1_3(X62,X63,X64),X62)))
        | v2_funct_1(X64)
        | X62 = k1_xboole_0
        | X63 = k1_xboole_0
        | ~ v1_funct_1(X64)
        | ~ v1_funct_2(X64,X62,X63)
        | ~ m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X62,X63))) )
      & ( v1_funct_1(esk3_3(X62,X63,X64))
        | v2_funct_1(X64)
        | X62 = k1_xboole_0
        | X63 = k1_xboole_0
        | ~ v1_funct_1(X64)
        | ~ v1_funct_2(X64,X62,X63)
        | ~ m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X62,X63))) )
      & ( v1_funct_2(esk3_3(X62,X63,X64),esk1_3(X62,X63,X64),X62)
        | v2_funct_1(X64)
        | X62 = k1_xboole_0
        | X63 = k1_xboole_0
        | ~ v1_funct_1(X64)
        | ~ v1_funct_2(X64,X62,X63)
        | ~ m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X62,X63))) )
      & ( m1_subset_1(esk3_3(X62,X63,X64),k1_zfmisc_1(k2_zfmisc_1(esk1_3(X62,X63,X64),X62)))
        | v2_funct_1(X64)
        | X62 = k1_xboole_0
        | X63 = k1_xboole_0
        | ~ v1_funct_1(X64)
        | ~ v1_funct_2(X64,X62,X63)
        | ~ m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X62,X63))) )
      & ( r2_relset_1(esk1_3(X62,X63,X64),X63,k1_partfun1(esk1_3(X62,X63,X64),X62,X62,X63,esk2_3(X62,X63,X64),X64),k1_partfun1(esk1_3(X62,X63,X64),X62,X62,X63,esk3_3(X62,X63,X64),X64))
        | v2_funct_1(X64)
        | X62 = k1_xboole_0
        | X63 = k1_xboole_0
        | ~ v1_funct_1(X64)
        | ~ v1_funct_2(X64,X62,X63)
        | ~ m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X62,X63))) )
      & ( ~ r2_relset_1(esk1_3(X62,X63,X64),X62,esk2_3(X62,X63,X64),esk3_3(X62,X63,X64))
        | v2_funct_1(X64)
        | X62 = k1_xboole_0
        | X63 = k1_xboole_0
        | ~ v1_funct_1(X64)
        | ~ v1_funct_2(X64,X62,X63)
        | ~ m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X62,X63))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t27_funct_2])])])])])).

cnf(c_0_57,negated_conjecture,
    ( r2_relset_1(esk4_0,esk4_0,k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,esk6_0,esk5_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_58,plain,(
    ! [X35,X36,X37,X38,X39,X40] :
      ( ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))
      | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))
      | k4_relset_1(X35,X36,X37,X38,X39,X40) = k5_relat_1(X39,X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_relset_1])])).

cnf(c_0_59,plain,
    ( k4_relset_1(X1,X1,X1,X2,k6_relat_1(X1),X3) = X3
    | ~ m1_subset_1(k4_relset_1(X1,X1,X1,X2,k6_relat_1(X1),X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_60,plain,
    ( m1_subset_1(k4_relset_1(X2,X3,X5,X6,X1,X4),k1_zfmisc_1(k2_zfmisc_1(X2,X6)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_61,plain,
    ( m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(rw,[status(thm)],[c_0_48,c_0_34])).

cnf(c_0_62,plain,
    ( v1_funct_1(k5_relat_1(X1,X2))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_63,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k2_relat_1(esk5_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_42]),c_0_53])])).

cnf(c_0_65,negated_conjecture,
    ( v1_funct_2(esk5_0,esk4_0,k2_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_52]),c_0_42]),c_0_53])])).

cnf(c_0_66,negated_conjecture,
    ( v2_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_67,plain,(
    ! [X32,X33,X34] :
      ( ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))
      | k2_relset_1(X32,X33,X34) = k2_relat_1(X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_68,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v1_funct_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_55])).

cnf(c_0_69,plain,
    ( r2_relset_1(X1,X2,k4_relset_1(X1,X2,X2,X2,X3,k6_partfun1(X2)),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_70,plain,(
    ! [X7,X8] :
      ( ( r1_tarski(X7,X8)
        | X7 != X8 )
      & ( r1_tarski(X8,X7)
        | X7 != X8 )
      & ( ~ r1_tarski(X7,X8)
        | ~ r1_tarski(X8,X7)
        | X7 = X8 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_71,plain,(
    ! [X12,X13] :
      ( ( ~ m1_subset_1(X12,k1_zfmisc_1(X13))
        | r1_tarski(X12,X13) )
      & ( ~ r1_tarski(X12,X13)
        | m1_subset_1(X12,k1_zfmisc_1(X13)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_72,plain,
    ( r2_relset_1(X3,X4,X2,X5)
    | X4 = k1_xboole_0
    | X6 = k1_xboole_0
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,X3,X4)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ r2_relset_1(X3,X6,k1_partfun1(X3,X4,X4,X6,X2,X1),k1_partfun1(X3,X4,X4,X6,X5,X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X4,X6)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_73,negated_conjecture,
    ( k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,esk6_0,esk5_0) = esk5_0
    | ~ m1_subset_1(k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,esk6_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_57]),c_0_40])])).

cnf(c_0_74,plain,
    ( m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X6)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_75,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_76,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_77,plain,
    ( k4_relset_1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_78,plain,
    ( k4_relset_1(X1,X1,X1,X2,k6_relat_1(X1),X3) = X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61])])).

cnf(c_0_79,plain,
    ( v1_funct_1(k5_relat_1(X1,X2))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(spm,[status(thm)],[c_0_62,c_0_51])).

fof(c_0_80,plain,(
    ! [X19] :
      ( ( k5_relat_1(X19,k2_funct_1(X19)) = k6_relat_1(k1_relat_1(X19))
        | ~ v2_funct_1(X19)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) )
      & ( k5_relat_1(k2_funct_1(X19),X19) = k6_relat_1(k2_relat_1(X19))
        | ~ v2_funct_1(X19)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_funct_1])])])).

cnf(c_0_81,negated_conjecture,
    ( v1_funct_1(k2_funct_1(esk5_0))
    | k2_relset_1(esk4_0,k2_relat_1(esk5_0),esk5_0) != k2_relat_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65]),c_0_42]),c_0_66])])).

cnf(c_0_82,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_83,negated_conjecture,
    ( v1_relat_1(k2_funct_1(esk5_0))
    | k2_relset_1(esk4_0,k2_relat_1(esk5_0),esk5_0) != k2_relat_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_64]),c_0_65]),c_0_42]),c_0_66])])).

cnf(c_0_84,plain,
    ( r2_relset_1(X1,X2,k4_relset_1(X1,X2,X2,X2,X3,k6_relat_1(X2)),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_69,c_0_34])).

fof(c_0_85,plain,(
    ! [X9,X10] :
      ( ( k2_zfmisc_1(X9,X10) != k1_xboole_0
        | X9 = k1_xboole_0
        | X10 = k1_xboole_0 )
      & ( X9 != k1_xboole_0
        | k2_zfmisc_1(X9,X10) = k1_xboole_0 )
      & ( X10 != k1_xboole_0
        | k2_zfmisc_1(X9,X10) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_86,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_87,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_88,negated_conjecture,
    ( v1_funct_2(esk6_0,esk4_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_89,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | r2_relset_1(X3,X1,X4,X5)
    | ~ v1_funct_2(X5,X3,X1)
    | ~ v1_funct_2(X4,X3,X1)
    | ~ v1_funct_2(X6,X1,X2)
    | ~ r2_relset_1(X3,X2,k1_partfun1(X3,X1,X1,X2,X4,X6),k5_relat_1(X5,X6))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X6)
    | ~ v2_funct_1(X6)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_72,c_0_50])).

cnf(c_0_90,negated_conjecture,
    ( k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,esk6_0,esk5_0) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_42]),c_0_75]),c_0_40]),c_0_76])])).

cnf(c_0_91,plain,
    ( k5_relat_1(k6_relat_1(X1),X2) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_61])])).

cnf(c_0_92,negated_conjecture,
    ( v1_funct_1(k5_relat_1(esk5_0,X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_40]),c_0_42])])).

cnf(c_0_93,plain,
    ( k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_94,negated_conjecture,
    ( v1_funct_1(k2_funct_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_64])])).

cnf(c_0_95,negated_conjecture,
    ( v1_relat_1(k2_funct_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_82]),c_0_64])])).

cnf(c_0_96,negated_conjecture,
    ( ~ r2_relset_1(esk4_0,esk4_0,esk6_0,k6_partfun1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_97,plain,(
    ! [X17] :
      ( k1_relat_1(k6_relat_1(X17)) = X17
      & k2_relat_1(k6_relat_1(X17)) = X17 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_98,plain,(
    ! [X18] :
      ( v1_relat_1(k6_relat_1(X18))
      & v2_funct_1(k6_relat_1(X18)) ) ),
    inference(variable_rename,[status(thm)],[fc4_funct_1])).

cnf(c_0_99,plain,
    ( k4_relset_1(X1,X2,X2,X2,X3,k6_relat_1(X2)) = X3
    | ~ m1_subset_1(k4_relset_1(X1,X2,X2,X2,X3,k6_relat_1(X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_84])).

cnf(c_0_100,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_101,plain,
    ( X1 = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_102,negated_conjecture,
    ( k1_relat_1(esk6_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_76]),c_0_88]),c_0_75])])).

cnf(c_0_103,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_76])).

cnf(c_0_104,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r2_relset_1(esk4_0,esk4_0,esk6_0,X1)
    | ~ v1_funct_2(X1,esk4_0,esk4_0)
    | ~ r2_relset_1(esk4_0,esk4_0,esk5_0,k5_relat_1(X1,esk5_0))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_88]),c_0_41]),c_0_75]),c_0_42]),c_0_66]),c_0_76]),c_0_40])])).

cnf(c_0_105,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1) = X1
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_91,c_0_51])).

cnf(c_0_106,negated_conjecture,
    ( r2_relset_1(esk4_0,esk4_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_57,c_0_90])).

cnf(c_0_107,negated_conjecture,
    ( v1_funct_1(k6_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_52]),c_0_94]),c_0_95]),c_0_42]),c_0_66]),c_0_53])])).

cnf(c_0_108,negated_conjecture,
    ( ~ r2_relset_1(esk4_0,esk4_0,esk6_0,k6_relat_1(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_96,c_0_34])).

cnf(c_0_109,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_97])).

cnf(c_0_110,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_97])).

cnf(c_0_111,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_98])).

cnf(c_0_112,plain,
    ( k4_relset_1(X1,X2,X2,X2,X3,k6_relat_1(X2)) = X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_60]),c_0_61])])).

fof(c_0_113,plain,(
    ! [X11] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X11)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_114,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_100])).

cnf(c_0_115,plain,
    ( X1 = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_101,c_0_87])).

cnf(c_0_116,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k2_relat_1(esk6_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_102]),c_0_75]),c_0_103])])).

cnf(c_0_117,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | ~ v1_funct_2(k6_relat_1(esk4_0),esk4_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_105]),c_0_52]),c_0_52]),c_0_106]),c_0_52]),c_0_107]),c_0_52]),c_0_61]),c_0_42]),c_0_53])]),c_0_108])).

cnf(c_0_118,plain,
    ( v1_funct_2(k6_relat_1(X1),X1,X1)
    | ~ v1_funct_1(k6_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_109]),c_0_110]),c_0_111])])).

cnf(c_0_119,plain,
    ( k5_relat_1(X1,k6_relat_1(X2)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_112]),c_0_61])])).

cnf(c_0_120,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_113])).

cnf(c_0_121,plain,
    ( m1_subset_1(k6_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_114])).

cnf(c_0_122,negated_conjecture,
    ( k2_zfmisc_1(esk4_0,k2_relat_1(esk6_0)) = esk6_0
    | ~ m1_subset_1(k2_zfmisc_1(esk4_0,k2_relat_1(esk6_0)),k1_zfmisc_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_115,c_0_116])).

cnf(c_0_123,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_118]),c_0_107])])).

cnf(c_0_124,plain,
    ( r2_relset_1(X1,X2,k5_relat_1(X3,k6_relat_1(X2)),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_77]),c_0_61])])).

cnf(c_0_125,plain,
    ( k5_relat_1(k1_xboole_0,k6_relat_1(X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_119,c_0_120])).

cnf(c_0_126,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_121]),c_0_120])])).

cnf(c_0_127,negated_conjecture,
    ( esk6_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_122,c_0_123]),c_0_114]),c_0_123]),c_0_114]),c_0_120])])).

cnf(c_0_128,plain,
    ( r2_relset_1(X1,X2,k1_xboole_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_125]),c_0_120])])).

cnf(c_0_129,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_108,c_0_123]),c_0_123]),c_0_123]),c_0_126]),c_0_127]),c_0_128])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:03:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.21/0.54  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.21/0.54  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.21/0.54  #
% 0.21/0.54  # Preprocessing time       : 0.030 s
% 0.21/0.54  # Presaturation interreduction done
% 0.21/0.54  
% 0.21/0.54  # Proof found!
% 0.21/0.54  # SZS status Theorem
% 0.21/0.54  # SZS output start CNFRefutation
% 0.21/0.54  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.21/0.54  fof(t67_funct_2, axiom, ![X1, X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>k1_relset_1(X1,X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_2)).
% 0.21/0.54  fof(t76_funct_2, conjecture, ![X1, X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X1))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>((r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X3,X2),X2)&v2_funct_1(X2))=>r2_relset_1(X1,X1,X3,k6_partfun1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_funct_2)).
% 0.21/0.54  fof(t23_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(r2_relset_1(X1,X2,k4_relset_1(X1,X1,X1,X2,k6_partfun1(X1),X3),X3)&r2_relset_1(X1,X2,k4_relset_1(X1,X2,X2,X2,X3,k6_partfun1(X2)),X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_funct_2)).
% 0.21/0.54  fof(redefinition_k6_partfun1, axiom, ![X1]:k6_partfun1(X1)=k6_relat_1(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 0.21/0.54  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.21/0.54  fof(redefinition_r2_relset_1, axiom, ![X1, X2, X3, X4]:((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_relset_1(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 0.21/0.54  fof(dt_k6_partfun1, axiom, ![X1]:(v1_partfun1(k6_partfun1(X1),X1)&m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 0.21/0.54  fof(dt_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>(v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))&m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 0.21/0.54  fof(redefinition_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>k1_partfun1(X1,X2,X3,X4,X5,X6)=k5_relat_1(X5,X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 0.21/0.54  fof(t3_funct_2, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 0.21/0.54  fof(t31_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 0.21/0.54  fof(dt_k4_relset_1, axiom, ![X1, X2, X3, X4, X5, X6]:((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>m1_subset_1(k4_relset_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relset_1)).
% 0.21/0.54  fof(t27_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>~(((X1!=k1_xboole_0&X2!=k1_xboole_0)&~((v2_funct_1(X3)<=>![X4, X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X4,X1))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,X4,X1))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X1))))=>(r2_relset_1(X4,X2,k1_partfun1(X4,X1,X1,X2,X5,X3),k1_partfun1(X4,X1,X1,X2,X6,X3))=>r2_relset_1(X4,X1,X5,X6))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_funct_2)).
% 0.21/0.54  fof(redefinition_k4_relset_1, axiom, ![X1, X2, X3, X4, X5, X6]:((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>k4_relset_1(X1,X2,X3,X4,X5,X6)=k5_relat_1(X5,X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 0.21/0.54  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.21/0.54  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.21/0.54  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.21/0.54  fof(t61_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(k1_relat_1(X1))&k5_relat_1(k2_funct_1(X1),X1)=k6_relat_1(k2_relat_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 0.21/0.54  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.21/0.54  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 0.21/0.54  fof(fc4_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v2_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 0.21/0.54  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.21/0.54  fof(c_0_23, plain, ![X29, X30, X31]:(~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))|k1_relset_1(X29,X30,X31)=k1_relat_1(X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.21/0.54  fof(c_0_24, plain, ![X75, X76]:(~v1_funct_1(X76)|~v1_funct_2(X76,X75,X75)|~m1_subset_1(X76,k1_zfmisc_1(k2_zfmisc_1(X75,X75)))|k1_relset_1(X75,X75,X76)=X75), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_funct_2])])).
% 0.21/0.54  fof(c_0_25, negated_conjecture, ~(![X1, X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X1))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>((r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X3,X2),X2)&v2_funct_1(X2))=>r2_relset_1(X1,X1,X3,k6_partfun1(X1)))))), inference(assume_negation,[status(cth)],[t76_funct_2])).
% 0.21/0.54  fof(c_0_26, plain, ![X59, X60, X61]:((r2_relset_1(X59,X60,k4_relset_1(X59,X59,X59,X60,k6_partfun1(X59),X61),X61)|~m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X59,X60))))&(r2_relset_1(X59,X60,k4_relset_1(X59,X60,X60,X60,X61,k6_partfun1(X60)),X61)|~m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X59,X60))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_funct_2])])])).
% 0.21/0.54  fof(c_0_27, plain, ![X58]:k6_partfun1(X58)=k6_relat_1(X58), inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).
% 0.21/0.54  cnf(c_0_28, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.54  cnf(c_0_29, plain, (k1_relset_1(X2,X2,X1)=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.21/0.54  fof(c_0_30, negated_conjecture, (((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,esk4_0,esk4_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0))))&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,esk4_0,esk4_0))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0))))&((r2_relset_1(esk4_0,esk4_0,k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,esk6_0,esk5_0),esk5_0)&v2_funct_1(esk5_0))&~r2_relset_1(esk4_0,esk4_0,esk6_0,k6_partfun1(esk4_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).
% 0.21/0.54  fof(c_0_31, plain, ![X20, X21, X22]:(~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))|v1_relat_1(X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.21/0.54  fof(c_0_32, plain, ![X41, X42, X43, X44]:((~r2_relset_1(X41,X42,X43,X44)|X43=X44|(~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))))&(X43!=X44|r2_relset_1(X41,X42,X43,X44)|(~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).
% 0.21/0.54  cnf(c_0_33, plain, (r2_relset_1(X1,X2,k4_relset_1(X1,X1,X1,X2,k6_partfun1(X1),X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.54  cnf(c_0_34, plain, (k6_partfun1(X1)=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.54  fof(c_0_35, plain, ![X51]:(v1_partfun1(k6_partfun1(X51),X51)&m1_subset_1(k6_partfun1(X51),k1_zfmisc_1(k2_zfmisc_1(X51,X51)))), inference(variable_rename,[status(thm)],[dt_k6_partfun1])).
% 0.21/0.54  fof(c_0_36, plain, ![X45, X46, X47, X48, X49, X50]:((v1_funct_1(k1_partfun1(X45,X46,X47,X48,X49,X50))|(~v1_funct_1(X49)|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))|~v1_funct_1(X50)|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))))&(m1_subset_1(k1_partfun1(X45,X46,X47,X48,X49,X50),k1_zfmisc_1(k2_zfmisc_1(X45,X48)))|(~v1_funct_1(X49)|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))|~v1_funct_1(X50)|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).
% 0.21/0.54  fof(c_0_37, plain, ![X52, X53, X54, X55, X56, X57]:(~v1_funct_1(X56)|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))|~v1_funct_1(X57)|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X54,X55)))|k1_partfun1(X52,X53,X54,X55,X56,X57)=k5_relat_1(X56,X57)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).
% 0.21/0.54  fof(c_0_38, plain, ![X74]:(((v1_funct_1(X74)|(~v1_relat_1(X74)|~v1_funct_1(X74)))&(v1_funct_2(X74,k1_relat_1(X74),k2_relat_1(X74))|(~v1_relat_1(X74)|~v1_funct_1(X74))))&(m1_subset_1(X74,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X74),k2_relat_1(X74))))|(~v1_relat_1(X74)|~v1_funct_1(X74)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).
% 0.21/0.54  cnf(c_0_39, plain, (X1=k1_relat_1(X2)|~v1_funct_2(X2,X1,X1)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.21/0.54  cnf(c_0_40, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.54  cnf(c_0_41, negated_conjecture, (v1_funct_2(esk5_0,esk4_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.54  cnf(c_0_42, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.54  cnf(c_0_43, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.21/0.54  fof(c_0_44, plain, ![X71, X72, X73]:(((v1_funct_1(k2_funct_1(X73))|(~v2_funct_1(X73)|k2_relset_1(X71,X72,X73)!=X72)|(~v1_funct_1(X73)|~v1_funct_2(X73,X71,X72)|~m1_subset_1(X73,k1_zfmisc_1(k2_zfmisc_1(X71,X72)))))&(v1_funct_2(k2_funct_1(X73),X72,X71)|(~v2_funct_1(X73)|k2_relset_1(X71,X72,X73)!=X72)|(~v1_funct_1(X73)|~v1_funct_2(X73,X71,X72)|~m1_subset_1(X73,k1_zfmisc_1(k2_zfmisc_1(X71,X72))))))&(m1_subset_1(k2_funct_1(X73),k1_zfmisc_1(k2_zfmisc_1(X72,X71)))|(~v2_funct_1(X73)|k2_relset_1(X71,X72,X73)!=X72)|(~v1_funct_1(X73)|~v1_funct_2(X73,X71,X72)|~m1_subset_1(X73,k1_zfmisc_1(k2_zfmisc_1(X71,X72)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_funct_2])])])).
% 0.21/0.54  cnf(c_0_45, plain, (X3=X4|~r2_relset_1(X1,X2,X3,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.21/0.54  cnf(c_0_46, plain, (r2_relset_1(X1,X2,k4_relset_1(X1,X1,X1,X2,k6_relat_1(X1),X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(rw,[status(thm)],[c_0_33, c_0_34])).
% 0.21/0.54  fof(c_0_47, plain, ![X23, X24, X25, X26, X27, X28]:(~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))|m1_subset_1(k4_relset_1(X23,X24,X25,X26,X27,X28),k1_zfmisc_1(k2_zfmisc_1(X23,X26)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relset_1])])).
% 0.21/0.54  cnf(c_0_48, plain, (m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.21/0.54  cnf(c_0_49, plain, (v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X6)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.21/0.54  cnf(c_0_50, plain, (k1_partfun1(X2,X3,X5,X6,X1,X4)=k5_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.21/0.54  cnf(c_0_51, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.21/0.54  cnf(c_0_52, negated_conjecture, (k1_relat_1(esk5_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41]), c_0_42])])).
% 0.21/0.54  cnf(c_0_53, negated_conjecture, (v1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_43, c_0_40])).
% 0.21/0.54  cnf(c_0_54, plain, (v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.21/0.54  cnf(c_0_55, plain, (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v2_funct_1(X1)|k2_relset_1(X3,X2,X1)!=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.21/0.54  fof(c_0_56, plain, ![X62, X63, X64, X65, X66, X67]:((~v2_funct_1(X64)|(~v1_funct_1(X66)|~v1_funct_2(X66,X65,X62)|~m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(X65,X62)))|(~v1_funct_1(X67)|~v1_funct_2(X67,X65,X62)|~m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(X65,X62)))|(~r2_relset_1(X65,X63,k1_partfun1(X65,X62,X62,X63,X66,X64),k1_partfun1(X65,X62,X62,X63,X67,X64))|r2_relset_1(X65,X62,X66,X67))))|(X62=k1_xboole_0|X63=k1_xboole_0)|(~v1_funct_1(X64)|~v1_funct_2(X64,X62,X63)|~m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X62,X63)))))&((((v1_funct_1(esk2_3(X62,X63,X64))|v2_funct_1(X64)|(X62=k1_xboole_0|X63=k1_xboole_0)|(~v1_funct_1(X64)|~v1_funct_2(X64,X62,X63)|~m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X62,X63)))))&(v1_funct_2(esk2_3(X62,X63,X64),esk1_3(X62,X63,X64),X62)|v2_funct_1(X64)|(X62=k1_xboole_0|X63=k1_xboole_0)|(~v1_funct_1(X64)|~v1_funct_2(X64,X62,X63)|~m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X62,X63))))))&(m1_subset_1(esk2_3(X62,X63,X64),k1_zfmisc_1(k2_zfmisc_1(esk1_3(X62,X63,X64),X62)))|v2_funct_1(X64)|(X62=k1_xboole_0|X63=k1_xboole_0)|(~v1_funct_1(X64)|~v1_funct_2(X64,X62,X63)|~m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X62,X63))))))&((((v1_funct_1(esk3_3(X62,X63,X64))|v2_funct_1(X64)|(X62=k1_xboole_0|X63=k1_xboole_0)|(~v1_funct_1(X64)|~v1_funct_2(X64,X62,X63)|~m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X62,X63)))))&(v1_funct_2(esk3_3(X62,X63,X64),esk1_3(X62,X63,X64),X62)|v2_funct_1(X64)|(X62=k1_xboole_0|X63=k1_xboole_0)|(~v1_funct_1(X64)|~v1_funct_2(X64,X62,X63)|~m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X62,X63))))))&(m1_subset_1(esk3_3(X62,X63,X64),k1_zfmisc_1(k2_zfmisc_1(esk1_3(X62,X63,X64),X62)))|v2_funct_1(X64)|(X62=k1_xboole_0|X63=k1_xboole_0)|(~v1_funct_1(X64)|~v1_funct_2(X64,X62,X63)|~m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X62,X63))))))&((r2_relset_1(esk1_3(X62,X63,X64),X63,k1_partfun1(esk1_3(X62,X63,X64),X62,X62,X63,esk2_3(X62,X63,X64),X64),k1_partfun1(esk1_3(X62,X63,X64),X62,X62,X63,esk3_3(X62,X63,X64),X64))|v2_funct_1(X64)|(X62=k1_xboole_0|X63=k1_xboole_0)|(~v1_funct_1(X64)|~v1_funct_2(X64,X62,X63)|~m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X62,X63)))))&(~r2_relset_1(esk1_3(X62,X63,X64),X62,esk2_3(X62,X63,X64),esk3_3(X62,X63,X64))|v2_funct_1(X64)|(X62=k1_xboole_0|X63=k1_xboole_0)|(~v1_funct_1(X64)|~v1_funct_2(X64,X62,X63)|~m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X62,X63))))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t27_funct_2])])])])])).
% 0.21/0.54  cnf(c_0_57, negated_conjecture, (r2_relset_1(esk4_0,esk4_0,k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,esk6_0,esk5_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.54  fof(c_0_58, plain, ![X35, X36, X37, X38, X39, X40]:(~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))|k4_relset_1(X35,X36,X37,X38,X39,X40)=k5_relat_1(X39,X40)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_relset_1])])).
% 0.21/0.54  cnf(c_0_59, plain, (k4_relset_1(X1,X1,X1,X2,k6_relat_1(X1),X3)=X3|~m1_subset_1(k4_relset_1(X1,X1,X1,X2,k6_relat_1(X1),X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.21/0.54  cnf(c_0_60, plain, (m1_subset_1(k4_relset_1(X2,X3,X5,X6,X1,X4),k1_zfmisc_1(k2_zfmisc_1(X2,X6)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.21/0.54  cnf(c_0_61, plain, (m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(rw,[status(thm)],[c_0_48, c_0_34])).
% 0.21/0.54  cnf(c_0_62, plain, (v1_funct_1(k5_relat_1(X1,X2))|~v1_funct_1(X2)|~v1_funct_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.21/0.54  cnf(c_0_63, plain, (v1_funct_1(k2_funct_1(X1))|~v2_funct_1(X1)|k2_relset_1(X2,X3,X1)!=X3|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.21/0.54  cnf(c_0_64, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k2_relat_1(esk5_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_42]), c_0_53])])).
% 0.21/0.54  cnf(c_0_65, negated_conjecture, (v1_funct_2(esk5_0,esk4_0,k2_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_52]), c_0_42]), c_0_53])])).
% 0.21/0.54  cnf(c_0_66, negated_conjecture, (v2_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.54  fof(c_0_67, plain, ![X32, X33, X34]:(~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))|k2_relset_1(X32,X33,X34)=k2_relat_1(X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.21/0.54  cnf(c_0_68, plain, (v1_relat_1(k2_funct_1(X1))|k2_relset_1(X2,X3,X1)!=X3|~v1_funct_2(X1,X2,X3)|~v1_funct_1(X1)|~v2_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(spm,[status(thm)],[c_0_43, c_0_55])).
% 0.21/0.54  cnf(c_0_69, plain, (r2_relset_1(X1,X2,k4_relset_1(X1,X2,X2,X2,X3,k6_partfun1(X2)),X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.54  fof(c_0_70, plain, ![X7, X8]:(((r1_tarski(X7,X8)|X7!=X8)&(r1_tarski(X8,X7)|X7!=X8))&(~r1_tarski(X7,X8)|~r1_tarski(X8,X7)|X7=X8)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.21/0.54  fof(c_0_71, plain, ![X12, X13]:((~m1_subset_1(X12,k1_zfmisc_1(X13))|r1_tarski(X12,X13))&(~r1_tarski(X12,X13)|m1_subset_1(X12,k1_zfmisc_1(X13)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.21/0.54  cnf(c_0_72, plain, (r2_relset_1(X3,X4,X2,X5)|X4=k1_xboole_0|X6=k1_xboole_0|~v2_funct_1(X1)|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X4)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_1(X5)|~v1_funct_2(X5,X3,X4)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~r2_relset_1(X3,X6,k1_partfun1(X3,X4,X4,X6,X2,X1),k1_partfun1(X3,X4,X4,X6,X5,X1))|~v1_funct_1(X1)|~v1_funct_2(X1,X4,X6)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X6)))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.21/0.54  cnf(c_0_73, negated_conjecture, (k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,esk6_0,esk5_0)=esk5_0|~m1_subset_1(k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,esk6_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_57]), c_0_40])])).
% 0.21/0.54  cnf(c_0_74, plain, (m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X6)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.21/0.54  cnf(c_0_75, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.54  cnf(c_0_76, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.54  cnf(c_0_77, plain, (k4_relset_1(X2,X3,X5,X6,X1,X4)=k5_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.21/0.54  cnf(c_0_78, plain, (k4_relset_1(X1,X1,X1,X2,k6_relat_1(X1),X3)=X3|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61])])).
% 0.21/0.54  cnf(c_0_79, plain, (v1_funct_1(k5_relat_1(X1,X2))|~v1_funct_1(X2)|~v1_funct_1(X1)|~v1_relat_1(X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(spm,[status(thm)],[c_0_62, c_0_51])).
% 0.21/0.54  fof(c_0_80, plain, ![X19]:((k5_relat_1(X19,k2_funct_1(X19))=k6_relat_1(k1_relat_1(X19))|~v2_funct_1(X19)|(~v1_relat_1(X19)|~v1_funct_1(X19)))&(k5_relat_1(k2_funct_1(X19),X19)=k6_relat_1(k2_relat_1(X19))|~v2_funct_1(X19)|(~v1_relat_1(X19)|~v1_funct_1(X19)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_funct_1])])])).
% 0.21/0.54  cnf(c_0_81, negated_conjecture, (v1_funct_1(k2_funct_1(esk5_0))|k2_relset_1(esk4_0,k2_relat_1(esk5_0),esk5_0)!=k2_relat_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_65]), c_0_42]), c_0_66])])).
% 0.21/0.54  cnf(c_0_82, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.21/0.54  cnf(c_0_83, negated_conjecture, (v1_relat_1(k2_funct_1(esk5_0))|k2_relset_1(esk4_0,k2_relat_1(esk5_0),esk5_0)!=k2_relat_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_64]), c_0_65]), c_0_42]), c_0_66])])).
% 0.21/0.54  cnf(c_0_84, plain, (r2_relset_1(X1,X2,k4_relset_1(X1,X2,X2,X2,X3,k6_relat_1(X2)),X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(rw,[status(thm)],[c_0_69, c_0_34])).
% 0.21/0.54  fof(c_0_85, plain, ![X9, X10]:((k2_zfmisc_1(X9,X10)!=k1_xboole_0|(X9=k1_xboole_0|X10=k1_xboole_0))&((X9!=k1_xboole_0|k2_zfmisc_1(X9,X10)=k1_xboole_0)&(X10!=k1_xboole_0|k2_zfmisc_1(X9,X10)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.21/0.54  cnf(c_0_86, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.21/0.54  cnf(c_0_87, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.21/0.54  cnf(c_0_88, negated_conjecture, (v1_funct_2(esk6_0,esk4_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.54  cnf(c_0_89, plain, (X1=k1_xboole_0|X2=k1_xboole_0|r2_relset_1(X3,X1,X4,X5)|~v1_funct_2(X5,X3,X1)|~v1_funct_2(X4,X3,X1)|~v1_funct_2(X6,X1,X2)|~r2_relset_1(X3,X2,k1_partfun1(X3,X1,X1,X2,X4,X6),k5_relat_1(X5,X6))|~v1_funct_1(X5)|~v1_funct_1(X4)|~v1_funct_1(X6)|~v2_funct_1(X6)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_72, c_0_50])).
% 0.21/0.54  cnf(c_0_90, negated_conjecture, (k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,esk6_0,esk5_0)=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_42]), c_0_75]), c_0_40]), c_0_76])])).
% 0.21/0.54  cnf(c_0_91, plain, (k5_relat_1(k6_relat_1(X1),X2)=X2|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_61])])).
% 0.21/0.54  cnf(c_0_92, negated_conjecture, (v1_funct_1(k5_relat_1(esk5_0,X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_40]), c_0_42])])).
% 0.21/0.54  cnf(c_0_93, plain, (k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(k1_relat_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.21/0.54  cnf(c_0_94, negated_conjecture, (v1_funct_1(k2_funct_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_64])])).
% 0.21/0.54  cnf(c_0_95, negated_conjecture, (v1_relat_1(k2_funct_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_82]), c_0_64])])).
% 0.21/0.54  cnf(c_0_96, negated_conjecture, (~r2_relset_1(esk4_0,esk4_0,esk6_0,k6_partfun1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.54  fof(c_0_97, plain, ![X17]:(k1_relat_1(k6_relat_1(X17))=X17&k2_relat_1(k6_relat_1(X17))=X17), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.21/0.54  fof(c_0_98, plain, ![X18]:(v1_relat_1(k6_relat_1(X18))&v2_funct_1(k6_relat_1(X18))), inference(variable_rename,[status(thm)],[fc4_funct_1])).
% 0.21/0.54  cnf(c_0_99, plain, (k4_relset_1(X1,X2,X2,X2,X3,k6_relat_1(X2))=X3|~m1_subset_1(k4_relset_1(X1,X2,X2,X2,X3,k6_relat_1(X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_45, c_0_84])).
% 0.21/0.54  cnf(c_0_100, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_85])).
% 0.21/0.54  cnf(c_0_101, plain, (X1=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_86, c_0_87])).
% 0.21/0.54  cnf(c_0_102, negated_conjecture, (k1_relat_1(esk6_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_76]), c_0_88]), c_0_75])])).
% 0.21/0.54  cnf(c_0_103, negated_conjecture, (v1_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_43, c_0_76])).
% 0.21/0.54  cnf(c_0_104, negated_conjecture, (esk4_0=k1_xboole_0|r2_relset_1(esk4_0,esk4_0,esk6_0,X1)|~v1_funct_2(X1,esk4_0,esk4_0)|~r2_relset_1(esk4_0,esk4_0,esk5_0,k5_relat_1(X1,esk5_0))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_88]), c_0_41]), c_0_75]), c_0_42]), c_0_66]), c_0_76]), c_0_40])])).
% 0.21/0.54  cnf(c_0_105, plain, (k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1)=X1|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_91, c_0_51])).
% 0.21/0.54  cnf(c_0_106, negated_conjecture, (r2_relset_1(esk4_0,esk4_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[c_0_57, c_0_90])).
% 0.21/0.54  cnf(c_0_107, negated_conjecture, (v1_funct_1(k6_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_52]), c_0_94]), c_0_95]), c_0_42]), c_0_66]), c_0_53])])).
% 0.21/0.54  cnf(c_0_108, negated_conjecture, (~r2_relset_1(esk4_0,esk4_0,esk6_0,k6_relat_1(esk4_0))), inference(rw,[status(thm)],[c_0_96, c_0_34])).
% 0.21/0.54  cnf(c_0_109, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_97])).
% 0.21/0.54  cnf(c_0_110, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_97])).
% 0.21/0.54  cnf(c_0_111, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_98])).
% 0.21/0.54  cnf(c_0_112, plain, (k4_relset_1(X1,X2,X2,X2,X3,k6_relat_1(X2))=X3|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_60]), c_0_61])])).
% 0.21/0.54  fof(c_0_113, plain, ![X11]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X11)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.21/0.54  cnf(c_0_114, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_100])).
% 0.21/0.54  cnf(c_0_115, plain, (X1=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_101, c_0_87])).
% 0.21/0.54  cnf(c_0_116, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k2_relat_1(esk6_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_102]), c_0_75]), c_0_103])])).
% 0.21/0.54  cnf(c_0_117, negated_conjecture, (esk4_0=k1_xboole_0|~v1_funct_2(k6_relat_1(esk4_0),esk4_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_105]), c_0_52]), c_0_52]), c_0_106]), c_0_52]), c_0_107]), c_0_52]), c_0_61]), c_0_42]), c_0_53])]), c_0_108])).
% 0.21/0.54  cnf(c_0_118, plain, (v1_funct_2(k6_relat_1(X1),X1,X1)|~v1_funct_1(k6_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_109]), c_0_110]), c_0_111])])).
% 0.21/0.54  cnf(c_0_119, plain, (k5_relat_1(X1,k6_relat_1(X2))=X1|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_112]), c_0_61])])).
% 0.21/0.54  cnf(c_0_120, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_113])).
% 0.21/0.54  cnf(c_0_121, plain, (m1_subset_1(k6_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_61, c_0_114])).
% 0.21/0.54  cnf(c_0_122, negated_conjecture, (k2_zfmisc_1(esk4_0,k2_relat_1(esk6_0))=esk6_0|~m1_subset_1(k2_zfmisc_1(esk4_0,k2_relat_1(esk6_0)),k1_zfmisc_1(esk6_0))), inference(spm,[status(thm)],[c_0_115, c_0_116])).
% 0.21/0.54  cnf(c_0_123, negated_conjecture, (esk4_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_118]), c_0_107])])).
% 0.21/0.54  cnf(c_0_124, plain, (r2_relset_1(X1,X2,k5_relat_1(X3,k6_relat_1(X2)),X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_77]), c_0_61])])).
% 0.21/0.54  cnf(c_0_125, plain, (k5_relat_1(k1_xboole_0,k6_relat_1(X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_119, c_0_120])).
% 0.21/0.54  cnf(c_0_126, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_121]), c_0_120])])).
% 0.21/0.54  cnf(c_0_127, negated_conjecture, (esk6_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_122, c_0_123]), c_0_114]), c_0_123]), c_0_114]), c_0_120])])).
% 0.21/0.54  cnf(c_0_128, plain, (r2_relset_1(X1,X2,k1_xboole_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124, c_0_125]), c_0_120])])).
% 0.21/0.54  cnf(c_0_129, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_108, c_0_123]), c_0_123]), c_0_123]), c_0_126]), c_0_127]), c_0_128])]), ['proof']).
% 0.21/0.54  # SZS output end CNFRefutation
% 0.21/0.54  # Proof object total steps             : 130
% 0.21/0.54  # Proof object clause steps            : 83
% 0.21/0.54  # Proof object formula steps           : 47
% 0.21/0.54  # Proof object conjectures             : 35
% 0.21/0.54  # Proof object clause conjectures      : 32
% 0.21/0.54  # Proof object formula conjectures     : 3
% 0.21/0.54  # Proof object initial clauses used    : 36
% 0.21/0.54  # Proof object initial formulas used   : 23
% 0.21/0.54  # Proof object generating inferences   : 39
% 0.21/0.54  # Proof object simplifying inferences  : 100
% 0.21/0.54  # Training examples: 0 positive, 0 negative
% 0.21/0.54  # Parsed axioms                        : 24
% 0.21/0.54  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.54  # Initial clauses                      : 56
% 0.21/0.54  # Removed in clause preprocessing      : 2
% 0.21/0.54  # Initial clauses in saturation        : 54
% 0.21/0.54  # Processed clauses                    : 1119
% 0.21/0.54  # ...of these trivial                  : 46
% 0.21/0.54  # ...subsumed                          : 462
% 0.21/0.54  # ...remaining for further processing  : 610
% 0.21/0.54  # Other redundant clauses eliminated   : 12
% 0.21/0.54  # Clauses deleted for lack of memory   : 0
% 0.21/0.54  # Backward-subsumed                    : 32
% 0.21/0.54  # Backward-rewritten                   : 284
% 0.21/0.54  # Generated clauses                    : 3879
% 0.21/0.54  # ...of the previous two non-trivial   : 2859
% 0.21/0.54  # Contextual simplify-reflections      : 71
% 0.21/0.54  # Paramodulations                      : 3847
% 0.21/0.54  # Factorizations                       : 20
% 0.21/0.54  # Equation resolutions                 : 12
% 0.21/0.54  # Propositional unsat checks           : 0
% 0.21/0.54  #    Propositional check models        : 0
% 0.21/0.54  #    Propositional check unsatisfiable : 0
% 0.21/0.54  #    Propositional clauses             : 0
% 0.21/0.54  #    Propositional clauses after purity: 0
% 0.21/0.54  #    Propositional unsat core size     : 0
% 0.21/0.54  #    Propositional preprocessing time  : 0.000
% 0.21/0.54  #    Propositional encoding time       : 0.000
% 0.21/0.54  #    Propositional solver time         : 0.000
% 0.21/0.54  #    Success case prop preproc time    : 0.000
% 0.21/0.54  #    Success case prop encoding time   : 0.000
% 0.21/0.54  #    Success case prop solver time     : 0.000
% 0.21/0.54  # Current number of processed clauses  : 236
% 0.21/0.54  #    Positive orientable unit clauses  : 36
% 0.21/0.54  #    Positive unorientable unit clauses: 0
% 0.21/0.54  #    Negative unit clauses             : 0
% 0.21/0.54  #    Non-unit-clauses                  : 200
% 0.21/0.54  # Current number of unprocessed clauses: 1836
% 0.21/0.54  # ...number of literals in the above   : 12691
% 0.21/0.54  # Current number of archived formulas  : 0
% 0.21/0.54  # Current number of archived clauses   : 370
% 0.21/0.54  # Clause-clause subsumption calls (NU) : 37992
% 0.21/0.54  # Rec. Clause-clause subsumption calls : 8441
% 0.21/0.54  # Non-unit clause-clause subsumptions  : 562
% 0.21/0.54  # Unit Clause-clause subsumption calls : 652
% 0.21/0.54  # Rewrite failures with RHS unbound    : 0
% 0.21/0.54  # BW rewrite match attempts            : 67
% 0.21/0.54  # BW rewrite match successes           : 10
% 0.21/0.54  # Condensation attempts                : 0
% 0.21/0.54  # Condensation successes               : 0
% 0.21/0.54  # Termbank termtop insertions          : 134958
% 0.21/0.54  
% 0.21/0.54  # -------------------------------------------------
% 0.21/0.54  # User time                : 0.192 s
% 0.21/0.54  # System time              : 0.010 s
% 0.21/0.54  # Total time               : 0.202 s
% 0.21/0.54  # Maximum resident set size: 1612 pages
%------------------------------------------------------------------------------

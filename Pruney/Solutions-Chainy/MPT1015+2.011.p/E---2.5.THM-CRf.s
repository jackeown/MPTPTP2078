%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:05:46 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  122 (3093 expanded)
%              Number of clauses        :   76 (1091 expanded)
%              Number of leaves         :   23 ( 776 expanded)
%              Depth                    :   14
%              Number of atoms          :  460 (17795 expanded)
%              Number of equality atoms :  102 (1040 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   70 (   2 average)
%              Maximal term depth       :    4 (   1 average)

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

fof(redefinition_r2_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_relset_1(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(dt_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => ( v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))
        & m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(redefinition_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k1_partfun1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(t3_funct_2,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_funct_1(X1)
        & v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_funct_2)).

fof(t23_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( r2_relset_1(X1,X2,k4_relset_1(X1,X1,X1,X2,k6_partfun1(X1),X3),X3)
        & r2_relset_1(X1,X2,k4_relset_1(X1,X2,X2,X2,X3,k6_partfun1(X2)),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_2)).

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(dt_k6_partfun1,axiom,(
    ! [X1] :
      ( v1_partfun1(k6_partfun1(X1),X1)
      & m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(redefinition_k4_relset_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k4_relset_1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

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

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(t81_relat_1,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

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
    ! [X23,X24,X25] :
      ( ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))
      | k1_relset_1(X23,X24,X25) = k1_relat_1(X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_25,plain,(
    ! [X69,X70] :
      ( ~ v1_funct_1(X70)
      | ~ v1_funct_2(X70,X69,X69)
      | ~ m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(X69,X69)))
      | k1_relset_1(X69,X69,X70) = X69 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_funct_2])])).

fof(c_0_26,plain,(
    ! [X35,X36,X37,X38] :
      ( ( ~ r2_relset_1(X35,X36,X37,X38)
        | X37 = X38
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) )
      & ( X37 != X38
        | r2_relset_1(X35,X36,X37,X38)
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).

fof(c_0_27,negated_conjecture,
    ( v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,esk4_0,esk4_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0)))
    & v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,esk4_0,esk4_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0)))
    & r2_relset_1(esk4_0,esk4_0,k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,esk6_0,esk5_0),esk5_0)
    & v2_funct_1(esk5_0)
    & ~ r2_relset_1(esk4_0,esk4_0,esk6_0,k6_partfun1(esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).

cnf(c_0_28,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,plain,
    ( k1_relset_1(X2,X2,X1) = X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_30,plain,(
    ! [X20,X21,X22] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
      | v1_relat_1(X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_31,plain,
    ( X3 = X4
    | ~ r2_relset_1(X1,X2,X3,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( r2_relset_1(esk4_0,esk4_0,k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,esk6_0,esk5_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_34,plain,(
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

fof(c_0_35,plain,(
    ! [X46,X47,X48,X49,X50,X51] :
      ( ~ v1_funct_1(X50)
      | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X46,X47)))
      | ~ v1_funct_1(X51)
      | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X48,X49)))
      | k1_partfun1(X46,X47,X48,X49,X50,X51) = k5_relat_1(X50,X51) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).

fof(c_0_36,plain,(
    ! [X68] :
      ( ( v1_funct_1(X68)
        | ~ v1_relat_1(X68)
        | ~ v1_funct_1(X68) )
      & ( v1_funct_2(X68,k1_relat_1(X68),k2_relat_1(X68))
        | ~ v1_relat_1(X68)
        | ~ v1_funct_1(X68) )
      & ( m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X68),k2_relat_1(X68))))
        | ~ v1_relat_1(X68)
        | ~ v1_funct_1(X68) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).

cnf(c_0_37,plain,
    ( X1 = k1_relat_1(X2)
    | ~ v1_funct_2(X2,X1,X1)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_38,negated_conjecture,
    ( v1_funct_2(esk5_0,esk4_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_39,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_40,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_41,plain,(
    ! [X65,X66,X67] :
      ( ( v1_funct_1(k2_funct_1(X67))
        | ~ v2_funct_1(X67)
        | k2_relset_1(X65,X66,X67) != X66
        | ~ v1_funct_1(X67)
        | ~ v1_funct_2(X67,X65,X66)
        | ~ m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(X65,X66))) )
      & ( v1_funct_2(k2_funct_1(X67),X66,X65)
        | ~ v2_funct_1(X67)
        | k2_relset_1(X65,X66,X67) != X66
        | ~ v1_funct_1(X67)
        | ~ v1_funct_2(X67,X65,X66)
        | ~ m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(X65,X66))) )
      & ( m1_subset_1(k2_funct_1(X67),k1_zfmisc_1(k2_zfmisc_1(X66,X65)))
        | ~ v2_funct_1(X67)
        | k2_relset_1(X65,X66,X67) != X66
        | ~ v1_funct_1(X67)
        | ~ v1_funct_2(X67,X65,X66)
        | ~ m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(X65,X66))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_funct_2])])])).

fof(c_0_42,plain,(
    ! [X56,X57,X58,X59,X60,X61] :
      ( ( ~ v2_funct_1(X58)
        | ~ v1_funct_1(X60)
        | ~ v1_funct_2(X60,X59,X56)
        | ~ m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X59,X56)))
        | ~ v1_funct_1(X61)
        | ~ v1_funct_2(X61,X59,X56)
        | ~ m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X59,X56)))
        | ~ r2_relset_1(X59,X57,k1_partfun1(X59,X56,X56,X57,X60,X58),k1_partfun1(X59,X56,X56,X57,X61,X58))
        | r2_relset_1(X59,X56,X60,X61)
        | X56 = k1_xboole_0
        | X57 = k1_xboole_0
        | ~ v1_funct_1(X58)
        | ~ v1_funct_2(X58,X56,X57)
        | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57))) )
      & ( v1_funct_1(esk2_3(X56,X57,X58))
        | v2_funct_1(X58)
        | X56 = k1_xboole_0
        | X57 = k1_xboole_0
        | ~ v1_funct_1(X58)
        | ~ v1_funct_2(X58,X56,X57)
        | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57))) )
      & ( v1_funct_2(esk2_3(X56,X57,X58),esk1_3(X56,X57,X58),X56)
        | v2_funct_1(X58)
        | X56 = k1_xboole_0
        | X57 = k1_xboole_0
        | ~ v1_funct_1(X58)
        | ~ v1_funct_2(X58,X56,X57)
        | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57))) )
      & ( m1_subset_1(esk2_3(X56,X57,X58),k1_zfmisc_1(k2_zfmisc_1(esk1_3(X56,X57,X58),X56)))
        | v2_funct_1(X58)
        | X56 = k1_xboole_0
        | X57 = k1_xboole_0
        | ~ v1_funct_1(X58)
        | ~ v1_funct_2(X58,X56,X57)
        | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57))) )
      & ( v1_funct_1(esk3_3(X56,X57,X58))
        | v2_funct_1(X58)
        | X56 = k1_xboole_0
        | X57 = k1_xboole_0
        | ~ v1_funct_1(X58)
        | ~ v1_funct_2(X58,X56,X57)
        | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57))) )
      & ( v1_funct_2(esk3_3(X56,X57,X58),esk1_3(X56,X57,X58),X56)
        | v2_funct_1(X58)
        | X56 = k1_xboole_0
        | X57 = k1_xboole_0
        | ~ v1_funct_1(X58)
        | ~ v1_funct_2(X58,X56,X57)
        | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57))) )
      & ( m1_subset_1(esk3_3(X56,X57,X58),k1_zfmisc_1(k2_zfmisc_1(esk1_3(X56,X57,X58),X56)))
        | v2_funct_1(X58)
        | X56 = k1_xboole_0
        | X57 = k1_xboole_0
        | ~ v1_funct_1(X58)
        | ~ v1_funct_2(X58,X56,X57)
        | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57))) )
      & ( r2_relset_1(esk1_3(X56,X57,X58),X57,k1_partfun1(esk1_3(X56,X57,X58),X56,X56,X57,esk2_3(X56,X57,X58),X58),k1_partfun1(esk1_3(X56,X57,X58),X56,X56,X57,esk3_3(X56,X57,X58),X58))
        | v2_funct_1(X58)
        | X56 = k1_xboole_0
        | X57 = k1_xboole_0
        | ~ v1_funct_1(X58)
        | ~ v1_funct_2(X58,X56,X57)
        | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57))) )
      & ( ~ r2_relset_1(esk1_3(X56,X57,X58),X56,esk2_3(X56,X57,X58),esk3_3(X56,X57,X58))
        | v2_funct_1(X58)
        | X56 = k1_xboole_0
        | X57 = k1_xboole_0
        | ~ v1_funct_1(X58)
        | ~ v1_funct_2(X58,X56,X57)
        | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t27_funct_2])])])])])).

cnf(c_0_43,negated_conjecture,
    ( k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,esk6_0,esk5_0) = esk5_0
    | ~ m1_subset_1(k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,esk6_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])])).

cnf(c_0_44,plain,
    ( m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X6)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_45,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_47,plain,(
    ! [X53,X54,X55] :
      ( ( r2_relset_1(X53,X54,k4_relset_1(X53,X53,X53,X54,k6_partfun1(X53),X55),X55)
        | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X54))) )
      & ( r2_relset_1(X53,X54,k4_relset_1(X53,X54,X54,X54,X55,k6_partfun1(X54)),X55)
        | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X54))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_funct_2])])])).

fof(c_0_48,plain,(
    ! [X52] : k6_partfun1(X52) = k6_relat_1(X52) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

fof(c_0_49,plain,(
    ! [X45] :
      ( v1_partfun1(k6_partfun1(X45),X45)
      & m1_subset_1(k6_partfun1(X45),k1_zfmisc_1(k2_zfmisc_1(X45,X45))) ) ),
    inference(variable_rename,[status(thm)],[dt_k6_partfun1])).

cnf(c_0_50,plain,
    ( v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X6)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_51,plain,
    ( k1_partfun1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_52,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_53,negated_conjecture,
    ( k1_relat_1(esk5_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_33]),c_0_38]),c_0_39])])).

cnf(c_0_54,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_33])).

cnf(c_0_55,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_56,plain,
    ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v2_funct_1(X1)
    | k2_relset_1(X3,X2,X1) != X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_57,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_58,negated_conjecture,
    ( k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,esk6_0,esk5_0) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_39]),c_0_45]),c_0_33]),c_0_46])])).

cnf(c_0_59,negated_conjecture,
    ( v1_funct_2(esk6_0,esk4_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_60,negated_conjecture,
    ( v2_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_61,plain,
    ( r2_relset_1(X1,X2,k4_relset_1(X1,X1,X1,X2,k6_partfun1(X1),X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_62,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

fof(c_0_63,plain,(
    ! [X29,X30,X31,X32,X33,X34] :
      ( ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))
      | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))
      | k4_relset_1(X29,X30,X31,X32,X33,X34) = k5_relat_1(X33,X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_relset_1])])).

cnf(c_0_64,plain,
    ( m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_65,plain,(
    ! [X17] :
      ( k1_relat_1(k6_relat_1(X17)) = X17
      & k2_relat_1(k6_relat_1(X17)) = X17 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_66,plain,(
    ! [X18] :
      ( v1_relat_1(k6_relat_1(X18))
      & v2_funct_1(k6_relat_1(X18)) ) ),
    inference(variable_rename,[status(thm)],[fc4_funct_1])).

cnf(c_0_67,plain,
    ( v1_funct_1(k5_relat_1(X1,X2))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_68,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_69,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k2_relat_1(esk5_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_39]),c_0_54])])).

cnf(c_0_70,negated_conjecture,
    ( v1_funct_2(esk5_0,esk4_0,k2_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_53]),c_0_39]),c_0_54])])).

fof(c_0_71,plain,(
    ! [X26,X27,X28] :
      ( ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
      | k2_relset_1(X26,X27,X28) = k2_relat_1(X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_72,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v1_funct_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_56])).

cnf(c_0_73,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r2_relset_1(esk4_0,esk4_0,X1,esk6_0)
    | ~ v1_funct_2(X1,esk4_0,esk4_0)
    | ~ r2_relset_1(esk4_0,esk4_0,k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,X1,esk5_0),esk5_0)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59]),c_0_38]),c_0_45]),c_0_39]),c_0_60]),c_0_46]),c_0_33])])).

cnf(c_0_74,plain,
    ( r2_relset_1(X1,X2,k4_relset_1(X1,X1,X1,X2,k6_relat_1(X1),X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_75,plain,
    ( k4_relset_1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_76,plain,
    ( m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(rw,[status(thm)],[c_0_64,c_0_62])).

cnf(c_0_77,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_78,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_79,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_80,plain,
    ( v1_funct_1(k5_relat_1(X1,X2))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(spm,[status(thm)],[c_0_67,c_0_52])).

fof(c_0_81,plain,(
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

cnf(c_0_82,negated_conjecture,
    ( v1_funct_1(k2_funct_1(esk5_0))
    | k2_relset_1(esk4_0,k2_relat_1(esk5_0),esk5_0) != k2_relat_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70]),c_0_39]),c_0_60])])).

cnf(c_0_83,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_84,negated_conjecture,
    ( v1_relat_1(k2_funct_1(esk5_0))
    | k2_relset_1(esk4_0,k2_relat_1(esk5_0),esk5_0) != k2_relat_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_69]),c_0_70]),c_0_39]),c_0_60])])).

fof(c_0_85,plain,(
    ! [X7,X8] :
      ( ( r1_tarski(X7,X8)
        | X7 != X8 )
      & ( r1_tarski(X8,X7)
        | X7 != X8 )
      & ( ~ r1_tarski(X7,X8)
        | ~ r1_tarski(X8,X7)
        | X7 = X8 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_86,plain,(
    ! [X12,X13] :
      ( ( ~ m1_subset_1(X12,k1_zfmisc_1(X13))
        | r1_tarski(X12,X13) )
      & ( ~ r1_tarski(X12,X13)
        | m1_subset_1(X12,k1_zfmisc_1(X13)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_87,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r2_relset_1(esk4_0,esk4_0,X1,esk6_0)
    | ~ v1_funct_2(X1,esk4_0,esk4_0)
    | ~ r2_relset_1(esk4_0,esk4_0,k5_relat_1(X1,esk5_0),esk5_0)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_51]),c_0_39]),c_0_33])])).

cnf(c_0_88,plain,
    ( r2_relset_1(X1,X2,k5_relat_1(k6_relat_1(X1),X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_76])])).

cnf(c_0_89,plain,
    ( v1_funct_2(k6_relat_1(X1),X1,X1)
    | ~ v1_funct_1(k6_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_77]),c_0_78]),c_0_79])])).

cnf(c_0_90,negated_conjecture,
    ( v1_funct_1(k5_relat_1(esk5_0,X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_33]),c_0_39])])).

cnf(c_0_91,plain,
    ( k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_92,negated_conjecture,
    ( v1_funct_1(k2_funct_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_69])])).

cnf(c_0_93,negated_conjecture,
    ( v1_relat_1(k2_funct_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_83]),c_0_69])])).

cnf(c_0_94,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_95,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_96,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r2_relset_1(esk4_0,esk4_0,k6_relat_1(esk4_0),esk6_0)
    | ~ v1_funct_1(k6_relat_1(esk4_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_76]),c_0_33])]),c_0_89])).

cnf(c_0_97,negated_conjecture,
    ( v1_funct_1(k6_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_53]),c_0_92]),c_0_93]),c_0_39]),c_0_60]),c_0_54])])).

cnf(c_0_98,plain,
    ( X1 = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_99,negated_conjecture,
    ( k1_relat_1(esk6_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_46]),c_0_59]),c_0_45])])).

cnf(c_0_100,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_46])).

cnf(c_0_101,negated_conjecture,
    ( ~ r2_relset_1(esk4_0,esk4_0,esk6_0,k6_partfun1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_102,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r2_relset_1(esk4_0,esk4_0,k6_relat_1(esk4_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_96,c_0_97])])).

cnf(c_0_103,negated_conjecture,
    ( r2_relset_1(esk4_0,esk4_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_32,c_0_58])).

fof(c_0_104,plain,(
    ! [X9,X10] :
      ( ( k2_zfmisc_1(X9,X10) != k1_xboole_0
        | X9 = k1_xboole_0
        | X10 = k1_xboole_0 )
      & ( X9 != k1_xboole_0
        | k2_zfmisc_1(X9,X10) = k1_xboole_0 )
      & ( X10 != k1_xboole_0
        | k2_zfmisc_1(X9,X10) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_105,plain,
    ( X1 = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_98,c_0_95])).

cnf(c_0_106,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k2_relat_1(esk6_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_99]),c_0_45]),c_0_100])])).

cnf(c_0_107,negated_conjecture,
    ( ~ r2_relset_1(esk4_0,esk4_0,esk6_0,k6_relat_1(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_101,c_0_62])).

cnf(c_0_108,negated_conjecture,
    ( k6_relat_1(esk4_0) = esk6_0
    | esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_102]),c_0_46]),c_0_76])])).

cnf(c_0_109,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r2_relset_1(esk4_0,esk4_0,esk6_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_58]),c_0_59]),c_0_103]),c_0_45]),c_0_46])])).

cnf(c_0_110,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_104])).

fof(c_0_111,plain,(
    ! [X11] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X11)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_112,negated_conjecture,
    ( k2_zfmisc_1(esk4_0,k2_relat_1(esk6_0)) = esk6_0
    | ~ m1_subset_1(k2_zfmisc_1(esk4_0,k2_relat_1(esk6_0)),k1_zfmisc_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_105,c_0_106])).

cnf(c_0_113,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_108]),c_0_109])).

cnf(c_0_114,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_110])).

cnf(c_0_115,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_111])).

cnf(c_0_116,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t81_relat_1])).

cnf(c_0_117,negated_conjecture,
    ( esk6_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_112,c_0_113]),c_0_114]),c_0_113]),c_0_114]),c_0_115])])).

cnf(c_0_118,plain,
    ( r2_relset_1(X3,X4,X1,X2)
    | X1 != X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_119,negated_conjecture,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_107,c_0_113]),c_0_113]),c_0_113]),c_0_116]),c_0_117])).

cnf(c_0_120,plain,
    ( r2_relset_1(X1,X2,X3,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(er,[status(thm)],[c_0_118])).

cnf(c_0_121,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_120]),c_0_114]),c_0_115])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:45:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.19/0.34  # No SInE strategy applied
% 0.19/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.41  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.19/0.41  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.19/0.41  #
% 0.19/0.41  # Preprocessing time       : 0.030 s
% 0.19/0.41  # Presaturation interreduction done
% 0.19/0.41  
% 0.19/0.41  # Proof found!
% 0.19/0.41  # SZS status Theorem
% 0.19/0.41  # SZS output start CNFRefutation
% 0.19/0.41  fof(t76_funct_2, conjecture, ![X1, X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X1))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>((r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X3,X2),X2)&v2_funct_1(X2))=>r2_relset_1(X1,X1,X3,k6_partfun1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_funct_2)).
% 0.19/0.41  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.19/0.41  fof(t67_funct_2, axiom, ![X1, X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>k1_relset_1(X1,X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_2)).
% 0.19/0.41  fof(redefinition_r2_relset_1, axiom, ![X1, X2, X3, X4]:((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_relset_1(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 0.19/0.41  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.19/0.41  fof(dt_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>(v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))&m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 0.19/0.41  fof(redefinition_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>k1_partfun1(X1,X2,X3,X4,X5,X6)=k5_relat_1(X5,X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 0.19/0.41  fof(t3_funct_2, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 0.19/0.41  fof(t31_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 0.19/0.41  fof(t27_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>~(((X1!=k1_xboole_0&X2!=k1_xboole_0)&~((v2_funct_1(X3)<=>![X4, X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X4,X1))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,X4,X1))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X1))))=>(r2_relset_1(X4,X2,k1_partfun1(X4,X1,X1,X2,X5,X3),k1_partfun1(X4,X1,X1,X2,X6,X3))=>r2_relset_1(X4,X1,X5,X6))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_funct_2)).
% 0.19/0.41  fof(t23_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(r2_relset_1(X1,X2,k4_relset_1(X1,X1,X1,X2,k6_partfun1(X1),X3),X3)&r2_relset_1(X1,X2,k4_relset_1(X1,X2,X2,X2,X3,k6_partfun1(X2)),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_funct_2)).
% 0.19/0.41  fof(redefinition_k6_partfun1, axiom, ![X1]:k6_partfun1(X1)=k6_relat_1(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 0.19/0.41  fof(dt_k6_partfun1, axiom, ![X1]:(v1_partfun1(k6_partfun1(X1),X1)&m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 0.19/0.41  fof(redefinition_k4_relset_1, axiom, ![X1, X2, X3, X4, X5, X6]:((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>k4_relset_1(X1,X2,X3,X4,X5,X6)=k5_relat_1(X5,X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 0.19/0.41  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 0.19/0.41  fof(fc4_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v2_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 0.19/0.41  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.19/0.41  fof(t61_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(k1_relat_1(X1))&k5_relat_1(k2_funct_1(X1),X1)=k6_relat_1(k2_relat_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 0.19/0.41  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.41  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.41  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.19/0.41  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.19/0.41  fof(t81_relat_1, axiom, k6_relat_1(k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 0.19/0.41  fof(c_0_23, negated_conjecture, ~(![X1, X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X1))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>((r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X3,X2),X2)&v2_funct_1(X2))=>r2_relset_1(X1,X1,X3,k6_partfun1(X1)))))), inference(assume_negation,[status(cth)],[t76_funct_2])).
% 0.19/0.41  fof(c_0_24, plain, ![X23, X24, X25]:(~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))|k1_relset_1(X23,X24,X25)=k1_relat_1(X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.19/0.41  fof(c_0_25, plain, ![X69, X70]:(~v1_funct_1(X70)|~v1_funct_2(X70,X69,X69)|~m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(X69,X69)))|k1_relset_1(X69,X69,X70)=X69), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_funct_2])])).
% 0.19/0.41  fof(c_0_26, plain, ![X35, X36, X37, X38]:((~r2_relset_1(X35,X36,X37,X38)|X37=X38|(~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))))&(X37!=X38|r2_relset_1(X35,X36,X37,X38)|(~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).
% 0.19/0.41  fof(c_0_27, negated_conjecture, (((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,esk4_0,esk4_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0))))&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,esk4_0,esk4_0))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0))))&((r2_relset_1(esk4_0,esk4_0,k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,esk6_0,esk5_0),esk5_0)&v2_funct_1(esk5_0))&~r2_relset_1(esk4_0,esk4_0,esk6_0,k6_partfun1(esk4_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).
% 0.19/0.41  cnf(c_0_28, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.41  cnf(c_0_29, plain, (k1_relset_1(X2,X2,X1)=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.41  fof(c_0_30, plain, ![X20, X21, X22]:(~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))|v1_relat_1(X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.19/0.41  cnf(c_0_31, plain, (X3=X4|~r2_relset_1(X1,X2,X3,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.41  cnf(c_0_32, negated_conjecture, (r2_relset_1(esk4_0,esk4_0,k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,esk6_0,esk5_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.41  cnf(c_0_33, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.41  fof(c_0_34, plain, ![X39, X40, X41, X42, X43, X44]:((v1_funct_1(k1_partfun1(X39,X40,X41,X42,X43,X44))|(~v1_funct_1(X43)|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))|~v1_funct_1(X44)|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))))&(m1_subset_1(k1_partfun1(X39,X40,X41,X42,X43,X44),k1_zfmisc_1(k2_zfmisc_1(X39,X42)))|(~v1_funct_1(X43)|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))|~v1_funct_1(X44)|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).
% 0.19/0.41  fof(c_0_35, plain, ![X46, X47, X48, X49, X50, X51]:(~v1_funct_1(X50)|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X46,X47)))|~v1_funct_1(X51)|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X48,X49)))|k1_partfun1(X46,X47,X48,X49,X50,X51)=k5_relat_1(X50,X51)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).
% 0.19/0.41  fof(c_0_36, plain, ![X68]:(((v1_funct_1(X68)|(~v1_relat_1(X68)|~v1_funct_1(X68)))&(v1_funct_2(X68,k1_relat_1(X68),k2_relat_1(X68))|(~v1_relat_1(X68)|~v1_funct_1(X68))))&(m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X68),k2_relat_1(X68))))|(~v1_relat_1(X68)|~v1_funct_1(X68)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).
% 0.19/0.41  cnf(c_0_37, plain, (X1=k1_relat_1(X2)|~v1_funct_2(X2,X1,X1)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.19/0.41  cnf(c_0_38, negated_conjecture, (v1_funct_2(esk5_0,esk4_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.41  cnf(c_0_39, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.41  cnf(c_0_40, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.41  fof(c_0_41, plain, ![X65, X66, X67]:(((v1_funct_1(k2_funct_1(X67))|(~v2_funct_1(X67)|k2_relset_1(X65,X66,X67)!=X66)|(~v1_funct_1(X67)|~v1_funct_2(X67,X65,X66)|~m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(X65,X66)))))&(v1_funct_2(k2_funct_1(X67),X66,X65)|(~v2_funct_1(X67)|k2_relset_1(X65,X66,X67)!=X66)|(~v1_funct_1(X67)|~v1_funct_2(X67,X65,X66)|~m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(X65,X66))))))&(m1_subset_1(k2_funct_1(X67),k1_zfmisc_1(k2_zfmisc_1(X66,X65)))|(~v2_funct_1(X67)|k2_relset_1(X65,X66,X67)!=X66)|(~v1_funct_1(X67)|~v1_funct_2(X67,X65,X66)|~m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(X65,X66)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_funct_2])])])).
% 0.19/0.41  fof(c_0_42, plain, ![X56, X57, X58, X59, X60, X61]:((~v2_funct_1(X58)|(~v1_funct_1(X60)|~v1_funct_2(X60,X59,X56)|~m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X59,X56)))|(~v1_funct_1(X61)|~v1_funct_2(X61,X59,X56)|~m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X59,X56)))|(~r2_relset_1(X59,X57,k1_partfun1(X59,X56,X56,X57,X60,X58),k1_partfun1(X59,X56,X56,X57,X61,X58))|r2_relset_1(X59,X56,X60,X61))))|(X56=k1_xboole_0|X57=k1_xboole_0)|(~v1_funct_1(X58)|~v1_funct_2(X58,X56,X57)|~m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57)))))&((((v1_funct_1(esk2_3(X56,X57,X58))|v2_funct_1(X58)|(X56=k1_xboole_0|X57=k1_xboole_0)|(~v1_funct_1(X58)|~v1_funct_2(X58,X56,X57)|~m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57)))))&(v1_funct_2(esk2_3(X56,X57,X58),esk1_3(X56,X57,X58),X56)|v2_funct_1(X58)|(X56=k1_xboole_0|X57=k1_xboole_0)|(~v1_funct_1(X58)|~v1_funct_2(X58,X56,X57)|~m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57))))))&(m1_subset_1(esk2_3(X56,X57,X58),k1_zfmisc_1(k2_zfmisc_1(esk1_3(X56,X57,X58),X56)))|v2_funct_1(X58)|(X56=k1_xboole_0|X57=k1_xboole_0)|(~v1_funct_1(X58)|~v1_funct_2(X58,X56,X57)|~m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57))))))&((((v1_funct_1(esk3_3(X56,X57,X58))|v2_funct_1(X58)|(X56=k1_xboole_0|X57=k1_xboole_0)|(~v1_funct_1(X58)|~v1_funct_2(X58,X56,X57)|~m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57)))))&(v1_funct_2(esk3_3(X56,X57,X58),esk1_3(X56,X57,X58),X56)|v2_funct_1(X58)|(X56=k1_xboole_0|X57=k1_xboole_0)|(~v1_funct_1(X58)|~v1_funct_2(X58,X56,X57)|~m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57))))))&(m1_subset_1(esk3_3(X56,X57,X58),k1_zfmisc_1(k2_zfmisc_1(esk1_3(X56,X57,X58),X56)))|v2_funct_1(X58)|(X56=k1_xboole_0|X57=k1_xboole_0)|(~v1_funct_1(X58)|~v1_funct_2(X58,X56,X57)|~m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57))))))&((r2_relset_1(esk1_3(X56,X57,X58),X57,k1_partfun1(esk1_3(X56,X57,X58),X56,X56,X57,esk2_3(X56,X57,X58),X58),k1_partfun1(esk1_3(X56,X57,X58),X56,X56,X57,esk3_3(X56,X57,X58),X58))|v2_funct_1(X58)|(X56=k1_xboole_0|X57=k1_xboole_0)|(~v1_funct_1(X58)|~v1_funct_2(X58,X56,X57)|~m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57)))))&(~r2_relset_1(esk1_3(X56,X57,X58),X56,esk2_3(X56,X57,X58),esk3_3(X56,X57,X58))|v2_funct_1(X58)|(X56=k1_xboole_0|X57=k1_xboole_0)|(~v1_funct_1(X58)|~v1_funct_2(X58,X56,X57)|~m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57))))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t27_funct_2])])])])])).
% 0.19/0.41  cnf(c_0_43, negated_conjecture, (k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,esk6_0,esk5_0)=esk5_0|~m1_subset_1(k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,esk6_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])])).
% 0.19/0.41  cnf(c_0_44, plain, (m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X6)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.41  cnf(c_0_45, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.41  cnf(c_0_46, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.41  fof(c_0_47, plain, ![X53, X54, X55]:((r2_relset_1(X53,X54,k4_relset_1(X53,X53,X53,X54,k6_partfun1(X53),X55),X55)|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X54))))&(r2_relset_1(X53,X54,k4_relset_1(X53,X54,X54,X54,X55,k6_partfun1(X54)),X55)|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X54))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_funct_2])])])).
% 0.19/0.41  fof(c_0_48, plain, ![X52]:k6_partfun1(X52)=k6_relat_1(X52), inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).
% 0.19/0.41  fof(c_0_49, plain, ![X45]:(v1_partfun1(k6_partfun1(X45),X45)&m1_subset_1(k6_partfun1(X45),k1_zfmisc_1(k2_zfmisc_1(X45,X45)))), inference(variable_rename,[status(thm)],[dt_k6_partfun1])).
% 0.19/0.41  cnf(c_0_50, plain, (v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X6)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.41  cnf(c_0_51, plain, (k1_partfun1(X2,X3,X5,X6,X1,X4)=k5_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.41  cnf(c_0_52, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.41  cnf(c_0_53, negated_conjecture, (k1_relat_1(esk5_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_33]), c_0_38]), c_0_39])])).
% 0.19/0.41  cnf(c_0_54, negated_conjecture, (v1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_40, c_0_33])).
% 0.19/0.41  cnf(c_0_55, plain, (v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.41  cnf(c_0_56, plain, (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v2_funct_1(X1)|k2_relset_1(X3,X2,X1)!=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.41  cnf(c_0_57, plain, (r2_relset_1(X3,X4,X2,X5)|X4=k1_xboole_0|X6=k1_xboole_0|~v2_funct_1(X1)|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X4)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_1(X5)|~v1_funct_2(X5,X3,X4)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~r2_relset_1(X3,X6,k1_partfun1(X3,X4,X4,X6,X2,X1),k1_partfun1(X3,X4,X4,X6,X5,X1))|~v1_funct_1(X1)|~v1_funct_2(X1,X4,X6)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X6)))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.41  cnf(c_0_58, negated_conjecture, (k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,esk6_0,esk5_0)=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_39]), c_0_45]), c_0_33]), c_0_46])])).
% 0.19/0.41  cnf(c_0_59, negated_conjecture, (v1_funct_2(esk6_0,esk4_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.41  cnf(c_0_60, negated_conjecture, (v2_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.41  cnf(c_0_61, plain, (r2_relset_1(X1,X2,k4_relset_1(X1,X1,X1,X2,k6_partfun1(X1),X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.41  cnf(c_0_62, plain, (k6_partfun1(X1)=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.41  fof(c_0_63, plain, ![X29, X30, X31, X32, X33, X34]:(~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))|k4_relset_1(X29,X30,X31,X32,X33,X34)=k5_relat_1(X33,X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_relset_1])])).
% 0.19/0.41  cnf(c_0_64, plain, (m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.19/0.41  fof(c_0_65, plain, ![X17]:(k1_relat_1(k6_relat_1(X17))=X17&k2_relat_1(k6_relat_1(X17))=X17), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.19/0.41  fof(c_0_66, plain, ![X18]:(v1_relat_1(k6_relat_1(X18))&v2_funct_1(k6_relat_1(X18))), inference(variable_rename,[status(thm)],[fc4_funct_1])).
% 0.19/0.41  cnf(c_0_67, plain, (v1_funct_1(k5_relat_1(X1,X2))|~v1_funct_1(X2)|~v1_funct_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.19/0.41  cnf(c_0_68, plain, (v1_funct_1(k2_funct_1(X1))|~v2_funct_1(X1)|k2_relset_1(X2,X3,X1)!=X3|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.41  cnf(c_0_69, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k2_relat_1(esk5_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_39]), c_0_54])])).
% 0.19/0.41  cnf(c_0_70, negated_conjecture, (v1_funct_2(esk5_0,esk4_0,k2_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_53]), c_0_39]), c_0_54])])).
% 0.19/0.41  fof(c_0_71, plain, ![X26, X27, X28]:(~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))|k2_relset_1(X26,X27,X28)=k2_relat_1(X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.19/0.41  cnf(c_0_72, plain, (v1_relat_1(k2_funct_1(X1))|k2_relset_1(X2,X3,X1)!=X3|~v1_funct_2(X1,X2,X3)|~v1_funct_1(X1)|~v2_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(spm,[status(thm)],[c_0_40, c_0_56])).
% 0.19/0.41  cnf(c_0_73, negated_conjecture, (esk4_0=k1_xboole_0|r2_relset_1(esk4_0,esk4_0,X1,esk6_0)|~v1_funct_2(X1,esk4_0,esk4_0)|~r2_relset_1(esk4_0,esk4_0,k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,X1,esk5_0),esk5_0)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59]), c_0_38]), c_0_45]), c_0_39]), c_0_60]), c_0_46]), c_0_33])])).
% 0.19/0.41  cnf(c_0_74, plain, (r2_relset_1(X1,X2,k4_relset_1(X1,X1,X1,X2,k6_relat_1(X1),X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(rw,[status(thm)],[c_0_61, c_0_62])).
% 0.19/0.41  cnf(c_0_75, plain, (k4_relset_1(X2,X3,X5,X6,X1,X4)=k5_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.19/0.41  cnf(c_0_76, plain, (m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(rw,[status(thm)],[c_0_64, c_0_62])).
% 0.19/0.41  cnf(c_0_77, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.19/0.41  cnf(c_0_78, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.19/0.41  cnf(c_0_79, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.19/0.41  cnf(c_0_80, plain, (v1_funct_1(k5_relat_1(X1,X2))|~v1_funct_1(X2)|~v1_funct_1(X1)|~v1_relat_1(X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(spm,[status(thm)],[c_0_67, c_0_52])).
% 0.19/0.41  fof(c_0_81, plain, ![X19]:((k5_relat_1(X19,k2_funct_1(X19))=k6_relat_1(k1_relat_1(X19))|~v2_funct_1(X19)|(~v1_relat_1(X19)|~v1_funct_1(X19)))&(k5_relat_1(k2_funct_1(X19),X19)=k6_relat_1(k2_relat_1(X19))|~v2_funct_1(X19)|(~v1_relat_1(X19)|~v1_funct_1(X19)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_funct_1])])])).
% 0.19/0.41  cnf(c_0_82, negated_conjecture, (v1_funct_1(k2_funct_1(esk5_0))|k2_relset_1(esk4_0,k2_relat_1(esk5_0),esk5_0)!=k2_relat_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_70]), c_0_39]), c_0_60])])).
% 0.19/0.41  cnf(c_0_83, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.19/0.41  cnf(c_0_84, negated_conjecture, (v1_relat_1(k2_funct_1(esk5_0))|k2_relset_1(esk4_0,k2_relat_1(esk5_0),esk5_0)!=k2_relat_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_69]), c_0_70]), c_0_39]), c_0_60])])).
% 0.19/0.41  fof(c_0_85, plain, ![X7, X8]:(((r1_tarski(X7,X8)|X7!=X8)&(r1_tarski(X8,X7)|X7!=X8))&(~r1_tarski(X7,X8)|~r1_tarski(X8,X7)|X7=X8)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.41  fof(c_0_86, plain, ![X12, X13]:((~m1_subset_1(X12,k1_zfmisc_1(X13))|r1_tarski(X12,X13))&(~r1_tarski(X12,X13)|m1_subset_1(X12,k1_zfmisc_1(X13)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.41  cnf(c_0_87, negated_conjecture, (esk4_0=k1_xboole_0|r2_relset_1(esk4_0,esk4_0,X1,esk6_0)|~v1_funct_2(X1,esk4_0,esk4_0)|~r2_relset_1(esk4_0,esk4_0,k5_relat_1(X1,esk5_0),esk5_0)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_51]), c_0_39]), c_0_33])])).
% 0.19/0.41  cnf(c_0_88, plain, (r2_relset_1(X1,X2,k5_relat_1(k6_relat_1(X1),X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_76])])).
% 0.19/0.41  cnf(c_0_89, plain, (v1_funct_2(k6_relat_1(X1),X1,X1)|~v1_funct_1(k6_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_77]), c_0_78]), c_0_79])])).
% 0.19/0.41  cnf(c_0_90, negated_conjecture, (v1_funct_1(k5_relat_1(esk5_0,X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_33]), c_0_39])])).
% 0.19/0.41  cnf(c_0_91, plain, (k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(k1_relat_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.19/0.41  cnf(c_0_92, negated_conjecture, (v1_funct_1(k2_funct_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_69])])).
% 0.19/0.41  cnf(c_0_93, negated_conjecture, (v1_relat_1(k2_funct_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_83]), c_0_69])])).
% 0.19/0.41  cnf(c_0_94, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_85])).
% 0.19/0.41  cnf(c_0_95, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_86])).
% 0.19/0.41  cnf(c_0_96, negated_conjecture, (esk4_0=k1_xboole_0|r2_relset_1(esk4_0,esk4_0,k6_relat_1(esk4_0),esk6_0)|~v1_funct_1(k6_relat_1(esk4_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_76]), c_0_33])]), c_0_89])).
% 0.19/0.41  cnf(c_0_97, negated_conjecture, (v1_funct_1(k6_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_91]), c_0_53]), c_0_92]), c_0_93]), c_0_39]), c_0_60]), c_0_54])])).
% 0.19/0.41  cnf(c_0_98, plain, (X1=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_94, c_0_95])).
% 0.19/0.41  cnf(c_0_99, negated_conjecture, (k1_relat_1(esk6_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_46]), c_0_59]), c_0_45])])).
% 0.19/0.41  cnf(c_0_100, negated_conjecture, (v1_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_40, c_0_46])).
% 0.19/0.41  cnf(c_0_101, negated_conjecture, (~r2_relset_1(esk4_0,esk4_0,esk6_0,k6_partfun1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.41  cnf(c_0_102, negated_conjecture, (esk4_0=k1_xboole_0|r2_relset_1(esk4_0,esk4_0,k6_relat_1(esk4_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_96, c_0_97])])).
% 0.19/0.41  cnf(c_0_103, negated_conjecture, (r2_relset_1(esk4_0,esk4_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[c_0_32, c_0_58])).
% 0.19/0.41  fof(c_0_104, plain, ![X9, X10]:((k2_zfmisc_1(X9,X10)!=k1_xboole_0|(X9=k1_xboole_0|X10=k1_xboole_0))&((X9!=k1_xboole_0|k2_zfmisc_1(X9,X10)=k1_xboole_0)&(X10!=k1_xboole_0|k2_zfmisc_1(X9,X10)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.19/0.41  cnf(c_0_105, plain, (X1=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_98, c_0_95])).
% 0.19/0.41  cnf(c_0_106, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k2_relat_1(esk6_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_99]), c_0_45]), c_0_100])])).
% 0.19/0.41  cnf(c_0_107, negated_conjecture, (~r2_relset_1(esk4_0,esk4_0,esk6_0,k6_relat_1(esk4_0))), inference(rw,[status(thm)],[c_0_101, c_0_62])).
% 0.19/0.41  cnf(c_0_108, negated_conjecture, (k6_relat_1(esk4_0)=esk6_0|esk4_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_102]), c_0_46]), c_0_76])])).
% 0.19/0.41  cnf(c_0_109, negated_conjecture, (esk4_0=k1_xboole_0|r2_relset_1(esk4_0,esk4_0,esk6_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_58]), c_0_59]), c_0_103]), c_0_45]), c_0_46])])).
% 0.19/0.41  cnf(c_0_110, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_104])).
% 0.19/0.41  fof(c_0_111, plain, ![X11]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X11)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.19/0.41  cnf(c_0_112, negated_conjecture, (k2_zfmisc_1(esk4_0,k2_relat_1(esk6_0))=esk6_0|~m1_subset_1(k2_zfmisc_1(esk4_0,k2_relat_1(esk6_0)),k1_zfmisc_1(esk6_0))), inference(spm,[status(thm)],[c_0_105, c_0_106])).
% 0.19/0.41  cnf(c_0_113, negated_conjecture, (esk4_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_108]), c_0_109])).
% 0.19/0.41  cnf(c_0_114, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_110])).
% 0.19/0.41  cnf(c_0_115, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_111])).
% 0.19/0.41  cnf(c_0_116, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t81_relat_1])).
% 0.19/0.41  cnf(c_0_117, negated_conjecture, (esk6_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_112, c_0_113]), c_0_114]), c_0_113]), c_0_114]), c_0_115])])).
% 0.19/0.41  cnf(c_0_118, plain, (r2_relset_1(X3,X4,X1,X2)|X1!=X2|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.41  cnf(c_0_119, negated_conjecture, (~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_107, c_0_113]), c_0_113]), c_0_113]), c_0_116]), c_0_117])).
% 0.19/0.41  cnf(c_0_120, plain, (r2_relset_1(X1,X2,X3,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(er,[status(thm)],[c_0_118])).
% 0.19/0.41  cnf(c_0_121, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_120]), c_0_114]), c_0_115])]), ['proof']).
% 0.19/0.41  # SZS output end CNFRefutation
% 0.19/0.41  # Proof object total steps             : 122
% 0.19/0.41  # Proof object clause steps            : 76
% 0.19/0.41  # Proof object formula steps           : 46
% 0.19/0.41  # Proof object conjectures             : 40
% 0.19/0.41  # Proof object clause conjectures      : 37
% 0.19/0.41  # Proof object formula conjectures     : 3
% 0.19/0.41  # Proof object initial clauses used    : 36
% 0.19/0.41  # Proof object initial formulas used   : 23
% 0.19/0.41  # Proof object generating inferences   : 31
% 0.19/0.41  # Proof object simplifying inferences  : 94
% 0.19/0.41  # Training examples: 0 positive, 0 negative
% 0.19/0.41  # Parsed axioms                        : 24
% 0.19/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.41  # Initial clauses                      : 56
% 0.19/0.41  # Removed in clause preprocessing      : 2
% 0.19/0.41  # Initial clauses in saturation        : 54
% 0.19/0.41  # Processed clauses                    : 404
% 0.19/0.41  # ...of these trivial                  : 10
% 0.19/0.41  # ...subsumed                          : 81
% 0.19/0.41  # ...remaining for further processing  : 313
% 0.19/0.41  # Other redundant clauses eliminated   : 10
% 0.19/0.41  # Clauses deleted for lack of memory   : 0
% 0.19/0.41  # Backward-subsumed                    : 42
% 0.19/0.41  # Backward-rewritten                   : 100
% 0.19/0.41  # Generated clauses                    : 650
% 0.19/0.41  # ...of the previous two non-trivial   : 614
% 0.19/0.41  # Contextual simplify-reflections      : 27
% 0.19/0.41  # Paramodulations                      : 624
% 0.19/0.41  # Factorizations                       : 16
% 0.19/0.41  # Equation resolutions                 : 10
% 0.19/0.41  # Propositional unsat checks           : 0
% 0.19/0.41  #    Propositional check models        : 0
% 0.19/0.41  #    Propositional check unsatisfiable : 0
% 0.19/0.41  #    Propositional clauses             : 0
% 0.19/0.41  #    Propositional clauses after purity: 0
% 0.19/0.41  #    Propositional unsat core size     : 0
% 0.19/0.41  #    Propositional preprocessing time  : 0.000
% 0.19/0.41  #    Propositional encoding time       : 0.000
% 0.19/0.41  #    Propositional solver time         : 0.000
% 0.19/0.41  #    Success case prop preproc time    : 0.000
% 0.19/0.41  #    Success case prop encoding time   : 0.000
% 0.19/0.41  #    Success case prop solver time     : 0.000
% 0.19/0.41  # Current number of processed clauses  : 113
% 0.19/0.41  #    Positive orientable unit clauses  : 22
% 0.19/0.41  #    Positive unorientable unit clauses: 0
% 0.19/0.41  #    Negative unit clauses             : 1
% 0.19/0.41  #    Non-unit-clauses                  : 90
% 0.19/0.41  # Current number of unprocessed clauses: 305
% 0.19/0.41  # ...number of literals in the above   : 1811
% 0.19/0.41  # Current number of archived formulas  : 0
% 0.19/0.41  # Current number of archived clauses   : 196
% 0.19/0.41  # Clause-clause subsumption calls (NU) : 6932
% 0.19/0.41  # Rec. Clause-clause subsumption calls : 1718
% 0.19/0.41  # Non-unit clause-clause subsumptions  : 148
% 0.19/0.41  # Unit Clause-clause subsumption calls : 129
% 0.19/0.41  # Rewrite failures with RHS unbound    : 0
% 0.19/0.41  # BW rewrite match attempts            : 24
% 0.19/0.41  # BW rewrite match successes           : 9
% 0.19/0.41  # Condensation attempts                : 0
% 0.19/0.41  # Condensation successes               : 0
% 0.19/0.41  # Termbank termtop insertions          : 22904
% 0.19/0.41  
% 0.19/0.41  # -------------------------------------------------
% 0.19/0.41  # User time                : 0.068 s
% 0.19/0.41  # System time              : 0.005 s
% 0.19/0.41  # Total time               : 0.074 s
% 0.19/0.41  # Maximum resident set size: 1612 pages
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:01:47 EST 2020

% Result     : Theorem 3.10s
% Output     : CNFRefutation 3.10s
% Verified   : 
% Statistics : Number of formulae       :  194 ( 909 expanded)
%              Number of clauses        :  101 ( 269 expanded)
%              Number of leaves         :   25 ( 225 expanded)
%              Depth                    :   20
%              Number of atoms          :  643 (5774 expanded)
%              Number of equality atoms :  194 ( 489 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f39])).

fof(f85,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f35])).

fof(f55,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
           => ( v2_funct_2(X3,X0)
              & v2_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
             => ( v2_funct_2(X3,X0)
                & v2_funct_1(X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f45,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f46,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f45])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
     => ( ( ~ v2_funct_2(sK4,X0)
          | ~ v2_funct_1(X2) )
        & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK4),k6_partfun1(X0))
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(sK4,X1,X0)
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ( ~ v2_funct_2(X3,X0)
              | ~ v2_funct_1(X2) )
            & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ( ~ v2_funct_2(X3,sK1)
            | ~ v2_funct_1(sK3) )
          & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,X3),k6_partfun1(sK1))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
          & v1_funct_2(X3,sK2,sK1)
          & v1_funct_1(X3) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
    ( ( ~ v2_funct_2(sK4,sK1)
      | ~ v2_funct_1(sK3) )
    & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1))
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    & v1_funct_2(sK4,sK2,sK1)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f46,f58,f57])).

fof(f97,plain,(
    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f59])).

fof(f17,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f86,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f91,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f59])).

fof(f93,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f59])).

fof(f94,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f59])).

fof(f96,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f59])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
           => ( v2_funct_1(X3)
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f43])).

fof(f89,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v2_funct_1(X3)
      | k1_xboole_0 = X2
      | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f92,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f59])).

fof(f95,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f59])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
           => k2_relset_1(X0,X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f83,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f105,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f83])).

fof(f98,plain,
    ( ~ v2_funct_2(sK4,sK1)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f59])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f8,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f18,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f87,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f100,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f74,f87])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0)
        & v1_xboole_0(X0) )
     => ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f29,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f72,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f69,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f73,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f101,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f73,f87])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v5_relat_1(k1_xboole_0,X1)
      & v4_relat_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : v5_relat_1(k1_xboole_0,X1) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f54,plain,(
    ! [X1] : v5_relat_1(k1_xboole_0,X1) ),
    inference(rectify,[],[f24])).

fof(f67,plain,(
    ! [X1] : v5_relat_1(k1_xboole_0,X1) ),
    inference(cnf_transformation,[],[f54])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f48,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f47])).

fof(f49,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f48,f49])).

fof(f61,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f5,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f99,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f68,f87])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f51])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f102,plain,(
    ! [X0] : k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f64])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1501,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_21,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_31,negated_conjecture,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_695,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) != X0
    | k6_partfun1(sK1) != X3
    | sK1 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_31])).

cnf(c_696,plain,
    ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
    inference(unflattening,[status(thm)],[c_695])).

cnf(c_26,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_704,plain,
    ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_696,c_26])).

cnf(c_1483,plain,
    ( k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_704])).

cnf(c_5319,plain,
    ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k6_partfun1(sK1)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1501,c_1483])).

cnf(c_37,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_38,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_40,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_41,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_43,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_5750,plain,
    ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5319,c_38,c_40,c_41,c_43])).

cnf(c_29,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v2_funct_1(X3)
    | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1497,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | v1_funct_2(X3,X4,X2) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | v2_funct_1(X3) = iProver_top
    | v2_funct_1(k1_partfun1(X4,X2,X2,X0,X3,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_5776,plain,
    ( sK1 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v2_funct_1(k6_partfun1(sK1)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5750,c_1497])).

cnf(c_36,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_39,plain,
    ( v1_funct_2(sK3,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_33,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_42,plain,
    ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_1496,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1502,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3053,plain,
    ( k2_relset_1(sK2,sK1,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1496,c_1502])).

cnf(c_27,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_708,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | k2_relset_1(X2,X1,X3) = X1
    | k6_partfun1(X1) != k6_partfun1(sK1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_31])).

cnf(c_709,plain,
    ( ~ v1_funct_2(X0,X1,sK1)
    | ~ v1_funct_2(X2,sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X0)
    | k1_partfun1(sK1,X1,X1,sK1,X2,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | k2_relset_1(X1,sK1,X0) = sK1
    | k6_partfun1(sK1) != k6_partfun1(sK1) ),
    inference(unflattening,[status(thm)],[c_708])).

cnf(c_788,plain,
    ( ~ v1_funct_2(X0,X1,sK1)
    | ~ v1_funct_2(X2,sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK1,X1,X1,sK1,X2,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | k2_relset_1(X1,sK1,X0) = sK1 ),
    inference(equality_resolution_simp,[status(thm)],[c_709])).

cnf(c_1482,plain,
    ( k1_partfun1(sK1,X0,X0,sK1,X1,X2) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | k2_relset_1(X0,sK1,X2) = sK1
    | v1_funct_2(X2,X0,sK1) != iProver_top
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_788])).

cnf(c_2085,plain,
    ( k2_relset_1(sK2,sK1,sK4) = sK1
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1482])).

cnf(c_1737,plain,
    ( ~ v1_funct_2(X0,sK1,sK2)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK4)
    | k1_partfun1(sK1,sK2,sK2,sK1,X0,sK4) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | k2_relset_1(sK2,sK1,sK4) = sK1 ),
    inference(instantiation,[status(thm)],[c_788])).

cnf(c_1877,plain,
    ( ~ v1_funct_2(sK3,sK1,sK2)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK4)
    | k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | k2_relset_1(sK2,sK1,sK4) = sK1 ),
    inference(instantiation,[status(thm)],[c_1737])).

cnf(c_996,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1984,plain,
    ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_996])).

cnf(c_2197,plain,
    ( k2_relset_1(sK2,sK1,sK4) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2085,c_37,c_36,c_35,c_34,c_33,c_32,c_1877,c_1984])).

cnf(c_3068,plain,
    ( k2_relat_1(sK4) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_3053,c_2197])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v5_relat_1(X0,X2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_22,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_30,negated_conjecture,
    ( ~ v2_funct_2(sK4,sK1)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_417,plain,
    ( ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) != sK1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_30])).

cnf(c_418,plain,
    ( ~ v5_relat_1(sK4,k2_relat_1(sK4))
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK4)
    | k2_relat_1(sK4) != sK1 ),
    inference(unflattening,[status(thm)],[c_417])).

cnf(c_479,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK4)
    | k2_relat_1(sK4) != X2
    | k2_relat_1(sK4) != sK1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_418])).

cnf(c_480,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK4))))
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK4)
    | k2_relat_1(sK4) != sK1 ),
    inference(unflattening,[status(thm)],[c_479])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_492,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK4))))
    | ~ v2_funct_1(sK3)
    | k2_relat_1(sK4) != sK1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_480,c_16])).

cnf(c_994,plain,
    ( ~ v2_funct_1(sK3)
    | sP0_iProver_split
    | k2_relat_1(sK4) != sK1 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_492])).

cnf(c_1486,plain,
    ( k2_relat_1(sK4) != sK1
    | v2_funct_1(sK3) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_994])).

cnf(c_3271,plain,
    ( sK1 != sK1
    | v2_funct_1(sK3) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_3068,c_1486])).

cnf(c_3278,plain,
    ( v2_funct_1(sK3) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3271])).

cnf(c_993,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK4))))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_492])).

cnf(c_1487,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK4)))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_993])).

cnf(c_3270,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(demodulation,[status(thm)],[c_3068,c_1487])).

cnf(c_3449,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_1496,c_3270])).

cnf(c_6030,plain,
    ( v2_funct_1(k6_partfun1(sK1)) != iProver_top
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5776,c_38,c_39,c_40,c_41,c_42,c_43,c_3278,c_3449])).

cnf(c_6031,plain,
    ( sK1 = k1_xboole_0
    | v2_funct_1(k6_partfun1(sK1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_6030])).

cnf(c_13,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1506,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_6036,plain,
    ( sK1 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6031,c_1506])).

cnf(c_1493,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1503,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4289,plain,
    ( v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1493,c_1503])).

cnf(c_1755,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1756,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1755])).

cnf(c_10,plain,
    ( v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_9,plain,
    ( v1_funct_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_212,plain,
    ( v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10,c_9])).

cnf(c_1868,plain,
    ( v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_212])).

cnf(c_1869,plain,
    ( v2_funct_1(sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1868])).

cnf(c_4731,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4289,c_40,c_1756,c_1869,c_3278,c_3449])).

cnf(c_6040,plain,
    ( v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6036,c_4731])).

cnf(c_14,plain,
    ( v1_relat_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_7,plain,
    ( v5_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_6,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_15,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_378,plain,
    ( ~ r1_tarski(X0,X1)
    | v1_xboole_0(X2)
    | X0 != X2
    | sK0(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_15])).

cnf(c_379,plain,
    ( ~ r1_tarski(X0,sK0(X0))
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_378])).

cnf(c_396,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | v1_xboole_0(X2)
    | k2_relat_1(X0) != X2
    | sK0(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_379])).

cnf(c_397,plain,
    ( ~ v5_relat_1(X0,sK0(k2_relat_1(X0)))
    | ~ v1_relat_1(X0)
    | v1_xboole_0(k2_relat_1(X0)) ),
    inference(unflattening,[status(thm)],[c_396])).

cnf(c_438,plain,
    ( ~ v1_relat_1(X0)
    | v1_xboole_0(k2_relat_1(X0))
    | sK0(k2_relat_1(X0)) != X1
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_397])).

cnf(c_439,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | v1_xboole_0(k2_relat_1(k1_xboole_0)) ),
    inference(unflattening,[status(thm)],[c_438])).

cnf(c_560,plain,
    ( v1_xboole_0(k2_relat_1(k1_xboole_0))
    | k6_partfun1(X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_439])).

cnf(c_8,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_562,plain,
    ( v1_xboole_0(k2_relat_1(k1_xboole_0))
    | k6_partfun1(k1_xboole_0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_560])).

cnf(c_564,plain,
    ( v1_xboole_0(k2_relat_1(k1_xboole_0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_560,c_8,c_562])).

cnf(c_1485,plain,
    ( v1_xboole_0(k2_relat_1(k1_xboole_0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_564])).

cnf(c_2,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1499,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2512,plain,
    ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_1499])).

cnf(c_2515,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2512,c_8])).

cnf(c_4290,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_1503])).

cnf(c_4622,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2515,c_4290])).

cnf(c_4841,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1485,c_4622])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6040,c_4841])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:23:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.10/0.92  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/0.92  
% 3.10/0.92  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.10/0.92  
% 3.10/0.92  ------  iProver source info
% 3.10/0.92  
% 3.10/0.92  git: date: 2020-06-30 10:37:57 +0100
% 3.10/0.92  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.10/0.92  git: non_committed_changes: false
% 3.10/0.92  git: last_make_outside_of_git: false
% 3.10/0.92  
% 3.10/0.92  ------ 
% 3.10/0.92  
% 3.10/0.92  ------ Input Options
% 3.10/0.92  
% 3.10/0.92  --out_options                           all
% 3.10/0.92  --tptp_safe_out                         true
% 3.10/0.92  --problem_path                          ""
% 3.10/0.92  --include_path                          ""
% 3.10/0.92  --clausifier                            res/vclausify_rel
% 3.10/0.92  --clausifier_options                    --mode clausify
% 3.10/0.92  --stdin                                 false
% 3.10/0.92  --stats_out                             all
% 3.10/0.92  
% 3.10/0.92  ------ General Options
% 3.10/0.92  
% 3.10/0.92  --fof                                   false
% 3.10/0.92  --time_out_real                         305.
% 3.10/0.92  --time_out_virtual                      -1.
% 3.10/0.92  --symbol_type_check                     false
% 3.10/0.92  --clausify_out                          false
% 3.10/0.92  --sig_cnt_out                           false
% 3.10/0.92  --trig_cnt_out                          false
% 3.10/0.92  --trig_cnt_out_tolerance                1.
% 3.10/0.92  --trig_cnt_out_sk_spl                   false
% 3.10/0.92  --abstr_cl_out                          false
% 3.10/0.92  
% 3.10/0.92  ------ Global Options
% 3.10/0.92  
% 3.10/0.92  --schedule                              default
% 3.10/0.92  --add_important_lit                     false
% 3.10/0.92  --prop_solver_per_cl                    1000
% 3.10/0.92  --min_unsat_core                        false
% 3.10/0.92  --soft_assumptions                      false
% 3.10/0.92  --soft_lemma_size                       3
% 3.10/0.92  --prop_impl_unit_size                   0
% 3.10/0.92  --prop_impl_unit                        []
% 3.10/0.92  --share_sel_clauses                     true
% 3.10/0.92  --reset_solvers                         false
% 3.10/0.92  --bc_imp_inh                            [conj_cone]
% 3.10/0.92  --conj_cone_tolerance                   3.
% 3.10/0.92  --extra_neg_conj                        none
% 3.10/0.92  --large_theory_mode                     true
% 3.10/0.92  --prolific_symb_bound                   200
% 3.10/0.92  --lt_threshold                          2000
% 3.10/0.92  --clause_weak_htbl                      true
% 3.10/0.92  --gc_record_bc_elim                     false
% 3.10/0.92  
% 3.10/0.92  ------ Preprocessing Options
% 3.10/0.92  
% 3.10/0.92  --preprocessing_flag                    true
% 3.10/0.92  --time_out_prep_mult                    0.1
% 3.10/0.92  --splitting_mode                        input
% 3.10/0.92  --splitting_grd                         true
% 3.10/0.92  --splitting_cvd                         false
% 3.10/0.92  --splitting_cvd_svl                     false
% 3.10/0.92  --splitting_nvd                         32
% 3.10/0.92  --sub_typing                            true
% 3.10/0.92  --prep_gs_sim                           true
% 3.10/0.92  --prep_unflatten                        true
% 3.10/0.92  --prep_res_sim                          true
% 3.10/0.92  --prep_upred                            true
% 3.10/0.92  --prep_sem_filter                       exhaustive
% 3.10/0.92  --prep_sem_filter_out                   false
% 3.10/0.92  --pred_elim                             true
% 3.10/0.92  --res_sim_input                         true
% 3.10/0.92  --eq_ax_congr_red                       true
% 3.10/0.92  --pure_diseq_elim                       true
% 3.10/0.92  --brand_transform                       false
% 3.10/0.92  --non_eq_to_eq                          false
% 3.10/0.92  --prep_def_merge                        true
% 3.10/0.92  --prep_def_merge_prop_impl              false
% 3.10/0.92  --prep_def_merge_mbd                    true
% 3.10/0.92  --prep_def_merge_tr_red                 false
% 3.10/0.92  --prep_def_merge_tr_cl                  false
% 3.10/0.92  --smt_preprocessing                     true
% 3.10/0.92  --smt_ac_axioms                         fast
% 3.10/0.92  --preprocessed_out                      false
% 3.10/0.92  --preprocessed_stats                    false
% 3.10/0.92  
% 3.10/0.92  ------ Abstraction refinement Options
% 3.10/0.92  
% 3.10/0.92  --abstr_ref                             []
% 3.10/0.92  --abstr_ref_prep                        false
% 3.10/0.92  --abstr_ref_until_sat                   false
% 3.10/0.92  --abstr_ref_sig_restrict                funpre
% 3.10/0.92  --abstr_ref_af_restrict_to_split_sk     false
% 3.10/0.92  --abstr_ref_under                       []
% 3.10/0.92  
% 3.10/0.92  ------ SAT Options
% 3.10/0.92  
% 3.10/0.92  --sat_mode                              false
% 3.10/0.92  --sat_fm_restart_options                ""
% 3.10/0.92  --sat_gr_def                            false
% 3.10/0.92  --sat_epr_types                         true
% 3.10/0.92  --sat_non_cyclic_types                  false
% 3.10/0.92  --sat_finite_models                     false
% 3.10/0.92  --sat_fm_lemmas                         false
% 3.10/0.92  --sat_fm_prep                           false
% 3.10/0.92  --sat_fm_uc_incr                        true
% 3.10/0.92  --sat_out_model                         small
% 3.10/0.92  --sat_out_clauses                       false
% 3.10/0.92  
% 3.10/0.92  ------ QBF Options
% 3.10/0.92  
% 3.10/0.92  --qbf_mode                              false
% 3.10/0.92  --qbf_elim_univ                         false
% 3.10/0.92  --qbf_dom_inst                          none
% 3.10/0.92  --qbf_dom_pre_inst                      false
% 3.10/0.92  --qbf_sk_in                             false
% 3.10/0.92  --qbf_pred_elim                         true
% 3.10/0.92  --qbf_split                             512
% 3.10/0.92  
% 3.10/0.92  ------ BMC1 Options
% 3.10/0.92  
% 3.10/0.92  --bmc1_incremental                      false
% 3.10/0.92  --bmc1_axioms                           reachable_all
% 3.10/0.92  --bmc1_min_bound                        0
% 3.10/0.92  --bmc1_max_bound                        -1
% 3.10/0.92  --bmc1_max_bound_default                -1
% 3.10/0.92  --bmc1_symbol_reachability              true
% 3.10/0.92  --bmc1_property_lemmas                  false
% 3.10/0.92  --bmc1_k_induction                      false
% 3.10/0.92  --bmc1_non_equiv_states                 false
% 3.10/0.92  --bmc1_deadlock                         false
% 3.10/0.92  --bmc1_ucm                              false
% 3.10/0.92  --bmc1_add_unsat_core                   none
% 3.10/0.92  --bmc1_unsat_core_children              false
% 3.10/0.92  --bmc1_unsat_core_extrapolate_axioms    false
% 3.10/0.92  --bmc1_out_stat                         full
% 3.10/0.92  --bmc1_ground_init                      false
% 3.10/0.92  --bmc1_pre_inst_next_state              false
% 3.10/0.92  --bmc1_pre_inst_state                   false
% 3.10/0.92  --bmc1_pre_inst_reach_state             false
% 3.10/0.92  --bmc1_out_unsat_core                   false
% 3.10/0.92  --bmc1_aig_witness_out                  false
% 3.10/0.92  --bmc1_verbose                          false
% 3.10/0.92  --bmc1_dump_clauses_tptp                false
% 3.10/0.92  --bmc1_dump_unsat_core_tptp             false
% 3.10/0.92  --bmc1_dump_file                        -
% 3.10/0.92  --bmc1_ucm_expand_uc_limit              128
% 3.10/0.92  --bmc1_ucm_n_expand_iterations          6
% 3.10/0.92  --bmc1_ucm_extend_mode                  1
% 3.10/0.92  --bmc1_ucm_init_mode                    2
% 3.10/0.92  --bmc1_ucm_cone_mode                    none
% 3.10/0.92  --bmc1_ucm_reduced_relation_type        0
% 3.10/0.92  --bmc1_ucm_relax_model                  4
% 3.10/0.92  --bmc1_ucm_full_tr_after_sat            true
% 3.10/0.92  --bmc1_ucm_expand_neg_assumptions       false
% 3.10/0.92  --bmc1_ucm_layered_model                none
% 3.10/0.92  --bmc1_ucm_max_lemma_size               10
% 3.10/0.92  
% 3.10/0.92  ------ AIG Options
% 3.10/0.92  
% 3.10/0.92  --aig_mode                              false
% 3.10/0.92  
% 3.10/0.92  ------ Instantiation Options
% 3.10/0.92  
% 3.10/0.92  --instantiation_flag                    true
% 3.10/0.92  --inst_sos_flag                         false
% 3.10/0.92  --inst_sos_phase                        true
% 3.10/0.92  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.10/0.92  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.10/0.92  --inst_lit_sel_side                     num_symb
% 3.10/0.92  --inst_solver_per_active                1400
% 3.10/0.92  --inst_solver_calls_frac                1.
% 3.10/0.92  --inst_passive_queue_type               priority_queues
% 3.10/0.92  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.10/0.92  --inst_passive_queues_freq              [25;2]
% 3.10/0.92  --inst_dismatching                      true
% 3.10/0.92  --inst_eager_unprocessed_to_passive     true
% 3.10/0.92  --inst_prop_sim_given                   true
% 3.10/0.92  --inst_prop_sim_new                     false
% 3.10/0.92  --inst_subs_new                         false
% 3.10/0.92  --inst_eq_res_simp                      false
% 3.10/0.92  --inst_subs_given                       false
% 3.10/0.92  --inst_orphan_elimination               true
% 3.10/0.92  --inst_learning_loop_flag               true
% 3.10/0.92  --inst_learning_start                   3000
% 3.10/0.92  --inst_learning_factor                  2
% 3.10/0.92  --inst_start_prop_sim_after_learn       3
% 3.10/0.92  --inst_sel_renew                        solver
% 3.10/0.92  --inst_lit_activity_flag                true
% 3.10/0.92  --inst_restr_to_given                   false
% 3.10/0.92  --inst_activity_threshold               500
% 3.10/0.92  --inst_out_proof                        true
% 3.10/0.92  
% 3.10/0.92  ------ Resolution Options
% 3.10/0.92  
% 3.10/0.92  --resolution_flag                       true
% 3.10/0.92  --res_lit_sel                           adaptive
% 3.10/0.92  --res_lit_sel_side                      none
% 3.10/0.92  --res_ordering                          kbo
% 3.10/0.92  --res_to_prop_solver                    active
% 3.10/0.92  --res_prop_simpl_new                    false
% 3.10/0.92  --res_prop_simpl_given                  true
% 3.10/0.92  --res_passive_queue_type                priority_queues
% 3.10/0.92  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.10/0.93  --res_passive_queues_freq               [15;5]
% 3.10/0.93  --res_forward_subs                      full
% 3.10/0.93  --res_backward_subs                     full
% 3.10/0.93  --res_forward_subs_resolution           true
% 3.10/0.93  --res_backward_subs_resolution          true
% 3.10/0.93  --res_orphan_elimination                true
% 3.10/0.93  --res_time_limit                        2.
% 3.10/0.93  --res_out_proof                         true
% 3.10/0.93  
% 3.10/0.93  ------ Superposition Options
% 3.10/0.93  
% 3.10/0.93  --superposition_flag                    true
% 3.10/0.93  --sup_passive_queue_type                priority_queues
% 3.10/0.93  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.10/0.93  --sup_passive_queues_freq               [8;1;4]
% 3.10/0.93  --demod_completeness_check              fast
% 3.10/0.93  --demod_use_ground                      true
% 3.10/0.93  --sup_to_prop_solver                    passive
% 3.10/0.93  --sup_prop_simpl_new                    true
% 3.10/0.93  --sup_prop_simpl_given                  true
% 3.10/0.93  --sup_fun_splitting                     false
% 3.10/0.93  --sup_smt_interval                      50000
% 3.10/0.93  
% 3.10/0.93  ------ Superposition Simplification Setup
% 3.10/0.93  
% 3.10/0.93  --sup_indices_passive                   []
% 3.10/0.93  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/0.93  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/0.93  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/0.93  --sup_full_triv                         [TrivRules;PropSubs]
% 3.10/0.93  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.10/0.93  --sup_full_bw                           [BwDemod]
% 3.10/0.93  --sup_immed_triv                        [TrivRules]
% 3.10/0.93  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.10/0.93  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.10/0.93  --sup_immed_bw_main                     []
% 3.10/0.93  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.10/0.93  --sup_input_triv                        [Unflattening;TrivRules]
% 3.10/0.93  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.10/0.93  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.10/0.93  
% 3.10/0.93  ------ Combination Options
% 3.10/0.93  
% 3.10/0.93  --comb_res_mult                         3
% 3.10/0.93  --comb_sup_mult                         2
% 3.10/0.93  --comb_inst_mult                        10
% 3.10/0.93  
% 3.10/0.93  ------ Debug Options
% 3.10/0.93  
% 3.10/0.93  --dbg_backtrace                         false
% 3.10/0.93  --dbg_dump_prop_clauses                 false
% 3.10/0.93  --dbg_dump_prop_clauses_file            -
% 3.10/0.93  --dbg_out_stat                          false
% 3.10/0.93  ------ Parsing...
% 3.10/0.93  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.10/0.93  
% 3.10/0.93  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 3.10/0.93  
% 3.10/0.93  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.10/0.93  
% 3.10/0.93  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.10/0.93  ------ Proving...
% 3.10/0.93  ------ Problem Properties 
% 3.10/0.93  
% 3.10/0.93  
% 3.10/0.93  clauses                                 30
% 3.10/0.93  conjectures                             6
% 3.10/0.93  EPR                                     6
% 3.10/0.93  Horn                                    28
% 3.10/0.93  unary                                   13
% 3.10/0.93  binary                                  6
% 3.10/0.93  lits                                    84
% 3.10/0.93  lits eq                                 16
% 3.10/0.93  fd_pure                                 0
% 3.10/0.93  fd_pseudo                               0
% 3.10/0.93  fd_cond                                 2
% 3.10/0.93  fd_pseudo_cond                          0
% 3.10/0.93  AC symbols                              0
% 3.10/0.93  
% 3.10/0.93  ------ Schedule dynamic 5 is on 
% 3.10/0.93  
% 3.10/0.93  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.10/0.93  
% 3.10/0.93  
% 3.10/0.93  ------ 
% 3.10/0.93  Current options:
% 3.10/0.93  ------ 
% 3.10/0.93  
% 3.10/0.93  ------ Input Options
% 3.10/0.93  
% 3.10/0.93  --out_options                           all
% 3.10/0.93  --tptp_safe_out                         true
% 3.10/0.93  --problem_path                          ""
% 3.10/0.93  --include_path                          ""
% 3.10/0.93  --clausifier                            res/vclausify_rel
% 3.10/0.93  --clausifier_options                    --mode clausify
% 3.10/0.93  --stdin                                 false
% 3.10/0.93  --stats_out                             all
% 3.10/0.93  
% 3.10/0.93  ------ General Options
% 3.10/0.93  
% 3.10/0.93  --fof                                   false
% 3.10/0.93  --time_out_real                         305.
% 3.10/0.93  --time_out_virtual                      -1.
% 3.10/0.93  --symbol_type_check                     false
% 3.10/0.93  --clausify_out                          false
% 3.10/0.93  --sig_cnt_out                           false
% 3.10/0.93  --trig_cnt_out                          false
% 3.10/0.93  --trig_cnt_out_tolerance                1.
% 3.10/0.93  --trig_cnt_out_sk_spl                   false
% 3.10/0.93  --abstr_cl_out                          false
% 3.10/0.93  
% 3.10/0.93  ------ Global Options
% 3.10/0.93  
% 3.10/0.93  --schedule                              default
% 3.10/0.93  --add_important_lit                     false
% 3.10/0.93  --prop_solver_per_cl                    1000
% 3.10/0.93  --min_unsat_core                        false
% 3.10/0.93  --soft_assumptions                      false
% 3.10/0.93  --soft_lemma_size                       3
% 3.10/0.93  --prop_impl_unit_size                   0
% 3.10/0.93  --prop_impl_unit                        []
% 3.10/0.93  --share_sel_clauses                     true
% 3.10/0.93  --reset_solvers                         false
% 3.10/0.93  --bc_imp_inh                            [conj_cone]
% 3.10/0.93  --conj_cone_tolerance                   3.
% 3.10/0.93  --extra_neg_conj                        none
% 3.10/0.93  --large_theory_mode                     true
% 3.10/0.93  --prolific_symb_bound                   200
% 3.10/0.93  --lt_threshold                          2000
% 3.10/0.93  --clause_weak_htbl                      true
% 3.10/0.93  --gc_record_bc_elim                     false
% 3.10/0.93  
% 3.10/0.93  ------ Preprocessing Options
% 3.10/0.93  
% 3.10/0.93  --preprocessing_flag                    true
% 3.10/0.93  --time_out_prep_mult                    0.1
% 3.10/0.93  --splitting_mode                        input
% 3.10/0.93  --splitting_grd                         true
% 3.10/0.93  --splitting_cvd                         false
% 3.10/0.93  --splitting_cvd_svl                     false
% 3.10/0.93  --splitting_nvd                         32
% 3.10/0.93  --sub_typing                            true
% 3.10/0.93  --prep_gs_sim                           true
% 3.10/0.93  --prep_unflatten                        true
% 3.10/0.93  --prep_res_sim                          true
% 3.10/0.93  --prep_upred                            true
% 3.10/0.93  --prep_sem_filter                       exhaustive
% 3.10/0.93  --prep_sem_filter_out                   false
% 3.10/0.93  --pred_elim                             true
% 3.10/0.93  --res_sim_input                         true
% 3.10/0.93  --eq_ax_congr_red                       true
% 3.10/0.93  --pure_diseq_elim                       true
% 3.10/0.93  --brand_transform                       false
% 3.10/0.93  --non_eq_to_eq                          false
% 3.10/0.93  --prep_def_merge                        true
% 3.10/0.93  --prep_def_merge_prop_impl              false
% 3.10/0.93  --prep_def_merge_mbd                    true
% 3.10/0.93  --prep_def_merge_tr_red                 false
% 3.10/0.93  --prep_def_merge_tr_cl                  false
% 3.10/0.93  --smt_preprocessing                     true
% 3.10/0.93  --smt_ac_axioms                         fast
% 3.10/0.93  --preprocessed_out                      false
% 3.10/0.93  --preprocessed_stats                    false
% 3.10/0.93  
% 3.10/0.93  ------ Abstraction refinement Options
% 3.10/0.93  
% 3.10/0.93  --abstr_ref                             []
% 3.10/0.93  --abstr_ref_prep                        false
% 3.10/0.93  --abstr_ref_until_sat                   false
% 3.10/0.93  --abstr_ref_sig_restrict                funpre
% 3.10/0.93  --abstr_ref_af_restrict_to_split_sk     false
% 3.10/0.93  --abstr_ref_under                       []
% 3.10/0.93  
% 3.10/0.93  ------ SAT Options
% 3.10/0.93  
% 3.10/0.93  --sat_mode                              false
% 3.10/0.93  --sat_fm_restart_options                ""
% 3.10/0.93  --sat_gr_def                            false
% 3.10/0.93  --sat_epr_types                         true
% 3.10/0.93  --sat_non_cyclic_types                  false
% 3.10/0.93  --sat_finite_models                     false
% 3.10/0.93  --sat_fm_lemmas                         false
% 3.10/0.93  --sat_fm_prep                           false
% 3.10/0.93  --sat_fm_uc_incr                        true
% 3.10/0.93  --sat_out_model                         small
% 3.10/0.93  --sat_out_clauses                       false
% 3.10/0.93  
% 3.10/0.93  ------ QBF Options
% 3.10/0.93  
% 3.10/0.93  --qbf_mode                              false
% 3.10/0.93  --qbf_elim_univ                         false
% 3.10/0.93  --qbf_dom_inst                          none
% 3.10/0.93  --qbf_dom_pre_inst                      false
% 3.10/0.93  --qbf_sk_in                             false
% 3.10/0.93  --qbf_pred_elim                         true
% 3.10/0.93  --qbf_split                             512
% 3.10/0.93  
% 3.10/0.93  ------ BMC1 Options
% 3.10/0.93  
% 3.10/0.93  --bmc1_incremental                      false
% 3.10/0.93  --bmc1_axioms                           reachable_all
% 3.10/0.93  --bmc1_min_bound                        0
% 3.10/0.93  --bmc1_max_bound                        -1
% 3.10/0.93  --bmc1_max_bound_default                -1
% 3.10/0.93  --bmc1_symbol_reachability              true
% 3.10/0.93  --bmc1_property_lemmas                  false
% 3.10/0.93  --bmc1_k_induction                      false
% 3.10/0.93  --bmc1_non_equiv_states                 false
% 3.10/0.93  --bmc1_deadlock                         false
% 3.10/0.93  --bmc1_ucm                              false
% 3.10/0.93  --bmc1_add_unsat_core                   none
% 3.10/0.93  --bmc1_unsat_core_children              false
% 3.10/0.93  --bmc1_unsat_core_extrapolate_axioms    false
% 3.10/0.93  --bmc1_out_stat                         full
% 3.10/0.93  --bmc1_ground_init                      false
% 3.10/0.93  --bmc1_pre_inst_next_state              false
% 3.10/0.93  --bmc1_pre_inst_state                   false
% 3.10/0.93  --bmc1_pre_inst_reach_state             false
% 3.10/0.93  --bmc1_out_unsat_core                   false
% 3.10/0.93  --bmc1_aig_witness_out                  false
% 3.10/0.93  --bmc1_verbose                          false
% 3.10/0.93  --bmc1_dump_clauses_tptp                false
% 3.10/0.93  --bmc1_dump_unsat_core_tptp             false
% 3.10/0.93  --bmc1_dump_file                        -
% 3.10/0.93  --bmc1_ucm_expand_uc_limit              128
% 3.10/0.93  --bmc1_ucm_n_expand_iterations          6
% 3.10/0.93  --bmc1_ucm_extend_mode                  1
% 3.10/0.93  --bmc1_ucm_init_mode                    2
% 3.10/0.93  --bmc1_ucm_cone_mode                    none
% 3.10/0.93  --bmc1_ucm_reduced_relation_type        0
% 3.10/0.93  --bmc1_ucm_relax_model                  4
% 3.10/0.93  --bmc1_ucm_full_tr_after_sat            true
% 3.10/0.93  --bmc1_ucm_expand_neg_assumptions       false
% 3.10/0.93  --bmc1_ucm_layered_model                none
% 3.10/0.93  --bmc1_ucm_max_lemma_size               10
% 3.10/0.93  
% 3.10/0.93  ------ AIG Options
% 3.10/0.93  
% 3.10/0.93  --aig_mode                              false
% 3.10/0.93  
% 3.10/0.93  ------ Instantiation Options
% 3.10/0.93  
% 3.10/0.93  --instantiation_flag                    true
% 3.10/0.93  --inst_sos_flag                         false
% 3.10/0.93  --inst_sos_phase                        true
% 3.10/0.93  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.10/0.93  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.10/0.93  --inst_lit_sel_side                     none
% 3.10/0.93  --inst_solver_per_active                1400
% 3.10/0.93  --inst_solver_calls_frac                1.
% 3.10/0.93  --inst_passive_queue_type               priority_queues
% 3.10/0.93  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.10/0.93  --inst_passive_queues_freq              [25;2]
% 3.10/0.93  --inst_dismatching                      true
% 3.10/0.93  --inst_eager_unprocessed_to_passive     true
% 3.10/0.93  --inst_prop_sim_given                   true
% 3.10/0.93  --inst_prop_sim_new                     false
% 3.10/0.93  --inst_subs_new                         false
% 3.10/0.93  --inst_eq_res_simp                      false
% 3.10/0.93  --inst_subs_given                       false
% 3.10/0.93  --inst_orphan_elimination               true
% 3.10/0.93  --inst_learning_loop_flag               true
% 3.10/0.93  --inst_learning_start                   3000
% 3.10/0.93  --inst_learning_factor                  2
% 3.10/0.93  --inst_start_prop_sim_after_learn       3
% 3.10/0.93  --inst_sel_renew                        solver
% 3.10/0.93  --inst_lit_activity_flag                true
% 3.10/0.93  --inst_restr_to_given                   false
% 3.10/0.93  --inst_activity_threshold               500
% 3.10/0.93  --inst_out_proof                        true
% 3.10/0.93  
% 3.10/0.93  ------ Resolution Options
% 3.10/0.93  
% 3.10/0.93  --resolution_flag                       false
% 3.10/0.93  --res_lit_sel                           adaptive
% 3.10/0.93  --res_lit_sel_side                      none
% 3.10/0.93  --res_ordering                          kbo
% 3.10/0.93  --res_to_prop_solver                    active
% 3.10/0.93  --res_prop_simpl_new                    false
% 3.10/0.93  --res_prop_simpl_given                  true
% 3.10/0.93  --res_passive_queue_type                priority_queues
% 3.10/0.93  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.10/0.93  --res_passive_queues_freq               [15;5]
% 3.10/0.93  --res_forward_subs                      full
% 3.10/0.93  --res_backward_subs                     full
% 3.10/0.93  --res_forward_subs_resolution           true
% 3.10/0.93  --res_backward_subs_resolution          true
% 3.10/0.93  --res_orphan_elimination                true
% 3.10/0.93  --res_time_limit                        2.
% 3.10/0.93  --res_out_proof                         true
% 3.10/0.93  
% 3.10/0.93  ------ Superposition Options
% 3.10/0.93  
% 3.10/0.93  --superposition_flag                    true
% 3.10/0.93  --sup_passive_queue_type                priority_queues
% 3.10/0.93  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.10/0.93  --sup_passive_queues_freq               [8;1;4]
% 3.10/0.93  --demod_completeness_check              fast
% 3.10/0.93  --demod_use_ground                      true
% 3.10/0.93  --sup_to_prop_solver                    passive
% 3.10/0.93  --sup_prop_simpl_new                    true
% 3.10/0.93  --sup_prop_simpl_given                  true
% 3.10/0.93  --sup_fun_splitting                     false
% 3.10/0.93  --sup_smt_interval                      50000
% 3.10/0.93  
% 3.10/0.93  ------ Superposition Simplification Setup
% 3.10/0.93  
% 3.10/0.93  --sup_indices_passive                   []
% 3.10/0.93  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/0.93  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/0.93  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/0.93  --sup_full_triv                         [TrivRules;PropSubs]
% 3.10/0.93  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.10/0.93  --sup_full_bw                           [BwDemod]
% 3.10/0.93  --sup_immed_triv                        [TrivRules]
% 3.10/0.93  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.10/0.93  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.10/0.93  --sup_immed_bw_main                     []
% 3.10/0.93  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.10/0.93  --sup_input_triv                        [Unflattening;TrivRules]
% 3.10/0.93  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.10/0.93  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.10/0.93  
% 3.10/0.93  ------ Combination Options
% 3.10/0.93  
% 3.10/0.93  --comb_res_mult                         3
% 3.10/0.93  --comb_sup_mult                         2
% 3.10/0.93  --comb_inst_mult                        10
% 3.10/0.93  
% 3.10/0.93  ------ Debug Options
% 3.10/0.93  
% 3.10/0.93  --dbg_backtrace                         false
% 3.10/0.93  --dbg_dump_prop_clauses                 false
% 3.10/0.93  --dbg_dump_prop_clauses_file            -
% 3.10/0.93  --dbg_out_stat                          false
% 3.10/0.93  
% 3.10/0.93  
% 3.10/0.93  
% 3.10/0.93  
% 3.10/0.93  ------ Proving...
% 3.10/0.93  
% 3.10/0.93  
% 3.10/0.93  % SZS status Theorem for theBenchmark.p
% 3.10/0.93  
% 3.10/0.93  % SZS output start CNFRefutation for theBenchmark.p
% 3.10/0.93  
% 3.10/0.93  fof(f16,axiom,(
% 3.10/0.93    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 3.10/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.93  
% 3.10/0.93  fof(f39,plain,(
% 3.10/0.93    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.10/0.93    inference(ennf_transformation,[],[f16])).
% 3.10/0.93  
% 3.10/0.93  fof(f40,plain,(
% 3.10/0.93    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.10/0.93    inference(flattening,[],[f39])).
% 3.10/0.93  
% 3.10/0.93  fof(f85,plain,(
% 3.10/0.93    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.10/0.93    inference(cnf_transformation,[],[f40])).
% 3.10/0.93  
% 3.10/0.93  fof(f14,axiom,(
% 3.10/0.93    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.10/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.93  
% 3.10/0.93  fof(f35,plain,(
% 3.10/0.93    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.10/0.93    inference(ennf_transformation,[],[f14])).
% 3.10/0.93  
% 3.10/0.93  fof(f36,plain,(
% 3.10/0.93    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.10/0.93    inference(flattening,[],[f35])).
% 3.10/0.93  
% 3.10/0.93  fof(f55,plain,(
% 3.10/0.93    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.10/0.93    inference(nnf_transformation,[],[f36])).
% 3.10/0.93  
% 3.10/0.93  fof(f80,plain,(
% 3.10/0.93    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.10/0.93    inference(cnf_transformation,[],[f55])).
% 3.10/0.93  
% 3.10/0.93  fof(f21,conjecture,(
% 3.10/0.93    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.10/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.93  
% 3.10/0.93  fof(f22,negated_conjecture,(
% 3.10/0.93    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.10/0.93    inference(negated_conjecture,[],[f21])).
% 3.10/0.93  
% 3.10/0.93  fof(f45,plain,(
% 3.10/0.93    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.10/0.93    inference(ennf_transformation,[],[f22])).
% 3.10/0.93  
% 3.10/0.93  fof(f46,plain,(
% 3.10/0.93    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.10/0.93    inference(flattening,[],[f45])).
% 3.10/0.93  
% 3.10/0.93  fof(f58,plain,(
% 3.10/0.93    ( ! [X2,X0,X1] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((~v2_funct_2(sK4,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK4),k6_partfun1(X0)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK4,X1,X0) & v1_funct_1(sK4))) )),
% 3.10/0.93    introduced(choice_axiom,[])).
% 3.10/0.93  
% 3.10/0.93  fof(f57,plain,(
% 3.10/0.93    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK1) | ~v2_funct_1(sK3)) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,X3),k6_partfun1(sK1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(X3,sK2,sK1) & v1_funct_1(X3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 3.10/0.93    introduced(choice_axiom,[])).
% 3.10/0.93  
% 3.10/0.93  fof(f59,plain,(
% 3.10/0.93    ((~v2_funct_2(sK4,sK1) | ~v2_funct_1(sK3)) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 3.10/0.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f46,f58,f57])).
% 3.10/0.93  
% 3.10/0.93  fof(f97,plain,(
% 3.10/0.93    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1))),
% 3.10/0.93    inference(cnf_transformation,[],[f59])).
% 3.10/0.93  
% 3.10/0.93  fof(f17,axiom,(
% 3.10/0.93    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 3.10/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.93  
% 3.10/0.93  fof(f23,plain,(
% 3.10/0.93    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.10/0.93    inference(pure_predicate_removal,[],[f17])).
% 3.10/0.93  
% 3.10/0.93  fof(f86,plain,(
% 3.10/0.93    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.10/0.93    inference(cnf_transformation,[],[f23])).
% 3.10/0.93  
% 3.10/0.93  fof(f91,plain,(
% 3.10/0.93    v1_funct_1(sK3)),
% 3.10/0.93    inference(cnf_transformation,[],[f59])).
% 3.10/0.93  
% 3.10/0.93  fof(f93,plain,(
% 3.10/0.93    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 3.10/0.93    inference(cnf_transformation,[],[f59])).
% 3.10/0.93  
% 3.10/0.93  fof(f94,plain,(
% 3.10/0.93    v1_funct_1(sK4)),
% 3.10/0.93    inference(cnf_transformation,[],[f59])).
% 3.10/0.93  
% 3.10/0.93  fof(f96,plain,(
% 3.10/0.93    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 3.10/0.93    inference(cnf_transformation,[],[f59])).
% 3.10/0.93  
% 3.10/0.93  fof(f20,axiom,(
% 3.10/0.93    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 3.10/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.93  
% 3.10/0.93  fof(f43,plain,(
% 3.10/0.93    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.10/0.93    inference(ennf_transformation,[],[f20])).
% 3.10/0.93  
% 3.10/0.93  fof(f44,plain,(
% 3.10/0.93    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.10/0.93    inference(flattening,[],[f43])).
% 3.10/0.93  
% 3.10/0.93  fof(f89,plain,(
% 3.10/0.93    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X3) | k1_xboole_0 = X2 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.10/0.93    inference(cnf_transformation,[],[f44])).
% 3.10/0.93  
% 3.10/0.93  fof(f92,plain,(
% 3.10/0.93    v1_funct_2(sK3,sK1,sK2)),
% 3.10/0.93    inference(cnf_transformation,[],[f59])).
% 3.10/0.93  
% 3.10/0.93  fof(f95,plain,(
% 3.10/0.93    v1_funct_2(sK4,sK2,sK1)),
% 3.10/0.93    inference(cnf_transformation,[],[f59])).
% 3.10/0.93  
% 3.10/0.93  fof(f13,axiom,(
% 3.10/0.93    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.10/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.93  
% 3.10/0.93  fof(f34,plain,(
% 3.10/0.93    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.10/0.93    inference(ennf_transformation,[],[f13])).
% 3.10/0.93  
% 3.10/0.93  fof(f79,plain,(
% 3.10/0.93    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.10/0.93    inference(cnf_transformation,[],[f34])).
% 3.10/0.93  
% 3.10/0.93  fof(f19,axiom,(
% 3.10/0.93    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 3.10/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.93  
% 3.10/0.93  fof(f41,plain,(
% 3.10/0.93    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.10/0.93    inference(ennf_transformation,[],[f19])).
% 3.10/0.93  
% 3.10/0.93  fof(f42,plain,(
% 3.10/0.93    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.10/0.93    inference(flattening,[],[f41])).
% 3.10/0.93  
% 3.10/0.93  fof(f88,plain,(
% 3.10/0.93    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.10/0.93    inference(cnf_transformation,[],[f42])).
% 3.10/0.93  
% 3.10/0.93  fof(f11,axiom,(
% 3.10/0.93    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.10/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.93  
% 3.10/0.93  fof(f25,plain,(
% 3.10/0.93    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.10/0.93    inference(pure_predicate_removal,[],[f11])).
% 3.10/0.93  
% 3.10/0.93  fof(f32,plain,(
% 3.10/0.93    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.10/0.93    inference(ennf_transformation,[],[f25])).
% 3.10/0.93  
% 3.10/0.93  fof(f77,plain,(
% 3.10/0.93    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.10/0.93    inference(cnf_transformation,[],[f32])).
% 3.10/0.93  
% 3.10/0.93  fof(f15,axiom,(
% 3.10/0.93    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.10/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.93  
% 3.10/0.93  fof(f37,plain,(
% 3.10/0.93    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.10/0.93    inference(ennf_transformation,[],[f15])).
% 3.10/0.93  
% 3.10/0.93  fof(f38,plain,(
% 3.10/0.93    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.10/0.93    inference(flattening,[],[f37])).
% 3.10/0.93  
% 3.10/0.93  fof(f56,plain,(
% 3.10/0.93    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.10/0.93    inference(nnf_transformation,[],[f38])).
% 3.10/0.93  
% 3.10/0.93  fof(f83,plain,(
% 3.10/0.93    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.10/0.93    inference(cnf_transformation,[],[f56])).
% 3.10/0.93  
% 3.10/0.93  fof(f105,plain,(
% 3.10/0.93    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.10/0.93    inference(equality_resolution,[],[f83])).
% 3.10/0.93  
% 3.10/0.93  fof(f98,plain,(
% 3.10/0.93    ~v2_funct_2(sK4,sK1) | ~v2_funct_1(sK3)),
% 3.10/0.93    inference(cnf_transformation,[],[f59])).
% 3.10/0.93  
% 3.10/0.93  fof(f10,axiom,(
% 3.10/0.93    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.10/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.93  
% 3.10/0.93  fof(f31,plain,(
% 3.10/0.93    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.10/0.93    inference(ennf_transformation,[],[f10])).
% 3.10/0.93  
% 3.10/0.93  fof(f76,plain,(
% 3.10/0.93    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.10/0.93    inference(cnf_transformation,[],[f31])).
% 3.10/0.93  
% 3.10/0.93  fof(f8,axiom,(
% 3.10/0.93    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.10/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.93  
% 3.10/0.93  fof(f74,plain,(
% 3.10/0.93    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 3.10/0.93    inference(cnf_transformation,[],[f8])).
% 3.10/0.93  
% 3.10/0.93  fof(f18,axiom,(
% 3.10/0.93    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.10/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.93  
% 3.10/0.93  fof(f87,plain,(
% 3.10/0.93    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.10/0.93    inference(cnf_transformation,[],[f18])).
% 3.10/0.93  
% 3.10/0.93  fof(f100,plain,(
% 3.10/0.93    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 3.10/0.93    inference(definition_unfolding,[],[f74,f87])).
% 3.10/0.93  
% 3.10/0.93  fof(f12,axiom,(
% 3.10/0.93    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 3.10/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.93  
% 3.10/0.93  fof(f33,plain,(
% 3.10/0.93    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 3.10/0.93    inference(ennf_transformation,[],[f12])).
% 3.10/0.93  
% 3.10/0.93  fof(f78,plain,(
% 3.10/0.93    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 3.10/0.93    inference(cnf_transformation,[],[f33])).
% 3.10/0.93  
% 3.10/0.93  fof(f7,axiom,(
% 3.10/0.93    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0) & v1_xboole_0(X0)) => (v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)))),
% 3.10/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.93  
% 3.10/0.93  fof(f28,plain,(
% 3.10/0.93    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_xboole_0(X0)))),
% 3.10/0.93    inference(ennf_transformation,[],[f7])).
% 3.10/0.93  
% 3.10/0.93  fof(f29,plain,(
% 3.10/0.93    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 3.10/0.93    inference(flattening,[],[f28])).
% 3.10/0.93  
% 3.10/0.93  fof(f72,plain,(
% 3.10/0.93    ( ! [X0] : (v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 3.10/0.93    inference(cnf_transformation,[],[f29])).
% 3.10/0.93  
% 3.10/0.93  fof(f6,axiom,(
% 3.10/0.93    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 3.10/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.93  
% 3.10/0.93  fof(f27,plain,(
% 3.10/0.93    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 3.10/0.93    inference(ennf_transformation,[],[f6])).
% 3.10/0.93  
% 3.10/0.93  fof(f69,plain,(
% 3.10/0.93    ( ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0)) )),
% 3.10/0.93    inference(cnf_transformation,[],[f27])).
% 3.10/0.93  
% 3.10/0.93  fof(f73,plain,(
% 3.10/0.93    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 3.10/0.93    inference(cnf_transformation,[],[f8])).
% 3.10/0.93  
% 3.10/0.93  fof(f101,plain,(
% 3.10/0.93    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 3.10/0.93    inference(definition_unfolding,[],[f73,f87])).
% 3.10/0.93  
% 3.10/0.93  fof(f4,axiom,(
% 3.10/0.93    ! [X0,X1] : (v5_relat_1(k1_xboole_0,X1) & v4_relat_1(k1_xboole_0,X0))),
% 3.10/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.93  
% 3.10/0.93  fof(f24,plain,(
% 3.10/0.93    ! [X0,X1] : v5_relat_1(k1_xboole_0,X1)),
% 3.10/0.93    inference(pure_predicate_removal,[],[f4])).
% 3.10/0.93  
% 3.10/0.93  fof(f54,plain,(
% 3.10/0.93    ! [X1] : v5_relat_1(k1_xboole_0,X1)),
% 3.10/0.93    inference(rectify,[],[f24])).
% 3.10/0.93  
% 3.10/0.93  fof(f67,plain,(
% 3.10/0.93    ( ! [X1] : (v5_relat_1(k1_xboole_0,X1)) )),
% 3.10/0.93    inference(cnf_transformation,[],[f54])).
% 3.10/0.93  
% 3.10/0.93  fof(f3,axiom,(
% 3.10/0.93    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.10/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.93  
% 3.10/0.93  fof(f26,plain,(
% 3.10/0.93    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.10/0.93    inference(ennf_transformation,[],[f3])).
% 3.10/0.93  
% 3.10/0.93  fof(f53,plain,(
% 3.10/0.93    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.10/0.93    inference(nnf_transformation,[],[f26])).
% 3.10/0.93  
% 3.10/0.93  fof(f65,plain,(
% 3.10/0.93    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.10/0.93    inference(cnf_transformation,[],[f53])).
% 3.10/0.93  
% 3.10/0.93  fof(f1,axiom,(
% 3.10/0.93    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.10/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.93  
% 3.10/0.93  fof(f47,plain,(
% 3.10/0.93    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.10/0.93    inference(nnf_transformation,[],[f1])).
% 3.10/0.93  
% 3.10/0.93  fof(f48,plain,(
% 3.10/0.93    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.10/0.93    inference(rectify,[],[f47])).
% 3.10/0.93  
% 3.10/0.93  fof(f49,plain,(
% 3.10/0.93    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.10/0.93    introduced(choice_axiom,[])).
% 3.10/0.93  
% 3.10/0.93  fof(f50,plain,(
% 3.10/0.93    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.10/0.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f48,f49])).
% 3.10/0.93  
% 3.10/0.93  fof(f61,plain,(
% 3.10/0.93    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 3.10/0.93    inference(cnf_transformation,[],[f50])).
% 3.10/0.93  
% 3.10/0.93  fof(f9,axiom,(
% 3.10/0.93    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.10/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.93  
% 3.10/0.93  fof(f30,plain,(
% 3.10/0.93    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.10/0.93    inference(ennf_transformation,[],[f9])).
% 3.10/0.93  
% 3.10/0.93  fof(f75,plain,(
% 3.10/0.93    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.10/0.93    inference(cnf_transformation,[],[f30])).
% 3.10/0.93  
% 3.10/0.93  fof(f5,axiom,(
% 3.10/0.93    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 3.10/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.93  
% 3.10/0.93  fof(f68,plain,(
% 3.10/0.93    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 3.10/0.93    inference(cnf_transformation,[],[f5])).
% 3.10/0.93  
% 3.10/0.93  fof(f99,plain,(
% 3.10/0.93    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 3.10/0.93    inference(definition_unfolding,[],[f68,f87])).
% 3.10/0.93  
% 3.10/0.93  fof(f2,axiom,(
% 3.10/0.93    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.10/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.93  
% 3.10/0.93  fof(f51,plain,(
% 3.10/0.93    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 3.10/0.93    inference(nnf_transformation,[],[f2])).
% 3.10/0.93  
% 3.10/0.93  fof(f52,plain,(
% 3.10/0.93    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 3.10/0.93    inference(flattening,[],[f51])).
% 3.10/0.93  
% 3.10/0.93  fof(f64,plain,(
% 3.10/0.93    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 3.10/0.93    inference(cnf_transformation,[],[f52])).
% 3.10/0.93  
% 3.10/0.93  fof(f102,plain,(
% 3.10/0.93    ( ! [X0] : (k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0) )),
% 3.10/0.93    inference(equality_resolution,[],[f64])).
% 3.10/0.93  
% 3.10/0.93  cnf(c_24,plain,
% 3.10/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.10/0.93      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.10/0.93      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.10/0.93      | ~ v1_funct_1(X0)
% 3.10/0.93      | ~ v1_funct_1(X3) ),
% 3.10/0.93      inference(cnf_transformation,[],[f85]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_1501,plain,
% 3.10/0.93      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.10/0.93      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 3.10/0.93      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 3.10/0.93      | v1_funct_1(X0) != iProver_top
% 3.10/0.93      | v1_funct_1(X3) != iProver_top ),
% 3.10/0.93      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_21,plain,
% 3.10/0.93      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.10/0.93      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.10/0.93      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.10/0.93      | X3 = X2 ),
% 3.10/0.93      inference(cnf_transformation,[],[f80]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_31,negated_conjecture,
% 3.10/0.93      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) ),
% 3.10/0.93      inference(cnf_transformation,[],[f97]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_695,plain,
% 3.10/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.10/0.93      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.10/0.93      | X3 = X0
% 3.10/0.93      | k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) != X0
% 3.10/0.93      | k6_partfun1(sK1) != X3
% 3.10/0.93      | sK1 != X2
% 3.10/0.93      | sK1 != X1 ),
% 3.10/0.93      inference(resolution_lifted,[status(thm)],[c_21,c_31]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_696,plain,
% 3.10/0.93      ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.10/0.93      | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.10/0.93      | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
% 3.10/0.93      inference(unflattening,[status(thm)],[c_695]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_26,plain,
% 3.10/0.93      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.10/0.93      inference(cnf_transformation,[],[f86]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_704,plain,
% 3.10/0.93      ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.10/0.93      | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
% 3.10/0.93      inference(forward_subsumption_resolution,
% 3.10/0.93                [status(thm)],
% 3.10/0.93                [c_696,c_26]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_1483,plain,
% 3.10/0.93      ( k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 3.10/0.93      | m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
% 3.10/0.93      inference(predicate_to_equality,[status(thm)],[c_704]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_5319,plain,
% 3.10/0.93      ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k6_partfun1(sK1)
% 3.10/0.93      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.10/0.93      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.10/0.93      | v1_funct_1(sK3) != iProver_top
% 3.10/0.93      | v1_funct_1(sK4) != iProver_top ),
% 3.10/0.93      inference(superposition,[status(thm)],[c_1501,c_1483]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_37,negated_conjecture,
% 3.10/0.93      ( v1_funct_1(sK3) ),
% 3.10/0.93      inference(cnf_transformation,[],[f91]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_38,plain,
% 3.10/0.93      ( v1_funct_1(sK3) = iProver_top ),
% 3.10/0.93      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_35,negated_conjecture,
% 3.10/0.93      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 3.10/0.93      inference(cnf_transformation,[],[f93]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_40,plain,
% 3.10/0.93      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.10/0.93      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_34,negated_conjecture,
% 3.10/0.93      ( v1_funct_1(sK4) ),
% 3.10/0.93      inference(cnf_transformation,[],[f94]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_41,plain,
% 3.10/0.93      ( v1_funct_1(sK4) = iProver_top ),
% 3.10/0.93      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_32,negated_conjecture,
% 3.10/0.93      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 3.10/0.93      inference(cnf_transformation,[],[f96]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_43,plain,
% 3.10/0.93      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 3.10/0.93      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_5750,plain,
% 3.10/0.93      ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k6_partfun1(sK1) ),
% 3.10/0.93      inference(global_propositional_subsumption,
% 3.10/0.93                [status(thm)],
% 3.10/0.93                [c_5319,c_38,c_40,c_41,c_43]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_29,plain,
% 3.10/0.93      ( ~ v1_funct_2(X0,X1,X2)
% 3.10/0.93      | ~ v1_funct_2(X3,X4,X1)
% 3.10/0.93      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 3.10/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.10/0.93      | v2_funct_1(X3)
% 3.10/0.93      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 3.10/0.93      | ~ v1_funct_1(X0)
% 3.10/0.93      | ~ v1_funct_1(X3)
% 3.10/0.93      | k1_xboole_0 = X2 ),
% 3.10/0.93      inference(cnf_transformation,[],[f89]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_1497,plain,
% 3.10/0.93      ( k1_xboole_0 = X0
% 3.10/0.93      | v1_funct_2(X1,X2,X0) != iProver_top
% 3.10/0.93      | v1_funct_2(X3,X4,X2) != iProver_top
% 3.10/0.93      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
% 3.10/0.93      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 3.10/0.93      | v2_funct_1(X3) = iProver_top
% 3.10/0.93      | v2_funct_1(k1_partfun1(X4,X2,X2,X0,X3,X1)) != iProver_top
% 3.10/0.93      | v1_funct_1(X1) != iProver_top
% 3.10/0.93      | v1_funct_1(X3) != iProver_top ),
% 3.10/0.93      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_5776,plain,
% 3.10/0.93      ( sK1 = k1_xboole_0
% 3.10/0.93      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 3.10/0.93      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 3.10/0.93      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.10/0.93      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.10/0.93      | v2_funct_1(k6_partfun1(sK1)) != iProver_top
% 3.10/0.93      | v2_funct_1(sK3) = iProver_top
% 3.10/0.93      | v1_funct_1(sK3) != iProver_top
% 3.10/0.93      | v1_funct_1(sK4) != iProver_top ),
% 3.10/0.93      inference(superposition,[status(thm)],[c_5750,c_1497]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_36,negated_conjecture,
% 3.10/0.93      ( v1_funct_2(sK3,sK1,sK2) ),
% 3.10/0.93      inference(cnf_transformation,[],[f92]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_39,plain,
% 3.10/0.93      ( v1_funct_2(sK3,sK1,sK2) = iProver_top ),
% 3.10/0.93      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_33,negated_conjecture,
% 3.10/0.93      ( v1_funct_2(sK4,sK2,sK1) ),
% 3.10/0.93      inference(cnf_transformation,[],[f95]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_42,plain,
% 3.10/0.93      ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
% 3.10/0.93      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_1496,plain,
% 3.10/0.93      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 3.10/0.93      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_19,plain,
% 3.10/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.10/0.93      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.10/0.93      inference(cnf_transformation,[],[f79]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_1502,plain,
% 3.10/0.93      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.10/0.93      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.10/0.93      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_3053,plain,
% 3.10/0.93      ( k2_relset_1(sK2,sK1,sK4) = k2_relat_1(sK4) ),
% 3.10/0.93      inference(superposition,[status(thm)],[c_1496,c_1502]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_27,plain,
% 3.10/0.93      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.10/0.93      | ~ v1_funct_2(X2,X0,X1)
% 3.10/0.93      | ~ v1_funct_2(X3,X1,X0)
% 3.10/0.93      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.10/0.93      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.10/0.93      | ~ v1_funct_1(X2)
% 3.10/0.93      | ~ v1_funct_1(X3)
% 3.10/0.93      | k2_relset_1(X1,X0,X3) = X0 ),
% 3.10/0.93      inference(cnf_transformation,[],[f88]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_708,plain,
% 3.10/0.93      ( ~ v1_funct_2(X0,X1,X2)
% 3.10/0.93      | ~ v1_funct_2(X3,X2,X1)
% 3.10/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.10/0.93      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.10/0.93      | ~ v1_funct_1(X3)
% 3.10/0.93      | ~ v1_funct_1(X0)
% 3.10/0.93      | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 3.10/0.93      | k2_relset_1(X2,X1,X3) = X1
% 3.10/0.93      | k6_partfun1(X1) != k6_partfun1(sK1)
% 3.10/0.93      | sK1 != X1 ),
% 3.10/0.93      inference(resolution_lifted,[status(thm)],[c_27,c_31]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_709,plain,
% 3.10/0.93      ( ~ v1_funct_2(X0,X1,sK1)
% 3.10/0.93      | ~ v1_funct_2(X2,sK1,X1)
% 3.10/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 3.10/0.93      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
% 3.10/0.93      | ~ v1_funct_1(X2)
% 3.10/0.93      | ~ v1_funct_1(X0)
% 3.10/0.93      | k1_partfun1(sK1,X1,X1,sK1,X2,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 3.10/0.93      | k2_relset_1(X1,sK1,X0) = sK1
% 3.10/0.93      | k6_partfun1(sK1) != k6_partfun1(sK1) ),
% 3.10/0.93      inference(unflattening,[status(thm)],[c_708]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_788,plain,
% 3.10/0.93      ( ~ v1_funct_2(X0,X1,sK1)
% 3.10/0.93      | ~ v1_funct_2(X2,sK1,X1)
% 3.10/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 3.10/0.93      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
% 3.10/0.93      | ~ v1_funct_1(X0)
% 3.10/0.93      | ~ v1_funct_1(X2)
% 3.10/0.93      | k1_partfun1(sK1,X1,X1,sK1,X2,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 3.10/0.93      | k2_relset_1(X1,sK1,X0) = sK1 ),
% 3.10/0.93      inference(equality_resolution_simp,[status(thm)],[c_709]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_1482,plain,
% 3.10/0.93      ( k1_partfun1(sK1,X0,X0,sK1,X1,X2) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 3.10/0.93      | k2_relset_1(X0,sK1,X2) = sK1
% 3.10/0.93      | v1_funct_2(X2,X0,sK1) != iProver_top
% 3.10/0.93      | v1_funct_2(X1,sK1,X0) != iProver_top
% 3.10/0.93      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 3.10/0.93      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 3.10/0.93      | v1_funct_1(X2) != iProver_top
% 3.10/0.93      | v1_funct_1(X1) != iProver_top ),
% 3.10/0.93      inference(predicate_to_equality,[status(thm)],[c_788]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_2085,plain,
% 3.10/0.93      ( k2_relset_1(sK2,sK1,sK4) = sK1
% 3.10/0.93      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 3.10/0.93      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 3.10/0.93      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.10/0.93      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.10/0.93      | v1_funct_1(sK3) != iProver_top
% 3.10/0.93      | v1_funct_1(sK4) != iProver_top ),
% 3.10/0.93      inference(equality_resolution,[status(thm)],[c_1482]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_1737,plain,
% 3.10/0.93      ( ~ v1_funct_2(X0,sK1,sK2)
% 3.10/0.93      | ~ v1_funct_2(sK4,sK2,sK1)
% 3.10/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.10/0.93      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.10/0.93      | ~ v1_funct_1(X0)
% 3.10/0.93      | ~ v1_funct_1(sK4)
% 3.10/0.93      | k1_partfun1(sK1,sK2,sK2,sK1,X0,sK4) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 3.10/0.93      | k2_relset_1(sK2,sK1,sK4) = sK1 ),
% 3.10/0.93      inference(instantiation,[status(thm)],[c_788]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_1877,plain,
% 3.10/0.93      ( ~ v1_funct_2(sK3,sK1,sK2)
% 3.10/0.93      | ~ v1_funct_2(sK4,sK2,sK1)
% 3.10/0.93      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.10/0.93      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.10/0.93      | ~ v1_funct_1(sK3)
% 3.10/0.93      | ~ v1_funct_1(sK4)
% 3.10/0.93      | k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 3.10/0.93      | k2_relset_1(sK2,sK1,sK4) = sK1 ),
% 3.10/0.93      inference(instantiation,[status(thm)],[c_1737]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_996,plain,( X0 = X0 ),theory(equality) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_1984,plain,
% 3.10/0.93      ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
% 3.10/0.93      inference(instantiation,[status(thm)],[c_996]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_2197,plain,
% 3.10/0.93      ( k2_relset_1(sK2,sK1,sK4) = sK1 ),
% 3.10/0.93      inference(global_propositional_subsumption,
% 3.10/0.93                [status(thm)],
% 3.10/0.93                [c_2085,c_37,c_36,c_35,c_34,c_33,c_32,c_1877,c_1984]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_3068,plain,
% 3.10/0.93      ( k2_relat_1(sK4) = sK1 ),
% 3.10/0.93      inference(light_normalisation,[status(thm)],[c_3053,c_2197]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_17,plain,
% 3.10/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.10/0.93      | v5_relat_1(X0,X2) ),
% 3.10/0.93      inference(cnf_transformation,[],[f77]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_22,plain,
% 3.10/0.93      ( v2_funct_2(X0,k2_relat_1(X0))
% 3.10/0.93      | ~ v5_relat_1(X0,k2_relat_1(X0))
% 3.10/0.93      | ~ v1_relat_1(X0) ),
% 3.10/0.93      inference(cnf_transformation,[],[f105]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_30,negated_conjecture,
% 3.10/0.93      ( ~ v2_funct_2(sK4,sK1) | ~ v2_funct_1(sK3) ),
% 3.10/0.93      inference(cnf_transformation,[],[f98]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_417,plain,
% 3.10/0.93      ( ~ v5_relat_1(X0,k2_relat_1(X0))
% 3.10/0.93      | ~ v2_funct_1(sK3)
% 3.10/0.93      | ~ v1_relat_1(X0)
% 3.10/0.93      | k2_relat_1(X0) != sK1
% 3.10/0.93      | sK4 != X0 ),
% 3.10/0.93      inference(resolution_lifted,[status(thm)],[c_22,c_30]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_418,plain,
% 3.10/0.93      ( ~ v5_relat_1(sK4,k2_relat_1(sK4))
% 3.10/0.93      | ~ v2_funct_1(sK3)
% 3.10/0.93      | ~ v1_relat_1(sK4)
% 3.10/0.93      | k2_relat_1(sK4) != sK1 ),
% 3.10/0.93      inference(unflattening,[status(thm)],[c_417]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_479,plain,
% 3.10/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.10/0.93      | ~ v2_funct_1(sK3)
% 3.10/0.93      | ~ v1_relat_1(sK4)
% 3.10/0.93      | k2_relat_1(sK4) != X2
% 3.10/0.93      | k2_relat_1(sK4) != sK1
% 3.10/0.93      | sK4 != X0 ),
% 3.10/0.93      inference(resolution_lifted,[status(thm)],[c_17,c_418]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_480,plain,
% 3.10/0.93      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK4))))
% 3.10/0.93      | ~ v2_funct_1(sK3)
% 3.10/0.93      | ~ v1_relat_1(sK4)
% 3.10/0.93      | k2_relat_1(sK4) != sK1 ),
% 3.10/0.93      inference(unflattening,[status(thm)],[c_479]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_16,plain,
% 3.10/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.10/0.93      | v1_relat_1(X0) ),
% 3.10/0.93      inference(cnf_transformation,[],[f76]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_492,plain,
% 3.10/0.93      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK4))))
% 3.10/0.93      | ~ v2_funct_1(sK3)
% 3.10/0.93      | k2_relat_1(sK4) != sK1 ),
% 3.10/0.93      inference(forward_subsumption_resolution,
% 3.10/0.93                [status(thm)],
% 3.10/0.93                [c_480,c_16]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_994,plain,
% 3.10/0.93      ( ~ v2_funct_1(sK3) | sP0_iProver_split | k2_relat_1(sK4) != sK1 ),
% 3.10/0.93      inference(splitting,
% 3.10/0.93                [splitting(split),new_symbols(definition,[])],
% 3.10/0.93                [c_492]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_1486,plain,
% 3.10/0.93      ( k2_relat_1(sK4) != sK1
% 3.10/0.93      | v2_funct_1(sK3) != iProver_top
% 3.10/0.93      | sP0_iProver_split = iProver_top ),
% 3.10/0.93      inference(predicate_to_equality,[status(thm)],[c_994]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_3271,plain,
% 3.10/0.93      ( sK1 != sK1
% 3.10/0.93      | v2_funct_1(sK3) != iProver_top
% 3.10/0.93      | sP0_iProver_split = iProver_top ),
% 3.10/0.93      inference(demodulation,[status(thm)],[c_3068,c_1486]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_3278,plain,
% 3.10/0.93      ( v2_funct_1(sK3) != iProver_top
% 3.10/0.93      | sP0_iProver_split = iProver_top ),
% 3.10/0.93      inference(equality_resolution_simp,[status(thm)],[c_3271]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_993,plain,
% 3.10/0.93      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK4))))
% 3.10/0.93      | ~ sP0_iProver_split ),
% 3.10/0.93      inference(splitting,
% 3.10/0.93                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 3.10/0.93                [c_492]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_1487,plain,
% 3.10/0.93      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK4)))) != iProver_top
% 3.10/0.93      | sP0_iProver_split != iProver_top ),
% 3.10/0.93      inference(predicate_to_equality,[status(thm)],[c_993]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_3270,plain,
% 3.10/0.93      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 3.10/0.93      | sP0_iProver_split != iProver_top ),
% 3.10/0.93      inference(demodulation,[status(thm)],[c_3068,c_1487]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_3449,plain,
% 3.10/0.93      ( sP0_iProver_split != iProver_top ),
% 3.10/0.93      inference(superposition,[status(thm)],[c_1496,c_3270]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_6030,plain,
% 3.10/0.93      ( v2_funct_1(k6_partfun1(sK1)) != iProver_top | sK1 = k1_xboole_0 ),
% 3.10/0.93      inference(global_propositional_subsumption,
% 3.10/0.93                [status(thm)],
% 3.10/0.93                [c_5776,c_38,c_39,c_40,c_41,c_42,c_43,c_3278,c_3449]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_6031,plain,
% 3.10/0.93      ( sK1 = k1_xboole_0 | v2_funct_1(k6_partfun1(sK1)) != iProver_top ),
% 3.10/0.93      inference(renaming,[status(thm)],[c_6030]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_13,plain,
% 3.10/0.93      ( v2_funct_1(k6_partfun1(X0)) ),
% 3.10/0.93      inference(cnf_transformation,[],[f100]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_1506,plain,
% 3.10/0.93      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 3.10/0.93      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_6036,plain,
% 3.10/0.93      ( sK1 = k1_xboole_0 ),
% 3.10/0.93      inference(forward_subsumption_resolution,
% 3.10/0.93                [status(thm)],
% 3.10/0.93                [c_6031,c_1506]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_1493,plain,
% 3.10/0.93      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.10/0.93      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_18,plain,
% 3.10/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.10/0.93      | ~ v1_xboole_0(X1)
% 3.10/0.93      | v1_xboole_0(X0) ),
% 3.10/0.93      inference(cnf_transformation,[],[f78]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_1503,plain,
% 3.10/0.93      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.10/0.93      | v1_xboole_0(X1) != iProver_top
% 3.10/0.93      | v1_xboole_0(X0) = iProver_top ),
% 3.10/0.93      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_4289,plain,
% 3.10/0.93      ( v1_xboole_0(sK3) = iProver_top
% 3.10/0.93      | v1_xboole_0(sK1) != iProver_top ),
% 3.10/0.93      inference(superposition,[status(thm)],[c_1493,c_1503]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_1755,plain,
% 3.10/0.93      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.10/0.93      | v1_relat_1(sK3) ),
% 3.10/0.93      inference(instantiation,[status(thm)],[c_16]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_1756,plain,
% 3.10/0.93      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.10/0.93      | v1_relat_1(sK3) = iProver_top ),
% 3.10/0.93      inference(predicate_to_equality,[status(thm)],[c_1755]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_10,plain,
% 3.10/0.93      ( v2_funct_1(X0)
% 3.10/0.93      | ~ v1_funct_1(X0)
% 3.10/0.93      | ~ v1_relat_1(X0)
% 3.10/0.93      | ~ v1_xboole_0(X0) ),
% 3.10/0.93      inference(cnf_transformation,[],[f72]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_9,plain,
% 3.10/0.93      ( v1_funct_1(X0) | ~ v1_xboole_0(X0) ),
% 3.10/0.93      inference(cnf_transformation,[],[f69]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_212,plain,
% 3.10/0.93      ( v2_funct_1(X0) | ~ v1_relat_1(X0) | ~ v1_xboole_0(X0) ),
% 3.10/0.93      inference(global_propositional_subsumption,
% 3.10/0.93                [status(thm)],
% 3.10/0.93                [c_10,c_9]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_1868,plain,
% 3.10/0.93      ( v2_funct_1(sK3) | ~ v1_relat_1(sK3) | ~ v1_xboole_0(sK3) ),
% 3.10/0.93      inference(instantiation,[status(thm)],[c_212]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_1869,plain,
% 3.10/0.93      ( v2_funct_1(sK3) = iProver_top
% 3.10/0.93      | v1_relat_1(sK3) != iProver_top
% 3.10/0.93      | v1_xboole_0(sK3) != iProver_top ),
% 3.10/0.93      inference(predicate_to_equality,[status(thm)],[c_1868]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_4731,plain,
% 3.10/0.93      ( v1_xboole_0(sK1) != iProver_top ),
% 3.10/0.93      inference(global_propositional_subsumption,
% 3.10/0.93                [status(thm)],
% 3.10/0.93                [c_4289,c_40,c_1756,c_1869,c_3278,c_3449]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_6040,plain,
% 3.10/0.93      ( v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.10/0.93      inference(demodulation,[status(thm)],[c_6036,c_4731]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_14,plain,
% 3.10/0.93      ( v1_relat_1(k6_partfun1(X0)) ),
% 3.10/0.93      inference(cnf_transformation,[],[f101]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_7,plain,
% 3.10/0.93      ( v5_relat_1(k1_xboole_0,X0) ),
% 3.10/0.93      inference(cnf_transformation,[],[f67]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_6,plain,
% 3.10/0.93      ( r1_tarski(k2_relat_1(X0),X1)
% 3.10/0.93      | ~ v5_relat_1(X0,X1)
% 3.10/0.93      | ~ v1_relat_1(X0) ),
% 3.10/0.93      inference(cnf_transformation,[],[f65]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_0,plain,
% 3.10/0.93      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.10/0.93      inference(cnf_transformation,[],[f61]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_15,plain,
% 3.10/0.93      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 3.10/0.93      inference(cnf_transformation,[],[f75]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_378,plain,
% 3.10/0.93      ( ~ r1_tarski(X0,X1) | v1_xboole_0(X2) | X0 != X2 | sK0(X2) != X1 ),
% 3.10/0.93      inference(resolution_lifted,[status(thm)],[c_0,c_15]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_379,plain,
% 3.10/0.93      ( ~ r1_tarski(X0,sK0(X0)) | v1_xboole_0(X0) ),
% 3.10/0.93      inference(unflattening,[status(thm)],[c_378]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_396,plain,
% 3.10/0.93      ( ~ v5_relat_1(X0,X1)
% 3.10/0.93      | ~ v1_relat_1(X0)
% 3.10/0.93      | v1_xboole_0(X2)
% 3.10/0.93      | k2_relat_1(X0) != X2
% 3.10/0.93      | sK0(X2) != X1 ),
% 3.10/0.93      inference(resolution_lifted,[status(thm)],[c_6,c_379]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_397,plain,
% 3.10/0.93      ( ~ v5_relat_1(X0,sK0(k2_relat_1(X0)))
% 3.10/0.93      | ~ v1_relat_1(X0)
% 3.10/0.93      | v1_xboole_0(k2_relat_1(X0)) ),
% 3.10/0.93      inference(unflattening,[status(thm)],[c_396]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_438,plain,
% 3.10/0.93      ( ~ v1_relat_1(X0)
% 3.10/0.93      | v1_xboole_0(k2_relat_1(X0))
% 3.10/0.93      | sK0(k2_relat_1(X0)) != X1
% 3.10/0.93      | k1_xboole_0 != X0 ),
% 3.10/0.93      inference(resolution_lifted,[status(thm)],[c_7,c_397]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_439,plain,
% 3.10/0.93      ( ~ v1_relat_1(k1_xboole_0)
% 3.10/0.93      | v1_xboole_0(k2_relat_1(k1_xboole_0)) ),
% 3.10/0.93      inference(unflattening,[status(thm)],[c_438]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_560,plain,
% 3.10/0.93      ( v1_xboole_0(k2_relat_1(k1_xboole_0))
% 3.10/0.93      | k6_partfun1(X0) != k1_xboole_0 ),
% 3.10/0.93      inference(resolution_lifted,[status(thm)],[c_14,c_439]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_8,plain,
% 3.10/0.93      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 3.10/0.93      inference(cnf_transformation,[],[f99]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_562,plain,
% 3.10/0.93      ( v1_xboole_0(k2_relat_1(k1_xboole_0))
% 3.10/0.93      | k6_partfun1(k1_xboole_0) != k1_xboole_0 ),
% 3.10/0.93      inference(instantiation,[status(thm)],[c_560]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_564,plain,
% 3.10/0.93      ( v1_xboole_0(k2_relat_1(k1_xboole_0)) ),
% 3.10/0.93      inference(global_propositional_subsumption,
% 3.10/0.93                [status(thm)],
% 3.10/0.93                [c_560,c_8,c_562]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_1485,plain,
% 3.10/0.93      ( v1_xboole_0(k2_relat_1(k1_xboole_0)) = iProver_top ),
% 3.10/0.93      inference(predicate_to_equality,[status(thm)],[c_564]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_2,plain,
% 3.10/0.93      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.10/0.93      inference(cnf_transformation,[],[f102]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_1499,plain,
% 3.10/0.93      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 3.10/0.93      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_2512,plain,
% 3.10/0.93      ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.10/0.93      inference(superposition,[status(thm)],[c_2,c_1499]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_2515,plain,
% 3.10/0.93      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.10/0.93      inference(light_normalisation,[status(thm)],[c_2512,c_8]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_4290,plain,
% 3.10/0.93      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.10/0.93      | v1_xboole_0(X1) != iProver_top
% 3.10/0.93      | v1_xboole_0(X0) = iProver_top ),
% 3.10/0.93      inference(superposition,[status(thm)],[c_2,c_1503]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_4622,plain,
% 3.10/0.93      ( v1_xboole_0(X0) != iProver_top
% 3.10/0.93      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.10/0.93      inference(superposition,[status(thm)],[c_2515,c_4290]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(c_4841,plain,
% 3.10/0.93      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.10/0.93      inference(superposition,[status(thm)],[c_1485,c_4622]) ).
% 3.10/0.93  
% 3.10/0.93  cnf(contradiction,plain,
% 3.10/0.93      ( $false ),
% 3.10/0.93      inference(minisat,[status(thm)],[c_6040,c_4841]) ).
% 3.10/0.93  
% 3.10/0.93  
% 3.10/0.93  % SZS output end CNFRefutation for theBenchmark.p
% 3.10/0.93  
% 3.10/0.93  ------                               Statistics
% 3.10/0.93  
% 3.10/0.93  ------ General
% 3.10/0.93  
% 3.10/0.93  abstr_ref_over_cycles:                  0
% 3.10/0.93  abstr_ref_under_cycles:                 0
% 3.10/0.93  gc_basic_clause_elim:                   0
% 3.10/0.93  forced_gc_time:                         0
% 3.10/0.93  parsing_time:                           0.01
% 3.10/0.93  unif_index_cands_time:                  0.
% 3.10/0.93  unif_index_add_time:                    0.
% 3.10/0.93  orderings_time:                         0.
% 3.10/0.93  out_proof_time:                         0.018
% 3.10/0.93  total_time:                             0.245
% 3.10/0.93  num_of_symbols:                         55
% 3.10/0.93  num_of_terms:                           8494
% 3.10/0.93  
% 3.10/0.93  ------ Preprocessing
% 3.10/0.93  
% 3.10/0.93  num_of_splits:                          1
% 3.10/0.93  num_of_split_atoms:                     1
% 3.10/0.93  num_of_reused_defs:                     0
% 3.10/0.93  num_eq_ax_congr_red:                    12
% 3.10/0.93  num_of_sem_filtered_clauses:            1
% 3.10/0.93  num_of_subtypes:                        0
% 3.10/0.93  monotx_restored_types:                  0
% 3.10/0.93  sat_num_of_epr_types:                   0
% 3.10/0.93  sat_num_of_non_cyclic_types:            0
% 3.10/0.93  sat_guarded_non_collapsed_types:        0
% 3.10/0.93  num_pure_diseq_elim:                    0
% 3.10/0.93  simp_replaced_by:                       0
% 3.10/0.93  res_preprocessed:                       156
% 3.10/0.93  prep_upred:                             0
% 3.10/0.93  prep_unflattend:                        35
% 3.10/0.93  smt_new_axioms:                         0
% 3.10/0.93  pred_elim_cands:                        6
% 3.10/0.93  pred_elim:                              5
% 3.10/0.93  pred_elim_cl:                           7
% 3.10/0.93  pred_elim_cycles:                       9
% 3.10/0.93  merged_defs:                            0
% 3.10/0.93  merged_defs_ncl:                        0
% 3.10/0.93  bin_hyper_res:                          0
% 3.10/0.93  prep_cycles:                            4
% 3.10/0.93  pred_elim_time:                         0.009
% 3.10/0.93  splitting_time:                         0.
% 3.10/0.93  sem_filter_time:                        0.
% 3.10/0.93  monotx_time:                            0.001
% 3.10/0.93  subtype_inf_time:                       0.
% 3.10/0.93  
% 3.10/0.93  ------ Problem properties
% 3.10/0.93  
% 3.10/0.93  clauses:                                30
% 3.10/0.93  conjectures:                            6
% 3.10/0.93  epr:                                    6
% 3.10/0.93  horn:                                   28
% 3.10/0.93  ground:                                 11
% 3.10/0.93  unary:                                  13
% 3.10/0.93  binary:                                 6
% 3.10/0.93  lits:                                   84
% 3.10/0.93  lits_eq:                                16
% 3.10/0.93  fd_pure:                                0
% 3.10/0.93  fd_pseudo:                              0
% 3.10/0.93  fd_cond:                                2
% 3.10/0.93  fd_pseudo_cond:                         0
% 3.10/0.93  ac_symbols:                             0
% 3.10/0.93  
% 3.10/0.93  ------ Propositional Solver
% 3.10/0.93  
% 3.10/0.93  prop_solver_calls:                      27
% 3.10/0.93  prop_fast_solver_calls:                 1142
% 3.10/0.93  smt_solver_calls:                       0
% 3.10/0.93  smt_fast_solver_calls:                  0
% 3.10/0.93  prop_num_of_clauses:                    2697
% 3.10/0.93  prop_preprocess_simplified:             7332
% 3.10/0.93  prop_fo_subsumed:                       27
% 3.10/0.93  prop_solver_time:                       0.
% 3.10/0.93  smt_solver_time:                        0.
% 3.10/0.93  smt_fast_solver_time:                   0.
% 3.10/0.93  prop_fast_solver_time:                  0.
% 3.10/0.93  prop_unsat_core_time:                   0.
% 3.10/0.93  
% 3.10/0.93  ------ QBF
% 3.10/0.93  
% 3.10/0.93  qbf_q_res:                              0
% 3.10/0.93  qbf_num_tautologies:                    0
% 3.10/0.93  qbf_prep_cycles:                        0
% 3.10/0.93  
% 3.10/0.93  ------ BMC1
% 3.10/0.93  
% 3.10/0.93  bmc1_current_bound:                     -1
% 3.10/0.93  bmc1_last_solved_bound:                 -1
% 3.10/0.93  bmc1_unsat_core_size:                   -1
% 3.10/0.93  bmc1_unsat_core_parents_size:           -1
% 3.10/0.93  bmc1_merge_next_fun:                    0
% 3.10/0.93  bmc1_unsat_core_clauses_time:           0.
% 3.10/0.93  
% 3.10/0.93  ------ Instantiation
% 3.10/0.93  
% 3.10/0.93  inst_num_of_clauses:                    779
% 3.10/0.93  inst_num_in_passive:                    82
% 3.10/0.93  inst_num_in_active:                     317
% 3.10/0.93  inst_num_in_unprocessed:                380
% 3.10/0.93  inst_num_of_loops:                      340
% 3.10/0.93  inst_num_of_learning_restarts:          0
% 3.10/0.93  inst_num_moves_active_passive:          21
% 3.10/0.93  inst_lit_activity:                      0
% 3.10/0.93  inst_lit_activity_moves:                0
% 3.10/0.93  inst_num_tautologies:                   0
% 3.10/0.93  inst_num_prop_implied:                  0
% 3.10/0.93  inst_num_existing_simplified:           0
% 3.10/0.93  inst_num_eq_res_simplified:             0
% 3.10/0.93  inst_num_child_elim:                    0
% 3.10/0.93  inst_num_of_dismatching_blockings:      57
% 3.10/0.93  inst_num_of_non_proper_insts:           605
% 3.10/0.93  inst_num_of_duplicates:                 0
% 3.10/0.93  inst_inst_num_from_inst_to_res:         0
% 3.10/0.93  inst_dismatching_checking_time:         0.
% 3.10/0.93  
% 3.10/0.93  ------ Resolution
% 3.10/0.93  
% 3.10/0.93  res_num_of_clauses:                     0
% 3.10/0.93  res_num_in_passive:                     0
% 3.10/0.93  res_num_in_active:                      0
% 3.10/0.93  res_num_of_loops:                       160
% 3.10/0.93  res_forward_subset_subsumed:            36
% 3.10/0.93  res_backward_subset_subsumed:           0
% 3.10/0.93  res_forward_subsumed:                   0
% 3.10/0.93  res_backward_subsumed:                  2
% 3.10/0.93  res_forward_subsumption_resolution:     4
% 3.10/0.93  res_backward_subsumption_resolution:    0
% 3.10/0.93  res_clause_to_clause_subsumption:       141
% 3.10/0.93  res_orphan_elimination:                 0
% 3.10/0.93  res_tautology_del:                      34
% 3.10/0.93  res_num_eq_res_simplified:              1
% 3.10/0.93  res_num_sel_changes:                    0
% 3.10/0.93  res_moves_from_active_to_pass:          0
% 3.10/0.93  
% 3.10/0.93  ------ Superposition
% 3.10/0.93  
% 3.10/0.93  sup_time_total:                         0.
% 3.10/0.93  sup_time_generating:                    0.
% 3.10/0.93  sup_time_sim_full:                      0.
% 3.10/0.93  sup_time_sim_immed:                     0.
% 3.10/0.93  
% 3.10/0.93  sup_num_of_clauses:                     64
% 3.10/0.93  sup_num_in_active:                      47
% 3.10/0.93  sup_num_in_passive:                     17
% 3.10/0.93  sup_num_of_loops:                       66
% 3.10/0.93  sup_fw_superposition:                   43
% 3.10/0.93  sup_bw_superposition:                   23
% 3.10/0.93  sup_immediate_simplified:               14
% 3.10/0.93  sup_given_eliminated:                   1
% 3.10/0.93  comparisons_done:                       0
% 3.10/0.93  comparisons_avoided:                    0
% 3.10/0.93  
% 3.10/0.93  ------ Simplifications
% 3.10/0.93  
% 3.10/0.93  
% 3.10/0.93  sim_fw_subset_subsumed:                 4
% 3.10/0.93  sim_bw_subset_subsumed:                 0
% 3.10/0.93  sim_fw_subsumed:                        2
% 3.10/0.93  sim_bw_subsumed:                        2
% 3.10/0.93  sim_fw_subsumption_res:                 1
% 3.10/0.93  sim_bw_subsumption_res:                 0
% 3.10/0.93  sim_tautology_del:                      1
% 3.10/0.93  sim_eq_tautology_del:                   2
% 3.10/0.93  sim_eq_res_simp:                        2
% 3.10/0.93  sim_fw_demodulated:                     6
% 3.10/0.93  sim_bw_demodulated:                     18
% 3.10/0.93  sim_light_normalised:                   7
% 3.10/0.93  sim_joinable_taut:                      0
% 3.10/0.93  sim_joinable_simp:                      0
% 3.10/0.93  sim_ac_normalised:                      0
% 3.10/0.93  sim_smt_subsumption:                    0
% 3.10/0.93  
%------------------------------------------------------------------------------

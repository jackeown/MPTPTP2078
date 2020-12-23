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
% DateTime   : Thu Dec  3 12:01:59 EST 2020

% Result     : Theorem 3.55s
% Output     : CNFRefutation 3.55s
% Verified   : 
% Statistics : Number of formulae       :  230 (7599 expanded)
%              Number of clauses        :  147 (1948 expanded)
%              Number of leaves         :   24 (1987 expanded)
%              Depth                    :   32
%              Number of atoms          :  727 (49020 expanded)
%              Number of equality atoms :  302 (3554 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f19,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f86,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f19])).

fof(f101,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f73,f86])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f22,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
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
    inference(negated_conjecture,[],[f22])).

fof(f47,plain,(
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
    inference(ennf_transformation,[],[f23])).

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
     => ( ( ~ v2_funct_2(sK3,X0)
          | ~ v2_funct_1(X2) )
        & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0))
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(sK3,X1,X0)
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
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
          ( ( ~ v2_funct_2(X3,sK0)
            | ~ v2_funct_1(sK2) )
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( ( ~ v2_funct_2(sK3,sK0)
      | ~ v2_funct_1(sK2) )
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f48,f55,f54])).

fof(f96,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f56])).

fof(f15,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f80,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f103,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f80,f86])).

fof(f90,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f92,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f56])).

fof(f93,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f95,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f56])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f39])).

fof(f84,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f21,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f88,plain,(
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
    inference(cnf_transformation,[],[f46])).

fof(f91,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f94,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f56])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f20,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f82,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f107,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f82])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f97,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f30,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f68,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f41])).

fof(f85,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f49])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f105,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f58])).

fof(f60,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f8,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f99,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f69,f86])).

fof(f67,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f72,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f102,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f72,f86])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_15,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1409,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_22,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_33,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_547,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_33])).

cnf(c_548,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_547])).

cnf(c_23,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_556,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_548,c_23])).

cnf(c_1389,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_556])).

cnf(c_39,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_37,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1472,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_1972,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1389,c_39,c_37,c_36,c_34,c_556,c_1472])).

cnf(c_31,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v2_funct_1(X3)
    | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1400,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | v1_funct_2(X3,X4,X2) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v2_funct_1(X3) = iProver_top
    | v2_funct_1(k1_partfun1(X4,X2,X2,X0,X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_4113,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1972,c_1400])).

cnf(c_40,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_38,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_41,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_42,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_43,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_35,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_44,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_45,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_1399,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1406,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3737,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1399,c_1406])).

cnf(c_29,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_560,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X2,X1,X1,X2,X3,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,X2,X0) = X2
    | k6_partfun1(X2) != k6_partfun1(sK0)
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_33])).

cnf(c_561,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0
    | k6_partfun1(sK0) != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_560])).

cnf(c_646,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_561])).

cnf(c_1388,plain,
    ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X0,sK0,X2) = sK0
    | v1_funct_2(X2,X0,sK0) != iProver_top
    | v1_funct_2(X1,sK0,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_646])).

cnf(c_2074,plain,
    ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k6_partfun1(sK0)
    | k2_relset_1(X0,sK0,X2) = sK0
    | v1_funct_2(X2,X0,sK0) != iProver_top
    | v1_funct_2(X1,sK0,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1388,c_1972])).

cnf(c_2078,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1972,c_2074])).

cnf(c_2081,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2078,c_40,c_41,c_42,c_43,c_44,c_45])).

cnf(c_3739,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_3737,c_2081])).

cnf(c_18,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_24,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_465,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X0)
    | X0 != X1
    | k2_relat_1(X0) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_24])).

cnf(c_466,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_465])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_476,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0)))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_466,c_17])).

cnf(c_32,negated_conjecture,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_491,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
    | ~ v2_funct_1(sK2)
    | k2_relat_1(X0) != sK0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_476,c_32])).

cnf(c_492,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3))))
    | ~ v2_funct_1(sK2)
    | k2_relat_1(sK3) != sK0 ),
    inference(unflattening,[status(thm)],[c_491])).

cnf(c_828,plain,
    ( ~ v2_funct_1(sK2)
    | sP0_iProver_split
    | k2_relat_1(sK3) != sK0 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_492])).

cnf(c_1391,plain,
    ( k2_relat_1(sK3) != sK0
    | v2_funct_1(sK2) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_828])).

cnf(c_4045,plain,
    ( sK0 != sK0
    | v2_funct_1(sK2) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_3739,c_1391])).

cnf(c_4046,plain,
    ( v2_funct_1(sK2) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4045])).

cnf(c_827,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3))))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_492])).

cnf(c_1392,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3)))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_827])).

cnf(c_4044,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(demodulation,[status(thm)],[c_3739,c_1392])).

cnf(c_4069,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_1399,c_4044])).

cnf(c_4513,plain,
    ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4113,c_40,c_41,c_42,c_43,c_44,c_45,c_4046,c_4069])).

cnf(c_4514,plain,
    ( sK0 = k1_xboole_0
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4513])).

cnf(c_4517,plain,
    ( sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1409,c_4514])).

cnf(c_1396,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_4527,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4517,c_1396])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1412,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4051,plain,
    ( sK0 != k1_xboole_0
    | sK3 = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3739,c_1412])).

cnf(c_1407,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2433,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1399,c_1407])).

cnf(c_4249,plain,
    ( sK3 = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4051,c_2433])).

cnf(c_4250,plain,
    ( sK0 != k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_4249])).

cnf(c_4518,plain,
    ( sK3 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4517,c_4250])).

cnf(c_4532,plain,
    ( sK3 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_4518])).

cnf(c_4526,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4517,c_1399])).

cnf(c_4536,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4532,c_4526])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1402,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_4761,plain,
    ( k1_partfun1(X0,X1,sK1,k1_xboole_0,X2,k1_xboole_0) = k5_relat_1(X2,k1_xboole_0)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4536,c_1402])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_129,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_133,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_845,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1570,plain,
    ( v1_funct_1(X0)
    | ~ v1_funct_1(sK3)
    | X0 != sK3 ),
    inference(instantiation,[status(thm)],[c_845])).

cnf(c_1571,plain,
    ( X0 != sK3
    | v1_funct_1(X0) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1570])).

cnf(c_1573,plain,
    ( k1_xboole_0 != sK3
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1571])).

cnf(c_831,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1624,plain,
    ( X0 != X1
    | X0 = sK3
    | sK3 != X1 ),
    inference(instantiation,[status(thm)],[c_831])).

cnf(c_1625,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1624])).

cnf(c_5385,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,k1_xboole_0,X2,k1_xboole_0) = k5_relat_1(X2,k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4761,c_43,c_129,c_133,c_1573,c_1625,c_2433,c_4051,c_4517])).

cnf(c_5386,plain,
    ( k1_partfun1(X0,X1,sK1,k1_xboole_0,X2,k1_xboole_0) = k5_relat_1(X2,k1_xboole_0)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_5385])).

cnf(c_5392,plain,
    ( k1_partfun1(k1_xboole_0,sK1,sK1,k1_xboole_0,sK2,k1_xboole_0) = k5_relat_1(sK2,k1_xboole_0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4527,c_5386])).

cnf(c_4525,plain,
    ( k1_partfun1(k1_xboole_0,sK1,sK1,k1_xboole_0,sK2,sK3) = k6_partfun1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_4517,c_1972])).

cnf(c_13,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1411,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2510,plain,
    ( k6_partfun1(X0) = k1_xboole_0
    | k1_xboole_0 != X0
    | v1_relat_1(k6_partfun1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_1411])).

cnf(c_16,plain,
    ( v1_relat_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_93,plain,
    ( v1_relat_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2666,plain,
    ( k1_xboole_0 != X0
    | k6_partfun1(X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2510,c_93])).

cnf(c_2667,plain,
    ( k6_partfun1(X0) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(renaming,[status(thm)],[c_2666])).

cnf(c_2669,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_2667])).

cnf(c_4530,plain,
    ( k1_partfun1(k1_xboole_0,sK1,sK1,k1_xboole_0,sK2,sK3) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4525,c_2669])).

cnf(c_4535,plain,
    ( k1_partfun1(k1_xboole_0,sK1,sK1,k1_xboole_0,sK2,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4532,c_4530])).

cnf(c_5396,plain,
    ( k5_relat_1(sK2,k1_xboole_0) = k1_xboole_0
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5392,c_4535])).

cnf(c_5464,plain,
    ( k5_relat_1(sK2,k1_xboole_0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5396,c_40])).

cnf(c_9,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1413,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_5466,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),k1_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5464,c_1413])).

cnf(c_2923,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2669,c_13])).

cnf(c_5469,plain,
    ( r1_tarski(k1_xboole_0,k1_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5466,c_2923])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v4_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_6,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_425,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_19,c_6])).

cnf(c_429,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_425,c_17])).

cnf(c_430,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_429])).

cnf(c_1393,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_430])).

cnf(c_3409,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1396,c_1393])).

cnf(c_1418,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4015,plain,
    ( k1_relat_1(sK2) = sK0
    | r1_tarski(sK0,k1_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3409,c_1418])).

cnf(c_4519,plain,
    ( k1_relat_1(sK2) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k1_relat_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4517,c_4015])).

cnf(c_835,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2828,plain,
    ( v1_relat_1(X0)
    | ~ v1_relat_1(k6_partfun1(X1))
    | X0 != k6_partfun1(X1) ),
    inference(instantiation,[status(thm)],[c_835])).

cnf(c_2829,plain,
    ( X0 != k6_partfun1(X1)
    | v1_relat_1(X0) = iProver_top
    | v1_relat_1(k6_partfun1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2828])).

cnf(c_2831,plain,
    ( k1_xboole_0 != k6_partfun1(k1_xboole_0)
    | v1_relat_1(k6_partfun1(k1_xboole_0)) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2829])).

cnf(c_2434,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1396,c_1407])).

cnf(c_2436,plain,
    ( v1_relat_1(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2434])).

cnf(c_2416,plain,
    ( ~ v1_relat_1(k6_partfun1(X0))
    | k1_relat_1(k6_partfun1(X0)) != k1_xboole_0
    | k1_xboole_0 = k6_partfun1(X0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2418,plain,
    ( ~ v1_relat_1(k6_partfun1(k1_xboole_0))
    | k1_relat_1(k6_partfun1(k1_xboole_0)) != k1_xboole_0
    | k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2416])).

cnf(c_1840,plain,
    ( X0 != X1
    | sK2 != X1
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_831])).

cnf(c_2250,plain,
    ( X0 != sK2
    | sK2 = X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1840])).

cnf(c_2251,plain,
    ( sK2 != sK2
    | sK2 = k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_2250])).

cnf(c_2201,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1631,plain,
    ( ~ r1_tarski(X0,sK2)
    | ~ r1_tarski(sK2,X0)
    | X0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1796,plain,
    ( ~ r1_tarski(sK2,sK2)
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1631])).

cnf(c_1746,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) != k1_xboole_0
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_839,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1565,plain,
    ( v2_funct_1(X0)
    | ~ v2_funct_1(k6_partfun1(X1))
    | X0 != k6_partfun1(X1) ),
    inference(instantiation,[status(thm)],[c_839])).

cnf(c_1566,plain,
    ( X0 != k6_partfun1(X1)
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k6_partfun1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1565])).

cnf(c_1568,plain,
    ( k1_xboole_0 != k6_partfun1(k1_xboole_0)
    | v2_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top
    | v2_funct_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1566])).

cnf(c_1467,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(sK2)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_839])).

cnf(c_1468,plain,
    ( sK2 != X0
    | v2_funct_1(X0) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1467])).

cnf(c_1470,plain,
    ( sK2 != k1_xboole_0
    | v2_funct_1(sK2) = iProver_top
    | v2_funct_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1468])).

cnf(c_102,plain,
    ( k1_relat_1(k6_partfun1(k1_xboole_0)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_96,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_98,plain,
    ( v2_funct_1(k6_partfun1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_96])).

cnf(c_95,plain,
    ( v1_relat_1(k6_partfun1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_93])).

cnf(c_94,plain,
    ( v1_relat_1(k6_partfun1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5469,c_4519,c_4069,c_4046,c_2831,c_2436,c_2434,c_2418,c_2251,c_2201,c_1796,c_1746,c_1568,c_1470,c_102,c_98,c_95,c_94])).

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
% 0.12/0.34  % DateTime   : Tue Dec  1 16:39:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.55/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.55/0.97  
% 3.55/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.55/0.97  
% 3.55/0.97  ------  iProver source info
% 3.55/0.97  
% 3.55/0.97  git: date: 2020-06-30 10:37:57 +0100
% 3.55/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.55/0.97  git: non_committed_changes: false
% 3.55/0.97  git: last_make_outside_of_git: false
% 3.55/0.97  
% 3.55/0.97  ------ 
% 3.55/0.97  
% 3.55/0.97  ------ Input Options
% 3.55/0.97  
% 3.55/0.97  --out_options                           all
% 3.55/0.97  --tptp_safe_out                         true
% 3.55/0.97  --problem_path                          ""
% 3.55/0.97  --include_path                          ""
% 3.55/0.97  --clausifier                            res/vclausify_rel
% 3.55/0.97  --clausifier_options                    ""
% 3.55/0.97  --stdin                                 false
% 3.55/0.97  --stats_out                             all
% 3.55/0.97  
% 3.55/0.97  ------ General Options
% 3.55/0.97  
% 3.55/0.97  --fof                                   false
% 3.55/0.97  --time_out_real                         305.
% 3.55/0.97  --time_out_virtual                      -1.
% 3.55/0.97  --symbol_type_check                     false
% 3.55/0.97  --clausify_out                          false
% 3.55/0.97  --sig_cnt_out                           false
% 3.55/0.97  --trig_cnt_out                          false
% 3.55/0.97  --trig_cnt_out_tolerance                1.
% 3.55/0.97  --trig_cnt_out_sk_spl                   false
% 3.55/0.97  --abstr_cl_out                          false
% 3.55/0.97  
% 3.55/0.97  ------ Global Options
% 3.55/0.97  
% 3.55/0.97  --schedule                              default
% 3.55/0.97  --add_important_lit                     false
% 3.55/0.97  --prop_solver_per_cl                    1000
% 3.55/0.97  --min_unsat_core                        false
% 3.55/0.97  --soft_assumptions                      false
% 3.55/0.97  --soft_lemma_size                       3
% 3.55/0.97  --prop_impl_unit_size                   0
% 3.55/0.97  --prop_impl_unit                        []
% 3.55/0.97  --share_sel_clauses                     true
% 3.55/0.97  --reset_solvers                         false
% 3.55/0.97  --bc_imp_inh                            [conj_cone]
% 3.55/0.97  --conj_cone_tolerance                   3.
% 3.55/0.97  --extra_neg_conj                        none
% 3.55/0.97  --large_theory_mode                     true
% 3.55/0.97  --prolific_symb_bound                   200
% 3.55/0.97  --lt_threshold                          2000
% 3.55/0.97  --clause_weak_htbl                      true
% 3.55/0.97  --gc_record_bc_elim                     false
% 3.55/0.97  
% 3.55/0.97  ------ Preprocessing Options
% 3.55/0.97  
% 3.55/0.97  --preprocessing_flag                    true
% 3.55/0.97  --time_out_prep_mult                    0.1
% 3.55/0.97  --splitting_mode                        input
% 3.55/0.97  --splitting_grd                         true
% 3.55/0.97  --splitting_cvd                         false
% 3.55/0.97  --splitting_cvd_svl                     false
% 3.55/0.97  --splitting_nvd                         32
% 3.55/0.97  --sub_typing                            true
% 3.55/0.97  --prep_gs_sim                           true
% 3.55/0.97  --prep_unflatten                        true
% 3.55/0.97  --prep_res_sim                          true
% 3.55/0.97  --prep_upred                            true
% 3.55/0.97  --prep_sem_filter                       exhaustive
% 3.55/0.97  --prep_sem_filter_out                   false
% 3.55/0.97  --pred_elim                             true
% 3.55/0.97  --res_sim_input                         true
% 3.55/0.97  --eq_ax_congr_red                       true
% 3.55/0.97  --pure_diseq_elim                       true
% 3.55/0.97  --brand_transform                       false
% 3.55/0.97  --non_eq_to_eq                          false
% 3.55/0.97  --prep_def_merge                        true
% 3.55/0.97  --prep_def_merge_prop_impl              false
% 3.55/0.97  --prep_def_merge_mbd                    true
% 3.55/0.97  --prep_def_merge_tr_red                 false
% 3.55/0.97  --prep_def_merge_tr_cl                  false
% 3.55/0.97  --smt_preprocessing                     true
% 3.55/0.97  --smt_ac_axioms                         fast
% 3.55/0.97  --preprocessed_out                      false
% 3.55/0.97  --preprocessed_stats                    false
% 3.55/0.97  
% 3.55/0.97  ------ Abstraction refinement Options
% 3.55/0.97  
% 3.55/0.97  --abstr_ref                             []
% 3.55/0.97  --abstr_ref_prep                        false
% 3.55/0.97  --abstr_ref_until_sat                   false
% 3.55/0.97  --abstr_ref_sig_restrict                funpre
% 3.55/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.55/0.97  --abstr_ref_under                       []
% 3.55/0.97  
% 3.55/0.97  ------ SAT Options
% 3.55/0.97  
% 3.55/0.97  --sat_mode                              false
% 3.55/0.97  --sat_fm_restart_options                ""
% 3.55/0.97  --sat_gr_def                            false
% 3.55/0.97  --sat_epr_types                         true
% 3.55/0.97  --sat_non_cyclic_types                  false
% 3.55/0.97  --sat_finite_models                     false
% 3.55/0.97  --sat_fm_lemmas                         false
% 3.55/0.97  --sat_fm_prep                           false
% 3.55/0.97  --sat_fm_uc_incr                        true
% 3.55/0.98  --sat_out_model                         small
% 3.55/0.98  --sat_out_clauses                       false
% 3.55/0.98  
% 3.55/0.98  ------ QBF Options
% 3.55/0.98  
% 3.55/0.98  --qbf_mode                              false
% 3.55/0.98  --qbf_elim_univ                         false
% 3.55/0.98  --qbf_dom_inst                          none
% 3.55/0.98  --qbf_dom_pre_inst                      false
% 3.55/0.98  --qbf_sk_in                             false
% 3.55/0.98  --qbf_pred_elim                         true
% 3.55/0.98  --qbf_split                             512
% 3.55/0.98  
% 3.55/0.98  ------ BMC1 Options
% 3.55/0.98  
% 3.55/0.98  --bmc1_incremental                      false
% 3.55/0.98  --bmc1_axioms                           reachable_all
% 3.55/0.98  --bmc1_min_bound                        0
% 3.55/0.98  --bmc1_max_bound                        -1
% 3.55/0.98  --bmc1_max_bound_default                -1
% 3.55/0.98  --bmc1_symbol_reachability              true
% 3.55/0.98  --bmc1_property_lemmas                  false
% 3.55/0.98  --bmc1_k_induction                      false
% 3.55/0.98  --bmc1_non_equiv_states                 false
% 3.55/0.98  --bmc1_deadlock                         false
% 3.55/0.98  --bmc1_ucm                              false
% 3.55/0.98  --bmc1_add_unsat_core                   none
% 3.55/0.98  --bmc1_unsat_core_children              false
% 3.55/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.55/0.98  --bmc1_out_stat                         full
% 3.55/0.98  --bmc1_ground_init                      false
% 3.55/0.98  --bmc1_pre_inst_next_state              false
% 3.55/0.98  --bmc1_pre_inst_state                   false
% 3.55/0.98  --bmc1_pre_inst_reach_state             false
% 3.55/0.98  --bmc1_out_unsat_core                   false
% 3.55/0.98  --bmc1_aig_witness_out                  false
% 3.55/0.98  --bmc1_verbose                          false
% 3.55/0.98  --bmc1_dump_clauses_tptp                false
% 3.55/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.55/0.98  --bmc1_dump_file                        -
% 3.55/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.55/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.55/0.98  --bmc1_ucm_extend_mode                  1
% 3.55/0.98  --bmc1_ucm_init_mode                    2
% 3.55/0.98  --bmc1_ucm_cone_mode                    none
% 3.55/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.55/0.98  --bmc1_ucm_relax_model                  4
% 3.55/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.55/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.55/0.98  --bmc1_ucm_layered_model                none
% 3.55/0.98  --bmc1_ucm_max_lemma_size               10
% 3.55/0.98  
% 3.55/0.98  ------ AIG Options
% 3.55/0.98  
% 3.55/0.98  --aig_mode                              false
% 3.55/0.98  
% 3.55/0.98  ------ Instantiation Options
% 3.55/0.98  
% 3.55/0.98  --instantiation_flag                    true
% 3.55/0.98  --inst_sos_flag                         true
% 3.55/0.98  --inst_sos_phase                        true
% 3.55/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.55/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.55/0.98  --inst_lit_sel_side                     num_symb
% 3.55/0.98  --inst_solver_per_active                1400
% 3.55/0.98  --inst_solver_calls_frac                1.
% 3.55/0.98  --inst_passive_queue_type               priority_queues
% 3.55/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.55/0.98  --inst_passive_queues_freq              [25;2]
% 3.55/0.98  --inst_dismatching                      true
% 3.55/0.98  --inst_eager_unprocessed_to_passive     true
% 3.55/0.98  --inst_prop_sim_given                   true
% 3.55/0.98  --inst_prop_sim_new                     false
% 3.55/0.98  --inst_subs_new                         false
% 3.55/0.98  --inst_eq_res_simp                      false
% 3.55/0.98  --inst_subs_given                       false
% 3.55/0.98  --inst_orphan_elimination               true
% 3.55/0.98  --inst_learning_loop_flag               true
% 3.55/0.98  --inst_learning_start                   3000
% 3.55/0.98  --inst_learning_factor                  2
% 3.55/0.98  --inst_start_prop_sim_after_learn       3
% 3.55/0.98  --inst_sel_renew                        solver
% 3.55/0.98  --inst_lit_activity_flag                true
% 3.55/0.98  --inst_restr_to_given                   false
% 3.55/0.98  --inst_activity_threshold               500
% 3.55/0.98  --inst_out_proof                        true
% 3.55/0.98  
% 3.55/0.98  ------ Resolution Options
% 3.55/0.98  
% 3.55/0.98  --resolution_flag                       true
% 3.55/0.98  --res_lit_sel                           adaptive
% 3.55/0.98  --res_lit_sel_side                      none
% 3.55/0.98  --res_ordering                          kbo
% 3.55/0.98  --res_to_prop_solver                    active
% 3.55/0.98  --res_prop_simpl_new                    false
% 3.55/0.98  --res_prop_simpl_given                  true
% 3.55/0.98  --res_passive_queue_type                priority_queues
% 3.55/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.55/0.98  --res_passive_queues_freq               [15;5]
% 3.55/0.98  --res_forward_subs                      full
% 3.55/0.98  --res_backward_subs                     full
% 3.55/0.98  --res_forward_subs_resolution           true
% 3.55/0.98  --res_backward_subs_resolution          true
% 3.55/0.98  --res_orphan_elimination                true
% 3.55/0.98  --res_time_limit                        2.
% 3.55/0.98  --res_out_proof                         true
% 3.55/0.98  
% 3.55/0.98  ------ Superposition Options
% 3.55/0.98  
% 3.55/0.98  --superposition_flag                    true
% 3.55/0.98  --sup_passive_queue_type                priority_queues
% 3.55/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.55/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.55/0.98  --demod_completeness_check              fast
% 3.55/0.98  --demod_use_ground                      true
% 3.55/0.98  --sup_to_prop_solver                    passive
% 3.55/0.98  --sup_prop_simpl_new                    true
% 3.55/0.98  --sup_prop_simpl_given                  true
% 3.55/0.98  --sup_fun_splitting                     true
% 3.55/0.98  --sup_smt_interval                      50000
% 3.55/0.98  
% 3.55/0.98  ------ Superposition Simplification Setup
% 3.55/0.98  
% 3.55/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.55/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.55/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.55/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.55/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.55/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.55/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.55/0.98  --sup_immed_triv                        [TrivRules]
% 3.55/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.55/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.55/0.98  --sup_immed_bw_main                     []
% 3.55/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.55/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.55/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.55/0.98  --sup_input_bw                          []
% 3.55/0.98  
% 3.55/0.98  ------ Combination Options
% 3.55/0.98  
% 3.55/0.98  --comb_res_mult                         3
% 3.55/0.98  --comb_sup_mult                         2
% 3.55/0.98  --comb_inst_mult                        10
% 3.55/0.98  
% 3.55/0.98  ------ Debug Options
% 3.55/0.98  
% 3.55/0.98  --dbg_backtrace                         false
% 3.55/0.98  --dbg_dump_prop_clauses                 false
% 3.55/0.98  --dbg_dump_prop_clauses_file            -
% 3.55/0.98  --dbg_out_stat                          false
% 3.55/0.98  ------ Parsing...
% 3.55/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.55/0.98  
% 3.55/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.55/0.98  
% 3.55/0.98  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.55/0.98  
% 3.55/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.55/0.98  ------ Proving...
% 3.55/0.98  ------ Problem Properties 
% 3.55/0.98  
% 3.55/0.98  
% 3.55/0.98  clauses                                 34
% 3.55/0.98  conjectures                             6
% 3.55/0.98  EPR                                     8
% 3.55/0.98  Horn                                    33
% 3.55/0.98  unary                                   13
% 3.55/0.98  binary                                  6
% 3.55/0.98  lits                                    97
% 3.55/0.98  lits eq                                 18
% 3.55/0.98  fd_pure                                 0
% 3.55/0.98  fd_pseudo                               0
% 3.55/0.98  fd_cond                                 3
% 3.55/0.98  fd_pseudo_cond                          2
% 3.55/0.98  AC symbols                              0
% 3.55/0.98  
% 3.55/0.98  ------ Schedule dynamic 5 is on 
% 3.55/0.98  
% 3.55/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.55/0.98  
% 3.55/0.98  
% 3.55/0.98  ------ 
% 3.55/0.98  Current options:
% 3.55/0.98  ------ 
% 3.55/0.98  
% 3.55/0.98  ------ Input Options
% 3.55/0.98  
% 3.55/0.98  --out_options                           all
% 3.55/0.98  --tptp_safe_out                         true
% 3.55/0.98  --problem_path                          ""
% 3.55/0.98  --include_path                          ""
% 3.55/0.98  --clausifier                            res/vclausify_rel
% 3.55/0.98  --clausifier_options                    ""
% 3.55/0.98  --stdin                                 false
% 3.55/0.98  --stats_out                             all
% 3.55/0.98  
% 3.55/0.98  ------ General Options
% 3.55/0.98  
% 3.55/0.98  --fof                                   false
% 3.55/0.98  --time_out_real                         305.
% 3.55/0.98  --time_out_virtual                      -1.
% 3.55/0.98  --symbol_type_check                     false
% 3.55/0.98  --clausify_out                          false
% 3.55/0.98  --sig_cnt_out                           false
% 3.55/0.98  --trig_cnt_out                          false
% 3.55/0.98  --trig_cnt_out_tolerance                1.
% 3.55/0.98  --trig_cnt_out_sk_spl                   false
% 3.55/0.98  --abstr_cl_out                          false
% 3.55/0.98  
% 3.55/0.98  ------ Global Options
% 3.55/0.98  
% 3.55/0.98  --schedule                              default
% 3.55/0.98  --add_important_lit                     false
% 3.55/0.98  --prop_solver_per_cl                    1000
% 3.55/0.98  --min_unsat_core                        false
% 3.55/0.98  --soft_assumptions                      false
% 3.55/0.98  --soft_lemma_size                       3
% 3.55/0.98  --prop_impl_unit_size                   0
% 3.55/0.98  --prop_impl_unit                        []
% 3.55/0.98  --share_sel_clauses                     true
% 3.55/0.98  --reset_solvers                         false
% 3.55/0.98  --bc_imp_inh                            [conj_cone]
% 3.55/0.98  --conj_cone_tolerance                   3.
% 3.55/0.98  --extra_neg_conj                        none
% 3.55/0.98  --large_theory_mode                     true
% 3.55/0.98  --prolific_symb_bound                   200
% 3.55/0.98  --lt_threshold                          2000
% 3.55/0.98  --clause_weak_htbl                      true
% 3.55/0.98  --gc_record_bc_elim                     false
% 3.55/0.98  
% 3.55/0.98  ------ Preprocessing Options
% 3.55/0.98  
% 3.55/0.98  --preprocessing_flag                    true
% 3.55/0.98  --time_out_prep_mult                    0.1
% 3.55/0.98  --splitting_mode                        input
% 3.55/0.98  --splitting_grd                         true
% 3.55/0.98  --splitting_cvd                         false
% 3.55/0.98  --splitting_cvd_svl                     false
% 3.55/0.98  --splitting_nvd                         32
% 3.55/0.98  --sub_typing                            true
% 3.55/0.98  --prep_gs_sim                           true
% 3.55/0.98  --prep_unflatten                        true
% 3.55/0.98  --prep_res_sim                          true
% 3.55/0.98  --prep_upred                            true
% 3.55/0.98  --prep_sem_filter                       exhaustive
% 3.55/0.98  --prep_sem_filter_out                   false
% 3.55/0.98  --pred_elim                             true
% 3.55/0.98  --res_sim_input                         true
% 3.55/0.98  --eq_ax_congr_red                       true
% 3.55/0.98  --pure_diseq_elim                       true
% 3.55/0.98  --brand_transform                       false
% 3.55/0.98  --non_eq_to_eq                          false
% 3.55/0.98  --prep_def_merge                        true
% 3.55/0.98  --prep_def_merge_prop_impl              false
% 3.55/0.98  --prep_def_merge_mbd                    true
% 3.55/0.98  --prep_def_merge_tr_red                 false
% 3.55/0.98  --prep_def_merge_tr_cl                  false
% 3.55/0.98  --smt_preprocessing                     true
% 3.55/0.98  --smt_ac_axioms                         fast
% 3.55/0.98  --preprocessed_out                      false
% 3.55/0.98  --preprocessed_stats                    false
% 3.55/0.98  
% 3.55/0.98  ------ Abstraction refinement Options
% 3.55/0.98  
% 3.55/0.98  --abstr_ref                             []
% 3.55/0.98  --abstr_ref_prep                        false
% 3.55/0.98  --abstr_ref_until_sat                   false
% 3.55/0.98  --abstr_ref_sig_restrict                funpre
% 3.55/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.55/0.98  --abstr_ref_under                       []
% 3.55/0.98  
% 3.55/0.98  ------ SAT Options
% 3.55/0.98  
% 3.55/0.98  --sat_mode                              false
% 3.55/0.98  --sat_fm_restart_options                ""
% 3.55/0.98  --sat_gr_def                            false
% 3.55/0.98  --sat_epr_types                         true
% 3.55/0.98  --sat_non_cyclic_types                  false
% 3.55/0.98  --sat_finite_models                     false
% 3.55/0.98  --sat_fm_lemmas                         false
% 3.55/0.98  --sat_fm_prep                           false
% 3.55/0.98  --sat_fm_uc_incr                        true
% 3.55/0.98  --sat_out_model                         small
% 3.55/0.98  --sat_out_clauses                       false
% 3.55/0.98  
% 3.55/0.98  ------ QBF Options
% 3.55/0.98  
% 3.55/0.98  --qbf_mode                              false
% 3.55/0.98  --qbf_elim_univ                         false
% 3.55/0.98  --qbf_dom_inst                          none
% 3.55/0.98  --qbf_dom_pre_inst                      false
% 3.55/0.98  --qbf_sk_in                             false
% 3.55/0.98  --qbf_pred_elim                         true
% 3.55/0.98  --qbf_split                             512
% 3.55/0.98  
% 3.55/0.98  ------ BMC1 Options
% 3.55/0.98  
% 3.55/0.98  --bmc1_incremental                      false
% 3.55/0.98  --bmc1_axioms                           reachable_all
% 3.55/0.98  --bmc1_min_bound                        0
% 3.55/0.98  --bmc1_max_bound                        -1
% 3.55/0.98  --bmc1_max_bound_default                -1
% 3.55/0.98  --bmc1_symbol_reachability              true
% 3.55/0.98  --bmc1_property_lemmas                  false
% 3.55/0.98  --bmc1_k_induction                      false
% 3.55/0.98  --bmc1_non_equiv_states                 false
% 3.55/0.98  --bmc1_deadlock                         false
% 3.55/0.98  --bmc1_ucm                              false
% 3.55/0.98  --bmc1_add_unsat_core                   none
% 3.55/0.98  --bmc1_unsat_core_children              false
% 3.55/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.55/0.98  --bmc1_out_stat                         full
% 3.55/0.98  --bmc1_ground_init                      false
% 3.55/0.98  --bmc1_pre_inst_next_state              false
% 3.55/0.98  --bmc1_pre_inst_state                   false
% 3.55/0.98  --bmc1_pre_inst_reach_state             false
% 3.55/0.98  --bmc1_out_unsat_core                   false
% 3.55/0.98  --bmc1_aig_witness_out                  false
% 3.55/0.98  --bmc1_verbose                          false
% 3.55/0.98  --bmc1_dump_clauses_tptp                false
% 3.55/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.55/0.98  --bmc1_dump_file                        -
% 3.55/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.55/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.55/0.98  --bmc1_ucm_extend_mode                  1
% 3.55/0.98  --bmc1_ucm_init_mode                    2
% 3.55/0.98  --bmc1_ucm_cone_mode                    none
% 3.55/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.55/0.98  --bmc1_ucm_relax_model                  4
% 3.55/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.55/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.55/0.98  --bmc1_ucm_layered_model                none
% 3.55/0.98  --bmc1_ucm_max_lemma_size               10
% 3.55/0.98  
% 3.55/0.98  ------ AIG Options
% 3.55/0.98  
% 3.55/0.98  --aig_mode                              false
% 3.55/0.98  
% 3.55/0.98  ------ Instantiation Options
% 3.55/0.98  
% 3.55/0.98  --instantiation_flag                    true
% 3.55/0.98  --inst_sos_flag                         true
% 3.55/0.98  --inst_sos_phase                        true
% 3.55/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.55/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.55/0.98  --inst_lit_sel_side                     none
% 3.55/0.98  --inst_solver_per_active                1400
% 3.55/0.98  --inst_solver_calls_frac                1.
% 3.55/0.98  --inst_passive_queue_type               priority_queues
% 3.55/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.55/0.98  --inst_passive_queues_freq              [25;2]
% 3.55/0.98  --inst_dismatching                      true
% 3.55/0.98  --inst_eager_unprocessed_to_passive     true
% 3.55/0.98  --inst_prop_sim_given                   true
% 3.55/0.98  --inst_prop_sim_new                     false
% 3.55/0.98  --inst_subs_new                         false
% 3.55/0.98  --inst_eq_res_simp                      false
% 3.55/0.98  --inst_subs_given                       false
% 3.55/0.98  --inst_orphan_elimination               true
% 3.55/0.98  --inst_learning_loop_flag               true
% 3.55/0.98  --inst_learning_start                   3000
% 3.55/0.98  --inst_learning_factor                  2
% 3.55/0.98  --inst_start_prop_sim_after_learn       3
% 3.55/0.98  --inst_sel_renew                        solver
% 3.55/0.98  --inst_lit_activity_flag                true
% 3.55/0.98  --inst_restr_to_given                   false
% 3.55/0.98  --inst_activity_threshold               500
% 3.55/0.98  --inst_out_proof                        true
% 3.55/0.98  
% 3.55/0.98  ------ Resolution Options
% 3.55/0.98  
% 3.55/0.98  --resolution_flag                       false
% 3.55/0.98  --res_lit_sel                           adaptive
% 3.55/0.98  --res_lit_sel_side                      none
% 3.55/0.98  --res_ordering                          kbo
% 3.55/0.98  --res_to_prop_solver                    active
% 3.55/0.98  --res_prop_simpl_new                    false
% 3.55/0.98  --res_prop_simpl_given                  true
% 3.55/0.98  --res_passive_queue_type                priority_queues
% 3.55/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.55/0.98  --res_passive_queues_freq               [15;5]
% 3.55/0.98  --res_forward_subs                      full
% 3.55/0.98  --res_backward_subs                     full
% 3.55/0.98  --res_forward_subs_resolution           true
% 3.55/0.98  --res_backward_subs_resolution          true
% 3.55/0.98  --res_orphan_elimination                true
% 3.55/0.98  --res_time_limit                        2.
% 3.55/0.98  --res_out_proof                         true
% 3.55/0.98  
% 3.55/0.98  ------ Superposition Options
% 3.55/0.98  
% 3.55/0.98  --superposition_flag                    true
% 3.55/0.98  --sup_passive_queue_type                priority_queues
% 3.55/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.55/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.55/0.98  --demod_completeness_check              fast
% 3.55/0.98  --demod_use_ground                      true
% 3.55/0.98  --sup_to_prop_solver                    passive
% 3.55/0.98  --sup_prop_simpl_new                    true
% 3.55/0.98  --sup_prop_simpl_given                  true
% 3.55/0.98  --sup_fun_splitting                     true
% 3.55/0.98  --sup_smt_interval                      50000
% 3.55/0.98  
% 3.55/0.98  ------ Superposition Simplification Setup
% 3.55/0.98  
% 3.55/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.55/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.55/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.55/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.55/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.55/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.55/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.55/0.98  --sup_immed_triv                        [TrivRules]
% 3.55/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.55/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.55/0.98  --sup_immed_bw_main                     []
% 3.55/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.55/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.55/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.55/0.98  --sup_input_bw                          []
% 3.55/0.98  
% 3.55/0.98  ------ Combination Options
% 3.55/0.98  
% 3.55/0.98  --comb_res_mult                         3
% 3.55/0.98  --comb_sup_mult                         2
% 3.55/0.98  --comb_inst_mult                        10
% 3.55/0.98  
% 3.55/0.98  ------ Debug Options
% 3.55/0.98  
% 3.55/0.98  --dbg_backtrace                         false
% 3.55/0.98  --dbg_dump_prop_clauses                 false
% 3.55/0.98  --dbg_dump_prop_clauses_file            -
% 3.55/0.98  --dbg_out_stat                          false
% 3.55/0.98  
% 3.55/0.98  
% 3.55/0.98  
% 3.55/0.98  
% 3.55/0.98  ------ Proving...
% 3.55/0.98  
% 3.55/0.98  
% 3.55/0.98  % SZS status Theorem for theBenchmark.p
% 3.55/0.98  
% 3.55/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.55/0.98  
% 3.55/0.98  fof(f10,axiom,(
% 3.55/0.98    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.55/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.98  
% 3.55/0.98  fof(f73,plain,(
% 3.55/0.98    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 3.55/0.98    inference(cnf_transformation,[],[f10])).
% 3.55/0.98  
% 3.55/0.98  fof(f19,axiom,(
% 3.55/0.98    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.55/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.98  
% 3.55/0.98  fof(f86,plain,(
% 3.55/0.98    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.55/0.98    inference(cnf_transformation,[],[f19])).
% 3.55/0.98  
% 3.55/0.98  fof(f101,plain,(
% 3.55/0.98    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 3.55/0.98    inference(definition_unfolding,[],[f73,f86])).
% 3.55/0.98  
% 3.55/0.98  fof(f14,axiom,(
% 3.55/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.55/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.98  
% 3.55/0.98  fof(f35,plain,(
% 3.55/0.98    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.55/0.98    inference(ennf_transformation,[],[f14])).
% 3.55/0.98  
% 3.55/0.98  fof(f36,plain,(
% 3.55/0.98    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.55/0.98    inference(flattening,[],[f35])).
% 3.55/0.98  
% 3.55/0.98  fof(f52,plain,(
% 3.55/0.98    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.55/0.98    inference(nnf_transformation,[],[f36])).
% 3.55/0.98  
% 3.55/0.98  fof(f78,plain,(
% 3.55/0.98    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.55/0.98    inference(cnf_transformation,[],[f52])).
% 3.55/0.98  
% 3.55/0.98  fof(f22,conjecture,(
% 3.55/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.55/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.98  
% 3.55/0.98  fof(f23,negated_conjecture,(
% 3.55/0.98    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.55/0.98    inference(negated_conjecture,[],[f22])).
% 3.55/0.98  
% 3.55/0.98  fof(f47,plain,(
% 3.55/0.98    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.55/0.98    inference(ennf_transformation,[],[f23])).
% 3.55/0.98  
% 3.55/0.98  fof(f48,plain,(
% 3.55/0.98    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.55/0.98    inference(flattening,[],[f47])).
% 3.55/0.98  
% 3.55/0.98  fof(f55,plain,(
% 3.55/0.98    ( ! [X2,X0,X1] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((~v2_funct_2(sK3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 3.55/0.98    introduced(choice_axiom,[])).
% 3.55/0.98  
% 3.55/0.98  fof(f54,plain,(
% 3.55/0.98    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 3.55/0.98    introduced(choice_axiom,[])).
% 3.55/0.98  
% 3.55/0.98  fof(f56,plain,(
% 3.55/0.98    ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 3.55/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f48,f55,f54])).
% 3.55/0.98  
% 3.55/0.98  fof(f96,plain,(
% 3.55/0.98    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 3.55/0.98    inference(cnf_transformation,[],[f56])).
% 3.55/0.98  
% 3.55/0.98  fof(f15,axiom,(
% 3.55/0.98    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.55/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.98  
% 3.55/0.98  fof(f80,plain,(
% 3.55/0.98    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.55/0.98    inference(cnf_transformation,[],[f15])).
% 3.55/0.98  
% 3.55/0.98  fof(f103,plain,(
% 3.55/0.98    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.55/0.98    inference(definition_unfolding,[],[f80,f86])).
% 3.55/0.98  
% 3.55/0.98  fof(f90,plain,(
% 3.55/0.98    v1_funct_1(sK2)),
% 3.55/0.98    inference(cnf_transformation,[],[f56])).
% 3.55/0.98  
% 3.55/0.98  fof(f92,plain,(
% 3.55/0.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.55/0.98    inference(cnf_transformation,[],[f56])).
% 3.55/0.98  
% 3.55/0.98  fof(f93,plain,(
% 3.55/0.98    v1_funct_1(sK3)),
% 3.55/0.98    inference(cnf_transformation,[],[f56])).
% 3.55/0.98  
% 3.55/0.98  fof(f95,plain,(
% 3.55/0.98    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 3.55/0.98    inference(cnf_transformation,[],[f56])).
% 3.55/0.98  
% 3.55/0.98  fof(f17,axiom,(
% 3.55/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 3.55/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.98  
% 3.55/0.98  fof(f39,plain,(
% 3.55/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.55/0.98    inference(ennf_transformation,[],[f17])).
% 3.55/0.98  
% 3.55/0.98  fof(f40,plain,(
% 3.55/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.55/0.98    inference(flattening,[],[f39])).
% 3.55/0.98  
% 3.55/0.98  fof(f84,plain,(
% 3.55/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.55/0.98    inference(cnf_transformation,[],[f40])).
% 3.55/0.98  
% 3.55/0.98  fof(f21,axiom,(
% 3.55/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 3.55/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.98  
% 3.55/0.98  fof(f45,plain,(
% 3.55/0.98    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.55/0.98    inference(ennf_transformation,[],[f21])).
% 3.55/0.98  
% 3.55/0.98  fof(f46,plain,(
% 3.55/0.98    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.55/0.98    inference(flattening,[],[f45])).
% 3.55/0.98  
% 3.55/0.98  fof(f88,plain,(
% 3.55/0.98    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X3) | k1_xboole_0 = X2 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.55/0.98    inference(cnf_transformation,[],[f46])).
% 3.55/0.98  
% 3.55/0.98  fof(f91,plain,(
% 3.55/0.98    v1_funct_2(sK2,sK0,sK1)),
% 3.55/0.98    inference(cnf_transformation,[],[f56])).
% 3.55/0.98  
% 3.55/0.98  fof(f94,plain,(
% 3.55/0.98    v1_funct_2(sK3,sK1,sK0)),
% 3.55/0.98    inference(cnf_transformation,[],[f56])).
% 3.55/0.98  
% 3.55/0.98  fof(f13,axiom,(
% 3.55/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.55/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.98  
% 3.55/0.98  fof(f34,plain,(
% 3.55/0.98    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.55/0.98    inference(ennf_transformation,[],[f13])).
% 3.55/0.98  
% 3.55/0.98  fof(f77,plain,(
% 3.55/0.98    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.55/0.98    inference(cnf_transformation,[],[f34])).
% 3.55/0.98  
% 3.55/0.98  fof(f20,axiom,(
% 3.55/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 3.55/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.98  
% 3.55/0.98  fof(f43,plain,(
% 3.55/0.98    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.55/0.98    inference(ennf_transformation,[],[f20])).
% 3.55/0.98  
% 3.55/0.98  fof(f44,plain,(
% 3.55/0.98    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.55/0.98    inference(flattening,[],[f43])).
% 3.55/0.98  
% 3.55/0.98  fof(f87,plain,(
% 3.55/0.98    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.55/0.98    inference(cnf_transformation,[],[f44])).
% 3.55/0.98  
% 3.55/0.98  fof(f12,axiom,(
% 3.55/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.55/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.98  
% 3.55/0.98  fof(f33,plain,(
% 3.55/0.98    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.55/0.98    inference(ennf_transformation,[],[f12])).
% 3.55/0.98  
% 3.55/0.98  fof(f76,plain,(
% 3.55/0.98    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.55/0.98    inference(cnf_transformation,[],[f33])).
% 3.55/0.98  
% 3.55/0.98  fof(f16,axiom,(
% 3.55/0.98    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.55/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.98  
% 3.55/0.98  fof(f37,plain,(
% 3.55/0.98    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.55/0.98    inference(ennf_transformation,[],[f16])).
% 3.55/0.98  
% 3.55/0.98  fof(f38,plain,(
% 3.55/0.98    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.55/0.98    inference(flattening,[],[f37])).
% 3.55/0.98  
% 3.55/0.98  fof(f53,plain,(
% 3.55/0.98    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.55/0.98    inference(nnf_transformation,[],[f38])).
% 3.55/0.98  
% 3.55/0.98  fof(f82,plain,(
% 3.55/0.98    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.55/0.98    inference(cnf_transformation,[],[f53])).
% 3.55/0.98  
% 3.55/0.98  fof(f107,plain,(
% 3.55/0.98    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.55/0.98    inference(equality_resolution,[],[f82])).
% 3.55/0.98  
% 3.55/0.98  fof(f11,axiom,(
% 3.55/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.55/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.98  
% 3.55/0.98  fof(f32,plain,(
% 3.55/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.55/0.98    inference(ennf_transformation,[],[f11])).
% 3.55/0.98  
% 3.55/0.98  fof(f74,plain,(
% 3.55/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.55/0.98    inference(cnf_transformation,[],[f32])).
% 3.55/0.98  
% 3.55/0.98  fof(f97,plain,(
% 3.55/0.98    ~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)),
% 3.55/0.98    inference(cnf_transformation,[],[f56])).
% 3.55/0.98  
% 3.55/0.98  fof(f7,axiom,(
% 3.55/0.98    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 3.55/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.98  
% 3.55/0.98  fof(f29,plain,(
% 3.55/0.98    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.55/0.98    inference(ennf_transformation,[],[f7])).
% 3.55/0.98  
% 3.55/0.98  fof(f30,plain,(
% 3.55/0.98    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.55/0.98    inference(flattening,[],[f29])).
% 3.55/0.98  
% 3.55/0.98  fof(f68,plain,(
% 3.55/0.98    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.55/0.98    inference(cnf_transformation,[],[f30])).
% 3.55/0.98  
% 3.55/0.98  fof(f18,axiom,(
% 3.55/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.55/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.98  
% 3.55/0.98  fof(f41,plain,(
% 3.55/0.98    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.55/0.98    inference(ennf_transformation,[],[f18])).
% 3.55/0.98  
% 3.55/0.98  fof(f42,plain,(
% 3.55/0.98    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.55/0.98    inference(flattening,[],[f41])).
% 3.55/0.98  
% 3.55/0.98  fof(f85,plain,(
% 3.55/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.55/0.98    inference(cnf_transformation,[],[f42])).
% 3.55/0.98  
% 3.55/0.98  fof(f2,axiom,(
% 3.55/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.55/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.98  
% 3.55/0.98  fof(f49,plain,(
% 3.55/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.55/0.98    inference(nnf_transformation,[],[f2])).
% 3.55/0.98  
% 3.55/0.98  fof(f50,plain,(
% 3.55/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.55/0.98    inference(flattening,[],[f49])).
% 3.55/0.98  
% 3.55/0.98  fof(f58,plain,(
% 3.55/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.55/0.98    inference(cnf_transformation,[],[f50])).
% 3.55/0.98  
% 3.55/0.98  fof(f105,plain,(
% 3.55/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.55/0.98    inference(equality_resolution,[],[f58])).
% 3.55/0.98  
% 3.55/0.98  fof(f60,plain,(
% 3.55/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.55/0.98    inference(cnf_transformation,[],[f50])).
% 3.55/0.98  
% 3.55/0.98  fof(f8,axiom,(
% 3.55/0.98    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.55/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.98  
% 3.55/0.98  fof(f69,plain,(
% 3.55/0.98    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 3.55/0.98    inference(cnf_transformation,[],[f8])).
% 3.55/0.98  
% 3.55/0.98  fof(f99,plain,(
% 3.55/0.98    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 3.55/0.98    inference(definition_unfolding,[],[f69,f86])).
% 3.55/0.98  
% 3.55/0.98  fof(f67,plain,(
% 3.55/0.98    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.55/0.98    inference(cnf_transformation,[],[f30])).
% 3.55/0.98  
% 3.55/0.98  fof(f72,plain,(
% 3.55/0.98    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 3.55/0.98    inference(cnf_transformation,[],[f10])).
% 3.55/0.98  
% 3.55/0.98  fof(f102,plain,(
% 3.55/0.98    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 3.55/0.98    inference(definition_unfolding,[],[f72,f86])).
% 3.55/0.98  
% 3.55/0.98  fof(f6,axiom,(
% 3.55/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 3.55/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.98  
% 3.55/0.98  fof(f28,plain,(
% 3.55/0.98    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.55/0.98    inference(ennf_transformation,[],[f6])).
% 3.55/0.98  
% 3.55/0.98  fof(f66,plain,(
% 3.55/0.98    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.55/0.98    inference(cnf_transformation,[],[f28])).
% 3.55/0.98  
% 3.55/0.98  fof(f75,plain,(
% 3.55/0.98    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.55/0.98    inference(cnf_transformation,[],[f33])).
% 3.55/0.98  
% 3.55/0.98  fof(f4,axiom,(
% 3.55/0.98    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.55/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.98  
% 3.55/0.98  fof(f25,plain,(
% 3.55/0.98    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.55/0.98    inference(ennf_transformation,[],[f4])).
% 3.55/0.98  
% 3.55/0.98  fof(f51,plain,(
% 3.55/0.98    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.55/0.98    inference(nnf_transformation,[],[f25])).
% 3.55/0.98  
% 3.55/0.98  fof(f62,plain,(
% 3.55/0.98    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.55/0.98    inference(cnf_transformation,[],[f51])).
% 3.55/0.98  
% 3.55/0.98  cnf(c_15,plain,
% 3.55/0.98      ( v2_funct_1(k6_partfun1(X0)) ),
% 3.55/0.98      inference(cnf_transformation,[],[f101]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_1409,plain,
% 3.55/0.98      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 3.55/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_22,plain,
% 3.55/0.98      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.55/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.55/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.55/0.98      | X3 = X2 ),
% 3.55/0.98      inference(cnf_transformation,[],[f78]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_33,negated_conjecture,
% 3.55/0.98      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 3.55/0.98      inference(cnf_transformation,[],[f96]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_547,plain,
% 3.55/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.55/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.55/0.98      | X3 = X0
% 3.55/0.98      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 3.55/0.98      | k6_partfun1(sK0) != X3
% 3.55/0.98      | sK0 != X2
% 3.55/0.98      | sK0 != X1 ),
% 3.55/0.98      inference(resolution_lifted,[status(thm)],[c_22,c_33]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_548,plain,
% 3.55/0.98      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.55/0.98      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.55/0.98      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.55/0.98      inference(unflattening,[status(thm)],[c_547]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_23,plain,
% 3.55/0.98      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.55/0.98      inference(cnf_transformation,[],[f103]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_556,plain,
% 3.55/0.98      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.55/0.98      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.55/0.98      inference(forward_subsumption_resolution,
% 3.55/0.98                [status(thm)],
% 3.55/0.98                [c_548,c_23]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_1389,plain,
% 3.55/0.98      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.55/0.98      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.55/0.98      inference(predicate_to_equality,[status(thm)],[c_556]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_39,negated_conjecture,
% 3.55/0.98      ( v1_funct_1(sK2) ),
% 3.55/0.98      inference(cnf_transformation,[],[f90]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_37,negated_conjecture,
% 3.55/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.55/0.98      inference(cnf_transformation,[],[f92]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_36,negated_conjecture,
% 3.55/0.98      ( v1_funct_1(sK3) ),
% 3.55/0.98      inference(cnf_transformation,[],[f93]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_34,negated_conjecture,
% 3.55/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 3.55/0.98      inference(cnf_transformation,[],[f95]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_26,plain,
% 3.55/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.55/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.55/0.98      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.55/0.98      | ~ v1_funct_1(X0)
% 3.55/0.98      | ~ v1_funct_1(X3) ),
% 3.55/0.98      inference(cnf_transformation,[],[f84]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_1472,plain,
% 3.55/0.98      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.55/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.55/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.55/0.98      | ~ v1_funct_1(sK2)
% 3.55/0.98      | ~ v1_funct_1(sK3) ),
% 3.55/0.98      inference(instantiation,[status(thm)],[c_26]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_1972,plain,
% 3.55/0.98      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.55/0.98      inference(global_propositional_subsumption,
% 3.55/0.98                [status(thm)],
% 3.55/0.98                [c_1389,c_39,c_37,c_36,c_34,c_556,c_1472]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_31,plain,
% 3.55/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.55/0.98      | ~ v1_funct_2(X3,X4,X1)
% 3.55/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 3.55/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.55/0.98      | ~ v1_funct_1(X0)
% 3.55/0.98      | ~ v1_funct_1(X3)
% 3.55/0.98      | v2_funct_1(X3)
% 3.55/0.98      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 3.55/0.98      | k1_xboole_0 = X2 ),
% 3.55/0.98      inference(cnf_transformation,[],[f88]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_1400,plain,
% 3.55/0.98      ( k1_xboole_0 = X0
% 3.55/0.98      | v1_funct_2(X1,X2,X0) != iProver_top
% 3.55/0.98      | v1_funct_2(X3,X4,X2) != iProver_top
% 3.55/0.98      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
% 3.55/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 3.55/0.98      | v1_funct_1(X1) != iProver_top
% 3.55/0.98      | v1_funct_1(X3) != iProver_top
% 3.55/0.98      | v2_funct_1(X3) = iProver_top
% 3.55/0.98      | v2_funct_1(k1_partfun1(X4,X2,X2,X0,X3,X1)) != iProver_top ),
% 3.55/0.98      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_4113,plain,
% 3.55/0.98      ( sK0 = k1_xboole_0
% 3.55/0.98      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 3.55/0.98      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 3.55/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.55/0.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.55/0.98      | v1_funct_1(sK2) != iProver_top
% 3.55/0.98      | v1_funct_1(sK3) != iProver_top
% 3.55/0.98      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 3.55/0.98      | v2_funct_1(sK2) = iProver_top ),
% 3.55/0.98      inference(superposition,[status(thm)],[c_1972,c_1400]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_40,plain,
% 3.55/0.98      ( v1_funct_1(sK2) = iProver_top ),
% 3.55/0.98      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_38,negated_conjecture,
% 3.55/0.98      ( v1_funct_2(sK2,sK0,sK1) ),
% 3.55/0.98      inference(cnf_transformation,[],[f91]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_41,plain,
% 3.55/0.98      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 3.55/0.98      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_42,plain,
% 3.55/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.55/0.98      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_43,plain,
% 3.55/0.98      ( v1_funct_1(sK3) = iProver_top ),
% 3.55/0.98      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_35,negated_conjecture,
% 3.55/0.98      ( v1_funct_2(sK3,sK1,sK0) ),
% 3.55/0.98      inference(cnf_transformation,[],[f94]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_44,plain,
% 3.55/0.98      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 3.55/0.98      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_45,plain,
% 3.55/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.55/0.98      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_1399,plain,
% 3.55/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.55/0.98      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_20,plain,
% 3.55/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.55/0.98      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.55/0.98      inference(cnf_transformation,[],[f77]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_1406,plain,
% 3.55/0.98      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.55/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.55/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_3737,plain,
% 3.55/0.98      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 3.55/0.98      inference(superposition,[status(thm)],[c_1399,c_1406]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_29,plain,
% 3.55/0.98      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.55/0.98      | ~ v1_funct_2(X2,X0,X1)
% 3.55/0.98      | ~ v1_funct_2(X3,X1,X0)
% 3.55/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.55/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.55/0.98      | ~ v1_funct_1(X2)
% 3.55/0.98      | ~ v1_funct_1(X3)
% 3.55/0.98      | k2_relset_1(X1,X0,X3) = X0 ),
% 3.55/0.98      inference(cnf_transformation,[],[f87]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_560,plain,
% 3.55/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.55/0.98      | ~ v1_funct_2(X3,X2,X1)
% 3.55/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.55/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.55/0.98      | ~ v1_funct_1(X0)
% 3.55/0.98      | ~ v1_funct_1(X3)
% 3.55/0.98      | k1_partfun1(X2,X1,X1,X2,X3,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.55/0.98      | k2_relset_1(X1,X2,X0) = X2
% 3.55/0.98      | k6_partfun1(X2) != k6_partfun1(sK0)
% 3.55/0.98      | sK0 != X2 ),
% 3.55/0.98      inference(resolution_lifted,[status(thm)],[c_29,c_33]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_561,plain,
% 3.55/0.98      ( ~ v1_funct_2(X0,X1,sK0)
% 3.55/0.98      | ~ v1_funct_2(X2,sK0,X1)
% 3.55/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 3.55/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 3.55/0.98      | ~ v1_funct_1(X0)
% 3.55/0.98      | ~ v1_funct_1(X2)
% 3.55/0.98      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.55/0.98      | k2_relset_1(X1,sK0,X0) = sK0
% 3.55/0.98      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 3.55/0.98      inference(unflattening,[status(thm)],[c_560]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_646,plain,
% 3.55/0.98      ( ~ v1_funct_2(X0,X1,sK0)
% 3.55/0.98      | ~ v1_funct_2(X2,sK0,X1)
% 3.55/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 3.55/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 3.55/0.98      | ~ v1_funct_1(X0)
% 3.55/0.98      | ~ v1_funct_1(X2)
% 3.55/0.98      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.55/0.98      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 3.55/0.98      inference(equality_resolution_simp,[status(thm)],[c_561]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_1388,plain,
% 3.55/0.98      ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.55/0.98      | k2_relset_1(X0,sK0,X2) = sK0
% 3.55/0.98      | v1_funct_2(X2,X0,sK0) != iProver_top
% 3.55/0.98      | v1_funct_2(X1,sK0,X0) != iProver_top
% 3.55/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 3.55/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 3.55/0.98      | v1_funct_1(X2) != iProver_top
% 3.55/0.98      | v1_funct_1(X1) != iProver_top ),
% 3.55/0.98      inference(predicate_to_equality,[status(thm)],[c_646]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_2074,plain,
% 3.55/0.98      ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k6_partfun1(sK0)
% 3.55/0.98      | k2_relset_1(X0,sK0,X2) = sK0
% 3.55/0.98      | v1_funct_2(X2,X0,sK0) != iProver_top
% 3.55/0.98      | v1_funct_2(X1,sK0,X0) != iProver_top
% 3.55/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 3.55/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 3.55/0.98      | v1_funct_1(X1) != iProver_top
% 3.55/0.98      | v1_funct_1(X2) != iProver_top ),
% 3.55/0.98      inference(light_normalisation,[status(thm)],[c_1388,c_1972]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_2078,plain,
% 3.55/0.98      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 3.55/0.98      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 3.55/0.98      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 3.55/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.55/0.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.55/0.98      | v1_funct_1(sK2) != iProver_top
% 3.55/0.98      | v1_funct_1(sK3) != iProver_top ),
% 3.55/0.98      inference(superposition,[status(thm)],[c_1972,c_2074]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_2081,plain,
% 3.55/0.98      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 3.55/0.98      inference(global_propositional_subsumption,
% 3.55/0.98                [status(thm)],
% 3.55/0.98                [c_2078,c_40,c_41,c_42,c_43,c_44,c_45]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_3739,plain,
% 3.55/0.98      ( k2_relat_1(sK3) = sK0 ),
% 3.55/0.98      inference(light_normalisation,[status(thm)],[c_3737,c_2081]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_18,plain,
% 3.55/0.98      ( v5_relat_1(X0,X1)
% 3.55/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.55/0.98      inference(cnf_transformation,[],[f76]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_24,plain,
% 3.55/0.98      ( v2_funct_2(X0,k2_relat_1(X0))
% 3.55/0.98      | ~ v5_relat_1(X0,k2_relat_1(X0))
% 3.55/0.98      | ~ v1_relat_1(X0) ),
% 3.55/0.98      inference(cnf_transformation,[],[f107]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_465,plain,
% 3.55/0.98      ( v2_funct_2(X0,k2_relat_1(X0))
% 3.55/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.55/0.98      | ~ v1_relat_1(X0)
% 3.55/0.98      | X0 != X1
% 3.55/0.98      | k2_relat_1(X0) != X3 ),
% 3.55/0.98      inference(resolution_lifted,[status(thm)],[c_18,c_24]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_466,plain,
% 3.55/0.98      ( v2_funct_2(X0,k2_relat_1(X0))
% 3.55/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
% 3.55/0.98      | ~ v1_relat_1(X0) ),
% 3.55/0.98      inference(unflattening,[status(thm)],[c_465]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_17,plain,
% 3.55/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.55/0.98      | v1_relat_1(X0) ),
% 3.55/0.98      inference(cnf_transformation,[],[f74]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_476,plain,
% 3.55/0.98      ( v2_funct_2(X0,k2_relat_1(X0))
% 3.55/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0)))) ),
% 3.55/0.98      inference(forward_subsumption_resolution,
% 3.55/0.98                [status(thm)],
% 3.55/0.98                [c_466,c_17]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_32,negated_conjecture,
% 3.55/0.98      ( ~ v2_funct_2(sK3,sK0) | ~ v2_funct_1(sK2) ),
% 3.55/0.98      inference(cnf_transformation,[],[f97]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_491,plain,
% 3.55/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
% 3.55/0.98      | ~ v2_funct_1(sK2)
% 3.55/0.98      | k2_relat_1(X0) != sK0
% 3.55/0.98      | sK3 != X0 ),
% 3.55/0.98      inference(resolution_lifted,[status(thm)],[c_476,c_32]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_492,plain,
% 3.55/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3))))
% 3.55/0.98      | ~ v2_funct_1(sK2)
% 3.55/0.98      | k2_relat_1(sK3) != sK0 ),
% 3.55/0.98      inference(unflattening,[status(thm)],[c_491]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_828,plain,
% 3.55/0.98      ( ~ v2_funct_1(sK2) | sP0_iProver_split | k2_relat_1(sK3) != sK0 ),
% 3.55/0.98      inference(splitting,
% 3.55/0.98                [splitting(split),new_symbols(definition,[])],
% 3.55/0.98                [c_492]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_1391,plain,
% 3.55/0.98      ( k2_relat_1(sK3) != sK0
% 3.55/0.98      | v2_funct_1(sK2) != iProver_top
% 3.55/0.98      | sP0_iProver_split = iProver_top ),
% 3.55/0.98      inference(predicate_to_equality,[status(thm)],[c_828]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_4045,plain,
% 3.55/0.98      ( sK0 != sK0
% 3.55/0.98      | v2_funct_1(sK2) != iProver_top
% 3.55/0.98      | sP0_iProver_split = iProver_top ),
% 3.55/0.98      inference(demodulation,[status(thm)],[c_3739,c_1391]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_4046,plain,
% 3.55/0.98      ( v2_funct_1(sK2) != iProver_top
% 3.55/0.98      | sP0_iProver_split = iProver_top ),
% 3.55/0.98      inference(equality_resolution_simp,[status(thm)],[c_4045]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_827,plain,
% 3.55/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3))))
% 3.55/0.98      | ~ sP0_iProver_split ),
% 3.55/0.98      inference(splitting,
% 3.55/0.98                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 3.55/0.98                [c_492]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_1392,plain,
% 3.55/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3)))) != iProver_top
% 3.55/0.98      | sP0_iProver_split != iProver_top ),
% 3.55/0.98      inference(predicate_to_equality,[status(thm)],[c_827]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_4044,plain,
% 3.55/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 3.55/0.98      | sP0_iProver_split != iProver_top ),
% 3.55/0.98      inference(demodulation,[status(thm)],[c_3739,c_1392]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_4069,plain,
% 3.55/0.98      ( sP0_iProver_split != iProver_top ),
% 3.55/0.98      inference(superposition,[status(thm)],[c_1399,c_4044]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_4513,plain,
% 3.55/0.98      ( v2_funct_1(k6_partfun1(sK0)) != iProver_top | sK0 = k1_xboole_0 ),
% 3.55/0.98      inference(global_propositional_subsumption,
% 3.55/0.98                [status(thm)],
% 3.55/0.98                [c_4113,c_40,c_41,c_42,c_43,c_44,c_45,c_4046,c_4069]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_4514,plain,
% 3.55/0.98      ( sK0 = k1_xboole_0 | v2_funct_1(k6_partfun1(sK0)) != iProver_top ),
% 3.55/0.98      inference(renaming,[status(thm)],[c_4513]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_4517,plain,
% 3.55/0.98      ( sK0 = k1_xboole_0 ),
% 3.55/0.98      inference(superposition,[status(thm)],[c_1409,c_4514]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_1396,plain,
% 3.55/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.55/0.98      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_4527,plain,
% 3.55/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) = iProver_top ),
% 3.55/0.98      inference(demodulation,[status(thm)],[c_4517,c_1396]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_10,plain,
% 3.55/0.98      ( ~ v1_relat_1(X0)
% 3.55/0.98      | k2_relat_1(X0) != k1_xboole_0
% 3.55/0.98      | k1_xboole_0 = X0 ),
% 3.55/0.98      inference(cnf_transformation,[],[f68]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_1412,plain,
% 3.55/0.98      ( k2_relat_1(X0) != k1_xboole_0
% 3.55/0.98      | k1_xboole_0 = X0
% 3.55/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.55/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_4051,plain,
% 3.55/0.98      ( sK0 != k1_xboole_0
% 3.55/0.98      | sK3 = k1_xboole_0
% 3.55/0.98      | v1_relat_1(sK3) != iProver_top ),
% 3.55/0.98      inference(superposition,[status(thm)],[c_3739,c_1412]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_1407,plain,
% 3.55/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.55/0.98      | v1_relat_1(X0) = iProver_top ),
% 3.55/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_2433,plain,
% 3.55/0.98      ( v1_relat_1(sK3) = iProver_top ),
% 3.55/0.98      inference(superposition,[status(thm)],[c_1399,c_1407]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_4249,plain,
% 3.55/0.98      ( sK3 = k1_xboole_0 | sK0 != k1_xboole_0 ),
% 3.55/0.98      inference(global_propositional_subsumption,
% 3.55/0.98                [status(thm)],
% 3.55/0.98                [c_4051,c_2433]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_4250,plain,
% 3.55/0.98      ( sK0 != k1_xboole_0 | sK3 = k1_xboole_0 ),
% 3.55/0.98      inference(renaming,[status(thm)],[c_4249]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_4518,plain,
% 3.55/0.98      ( sK3 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.55/0.98      inference(demodulation,[status(thm)],[c_4517,c_4250]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_4532,plain,
% 3.55/0.98      ( sK3 = k1_xboole_0 ),
% 3.55/0.98      inference(equality_resolution_simp,[status(thm)],[c_4518]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_4526,plain,
% 3.55/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
% 3.55/0.98      inference(demodulation,[status(thm)],[c_4517,c_1399]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_4536,plain,
% 3.55/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
% 3.55/0.98      inference(demodulation,[status(thm)],[c_4532,c_4526]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_28,plain,
% 3.55/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.55/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.55/0.98      | ~ v1_funct_1(X0)
% 3.55/0.98      | ~ v1_funct_1(X3)
% 3.55/0.98      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.55/0.98      inference(cnf_transformation,[],[f85]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_1402,plain,
% 3.55/0.98      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 3.55/0.98      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.55/0.98      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.55/0.98      | v1_funct_1(X5) != iProver_top
% 3.55/0.98      | v1_funct_1(X4) != iProver_top ),
% 3.55/0.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_4761,plain,
% 3.55/0.98      ( k1_partfun1(X0,X1,sK1,k1_xboole_0,X2,k1_xboole_0) = k5_relat_1(X2,k1_xboole_0)
% 3.55/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.55/0.98      | v1_funct_1(X2) != iProver_top
% 3.55/0.98      | v1_funct_1(k1_xboole_0) != iProver_top ),
% 3.55/0.98      inference(superposition,[status(thm)],[c_4536,c_1402]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_3,plain,
% 3.55/0.98      ( r1_tarski(X0,X0) ),
% 3.55/0.98      inference(cnf_transformation,[],[f105]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_129,plain,
% 3.55/0.98      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 3.55/0.98      inference(instantiation,[status(thm)],[c_3]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_1,plain,
% 3.55/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.55/0.98      inference(cnf_transformation,[],[f60]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_133,plain,
% 3.55/0.98      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 3.55/0.98      | k1_xboole_0 = k1_xboole_0 ),
% 3.55/0.98      inference(instantiation,[status(thm)],[c_1]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_845,plain,
% 3.55/0.98      ( ~ v1_funct_1(X0) | v1_funct_1(X1) | X1 != X0 ),
% 3.55/0.98      theory(equality) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_1570,plain,
% 3.55/0.98      ( v1_funct_1(X0) | ~ v1_funct_1(sK3) | X0 != sK3 ),
% 3.55/0.98      inference(instantiation,[status(thm)],[c_845]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_1571,plain,
% 3.55/0.98      ( X0 != sK3
% 3.55/0.98      | v1_funct_1(X0) = iProver_top
% 3.55/0.98      | v1_funct_1(sK3) != iProver_top ),
% 3.55/0.98      inference(predicate_to_equality,[status(thm)],[c_1570]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_1573,plain,
% 3.55/0.98      ( k1_xboole_0 != sK3
% 3.55/0.98      | v1_funct_1(sK3) != iProver_top
% 3.55/0.98      | v1_funct_1(k1_xboole_0) = iProver_top ),
% 3.55/0.98      inference(instantiation,[status(thm)],[c_1571]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_831,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_1624,plain,
% 3.55/0.98      ( X0 != X1 | X0 = sK3 | sK3 != X1 ),
% 3.55/0.98      inference(instantiation,[status(thm)],[c_831]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_1625,plain,
% 3.55/0.98      ( sK3 != k1_xboole_0
% 3.55/0.98      | k1_xboole_0 = sK3
% 3.55/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 3.55/0.98      inference(instantiation,[status(thm)],[c_1624]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_5385,plain,
% 3.55/0.98      ( v1_funct_1(X2) != iProver_top
% 3.55/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.55/0.98      | k1_partfun1(X0,X1,sK1,k1_xboole_0,X2,k1_xboole_0) = k5_relat_1(X2,k1_xboole_0) ),
% 3.55/0.98      inference(global_propositional_subsumption,
% 3.55/0.98                [status(thm)],
% 3.55/0.98                [c_4761,c_43,c_129,c_133,c_1573,c_1625,c_2433,c_4051,
% 3.55/0.98                 c_4517]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_5386,plain,
% 3.55/0.98      ( k1_partfun1(X0,X1,sK1,k1_xboole_0,X2,k1_xboole_0) = k5_relat_1(X2,k1_xboole_0)
% 3.55/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.55/0.98      | v1_funct_1(X2) != iProver_top ),
% 3.55/0.98      inference(renaming,[status(thm)],[c_5385]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_5392,plain,
% 3.55/0.98      ( k1_partfun1(k1_xboole_0,sK1,sK1,k1_xboole_0,sK2,k1_xboole_0) = k5_relat_1(sK2,k1_xboole_0)
% 3.55/0.98      | v1_funct_1(sK2) != iProver_top ),
% 3.55/0.98      inference(superposition,[status(thm)],[c_4527,c_5386]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_4525,plain,
% 3.55/0.98      ( k1_partfun1(k1_xboole_0,sK1,sK1,k1_xboole_0,sK2,sK3) = k6_partfun1(k1_xboole_0) ),
% 3.55/0.98      inference(demodulation,[status(thm)],[c_4517,c_1972]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_13,plain,
% 3.55/0.98      ( k1_relat_1(k6_partfun1(X0)) = X0 ),
% 3.55/0.98      inference(cnf_transformation,[],[f99]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_11,plain,
% 3.55/0.98      ( ~ v1_relat_1(X0)
% 3.55/0.98      | k1_relat_1(X0) != k1_xboole_0
% 3.55/0.98      | k1_xboole_0 = X0 ),
% 3.55/0.98      inference(cnf_transformation,[],[f67]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_1411,plain,
% 3.55/0.98      ( k1_relat_1(X0) != k1_xboole_0
% 3.55/0.98      | k1_xboole_0 = X0
% 3.55/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.55/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_2510,plain,
% 3.55/0.98      ( k6_partfun1(X0) = k1_xboole_0
% 3.55/0.98      | k1_xboole_0 != X0
% 3.55/0.98      | v1_relat_1(k6_partfun1(X0)) != iProver_top ),
% 3.55/0.98      inference(superposition,[status(thm)],[c_13,c_1411]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_16,plain,
% 3.55/0.98      ( v1_relat_1(k6_partfun1(X0)) ),
% 3.55/0.98      inference(cnf_transformation,[],[f102]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_93,plain,
% 3.55/0.98      ( v1_relat_1(k6_partfun1(X0)) = iProver_top ),
% 3.55/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_2666,plain,
% 3.55/0.98      ( k1_xboole_0 != X0 | k6_partfun1(X0) = k1_xboole_0 ),
% 3.55/0.98      inference(global_propositional_subsumption,
% 3.55/0.98                [status(thm)],
% 3.55/0.98                [c_2510,c_93]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_2667,plain,
% 3.55/0.98      ( k6_partfun1(X0) = k1_xboole_0 | k1_xboole_0 != X0 ),
% 3.55/0.98      inference(renaming,[status(thm)],[c_2666]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_2669,plain,
% 3.55/0.98      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 3.55/0.98      inference(equality_resolution,[status(thm)],[c_2667]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_4530,plain,
% 3.55/0.98      ( k1_partfun1(k1_xboole_0,sK1,sK1,k1_xboole_0,sK2,sK3) = k1_xboole_0 ),
% 3.55/0.98      inference(light_normalisation,[status(thm)],[c_4525,c_2669]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_4535,plain,
% 3.55/0.98      ( k1_partfun1(k1_xboole_0,sK1,sK1,k1_xboole_0,sK2,k1_xboole_0) = k1_xboole_0 ),
% 3.55/0.98      inference(demodulation,[status(thm)],[c_4532,c_4530]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_5396,plain,
% 3.55/0.98      ( k5_relat_1(sK2,k1_xboole_0) = k1_xboole_0
% 3.55/0.98      | v1_funct_1(sK2) != iProver_top ),
% 3.55/0.98      inference(light_normalisation,[status(thm)],[c_5392,c_4535]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_5464,plain,
% 3.55/0.98      ( k5_relat_1(sK2,k1_xboole_0) = k1_xboole_0 ),
% 3.55/0.98      inference(global_propositional_subsumption,
% 3.55/0.98                [status(thm)],
% 3.55/0.98                [c_5396,c_40]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_9,plain,
% 3.55/0.98      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
% 3.55/0.98      | ~ v1_relat_1(X1)
% 3.55/0.98      | ~ v1_relat_1(X0) ),
% 3.55/0.98      inference(cnf_transformation,[],[f66]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_1413,plain,
% 3.55/0.98      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) = iProver_top
% 3.55/0.98      | v1_relat_1(X0) != iProver_top
% 3.55/0.98      | v1_relat_1(X1) != iProver_top ),
% 3.55/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_5466,plain,
% 3.55/0.98      ( r1_tarski(k1_relat_1(k1_xboole_0),k1_relat_1(sK2)) = iProver_top
% 3.55/0.98      | v1_relat_1(sK2) != iProver_top
% 3.55/0.98      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.55/0.98      inference(superposition,[status(thm)],[c_5464,c_1413]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_2923,plain,
% 3.55/0.98      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.55/0.98      inference(superposition,[status(thm)],[c_2669,c_13]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_5469,plain,
% 3.55/0.98      ( r1_tarski(k1_xboole_0,k1_relat_1(sK2)) = iProver_top
% 3.55/0.98      | v1_relat_1(sK2) != iProver_top
% 3.55/0.98      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.55/0.98      inference(light_normalisation,[status(thm)],[c_5466,c_2923]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_19,plain,
% 3.55/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.55/0.98      | v4_relat_1(X0,X1) ),
% 3.55/0.98      inference(cnf_transformation,[],[f75]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_6,plain,
% 3.55/0.98      ( ~ v4_relat_1(X0,X1)
% 3.55/0.98      | r1_tarski(k1_relat_1(X0),X1)
% 3.55/0.98      | ~ v1_relat_1(X0) ),
% 3.55/0.98      inference(cnf_transformation,[],[f62]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_425,plain,
% 3.55/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.55/0.98      | r1_tarski(k1_relat_1(X0),X1)
% 3.55/0.98      | ~ v1_relat_1(X0) ),
% 3.55/0.98      inference(resolution,[status(thm)],[c_19,c_6]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_429,plain,
% 3.55/0.98      ( r1_tarski(k1_relat_1(X0),X1)
% 3.55/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.55/0.98      inference(global_propositional_subsumption,
% 3.55/0.98                [status(thm)],
% 3.55/0.98                [c_425,c_17]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_430,plain,
% 3.55/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.55/0.98      | r1_tarski(k1_relat_1(X0),X1) ),
% 3.55/0.98      inference(renaming,[status(thm)],[c_429]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_1393,plain,
% 3.55/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.55/0.98      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 3.55/0.98      inference(predicate_to_equality,[status(thm)],[c_430]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_3409,plain,
% 3.55/0.98      ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
% 3.55/0.98      inference(superposition,[status(thm)],[c_1396,c_1393]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_1418,plain,
% 3.55/0.98      ( X0 = X1
% 3.55/0.98      | r1_tarski(X0,X1) != iProver_top
% 3.55/0.98      | r1_tarski(X1,X0) != iProver_top ),
% 3.55/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_4015,plain,
% 3.55/0.98      ( k1_relat_1(sK2) = sK0
% 3.55/0.98      | r1_tarski(sK0,k1_relat_1(sK2)) != iProver_top ),
% 3.55/0.98      inference(superposition,[status(thm)],[c_3409,c_1418]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_4519,plain,
% 3.55/0.98      ( k1_relat_1(sK2) = k1_xboole_0
% 3.55/0.98      | r1_tarski(k1_xboole_0,k1_relat_1(sK2)) != iProver_top ),
% 3.55/0.98      inference(demodulation,[status(thm)],[c_4517,c_4015]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_835,plain,
% 3.55/0.98      ( ~ v1_relat_1(X0) | v1_relat_1(X1) | X1 != X0 ),
% 3.55/0.98      theory(equality) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_2828,plain,
% 3.55/0.98      ( v1_relat_1(X0)
% 3.55/0.98      | ~ v1_relat_1(k6_partfun1(X1))
% 3.55/0.98      | X0 != k6_partfun1(X1) ),
% 3.55/0.98      inference(instantiation,[status(thm)],[c_835]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_2829,plain,
% 3.55/0.98      ( X0 != k6_partfun1(X1)
% 3.55/0.98      | v1_relat_1(X0) = iProver_top
% 3.55/0.98      | v1_relat_1(k6_partfun1(X1)) != iProver_top ),
% 3.55/0.98      inference(predicate_to_equality,[status(thm)],[c_2828]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_2831,plain,
% 3.55/0.98      ( k1_xboole_0 != k6_partfun1(k1_xboole_0)
% 3.55/0.98      | v1_relat_1(k6_partfun1(k1_xboole_0)) != iProver_top
% 3.55/0.98      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.55/0.98      inference(instantiation,[status(thm)],[c_2829]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_2434,plain,
% 3.55/0.98      ( v1_relat_1(sK2) = iProver_top ),
% 3.55/0.98      inference(superposition,[status(thm)],[c_1396,c_1407]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_2436,plain,
% 3.55/0.98      ( v1_relat_1(sK2) ),
% 3.55/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_2434]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_2416,plain,
% 3.55/0.98      ( ~ v1_relat_1(k6_partfun1(X0))
% 3.55/0.98      | k1_relat_1(k6_partfun1(X0)) != k1_xboole_0
% 3.55/0.98      | k1_xboole_0 = k6_partfun1(X0) ),
% 3.55/0.98      inference(instantiation,[status(thm)],[c_11]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_2418,plain,
% 3.55/0.98      ( ~ v1_relat_1(k6_partfun1(k1_xboole_0))
% 3.55/0.98      | k1_relat_1(k6_partfun1(k1_xboole_0)) != k1_xboole_0
% 3.55/0.98      | k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
% 3.55/0.98      inference(instantiation,[status(thm)],[c_2416]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_1840,plain,
% 3.55/0.98      ( X0 != X1 | sK2 != X1 | sK2 = X0 ),
% 3.55/0.98      inference(instantiation,[status(thm)],[c_831]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_2250,plain,
% 3.55/0.98      ( X0 != sK2 | sK2 = X0 | sK2 != sK2 ),
% 3.55/0.98      inference(instantiation,[status(thm)],[c_1840]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_2251,plain,
% 3.55/0.98      ( sK2 != sK2 | sK2 = k1_xboole_0 | k1_xboole_0 != sK2 ),
% 3.55/0.98      inference(instantiation,[status(thm)],[c_2250]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_2201,plain,
% 3.55/0.98      ( r1_tarski(sK2,sK2) ),
% 3.55/0.98      inference(instantiation,[status(thm)],[c_3]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_1631,plain,
% 3.55/0.98      ( ~ r1_tarski(X0,sK2) | ~ r1_tarski(sK2,X0) | X0 = sK2 ),
% 3.55/0.98      inference(instantiation,[status(thm)],[c_1]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_1796,plain,
% 3.55/0.98      ( ~ r1_tarski(sK2,sK2) | sK2 = sK2 ),
% 3.55/0.98      inference(instantiation,[status(thm)],[c_1631]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_1746,plain,
% 3.55/0.98      ( ~ v1_relat_1(sK2)
% 3.55/0.98      | k1_relat_1(sK2) != k1_xboole_0
% 3.55/0.98      | k1_xboole_0 = sK2 ),
% 3.55/0.98      inference(instantiation,[status(thm)],[c_11]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_839,plain,
% 3.55/0.98      ( ~ v2_funct_1(X0) | v2_funct_1(X1) | X1 != X0 ),
% 3.55/0.98      theory(equality) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_1565,plain,
% 3.55/0.98      ( v2_funct_1(X0)
% 3.55/0.98      | ~ v2_funct_1(k6_partfun1(X1))
% 3.55/0.98      | X0 != k6_partfun1(X1) ),
% 3.55/0.98      inference(instantiation,[status(thm)],[c_839]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_1566,plain,
% 3.55/0.98      ( X0 != k6_partfun1(X1)
% 3.55/0.98      | v2_funct_1(X0) = iProver_top
% 3.55/0.98      | v2_funct_1(k6_partfun1(X1)) != iProver_top ),
% 3.55/0.98      inference(predicate_to_equality,[status(thm)],[c_1565]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_1568,plain,
% 3.55/0.98      ( k1_xboole_0 != k6_partfun1(k1_xboole_0)
% 3.55/0.98      | v2_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top
% 3.55/0.98      | v2_funct_1(k1_xboole_0) = iProver_top ),
% 3.55/0.98      inference(instantiation,[status(thm)],[c_1566]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_1467,plain,
% 3.55/0.98      ( ~ v2_funct_1(X0) | v2_funct_1(sK2) | sK2 != X0 ),
% 3.55/0.98      inference(instantiation,[status(thm)],[c_839]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_1468,plain,
% 3.55/0.98      ( sK2 != X0
% 3.55/0.98      | v2_funct_1(X0) != iProver_top
% 3.55/0.98      | v2_funct_1(sK2) = iProver_top ),
% 3.55/0.98      inference(predicate_to_equality,[status(thm)],[c_1467]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_1470,plain,
% 3.55/0.98      ( sK2 != k1_xboole_0
% 3.55/0.98      | v2_funct_1(sK2) = iProver_top
% 3.55/0.98      | v2_funct_1(k1_xboole_0) != iProver_top ),
% 3.55/0.98      inference(instantiation,[status(thm)],[c_1468]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_102,plain,
% 3.55/0.98      ( k1_relat_1(k6_partfun1(k1_xboole_0)) = k1_xboole_0 ),
% 3.55/0.98      inference(instantiation,[status(thm)],[c_13]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_96,plain,
% 3.55/0.98      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 3.55/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_98,plain,
% 3.55/0.98      ( v2_funct_1(k6_partfun1(k1_xboole_0)) = iProver_top ),
% 3.55/0.98      inference(instantiation,[status(thm)],[c_96]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_95,plain,
% 3.55/0.98      ( v1_relat_1(k6_partfun1(k1_xboole_0)) = iProver_top ),
% 3.55/0.98      inference(instantiation,[status(thm)],[c_93]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(c_94,plain,
% 3.55/0.98      ( v1_relat_1(k6_partfun1(k1_xboole_0)) ),
% 3.55/0.98      inference(instantiation,[status(thm)],[c_16]) ).
% 3.55/0.98  
% 3.55/0.98  cnf(contradiction,plain,
% 3.55/0.98      ( $false ),
% 3.55/0.98      inference(minisat,
% 3.55/0.98                [status(thm)],
% 3.55/0.98                [c_5469,c_4519,c_4069,c_4046,c_2831,c_2436,c_2434,c_2418,
% 3.55/0.98                 c_2251,c_2201,c_1796,c_1746,c_1568,c_1470,c_102,c_98,
% 3.55/0.98                 c_95,c_94]) ).
% 3.55/0.98  
% 3.55/0.98  
% 3.55/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.55/0.98  
% 3.55/0.98  ------                               Statistics
% 3.55/0.98  
% 3.55/0.98  ------ General
% 3.55/0.98  
% 3.55/0.98  abstr_ref_over_cycles:                  0
% 3.55/0.98  abstr_ref_under_cycles:                 0
% 3.55/0.98  gc_basic_clause_elim:                   0
% 3.55/0.98  forced_gc_time:                         0
% 3.55/0.98  parsing_time:                           0.01
% 3.55/0.98  unif_index_cands_time:                  0.
% 3.55/0.98  unif_index_add_time:                    0.
% 3.55/0.98  orderings_time:                         0.
% 3.55/0.98  out_proof_time:                         0.016
% 3.55/0.98  total_time:                             0.248
% 3.55/0.98  num_of_symbols:                         56
% 3.55/0.98  num_of_terms:                           9086
% 3.55/0.98  
% 3.55/0.98  ------ Preprocessing
% 3.55/0.98  
% 3.55/0.98  num_of_splits:                          1
% 3.55/0.98  num_of_split_atoms:                     1
% 3.55/0.98  num_of_reused_defs:                     0
% 3.55/0.98  num_eq_ax_congr_red:                    13
% 3.55/0.98  num_of_sem_filtered_clauses:            1
% 3.55/0.98  num_of_subtypes:                        0
% 3.55/0.98  monotx_restored_types:                  0
% 3.55/0.98  sat_num_of_epr_types:                   0
% 3.55/0.98  sat_num_of_non_cyclic_types:            0
% 3.55/0.98  sat_guarded_non_collapsed_types:        0
% 3.55/0.98  num_pure_diseq_elim:                    0
% 3.55/0.98  simp_replaced_by:                       0
% 3.55/0.98  res_preprocessed:                       175
% 3.55/0.98  prep_upred:                             0
% 3.55/0.98  prep_unflattend:                        17
% 3.55/0.98  smt_new_axioms:                         0
% 3.55/0.98  pred_elim_cands:                        7
% 3.55/0.98  pred_elim:                              4
% 3.55/0.98  pred_elim_cl:                           6
% 3.55/0.98  pred_elim_cycles:                       6
% 3.55/0.98  merged_defs:                            0
% 3.55/0.98  merged_defs_ncl:                        0
% 3.55/0.98  bin_hyper_res:                          0
% 3.55/0.98  prep_cycles:                            4
% 3.55/0.98  pred_elim_time:                         0.007
% 3.55/0.98  splitting_time:                         0.
% 3.55/0.98  sem_filter_time:                        0.
% 3.55/0.98  monotx_time:                            0.001
% 3.55/0.98  subtype_inf_time:                       0.
% 3.55/0.98  
% 3.55/0.98  ------ Problem properties
% 3.55/0.98  
% 3.55/0.98  clauses:                                34
% 3.55/0.98  conjectures:                            6
% 3.55/0.98  epr:                                    8
% 3.55/0.98  horn:                                   33
% 3.55/0.98  ground:                                 9
% 3.55/0.98  unary:                                  13
% 3.55/0.98  binary:                                 6
% 3.55/0.98  lits:                                   97
% 3.55/0.98  lits_eq:                                18
% 3.55/0.98  fd_pure:                                0
% 3.55/0.98  fd_pseudo:                              0
% 3.55/0.98  fd_cond:                                3
% 3.55/0.98  fd_pseudo_cond:                         2
% 3.55/0.98  ac_symbols:                             0
% 3.55/0.98  
% 3.55/0.98  ------ Propositional Solver
% 3.55/0.98  
% 3.55/0.98  prop_solver_calls:                      30
% 3.55/0.98  prop_fast_solver_calls:                 1261
% 3.55/0.98  smt_solver_calls:                       0
% 3.55/0.98  smt_fast_solver_calls:                  0
% 3.55/0.98  prop_num_of_clauses:                    2717
% 3.55/0.98  prop_preprocess_simplified:             7768
% 3.55/0.98  prop_fo_subsumed:                       34
% 3.55/0.98  prop_solver_time:                       0.
% 3.55/0.98  smt_solver_time:                        0.
% 3.55/0.98  smt_fast_solver_time:                   0.
% 3.55/0.98  prop_fast_solver_time:                  0.
% 3.55/0.98  prop_unsat_core_time:                   0.
% 3.55/0.98  
% 3.55/0.98  ------ QBF
% 3.55/0.98  
% 3.55/0.98  qbf_q_res:                              0
% 3.55/0.98  qbf_num_tautologies:                    0
% 3.55/0.98  qbf_prep_cycles:                        0
% 3.55/0.98  
% 3.55/0.98  ------ BMC1
% 3.55/0.98  
% 3.55/0.98  bmc1_current_bound:                     -1
% 3.55/0.98  bmc1_last_solved_bound:                 -1
% 3.55/0.98  bmc1_unsat_core_size:                   -1
% 3.55/0.98  bmc1_unsat_core_parents_size:           -1
% 3.55/0.98  bmc1_merge_next_fun:                    0
% 3.55/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.55/0.98  
% 3.55/0.98  ------ Instantiation
% 3.55/0.98  
% 3.55/0.98  inst_num_of_clauses:                    673
% 3.55/0.98  inst_num_in_passive:                    65
% 3.55/0.98  inst_num_in_active:                     388
% 3.55/0.98  inst_num_in_unprocessed:                220
% 3.55/0.98  inst_num_of_loops:                      420
% 3.55/0.98  inst_num_of_learning_restarts:          0
% 3.55/0.98  inst_num_moves_active_passive:          28
% 3.55/0.98  inst_lit_activity:                      0
% 3.55/0.98  inst_lit_activity_moves:                0
% 3.55/0.98  inst_num_tautologies:                   0
% 3.55/0.98  inst_num_prop_implied:                  0
% 3.55/0.98  inst_num_existing_simplified:           0
% 3.55/0.98  inst_num_eq_res_simplified:             0
% 3.55/0.98  inst_num_child_elim:                    0
% 3.55/0.98  inst_num_of_dismatching_blockings:      114
% 3.55/0.98  inst_num_of_non_proper_insts:           770
% 3.55/0.98  inst_num_of_duplicates:                 0
% 3.55/0.98  inst_inst_num_from_inst_to_res:         0
% 3.55/0.98  inst_dismatching_checking_time:         0.
% 3.55/0.98  
% 3.55/0.98  ------ Resolution
% 3.55/0.98  
% 3.55/0.98  res_num_of_clauses:                     0
% 3.55/0.98  res_num_in_passive:                     0
% 3.55/0.98  res_num_in_active:                      0
% 3.55/0.98  res_num_of_loops:                       179
% 3.55/0.98  res_forward_subset_subsumed:            32
% 3.55/0.98  res_backward_subset_subsumed:           0
% 3.55/0.98  res_forward_subsumed:                   0
% 3.55/0.98  res_backward_subsumed:                  0
% 3.55/0.98  res_forward_subsumption_resolution:     4
% 3.55/0.98  res_backward_subsumption_resolution:    0
% 3.55/0.98  res_clause_to_clause_subsumption:       209
% 3.55/0.98  res_orphan_elimination:                 0
% 3.55/0.98  res_tautology_del:                      34
% 3.55/0.98  res_num_eq_res_simplified:              1
% 3.55/0.98  res_num_sel_changes:                    0
% 3.55/0.98  res_moves_from_active_to_pass:          0
% 3.55/0.98  
% 3.55/0.98  ------ Superposition
% 3.55/0.98  
% 3.55/0.98  sup_time_total:                         0.
% 3.55/0.98  sup_time_generating:                    0.
% 3.55/0.98  sup_time_sim_full:                      0.
% 3.55/0.98  sup_time_sim_immed:                     0.
% 3.55/0.98  
% 3.55/0.98  sup_num_of_clauses:                     105
% 3.55/0.98  sup_num_in_active:                      67
% 3.55/0.98  sup_num_in_passive:                     38
% 3.55/0.98  sup_num_of_loops:                       82
% 3.55/0.98  sup_fw_superposition:                   50
% 3.55/0.98  sup_bw_superposition:                   58
% 3.55/0.98  sup_immediate_simplified:               35
% 3.55/0.98  sup_given_eliminated:                   0
% 3.55/0.98  comparisons_done:                       0
% 3.55/0.98  comparisons_avoided:                    0
% 3.55/0.98  
% 3.55/0.98  ------ Simplifications
% 3.55/0.98  
% 3.55/0.98  
% 3.55/0.98  sim_fw_subset_subsumed:                 5
% 3.55/0.98  sim_bw_subset_subsumed:                 3
% 3.55/0.98  sim_fw_subsumed:                        7
% 3.55/0.98  sim_bw_subsumed:                        1
% 3.55/0.98  sim_fw_subsumption_res:                 0
% 3.55/0.98  sim_bw_subsumption_res:                 0
% 3.55/0.98  sim_tautology_del:                      5
% 3.55/0.98  sim_eq_tautology_del:                   7
% 3.55/0.98  sim_eq_res_simp:                        2
% 3.55/0.98  sim_fw_demodulated:                     4
% 3.55/0.98  sim_bw_demodulated:                     19
% 3.55/0.98  sim_light_normalised:                   19
% 3.55/0.98  sim_joinable_taut:                      0
% 3.55/0.98  sim_joinable_simp:                      0
% 3.55/0.98  sim_ac_normalised:                      0
% 3.55/0.98  sim_smt_subsumption:                    0
% 3.55/0.98  
%------------------------------------------------------------------------------

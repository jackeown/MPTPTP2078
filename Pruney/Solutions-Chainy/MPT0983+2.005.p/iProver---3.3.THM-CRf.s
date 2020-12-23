%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:01:46 EST 2020

% Result     : Theorem 2.70s
% Output     : CNFRefutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :  182 (1787 expanded)
%              Number of clauses        :  100 ( 522 expanded)
%              Number of leaves         :   22 ( 431 expanded)
%              Depth                    :   24
%              Number of atoms          :  657 (11130 expanded)
%              Number of equality atoms :  164 ( 837 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f31])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f19,conjecture,(
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

fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

fof(f41,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f50,plain,(
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

fof(f49,plain,
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

fof(f51,plain,
    ( ( ~ v2_funct_2(sK4,sK1)
      | ~ v2_funct_1(sK3) )
    & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1))
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    & v1_funct_2(sK4,sK2,sK1)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f42,f50,f49])).

fof(f84,plain,(
    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f51])).

fof(f13,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f16,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f88,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f69,f74])).

fof(f78,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f80,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f51])).

fof(f81,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f83,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f51])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f35])).

fof(f73,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f18,axiom,(
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

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f76,plain,(
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
    inference(cnf_transformation,[],[f40])).

fof(f79,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f82,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f8,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f86,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f63,f74])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f17,axiom,(
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

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f89,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f68])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f90,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f71])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f85,plain,
    ( ~ v2_funct_2(sK4,sK1)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f44,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f43])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f44,f45])).

fof(f53,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0)
        & v1_xboole_0(X0) )
     => ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f61,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f58,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f57,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

cnf(c_3,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_728,plain,
    ( ~ v1_xboole_0(X0_50)
    | v1_xboole_0(k2_zfmisc_1(X0_50,X1_50)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1171,plain,
    ( v1_xboole_0(X0_50) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X0_50,X1_50)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_728])).

cnf(c_16,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_26,negated_conjecture,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_485,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) != X0
    | k6_partfun1(sK1) != X3
    | sK1 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_26])).

cnf(c_486,plain,
    ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
    inference(unflattening,[status(thm)],[c_485])).

cnf(c_17,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_63,plain,
    ( m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_488,plain,
    ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_486,c_63])).

cnf(c_709,plain,
    ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
    inference(subtyping,[status(esa)],[c_488])).

cnf(c_1191,plain,
    ( k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_709])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_723,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
    | ~ m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X4_50,X5_50)))
    | m1_subset_1(k1_partfun1(X4_50,X5_50,X1_50,X2_50,X3_50,X0_50),k1_zfmisc_1(k2_zfmisc_1(X4_50,X2_50)))
    | ~ v1_funct_1(X0_50)
    | ~ v1_funct_1(X3_50) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1461,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
    | m1_subset_1(k1_partfun1(X1_50,X2_50,sK2,sK1,X0_50,sK4),k1_zfmisc_1(k2_zfmisc_1(X1_50,sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(X0_50)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_723])).

cnf(c_1560,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1461])).

cnf(c_1732,plain,
    ( k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1191,c_32,c_30,c_29,c_27,c_709,c_1560])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v2_funct_1(X3)
    | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_720,plain,
    ( ~ v1_funct_2(X0_50,X1_50,X2_50)
    | ~ v1_funct_2(X3_50,X4_50,X1_50)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
    | ~ m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X4_50,X1_50)))
    | v2_funct_1(X3_50)
    | ~ v2_funct_1(k1_partfun1(X4_50,X1_50,X1_50,X2_50,X3_50,X0_50))
    | ~ v1_funct_1(X0_50)
    | ~ v1_funct_1(X3_50)
    | k1_xboole_0 = X2_50 ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1179,plain,
    ( k1_xboole_0 = X0_50
    | v1_funct_2(X1_50,X2_50,X0_50) != iProver_top
    | v1_funct_2(X3_50,X4_50,X2_50) != iProver_top
    | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_50,X0_50))) != iProver_top
    | m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X4_50,X2_50))) != iProver_top
    | v2_funct_1(X3_50) = iProver_top
    | v2_funct_1(k1_partfun1(X4_50,X2_50,X2_50,X0_50,X3_50,X1_50)) != iProver_top
    | v1_funct_1(X3_50) != iProver_top
    | v1_funct_1(X1_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_720])).

cnf(c_2622,plain,
    ( sK1 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v2_funct_1(k6_partfun1(sK1)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1732,c_1179])).

cnf(c_33,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_34,plain,
    ( v1_funct_2(sK3,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_35,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_36,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_37,plain,
    ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_38,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_10,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_83,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_85,plain,
    ( v2_funct_1(k6_partfun1(sK1)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_83])).

cnf(c_719,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_1180,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_719])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_725,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
    | k2_relset_1(X1_50,X2_50,X0_50) = k2_relat_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1174,plain,
    ( k2_relset_1(X0_50,X1_50,X2_50) = k2_relat_1(X2_50)
    | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_725])).

cnf(c_2231,plain,
    ( k2_relset_1(sK2,sK1,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1180,c_1174])).

cnf(c_22,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_499,plain,
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
    inference(resolution_lifted,[status(thm)],[c_22,c_26])).

cnf(c_500,plain,
    ( ~ v1_funct_2(X0,X1,sK1)
    | ~ v1_funct_2(X2,sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X0)
    | k1_partfun1(sK1,X1,X1,sK1,X2,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | k2_relset_1(X1,sK1,X0) = sK1
    | k6_partfun1(sK1) != k6_partfun1(sK1) ),
    inference(unflattening,[status(thm)],[c_499])).

cnf(c_576,plain,
    ( ~ v1_funct_2(X0,X1,sK1)
    | ~ v1_funct_2(X2,sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK1,X1,X1,sK1,X2,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | k2_relset_1(X1,sK1,X0) = sK1 ),
    inference(equality_resolution_simp,[status(thm)],[c_500])).

cnf(c_708,plain,
    ( ~ v1_funct_2(X0_50,X1_50,sK1)
    | ~ v1_funct_2(X2_50,sK1,X1_50)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,sK1)))
    | ~ m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(sK1,X1_50)))
    | ~ v1_funct_1(X0_50)
    | ~ v1_funct_1(X2_50)
    | k1_partfun1(sK1,X1_50,X1_50,sK1,X2_50,X0_50) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | k2_relset_1(X1_50,sK1,X0_50) = sK1 ),
    inference(subtyping,[status(esa)],[c_576])).

cnf(c_1192,plain,
    ( k1_partfun1(sK1,X0_50,X0_50,sK1,X1_50,X2_50) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | k2_relset_1(X0_50,sK1,X2_50) = sK1
    | v1_funct_2(X2_50,X0_50,sK1) != iProver_top
    | v1_funct_2(X1_50,sK1,X0_50) != iProver_top
    | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,sK1))) != iProver_top
    | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(sK1,X0_50))) != iProver_top
    | v1_funct_1(X2_50) != iProver_top
    | v1_funct_1(X1_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_708])).

cnf(c_1771,plain,
    ( k1_partfun1(sK1,X0_50,X0_50,sK1,X1_50,X2_50) != k6_partfun1(sK1)
    | k2_relset_1(X0_50,sK1,X2_50) = sK1
    | v1_funct_2(X2_50,X0_50,sK1) != iProver_top
    | v1_funct_2(X1_50,sK1,X0_50) != iProver_top
    | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,sK1))) != iProver_top
    | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(sK1,X0_50))) != iProver_top
    | v1_funct_1(X1_50) != iProver_top
    | v1_funct_1(X2_50) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1192,c_1732])).

cnf(c_1783,plain,
    ( k2_relset_1(sK2,sK1,sK4) = sK1
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1732,c_1771])).

cnf(c_15,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_450,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | X1 != X6
    | X1 != X5
    | k1_partfun1(X1,X2,X2,X1,X0,X3) != X4
    | k2_relset_1(X2,X1,X3) = X1
    | k6_partfun1(X1) != X4 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_22])).

cnf(c_451,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ m1_subset_1(k1_partfun1(X1,X2,X2,X1,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X2,X1,X3) = X1
    | k6_partfun1(X1) != k1_partfun1(X1,X2,X2,X1,X0,X3) ),
    inference(unflattening,[status(thm)],[c_450])).

cnf(c_473,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X2,X1,X3) = X1
    | k6_partfun1(X1) != k1_partfun1(X1,X2,X2,X1,X0,X3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_451,c_20])).

cnf(c_710,plain,
    ( ~ v1_funct_2(X0_50,X1_50,X2_50)
    | ~ v1_funct_2(X3_50,X2_50,X1_50)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
    | ~ m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X2_50,X1_50)))
    | ~ v1_funct_1(X0_50)
    | ~ v1_funct_1(X3_50)
    | k2_relset_1(X2_50,X1_50,X3_50) = X1_50
    | k6_partfun1(X1_50) != k1_partfun1(X1_50,X2_50,X2_50,X1_50,X0_50,X3_50) ),
    inference(subtyping,[status(esa)],[c_473])).

cnf(c_1490,plain,
    ( ~ v1_funct_2(X0_50,sK2,sK1)
    | ~ v1_funct_2(sK3,sK1,sK2)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(X0_50)
    | ~ v1_funct_1(sK3)
    | k2_relset_1(sK2,sK1,X0_50) = sK1
    | k6_partfun1(sK1) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,X0_50) ),
    inference(instantiation,[status(thm)],[c_710])).

cnf(c_1521,plain,
    ( ~ v1_funct_2(sK3,sK1,sK2)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK4)
    | k2_relset_1(sK2,sK1,sK4) = sK1
    | k6_partfun1(sK1) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1490])).

cnf(c_1786,plain,
    ( k2_relset_1(sK2,sK1,sK4) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1783,c_32,c_31,c_30,c_29,c_28,c_27,c_709,c_1521,c_1560])).

cnf(c_2239,plain,
    ( k2_relat_1(sK4) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2231,c_1786])).

cnf(c_13,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_18,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_403,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X0)
    | X0 != X1
    | k2_relat_1(X0) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_18])).

cnf(c_404,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_403])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_414,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0)))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_404,c_12])).

cnf(c_25,negated_conjecture,
    ( ~ v2_funct_2(sK4,sK1)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_429,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
    | ~ v2_funct_1(sK3)
    | k2_relat_1(X0) != sK1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_414,c_25])).

cnf(c_430,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK4))))
    | ~ v2_funct_1(sK3)
    | k2_relat_1(sK4) != sK1 ),
    inference(unflattening,[status(thm)],[c_429])).

cnf(c_711,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_50,k2_relat_1(sK4))))
    | ~ v2_funct_1(sK3)
    | k2_relat_1(sK4) != sK1 ),
    inference(subtyping,[status(esa)],[c_430])).

cnf(c_731,plain,
    ( ~ v2_funct_1(sK3)
    | sP0_iProver_split
    | k2_relat_1(sK4) != sK1 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_711])).

cnf(c_1188,plain,
    ( k2_relat_1(sK4) != sK1
    | v2_funct_1(sK3) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_731])).

cnf(c_2907,plain,
    ( sK1 != sK1
    | v2_funct_1(sK3) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_2239,c_1188])).

cnf(c_2908,plain,
    ( v2_funct_1(sK3) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2907])).

cnf(c_730,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_50,k2_relat_1(sK4))))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_711])).

cnf(c_1189,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_50,k2_relat_1(sK4)))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_730])).

cnf(c_2906,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_50,sK1))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(demodulation,[status(thm)],[c_2239,c_1189])).

cnf(c_3158,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_1180,c_2906])).

cnf(c_3325,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2622,c_33,c_34,c_35,c_36,c_37,c_38,c_85,c_2908,c_3158])).

cnf(c_716,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_1183,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_716])).

cnf(c_3335,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3325,c_1183])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_367,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | X0 != X2
    | sK0(X2) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_4])).

cnf(c_368,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_367])).

cnf(c_712,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(X1_50))
    | ~ v1_xboole_0(X1_50)
    | v1_xboole_0(X0_50) ),
    inference(subtyping,[status(esa)],[c_368])).

cnf(c_1187,plain,
    ( m1_subset_1(X0_50,k1_zfmisc_1(X1_50)) != iProver_top
    | v1_xboole_0(X1_50) != iProver_top
    | v1_xboole_0(X0_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_712])).

cnf(c_4025,plain,
    ( v1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK2)) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3335,c_1187])).

cnf(c_7,plain,
    ( v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_6,plain,
    ( v1_funct_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_5,plain,
    ( v1_relat_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_200,plain,
    ( v2_funct_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7,c_6,c_5])).

cnf(c_713,plain,
    ( v2_funct_1(X0_50)
    | ~ v1_xboole_0(X0_50) ),
    inference(subtyping,[status(esa)],[c_200])).

cnf(c_1393,plain,
    ( v2_funct_1(sK3)
    | ~ v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_713])).

cnf(c_1394,plain,
    ( v2_funct_1(sK3) = iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1393])).

cnf(c_4736,plain,
    ( v1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4025,c_1394,c_2908,c_3158])).

cnf(c_4741,plain,
    ( v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1171,c_4736])).

cnf(c_2,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_103,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4741,c_103])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:37:23 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.70/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/0.99  
% 2.70/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.70/0.99  
% 2.70/0.99  ------  iProver source info
% 2.70/0.99  
% 2.70/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.70/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.70/0.99  git: non_committed_changes: false
% 2.70/0.99  git: last_make_outside_of_git: false
% 2.70/0.99  
% 2.70/0.99  ------ 
% 2.70/0.99  
% 2.70/0.99  ------ Input Options
% 2.70/0.99  
% 2.70/0.99  --out_options                           all
% 2.70/0.99  --tptp_safe_out                         true
% 2.70/0.99  --problem_path                          ""
% 2.70/0.99  --include_path                          ""
% 2.70/0.99  --clausifier                            res/vclausify_rel
% 2.70/0.99  --clausifier_options                    --mode clausify
% 2.70/0.99  --stdin                                 false
% 2.70/0.99  --stats_out                             all
% 2.70/0.99  
% 2.70/0.99  ------ General Options
% 2.70/0.99  
% 2.70/0.99  --fof                                   false
% 2.70/0.99  --time_out_real                         305.
% 2.70/0.99  --time_out_virtual                      -1.
% 2.70/0.99  --symbol_type_check                     false
% 2.70/0.99  --clausify_out                          false
% 2.70/0.99  --sig_cnt_out                           false
% 2.70/0.99  --trig_cnt_out                          false
% 2.70/0.99  --trig_cnt_out_tolerance                1.
% 2.70/0.99  --trig_cnt_out_sk_spl                   false
% 2.70/0.99  --abstr_cl_out                          false
% 2.70/0.99  
% 2.70/0.99  ------ Global Options
% 2.70/0.99  
% 2.70/0.99  --schedule                              default
% 2.70/0.99  --add_important_lit                     false
% 2.70/0.99  --prop_solver_per_cl                    1000
% 2.70/0.99  --min_unsat_core                        false
% 2.70/0.99  --soft_assumptions                      false
% 2.70/0.99  --soft_lemma_size                       3
% 2.70/0.99  --prop_impl_unit_size                   0
% 2.70/0.99  --prop_impl_unit                        []
% 2.70/0.99  --share_sel_clauses                     true
% 2.70/0.99  --reset_solvers                         false
% 2.70/0.99  --bc_imp_inh                            [conj_cone]
% 2.70/0.99  --conj_cone_tolerance                   3.
% 2.70/0.99  --extra_neg_conj                        none
% 2.70/0.99  --large_theory_mode                     true
% 2.70/0.99  --prolific_symb_bound                   200
% 2.70/0.99  --lt_threshold                          2000
% 2.70/0.99  --clause_weak_htbl                      true
% 2.70/0.99  --gc_record_bc_elim                     false
% 2.70/0.99  
% 2.70/0.99  ------ Preprocessing Options
% 2.70/0.99  
% 2.70/0.99  --preprocessing_flag                    true
% 2.70/0.99  --time_out_prep_mult                    0.1
% 2.70/0.99  --splitting_mode                        input
% 2.70/0.99  --splitting_grd                         true
% 2.70/0.99  --splitting_cvd                         false
% 2.70/0.99  --splitting_cvd_svl                     false
% 2.70/0.99  --splitting_nvd                         32
% 2.70/0.99  --sub_typing                            true
% 2.70/0.99  --prep_gs_sim                           true
% 2.70/0.99  --prep_unflatten                        true
% 2.70/0.99  --prep_res_sim                          true
% 2.70/0.99  --prep_upred                            true
% 2.70/0.99  --prep_sem_filter                       exhaustive
% 2.70/0.99  --prep_sem_filter_out                   false
% 2.70/0.99  --pred_elim                             true
% 2.70/0.99  --res_sim_input                         true
% 2.70/0.99  --eq_ax_congr_red                       true
% 2.70/0.99  --pure_diseq_elim                       true
% 2.70/0.99  --brand_transform                       false
% 2.70/0.99  --non_eq_to_eq                          false
% 2.70/0.99  --prep_def_merge                        true
% 2.70/0.99  --prep_def_merge_prop_impl              false
% 2.70/0.99  --prep_def_merge_mbd                    true
% 2.70/0.99  --prep_def_merge_tr_red                 false
% 2.70/0.99  --prep_def_merge_tr_cl                  false
% 2.70/0.99  --smt_preprocessing                     true
% 2.70/0.99  --smt_ac_axioms                         fast
% 2.70/0.99  --preprocessed_out                      false
% 2.70/0.99  --preprocessed_stats                    false
% 2.70/0.99  
% 2.70/0.99  ------ Abstraction refinement Options
% 2.70/0.99  
% 2.70/0.99  --abstr_ref                             []
% 2.70/0.99  --abstr_ref_prep                        false
% 2.70/0.99  --abstr_ref_until_sat                   false
% 2.70/0.99  --abstr_ref_sig_restrict                funpre
% 2.70/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.70/0.99  --abstr_ref_under                       []
% 2.70/0.99  
% 2.70/0.99  ------ SAT Options
% 2.70/0.99  
% 2.70/0.99  --sat_mode                              false
% 2.70/0.99  --sat_fm_restart_options                ""
% 2.70/0.99  --sat_gr_def                            false
% 2.70/0.99  --sat_epr_types                         true
% 2.70/0.99  --sat_non_cyclic_types                  false
% 2.70/0.99  --sat_finite_models                     false
% 2.70/0.99  --sat_fm_lemmas                         false
% 2.70/0.99  --sat_fm_prep                           false
% 2.70/0.99  --sat_fm_uc_incr                        true
% 2.70/0.99  --sat_out_model                         small
% 2.70/0.99  --sat_out_clauses                       false
% 2.70/0.99  
% 2.70/0.99  ------ QBF Options
% 2.70/0.99  
% 2.70/0.99  --qbf_mode                              false
% 2.70/0.99  --qbf_elim_univ                         false
% 2.70/0.99  --qbf_dom_inst                          none
% 2.70/0.99  --qbf_dom_pre_inst                      false
% 2.70/0.99  --qbf_sk_in                             false
% 2.70/0.99  --qbf_pred_elim                         true
% 2.70/0.99  --qbf_split                             512
% 2.70/0.99  
% 2.70/0.99  ------ BMC1 Options
% 2.70/0.99  
% 2.70/0.99  --bmc1_incremental                      false
% 2.70/0.99  --bmc1_axioms                           reachable_all
% 2.70/0.99  --bmc1_min_bound                        0
% 2.70/0.99  --bmc1_max_bound                        -1
% 2.70/0.99  --bmc1_max_bound_default                -1
% 2.70/0.99  --bmc1_symbol_reachability              true
% 2.70/0.99  --bmc1_property_lemmas                  false
% 2.70/0.99  --bmc1_k_induction                      false
% 2.70/0.99  --bmc1_non_equiv_states                 false
% 2.70/0.99  --bmc1_deadlock                         false
% 2.70/0.99  --bmc1_ucm                              false
% 2.70/0.99  --bmc1_add_unsat_core                   none
% 2.70/0.99  --bmc1_unsat_core_children              false
% 2.70/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.70/0.99  --bmc1_out_stat                         full
% 2.70/0.99  --bmc1_ground_init                      false
% 2.70/0.99  --bmc1_pre_inst_next_state              false
% 2.70/0.99  --bmc1_pre_inst_state                   false
% 2.70/0.99  --bmc1_pre_inst_reach_state             false
% 2.70/0.99  --bmc1_out_unsat_core                   false
% 2.70/0.99  --bmc1_aig_witness_out                  false
% 2.70/0.99  --bmc1_verbose                          false
% 2.70/0.99  --bmc1_dump_clauses_tptp                false
% 2.70/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.70/0.99  --bmc1_dump_file                        -
% 2.70/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.70/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.70/0.99  --bmc1_ucm_extend_mode                  1
% 2.70/0.99  --bmc1_ucm_init_mode                    2
% 2.70/0.99  --bmc1_ucm_cone_mode                    none
% 2.70/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.70/0.99  --bmc1_ucm_relax_model                  4
% 2.70/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.70/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.70/0.99  --bmc1_ucm_layered_model                none
% 2.70/0.99  --bmc1_ucm_max_lemma_size               10
% 2.70/0.99  
% 2.70/0.99  ------ AIG Options
% 2.70/0.99  
% 2.70/0.99  --aig_mode                              false
% 2.70/0.99  
% 2.70/0.99  ------ Instantiation Options
% 2.70/0.99  
% 2.70/0.99  --instantiation_flag                    true
% 2.70/0.99  --inst_sos_flag                         false
% 2.70/0.99  --inst_sos_phase                        true
% 2.70/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.70/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.70/0.99  --inst_lit_sel_side                     num_symb
% 2.70/0.99  --inst_solver_per_active                1400
% 2.70/0.99  --inst_solver_calls_frac                1.
% 2.70/0.99  --inst_passive_queue_type               priority_queues
% 2.70/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.70/0.99  --inst_passive_queues_freq              [25;2]
% 2.70/0.99  --inst_dismatching                      true
% 2.70/0.99  --inst_eager_unprocessed_to_passive     true
% 2.70/0.99  --inst_prop_sim_given                   true
% 2.70/0.99  --inst_prop_sim_new                     false
% 2.70/0.99  --inst_subs_new                         false
% 2.70/0.99  --inst_eq_res_simp                      false
% 2.70/0.99  --inst_subs_given                       false
% 2.70/0.99  --inst_orphan_elimination               true
% 2.70/0.99  --inst_learning_loop_flag               true
% 2.70/0.99  --inst_learning_start                   3000
% 2.70/0.99  --inst_learning_factor                  2
% 2.70/0.99  --inst_start_prop_sim_after_learn       3
% 2.70/0.99  --inst_sel_renew                        solver
% 2.70/0.99  --inst_lit_activity_flag                true
% 2.70/0.99  --inst_restr_to_given                   false
% 2.70/0.99  --inst_activity_threshold               500
% 2.70/0.99  --inst_out_proof                        true
% 2.70/0.99  
% 2.70/0.99  ------ Resolution Options
% 2.70/0.99  
% 2.70/0.99  --resolution_flag                       true
% 2.70/0.99  --res_lit_sel                           adaptive
% 2.70/0.99  --res_lit_sel_side                      none
% 2.70/0.99  --res_ordering                          kbo
% 2.70/0.99  --res_to_prop_solver                    active
% 2.70/0.99  --res_prop_simpl_new                    false
% 2.70/0.99  --res_prop_simpl_given                  true
% 2.70/0.99  --res_passive_queue_type                priority_queues
% 2.70/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.70/0.99  --res_passive_queues_freq               [15;5]
% 2.70/0.99  --res_forward_subs                      full
% 2.70/0.99  --res_backward_subs                     full
% 2.70/0.99  --res_forward_subs_resolution           true
% 2.70/0.99  --res_backward_subs_resolution          true
% 2.70/0.99  --res_orphan_elimination                true
% 2.70/0.99  --res_time_limit                        2.
% 2.70/0.99  --res_out_proof                         true
% 2.70/0.99  
% 2.70/0.99  ------ Superposition Options
% 2.70/0.99  
% 2.70/0.99  --superposition_flag                    true
% 2.70/0.99  --sup_passive_queue_type                priority_queues
% 2.70/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.70/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.70/0.99  --demod_completeness_check              fast
% 2.70/0.99  --demod_use_ground                      true
% 2.70/0.99  --sup_to_prop_solver                    passive
% 2.70/0.99  --sup_prop_simpl_new                    true
% 2.70/0.99  --sup_prop_simpl_given                  true
% 2.70/0.99  --sup_fun_splitting                     false
% 2.70/0.99  --sup_smt_interval                      50000
% 2.70/0.99  
% 2.70/0.99  ------ Superposition Simplification Setup
% 2.70/0.99  
% 2.70/0.99  --sup_indices_passive                   []
% 2.70/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.70/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.70/0.99  --sup_full_bw                           [BwDemod]
% 2.70/0.99  --sup_immed_triv                        [TrivRules]
% 2.70/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.70/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.70/0.99  --sup_immed_bw_main                     []
% 2.70/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.70/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.70/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.70/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.70/0.99  
% 2.70/0.99  ------ Combination Options
% 2.70/0.99  
% 2.70/0.99  --comb_res_mult                         3
% 2.70/0.99  --comb_sup_mult                         2
% 2.70/0.99  --comb_inst_mult                        10
% 2.70/0.99  
% 2.70/0.99  ------ Debug Options
% 2.70/0.99  
% 2.70/0.99  --dbg_backtrace                         false
% 2.70/0.99  --dbg_dump_prop_clauses                 false
% 2.70/0.99  --dbg_dump_prop_clauses_file            -
% 2.70/0.99  --dbg_out_stat                          false
% 2.70/0.99  ------ Parsing...
% 2.70/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.70/0.99  
% 2.70/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 2.70/0.99  
% 2.70/0.99  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.70/0.99  
% 2.70/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.70/0.99  ------ Proving...
% 2.70/0.99  ------ Problem Properties 
% 2.70/0.99  
% 2.70/0.99  
% 2.70/0.99  clauses                                 23
% 2.70/0.99  conjectures                             6
% 2.70/0.99  EPR                                     7
% 2.70/0.99  Horn                                    22
% 2.70/0.99  unary                                   9
% 2.70/0.99  binary                                  6
% 2.70/0.99  lits                                    70
% 2.70/0.99  lits eq                                 8
% 2.70/0.99  fd_pure                                 0
% 2.70/0.99  fd_pseudo                               0
% 2.70/0.99  fd_cond                                 1
% 2.70/0.99  fd_pseudo_cond                          0
% 2.70/0.99  AC symbols                              0
% 2.70/0.99  
% 2.70/0.99  ------ Schedule dynamic 5 is on 
% 2.70/0.99  
% 2.70/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.70/0.99  
% 2.70/0.99  
% 2.70/0.99  ------ 
% 2.70/0.99  Current options:
% 2.70/0.99  ------ 
% 2.70/0.99  
% 2.70/0.99  ------ Input Options
% 2.70/0.99  
% 2.70/0.99  --out_options                           all
% 2.70/0.99  --tptp_safe_out                         true
% 2.70/0.99  --problem_path                          ""
% 2.70/0.99  --include_path                          ""
% 2.70/0.99  --clausifier                            res/vclausify_rel
% 2.70/0.99  --clausifier_options                    --mode clausify
% 2.70/0.99  --stdin                                 false
% 2.70/0.99  --stats_out                             all
% 2.70/0.99  
% 2.70/0.99  ------ General Options
% 2.70/0.99  
% 2.70/0.99  --fof                                   false
% 2.70/0.99  --time_out_real                         305.
% 2.70/0.99  --time_out_virtual                      -1.
% 2.70/0.99  --symbol_type_check                     false
% 2.70/0.99  --clausify_out                          false
% 2.70/0.99  --sig_cnt_out                           false
% 2.70/0.99  --trig_cnt_out                          false
% 2.70/0.99  --trig_cnt_out_tolerance                1.
% 2.70/0.99  --trig_cnt_out_sk_spl                   false
% 2.70/0.99  --abstr_cl_out                          false
% 2.70/0.99  
% 2.70/0.99  ------ Global Options
% 2.70/0.99  
% 2.70/0.99  --schedule                              default
% 2.70/0.99  --add_important_lit                     false
% 2.70/0.99  --prop_solver_per_cl                    1000
% 2.70/0.99  --min_unsat_core                        false
% 2.70/0.99  --soft_assumptions                      false
% 2.70/0.99  --soft_lemma_size                       3
% 2.70/0.99  --prop_impl_unit_size                   0
% 2.70/0.99  --prop_impl_unit                        []
% 2.70/0.99  --share_sel_clauses                     true
% 2.70/0.99  --reset_solvers                         false
% 2.70/0.99  --bc_imp_inh                            [conj_cone]
% 2.70/0.99  --conj_cone_tolerance                   3.
% 2.70/0.99  --extra_neg_conj                        none
% 2.70/0.99  --large_theory_mode                     true
% 2.70/0.99  --prolific_symb_bound                   200
% 2.70/0.99  --lt_threshold                          2000
% 2.70/0.99  --clause_weak_htbl                      true
% 2.70/0.99  --gc_record_bc_elim                     false
% 2.70/0.99  
% 2.70/0.99  ------ Preprocessing Options
% 2.70/0.99  
% 2.70/0.99  --preprocessing_flag                    true
% 2.70/0.99  --time_out_prep_mult                    0.1
% 2.70/0.99  --splitting_mode                        input
% 2.70/0.99  --splitting_grd                         true
% 2.70/0.99  --splitting_cvd                         false
% 2.70/0.99  --splitting_cvd_svl                     false
% 2.70/0.99  --splitting_nvd                         32
% 2.70/0.99  --sub_typing                            true
% 2.70/0.99  --prep_gs_sim                           true
% 2.70/0.99  --prep_unflatten                        true
% 2.70/0.99  --prep_res_sim                          true
% 2.70/0.99  --prep_upred                            true
% 2.70/0.99  --prep_sem_filter                       exhaustive
% 2.70/0.99  --prep_sem_filter_out                   false
% 2.70/0.99  --pred_elim                             true
% 2.70/0.99  --res_sim_input                         true
% 2.70/0.99  --eq_ax_congr_red                       true
% 2.70/0.99  --pure_diseq_elim                       true
% 2.70/0.99  --brand_transform                       false
% 2.70/0.99  --non_eq_to_eq                          false
% 2.70/0.99  --prep_def_merge                        true
% 2.70/0.99  --prep_def_merge_prop_impl              false
% 2.70/0.99  --prep_def_merge_mbd                    true
% 2.70/0.99  --prep_def_merge_tr_red                 false
% 2.70/0.99  --prep_def_merge_tr_cl                  false
% 2.70/0.99  --smt_preprocessing                     true
% 2.70/0.99  --smt_ac_axioms                         fast
% 2.70/0.99  --preprocessed_out                      false
% 2.70/0.99  --preprocessed_stats                    false
% 2.70/0.99  
% 2.70/0.99  ------ Abstraction refinement Options
% 2.70/0.99  
% 2.70/0.99  --abstr_ref                             []
% 2.70/0.99  --abstr_ref_prep                        false
% 2.70/0.99  --abstr_ref_until_sat                   false
% 2.70/0.99  --abstr_ref_sig_restrict                funpre
% 2.70/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.70/0.99  --abstr_ref_under                       []
% 2.70/0.99  
% 2.70/0.99  ------ SAT Options
% 2.70/0.99  
% 2.70/0.99  --sat_mode                              false
% 2.70/0.99  --sat_fm_restart_options                ""
% 2.70/0.99  --sat_gr_def                            false
% 2.70/0.99  --sat_epr_types                         true
% 2.70/0.99  --sat_non_cyclic_types                  false
% 2.70/0.99  --sat_finite_models                     false
% 2.70/0.99  --sat_fm_lemmas                         false
% 2.70/0.99  --sat_fm_prep                           false
% 2.70/0.99  --sat_fm_uc_incr                        true
% 2.70/0.99  --sat_out_model                         small
% 2.70/0.99  --sat_out_clauses                       false
% 2.70/0.99  
% 2.70/0.99  ------ QBF Options
% 2.70/0.99  
% 2.70/0.99  --qbf_mode                              false
% 2.70/0.99  --qbf_elim_univ                         false
% 2.70/0.99  --qbf_dom_inst                          none
% 2.70/0.99  --qbf_dom_pre_inst                      false
% 2.70/0.99  --qbf_sk_in                             false
% 2.70/0.99  --qbf_pred_elim                         true
% 2.70/0.99  --qbf_split                             512
% 2.70/0.99  
% 2.70/0.99  ------ BMC1 Options
% 2.70/0.99  
% 2.70/0.99  --bmc1_incremental                      false
% 2.70/0.99  --bmc1_axioms                           reachable_all
% 2.70/0.99  --bmc1_min_bound                        0
% 2.70/0.99  --bmc1_max_bound                        -1
% 2.70/0.99  --bmc1_max_bound_default                -1
% 2.70/0.99  --bmc1_symbol_reachability              true
% 2.70/0.99  --bmc1_property_lemmas                  false
% 2.70/0.99  --bmc1_k_induction                      false
% 2.70/0.99  --bmc1_non_equiv_states                 false
% 2.70/0.99  --bmc1_deadlock                         false
% 2.70/0.99  --bmc1_ucm                              false
% 2.70/0.99  --bmc1_add_unsat_core                   none
% 2.70/0.99  --bmc1_unsat_core_children              false
% 2.70/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.70/0.99  --bmc1_out_stat                         full
% 2.70/0.99  --bmc1_ground_init                      false
% 2.70/0.99  --bmc1_pre_inst_next_state              false
% 2.70/0.99  --bmc1_pre_inst_state                   false
% 2.70/0.99  --bmc1_pre_inst_reach_state             false
% 2.70/0.99  --bmc1_out_unsat_core                   false
% 2.70/0.99  --bmc1_aig_witness_out                  false
% 2.70/0.99  --bmc1_verbose                          false
% 2.70/0.99  --bmc1_dump_clauses_tptp                false
% 2.70/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.70/0.99  --bmc1_dump_file                        -
% 2.70/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.70/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.70/0.99  --bmc1_ucm_extend_mode                  1
% 2.70/0.99  --bmc1_ucm_init_mode                    2
% 2.70/0.99  --bmc1_ucm_cone_mode                    none
% 2.70/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.70/0.99  --bmc1_ucm_relax_model                  4
% 2.70/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.70/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.70/0.99  --bmc1_ucm_layered_model                none
% 2.70/0.99  --bmc1_ucm_max_lemma_size               10
% 2.70/0.99  
% 2.70/0.99  ------ AIG Options
% 2.70/0.99  
% 2.70/0.99  --aig_mode                              false
% 2.70/0.99  
% 2.70/0.99  ------ Instantiation Options
% 2.70/0.99  
% 2.70/0.99  --instantiation_flag                    true
% 2.70/0.99  --inst_sos_flag                         false
% 2.70/0.99  --inst_sos_phase                        true
% 2.70/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.70/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.70/0.99  --inst_lit_sel_side                     none
% 2.70/0.99  --inst_solver_per_active                1400
% 2.70/0.99  --inst_solver_calls_frac                1.
% 2.70/0.99  --inst_passive_queue_type               priority_queues
% 2.70/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.70/0.99  --inst_passive_queues_freq              [25;2]
% 2.70/0.99  --inst_dismatching                      true
% 2.70/0.99  --inst_eager_unprocessed_to_passive     true
% 2.70/0.99  --inst_prop_sim_given                   true
% 2.70/0.99  --inst_prop_sim_new                     false
% 2.70/0.99  --inst_subs_new                         false
% 2.70/0.99  --inst_eq_res_simp                      false
% 2.70/0.99  --inst_subs_given                       false
% 2.70/0.99  --inst_orphan_elimination               true
% 2.70/0.99  --inst_learning_loop_flag               true
% 2.70/0.99  --inst_learning_start                   3000
% 2.70/0.99  --inst_learning_factor                  2
% 2.70/0.99  --inst_start_prop_sim_after_learn       3
% 2.70/0.99  --inst_sel_renew                        solver
% 2.70/0.99  --inst_lit_activity_flag                true
% 2.70/0.99  --inst_restr_to_given                   false
% 2.70/0.99  --inst_activity_threshold               500
% 2.70/0.99  --inst_out_proof                        true
% 2.70/0.99  
% 2.70/0.99  ------ Resolution Options
% 2.70/0.99  
% 2.70/0.99  --resolution_flag                       false
% 2.70/0.99  --res_lit_sel                           adaptive
% 2.70/0.99  --res_lit_sel_side                      none
% 2.70/0.99  --res_ordering                          kbo
% 2.70/0.99  --res_to_prop_solver                    active
% 2.70/0.99  --res_prop_simpl_new                    false
% 2.70/0.99  --res_prop_simpl_given                  true
% 2.70/0.99  --res_passive_queue_type                priority_queues
% 2.70/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.70/0.99  --res_passive_queues_freq               [15;5]
% 2.70/0.99  --res_forward_subs                      full
% 2.70/0.99  --res_backward_subs                     full
% 2.70/0.99  --res_forward_subs_resolution           true
% 2.70/0.99  --res_backward_subs_resolution          true
% 2.70/0.99  --res_orphan_elimination                true
% 2.70/0.99  --res_time_limit                        2.
% 2.70/0.99  --res_out_proof                         true
% 2.70/0.99  
% 2.70/0.99  ------ Superposition Options
% 2.70/0.99  
% 2.70/0.99  --superposition_flag                    true
% 2.70/0.99  --sup_passive_queue_type                priority_queues
% 2.70/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.70/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.70/0.99  --demod_completeness_check              fast
% 2.70/0.99  --demod_use_ground                      true
% 2.70/0.99  --sup_to_prop_solver                    passive
% 2.70/0.99  --sup_prop_simpl_new                    true
% 2.70/0.99  --sup_prop_simpl_given                  true
% 2.70/0.99  --sup_fun_splitting                     false
% 2.70/0.99  --sup_smt_interval                      50000
% 2.70/0.99  
% 2.70/0.99  ------ Superposition Simplification Setup
% 2.70/0.99  
% 2.70/0.99  --sup_indices_passive                   []
% 2.70/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.70/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.70/0.99  --sup_full_bw                           [BwDemod]
% 2.70/0.99  --sup_immed_triv                        [TrivRules]
% 2.70/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.70/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.70/0.99  --sup_immed_bw_main                     []
% 2.70/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.70/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.70/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.70/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.70/0.99  
% 2.70/0.99  ------ Combination Options
% 2.70/0.99  
% 2.70/0.99  --comb_res_mult                         3
% 2.70/0.99  --comb_sup_mult                         2
% 2.70/0.99  --comb_inst_mult                        10
% 2.70/0.99  
% 2.70/0.99  ------ Debug Options
% 2.70/0.99  
% 2.70/0.99  --dbg_backtrace                         false
% 2.70/0.99  --dbg_dump_prop_clauses                 false
% 2.70/0.99  --dbg_dump_prop_clauses_file            -
% 2.70/0.99  --dbg_out_stat                          false
% 2.70/0.99  
% 2.70/0.99  
% 2.70/0.99  
% 2.70/0.99  
% 2.70/0.99  ------ Proving...
% 2.70/0.99  
% 2.70/0.99  
% 2.70/0.99  % SZS status Theorem for theBenchmark.p
% 2.70/0.99  
% 2.70/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.70/0.99  
% 2.70/0.99  fof(f3,axiom,(
% 2.70/0.99    ! [X0,X1] : (v1_xboole_0(X0) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 2.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f22,plain,(
% 2.70/0.99    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0))),
% 2.70/0.99    inference(ennf_transformation,[],[f3])).
% 2.70/0.99  
% 2.70/0.99  fof(f55,plain,(
% 2.70/0.99    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0)) )),
% 2.70/0.99    inference(cnf_transformation,[],[f22])).
% 2.70/0.99  
% 2.70/0.99  fof(f12,axiom,(
% 2.70/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f31,plain,(
% 2.70/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.70/0.99    inference(ennf_transformation,[],[f12])).
% 2.70/0.99  
% 2.70/0.99  fof(f32,plain,(
% 2.70/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.70/0.99    inference(flattening,[],[f31])).
% 2.70/0.99  
% 2.70/0.99  fof(f47,plain,(
% 2.70/0.99    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.70/0.99    inference(nnf_transformation,[],[f32])).
% 2.70/0.99  
% 2.70/0.99  fof(f67,plain,(
% 2.70/0.99    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.70/0.99    inference(cnf_transformation,[],[f47])).
% 2.70/0.99  
% 2.70/0.99  fof(f19,conjecture,(
% 2.70/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 2.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f20,negated_conjecture,(
% 2.70/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 2.70/0.99    inference(negated_conjecture,[],[f19])).
% 2.70/0.99  
% 2.70/0.99  fof(f41,plain,(
% 2.70/0.99    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.70/0.99    inference(ennf_transformation,[],[f20])).
% 2.70/0.99  
% 2.70/0.99  fof(f42,plain,(
% 2.70/0.99    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.70/0.99    inference(flattening,[],[f41])).
% 2.70/0.99  
% 2.70/0.99  fof(f50,plain,(
% 2.70/0.99    ( ! [X2,X0,X1] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((~v2_funct_2(sK4,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK4),k6_partfun1(X0)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK4,X1,X0) & v1_funct_1(sK4))) )),
% 2.70/0.99    introduced(choice_axiom,[])).
% 2.70/0.99  
% 2.70/0.99  fof(f49,plain,(
% 2.70/0.99    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK1) | ~v2_funct_1(sK3)) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,X3),k6_partfun1(sK1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(X3,sK2,sK1) & v1_funct_1(X3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 2.70/0.99    introduced(choice_axiom,[])).
% 2.70/0.99  
% 2.70/0.99  fof(f51,plain,(
% 2.70/0.99    ((~v2_funct_2(sK4,sK1) | ~v2_funct_1(sK3)) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 2.70/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f42,f50,f49])).
% 2.70/0.99  
% 2.70/0.99  fof(f84,plain,(
% 2.70/0.99    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1))),
% 2.70/0.99    inference(cnf_transformation,[],[f51])).
% 2.70/0.99  
% 2.70/0.99  fof(f13,axiom,(
% 2.70/0.99    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 2.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f69,plain,(
% 2.70/0.99    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.70/0.99    inference(cnf_transformation,[],[f13])).
% 2.70/0.99  
% 2.70/0.99  fof(f16,axiom,(
% 2.70/0.99    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f74,plain,(
% 2.70/0.99    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.70/0.99    inference(cnf_transformation,[],[f16])).
% 2.70/0.99  
% 2.70/0.99  fof(f88,plain,(
% 2.70/0.99    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.70/0.99    inference(definition_unfolding,[],[f69,f74])).
% 2.70/0.99  
% 2.70/0.99  fof(f78,plain,(
% 2.70/0.99    v1_funct_1(sK3)),
% 2.70/0.99    inference(cnf_transformation,[],[f51])).
% 2.70/0.99  
% 2.70/0.99  fof(f80,plain,(
% 2.70/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 2.70/0.99    inference(cnf_transformation,[],[f51])).
% 2.70/0.99  
% 2.70/0.99  fof(f81,plain,(
% 2.70/0.99    v1_funct_1(sK4)),
% 2.70/0.99    inference(cnf_transformation,[],[f51])).
% 2.70/0.99  
% 2.70/0.99  fof(f83,plain,(
% 2.70/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 2.70/0.99    inference(cnf_transformation,[],[f51])).
% 2.70/0.99  
% 2.70/0.99  fof(f15,axiom,(
% 2.70/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 2.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f35,plain,(
% 2.70/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.70/0.99    inference(ennf_transformation,[],[f15])).
% 2.70/0.99  
% 2.70/0.99  fof(f36,plain,(
% 2.70/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.70/0.99    inference(flattening,[],[f35])).
% 2.70/0.99  
% 2.70/0.99  fof(f73,plain,(
% 2.70/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.70/0.99    inference(cnf_transformation,[],[f36])).
% 2.70/0.99  
% 2.70/0.99  fof(f18,axiom,(
% 2.70/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 2.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f39,plain,(
% 2.70/0.99    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.70/0.99    inference(ennf_transformation,[],[f18])).
% 2.70/0.99  
% 2.70/0.99  fof(f40,plain,(
% 2.70/0.99    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.70/0.99    inference(flattening,[],[f39])).
% 2.70/0.99  
% 2.70/0.99  fof(f76,plain,(
% 2.70/0.99    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X3) | k1_xboole_0 = X2 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.70/0.99    inference(cnf_transformation,[],[f40])).
% 2.70/0.99  
% 2.70/0.99  fof(f79,plain,(
% 2.70/0.99    v1_funct_2(sK3,sK1,sK2)),
% 2.70/0.99    inference(cnf_transformation,[],[f51])).
% 2.70/0.99  
% 2.70/0.99  fof(f82,plain,(
% 2.70/0.99    v1_funct_2(sK4,sK2,sK1)),
% 2.70/0.99    inference(cnf_transformation,[],[f51])).
% 2.70/0.99  
% 2.70/0.99  fof(f8,axiom,(
% 2.70/0.99    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f63,plain,(
% 2.70/0.99    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 2.70/0.99    inference(cnf_transformation,[],[f8])).
% 2.70/0.99  
% 2.70/0.99  fof(f86,plain,(
% 2.70/0.99    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 2.70/0.99    inference(definition_unfolding,[],[f63,f74])).
% 2.70/0.99  
% 2.70/0.99  fof(f11,axiom,(
% 2.70/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 2.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f30,plain,(
% 2.70/0.99    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.70/0.99    inference(ennf_transformation,[],[f11])).
% 2.70/0.99  
% 2.70/0.99  fof(f66,plain,(
% 2.70/0.99    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.70/0.99    inference(cnf_transformation,[],[f30])).
% 2.70/0.99  
% 2.70/0.99  fof(f17,axiom,(
% 2.70/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 2.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f37,plain,(
% 2.70/0.99    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.70/0.99    inference(ennf_transformation,[],[f17])).
% 2.70/0.99  
% 2.70/0.99  fof(f38,plain,(
% 2.70/0.99    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.70/0.99    inference(flattening,[],[f37])).
% 2.70/0.99  
% 2.70/0.99  fof(f75,plain,(
% 2.70/0.99    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.70/0.99    inference(cnf_transformation,[],[f38])).
% 2.70/0.99  
% 2.70/0.99  fof(f68,plain,(
% 2.70/0.99    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.70/0.99    inference(cnf_transformation,[],[f47])).
% 2.70/0.99  
% 2.70/0.99  fof(f89,plain,(
% 2.70/0.99    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.70/0.99    inference(equality_resolution,[],[f68])).
% 2.70/0.99  
% 2.70/0.99  fof(f10,axiom,(
% 2.70/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f21,plain,(
% 2.70/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 2.70/0.99    inference(pure_predicate_removal,[],[f10])).
% 2.70/0.99  
% 2.70/0.99  fof(f29,plain,(
% 2.70/0.99    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.70/0.99    inference(ennf_transformation,[],[f21])).
% 2.70/0.99  
% 2.70/0.99  fof(f65,plain,(
% 2.70/0.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.70/0.99    inference(cnf_transformation,[],[f29])).
% 2.70/0.99  
% 2.70/0.99  fof(f14,axiom,(
% 2.70/0.99    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 2.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f33,plain,(
% 2.70/0.99    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.70/0.99    inference(ennf_transformation,[],[f14])).
% 2.70/0.99  
% 2.70/0.99  fof(f34,plain,(
% 2.70/0.99    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.70/0.99    inference(flattening,[],[f33])).
% 2.70/0.99  
% 2.70/0.99  fof(f48,plain,(
% 2.70/0.99    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.70/0.99    inference(nnf_transformation,[],[f34])).
% 2.70/0.99  
% 2.70/0.99  fof(f71,plain,(
% 2.70/0.99    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.70/0.99    inference(cnf_transformation,[],[f48])).
% 2.70/0.99  
% 2.70/0.99  fof(f90,plain,(
% 2.70/0.99    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.70/0.99    inference(equality_resolution,[],[f71])).
% 2.70/0.99  
% 2.70/0.99  fof(f9,axiom,(
% 2.70/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f28,plain,(
% 2.70/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.70/0.99    inference(ennf_transformation,[],[f9])).
% 2.70/0.99  
% 2.70/0.99  fof(f64,plain,(
% 2.70/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.70/0.99    inference(cnf_transformation,[],[f28])).
% 2.70/0.99  
% 2.70/0.99  fof(f85,plain,(
% 2.70/0.99    ~v2_funct_2(sK4,sK1) | ~v2_funct_1(sK3)),
% 2.70/0.99    inference(cnf_transformation,[],[f51])).
% 2.70/0.99  
% 2.70/0.99  fof(f1,axiom,(
% 2.70/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f43,plain,(
% 2.70/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.70/0.99    inference(nnf_transformation,[],[f1])).
% 2.70/0.99  
% 2.70/0.99  fof(f44,plain,(
% 2.70/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.70/0.99    inference(rectify,[],[f43])).
% 2.70/0.99  
% 2.70/0.99  fof(f45,plain,(
% 2.70/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.70/0.99    introduced(choice_axiom,[])).
% 2.70/0.99  
% 2.70/0.99  fof(f46,plain,(
% 2.70/0.99    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.70/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f44,f45])).
% 2.70/0.99  
% 2.70/0.99  fof(f53,plain,(
% 2.70/0.99    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 2.70/0.99    inference(cnf_transformation,[],[f46])).
% 2.70/0.99  
% 2.70/0.99  fof(f4,axiom,(
% 2.70/0.99    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f23,plain,(
% 2.70/0.99    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.70/0.99    inference(ennf_transformation,[],[f4])).
% 2.70/0.99  
% 2.70/0.99  fof(f56,plain,(
% 2.70/0.99    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.70/0.99    inference(cnf_transformation,[],[f23])).
% 2.70/0.99  
% 2.70/0.99  fof(f7,axiom,(
% 2.70/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0) & v1_xboole_0(X0)) => (v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)))),
% 2.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f26,plain,(
% 2.70/0.99    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_xboole_0(X0)))),
% 2.70/0.99    inference(ennf_transformation,[],[f7])).
% 2.70/0.99  
% 2.70/0.99  fof(f27,plain,(
% 2.70/0.99    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 2.70/0.99    inference(flattening,[],[f26])).
% 2.70/0.99  
% 2.70/0.99  fof(f61,plain,(
% 2.70/0.99    ( ! [X0] : (v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 2.70/0.99    inference(cnf_transformation,[],[f27])).
% 2.70/0.99  
% 2.70/0.99  fof(f6,axiom,(
% 2.70/0.99    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 2.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f25,plain,(
% 2.70/0.99    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 2.70/0.99    inference(ennf_transformation,[],[f6])).
% 2.70/0.99  
% 2.70/0.99  fof(f58,plain,(
% 2.70/0.99    ( ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0)) )),
% 2.70/0.99    inference(cnf_transformation,[],[f25])).
% 2.70/0.99  
% 2.70/0.99  fof(f5,axiom,(
% 2.70/0.99    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 2.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f24,plain,(
% 2.70/0.99    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 2.70/0.99    inference(ennf_transformation,[],[f5])).
% 2.70/0.99  
% 2.70/0.99  fof(f57,plain,(
% 2.70/0.99    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 2.70/0.99    inference(cnf_transformation,[],[f24])).
% 2.70/0.99  
% 2.70/0.99  fof(f2,axiom,(
% 2.70/0.99    v1_xboole_0(k1_xboole_0)),
% 2.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f54,plain,(
% 2.70/0.99    v1_xboole_0(k1_xboole_0)),
% 2.70/0.99    inference(cnf_transformation,[],[f2])).
% 2.70/0.99  
% 2.70/0.99  cnf(c_3,plain,
% 2.70/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(k2_zfmisc_1(X0,X1)) ),
% 2.70/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_728,plain,
% 2.70/0.99      ( ~ v1_xboole_0(X0_50) | v1_xboole_0(k2_zfmisc_1(X0_50,X1_50)) ),
% 2.70/0.99      inference(subtyping,[status(esa)],[c_3]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1171,plain,
% 2.70/0.99      ( v1_xboole_0(X0_50) != iProver_top
% 2.70/0.99      | v1_xboole_0(k2_zfmisc_1(X0_50,X1_50)) = iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_728]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_16,plain,
% 2.70/0.99      ( ~ r2_relset_1(X0,X1,X2,X3)
% 2.70/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.70/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.70/0.99      | X3 = X2 ),
% 2.70/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_26,negated_conjecture,
% 2.70/0.99      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) ),
% 2.70/0.99      inference(cnf_transformation,[],[f84]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_485,plain,
% 2.70/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.70/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.70/0.99      | X3 = X0
% 2.70/0.99      | k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) != X0
% 2.70/0.99      | k6_partfun1(sK1) != X3
% 2.70/0.99      | sK1 != X2
% 2.70/0.99      | sK1 != X1 ),
% 2.70/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_26]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_486,plain,
% 2.70/0.99      ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.70/0.99      | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.70/0.99      | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
% 2.70/0.99      inference(unflattening,[status(thm)],[c_485]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_17,plain,
% 2.70/0.99      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 2.70/0.99      inference(cnf_transformation,[],[f88]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_63,plain,
% 2.70/0.99      ( m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 2.70/0.99      inference(instantiation,[status(thm)],[c_17]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_488,plain,
% 2.70/0.99      ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.70/0.99      | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
% 2.70/0.99      inference(global_propositional_subsumption,
% 2.70/0.99                [status(thm)],
% 2.70/0.99                [c_486,c_63]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_709,plain,
% 2.70/0.99      ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.70/0.99      | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
% 2.70/0.99      inference(subtyping,[status(esa)],[c_488]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1191,plain,
% 2.70/0.99      ( k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 2.70/0.99      | m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_709]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_32,negated_conjecture,
% 2.70/0.99      ( v1_funct_1(sK3) ),
% 2.70/0.99      inference(cnf_transformation,[],[f78]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_30,negated_conjecture,
% 2.70/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 2.70/0.99      inference(cnf_transformation,[],[f80]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_29,negated_conjecture,
% 2.70/0.99      ( v1_funct_1(sK4) ),
% 2.70/0.99      inference(cnf_transformation,[],[f81]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_27,negated_conjecture,
% 2.70/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 2.70/0.99      inference(cnf_transformation,[],[f83]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_20,plain,
% 2.70/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.70/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 2.70/0.99      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 2.70/0.99      | ~ v1_funct_1(X0)
% 2.70/0.99      | ~ v1_funct_1(X3) ),
% 2.70/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_723,plain,
% 2.70/0.99      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
% 2.70/0.99      | ~ m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X4_50,X5_50)))
% 2.70/0.99      | m1_subset_1(k1_partfun1(X4_50,X5_50,X1_50,X2_50,X3_50,X0_50),k1_zfmisc_1(k2_zfmisc_1(X4_50,X2_50)))
% 2.70/0.99      | ~ v1_funct_1(X0_50)
% 2.70/0.99      | ~ v1_funct_1(X3_50) ),
% 2.70/0.99      inference(subtyping,[status(esa)],[c_20]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1461,plain,
% 2.70/0.99      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
% 2.70/0.99      | m1_subset_1(k1_partfun1(X1_50,X2_50,sK2,sK1,X0_50,sK4),k1_zfmisc_1(k2_zfmisc_1(X1_50,sK1)))
% 2.70/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 2.70/0.99      | ~ v1_funct_1(X0_50)
% 2.70/0.99      | ~ v1_funct_1(sK4) ),
% 2.70/0.99      inference(instantiation,[status(thm)],[c_723]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1560,plain,
% 2.70/0.99      ( m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.70/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.70/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 2.70/0.99      | ~ v1_funct_1(sK3)
% 2.70/0.99      | ~ v1_funct_1(sK4) ),
% 2.70/0.99      inference(instantiation,[status(thm)],[c_1461]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1732,plain,
% 2.70/0.99      ( k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
% 2.70/0.99      inference(global_propositional_subsumption,
% 2.70/0.99                [status(thm)],
% 2.70/0.99                [c_1191,c_32,c_30,c_29,c_27,c_709,c_1560]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_24,plain,
% 2.70/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.70/0.99      | ~ v1_funct_2(X3,X4,X1)
% 2.70/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 2.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.70/0.99      | v2_funct_1(X3)
% 2.70/0.99      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 2.70/0.99      | ~ v1_funct_1(X0)
% 2.70/0.99      | ~ v1_funct_1(X3)
% 2.70/0.99      | k1_xboole_0 = X2 ),
% 2.70/0.99      inference(cnf_transformation,[],[f76]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_720,plain,
% 2.70/0.99      ( ~ v1_funct_2(X0_50,X1_50,X2_50)
% 2.70/0.99      | ~ v1_funct_2(X3_50,X4_50,X1_50)
% 2.70/0.99      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
% 2.70/0.99      | ~ m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X4_50,X1_50)))
% 2.70/0.99      | v2_funct_1(X3_50)
% 2.70/0.99      | ~ v2_funct_1(k1_partfun1(X4_50,X1_50,X1_50,X2_50,X3_50,X0_50))
% 2.70/0.99      | ~ v1_funct_1(X0_50)
% 2.70/0.99      | ~ v1_funct_1(X3_50)
% 2.70/0.99      | k1_xboole_0 = X2_50 ),
% 2.70/0.99      inference(subtyping,[status(esa)],[c_24]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1179,plain,
% 2.70/0.99      ( k1_xboole_0 = X0_50
% 2.70/0.99      | v1_funct_2(X1_50,X2_50,X0_50) != iProver_top
% 2.70/0.99      | v1_funct_2(X3_50,X4_50,X2_50) != iProver_top
% 2.70/0.99      | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_50,X0_50))) != iProver_top
% 2.70/0.99      | m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X4_50,X2_50))) != iProver_top
% 2.70/0.99      | v2_funct_1(X3_50) = iProver_top
% 2.70/0.99      | v2_funct_1(k1_partfun1(X4_50,X2_50,X2_50,X0_50,X3_50,X1_50)) != iProver_top
% 2.70/0.99      | v1_funct_1(X3_50) != iProver_top
% 2.70/0.99      | v1_funct_1(X1_50) != iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_720]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_2622,plain,
% 2.70/0.99      ( sK1 = k1_xboole_0
% 2.70/0.99      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 2.70/0.99      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 2.70/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 2.70/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 2.70/0.99      | v2_funct_1(k6_partfun1(sK1)) != iProver_top
% 2.70/0.99      | v2_funct_1(sK3) = iProver_top
% 2.70/0.99      | v1_funct_1(sK3) != iProver_top
% 2.70/0.99      | v1_funct_1(sK4) != iProver_top ),
% 2.70/0.99      inference(superposition,[status(thm)],[c_1732,c_1179]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_33,plain,
% 2.70/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_31,negated_conjecture,
% 2.70/0.99      ( v1_funct_2(sK3,sK1,sK2) ),
% 2.70/0.99      inference(cnf_transformation,[],[f79]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_34,plain,
% 2.70/0.99      ( v1_funct_2(sK3,sK1,sK2) = iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_35,plain,
% 2.70/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_36,plain,
% 2.70/0.99      ( v1_funct_1(sK4) = iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_28,negated_conjecture,
% 2.70/0.99      ( v1_funct_2(sK4,sK2,sK1) ),
% 2.70/0.99      inference(cnf_transformation,[],[f82]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_37,plain,
% 2.70/0.99      ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_38,plain,
% 2.70/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_10,plain,
% 2.70/0.99      ( v2_funct_1(k6_partfun1(X0)) ),
% 2.70/0.99      inference(cnf_transformation,[],[f86]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_83,plain,
% 2.70/0.99      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_85,plain,
% 2.70/0.99      ( v2_funct_1(k6_partfun1(sK1)) = iProver_top ),
% 2.70/0.99      inference(instantiation,[status(thm)],[c_83]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_719,negated_conjecture,
% 2.70/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 2.70/0.99      inference(subtyping,[status(esa)],[c_27]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1180,plain,
% 2.70/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_719]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_14,plain,
% 2.70/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.70/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.70/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_725,plain,
% 2.70/0.99      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
% 2.70/0.99      | k2_relset_1(X1_50,X2_50,X0_50) = k2_relat_1(X0_50) ),
% 2.70/0.99      inference(subtyping,[status(esa)],[c_14]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1174,plain,
% 2.70/0.99      ( k2_relset_1(X0_50,X1_50,X2_50) = k2_relat_1(X2_50)
% 2.70/0.99      | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_725]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_2231,plain,
% 2.70/0.99      ( k2_relset_1(sK2,sK1,sK4) = k2_relat_1(sK4) ),
% 2.70/0.99      inference(superposition,[status(thm)],[c_1180,c_1174]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_22,plain,
% 2.70/0.99      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 2.70/0.99      | ~ v1_funct_2(X2,X0,X1)
% 2.70/0.99      | ~ v1_funct_2(X3,X1,X0)
% 2.70/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.70/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.70/0.99      | ~ v1_funct_1(X2)
% 2.70/0.99      | ~ v1_funct_1(X3)
% 2.70/0.99      | k2_relset_1(X1,X0,X3) = X0 ),
% 2.70/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_499,plain,
% 2.70/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.70/0.99      | ~ v1_funct_2(X3,X2,X1)
% 2.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.70/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.70/0.99      | ~ v1_funct_1(X3)
% 2.70/0.99      | ~ v1_funct_1(X0)
% 2.70/0.99      | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 2.70/0.99      | k2_relset_1(X2,X1,X3) = X1
% 2.70/0.99      | k6_partfun1(X1) != k6_partfun1(sK1)
% 2.70/0.99      | sK1 != X1 ),
% 2.70/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_26]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_500,plain,
% 2.70/0.99      ( ~ v1_funct_2(X0,X1,sK1)
% 2.70/0.99      | ~ v1_funct_2(X2,sK1,X1)
% 2.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 2.70/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
% 2.70/0.99      | ~ v1_funct_1(X2)
% 2.70/0.99      | ~ v1_funct_1(X0)
% 2.70/0.99      | k1_partfun1(sK1,X1,X1,sK1,X2,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 2.70/0.99      | k2_relset_1(X1,sK1,X0) = sK1
% 2.70/0.99      | k6_partfun1(sK1) != k6_partfun1(sK1) ),
% 2.70/0.99      inference(unflattening,[status(thm)],[c_499]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_576,plain,
% 2.70/0.99      ( ~ v1_funct_2(X0,X1,sK1)
% 2.70/0.99      | ~ v1_funct_2(X2,sK1,X1)
% 2.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 2.70/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
% 2.70/0.99      | ~ v1_funct_1(X0)
% 2.70/0.99      | ~ v1_funct_1(X2)
% 2.70/0.99      | k1_partfun1(sK1,X1,X1,sK1,X2,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 2.70/0.99      | k2_relset_1(X1,sK1,X0) = sK1 ),
% 2.70/0.99      inference(equality_resolution_simp,[status(thm)],[c_500]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_708,plain,
% 2.70/0.99      ( ~ v1_funct_2(X0_50,X1_50,sK1)
% 2.70/0.99      | ~ v1_funct_2(X2_50,sK1,X1_50)
% 2.70/0.99      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,sK1)))
% 2.70/0.99      | ~ m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(sK1,X1_50)))
% 2.70/0.99      | ~ v1_funct_1(X0_50)
% 2.70/0.99      | ~ v1_funct_1(X2_50)
% 2.70/0.99      | k1_partfun1(sK1,X1_50,X1_50,sK1,X2_50,X0_50) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 2.70/0.99      | k2_relset_1(X1_50,sK1,X0_50) = sK1 ),
% 2.70/0.99      inference(subtyping,[status(esa)],[c_576]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1192,plain,
% 2.70/0.99      ( k1_partfun1(sK1,X0_50,X0_50,sK1,X1_50,X2_50) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 2.70/0.99      | k2_relset_1(X0_50,sK1,X2_50) = sK1
% 2.70/0.99      | v1_funct_2(X2_50,X0_50,sK1) != iProver_top
% 2.70/0.99      | v1_funct_2(X1_50,sK1,X0_50) != iProver_top
% 2.70/0.99      | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,sK1))) != iProver_top
% 2.70/0.99      | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(sK1,X0_50))) != iProver_top
% 2.70/0.99      | v1_funct_1(X2_50) != iProver_top
% 2.70/0.99      | v1_funct_1(X1_50) != iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_708]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1771,plain,
% 2.70/0.99      ( k1_partfun1(sK1,X0_50,X0_50,sK1,X1_50,X2_50) != k6_partfun1(sK1)
% 2.70/0.99      | k2_relset_1(X0_50,sK1,X2_50) = sK1
% 2.70/0.99      | v1_funct_2(X2_50,X0_50,sK1) != iProver_top
% 2.70/0.99      | v1_funct_2(X1_50,sK1,X0_50) != iProver_top
% 2.70/0.99      | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,sK1))) != iProver_top
% 2.70/0.99      | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(sK1,X0_50))) != iProver_top
% 2.70/0.99      | v1_funct_1(X1_50) != iProver_top
% 2.70/0.99      | v1_funct_1(X2_50) != iProver_top ),
% 2.70/0.99      inference(light_normalisation,[status(thm)],[c_1192,c_1732]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1783,plain,
% 2.70/0.99      ( k2_relset_1(sK2,sK1,sK4) = sK1
% 2.70/0.99      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 2.70/0.99      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 2.70/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 2.70/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 2.70/0.99      | v1_funct_1(sK3) != iProver_top
% 2.70/0.99      | v1_funct_1(sK4) != iProver_top ),
% 2.70/0.99      inference(superposition,[status(thm)],[c_1732,c_1771]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_15,plain,
% 2.70/0.99      ( r2_relset_1(X0,X1,X2,X2)
% 2.70/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 2.70/0.99      inference(cnf_transformation,[],[f89]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_450,plain,
% 2.70/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.70/0.99      | ~ v1_funct_2(X3,X2,X1)
% 2.70/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
% 2.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.70/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.70/0.99      | ~ v1_funct_1(X0)
% 2.70/0.99      | ~ v1_funct_1(X3)
% 2.70/0.99      | X1 != X6
% 2.70/0.99      | X1 != X5
% 2.70/0.99      | k1_partfun1(X1,X2,X2,X1,X0,X3) != X4
% 2.70/0.99      | k2_relset_1(X2,X1,X3) = X1
% 2.70/0.99      | k6_partfun1(X1) != X4 ),
% 2.70/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_22]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_451,plain,
% 2.70/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.70/0.99      | ~ v1_funct_2(X3,X2,X1)
% 2.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.70/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.70/0.99      | ~ m1_subset_1(k1_partfun1(X1,X2,X2,X1,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 2.70/0.99      | ~ v1_funct_1(X0)
% 2.70/0.99      | ~ v1_funct_1(X3)
% 2.70/0.99      | k2_relset_1(X2,X1,X3) = X1
% 2.70/0.99      | k6_partfun1(X1) != k1_partfun1(X1,X2,X2,X1,X0,X3) ),
% 2.70/0.99      inference(unflattening,[status(thm)],[c_450]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_473,plain,
% 2.70/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.70/0.99      | ~ v1_funct_2(X3,X2,X1)
% 2.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.70/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.70/0.99      | ~ v1_funct_1(X0)
% 2.70/0.99      | ~ v1_funct_1(X3)
% 2.70/0.99      | k2_relset_1(X2,X1,X3) = X1
% 2.70/0.99      | k6_partfun1(X1) != k1_partfun1(X1,X2,X2,X1,X0,X3) ),
% 2.70/0.99      inference(forward_subsumption_resolution,
% 2.70/0.99                [status(thm)],
% 2.70/0.99                [c_451,c_20]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_710,plain,
% 2.70/0.99      ( ~ v1_funct_2(X0_50,X1_50,X2_50)
% 2.70/0.99      | ~ v1_funct_2(X3_50,X2_50,X1_50)
% 2.70/0.99      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
% 2.70/0.99      | ~ m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X2_50,X1_50)))
% 2.70/0.99      | ~ v1_funct_1(X0_50)
% 2.70/0.99      | ~ v1_funct_1(X3_50)
% 2.70/0.99      | k2_relset_1(X2_50,X1_50,X3_50) = X1_50
% 2.70/0.99      | k6_partfun1(X1_50) != k1_partfun1(X1_50,X2_50,X2_50,X1_50,X0_50,X3_50) ),
% 2.70/0.99      inference(subtyping,[status(esa)],[c_473]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1490,plain,
% 2.70/0.99      ( ~ v1_funct_2(X0_50,sK2,sK1)
% 2.70/0.99      | ~ v1_funct_2(sK3,sK1,sK2)
% 2.70/0.99      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 2.70/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.70/0.99      | ~ v1_funct_1(X0_50)
% 2.70/0.99      | ~ v1_funct_1(sK3)
% 2.70/0.99      | k2_relset_1(sK2,sK1,X0_50) = sK1
% 2.70/0.99      | k6_partfun1(sK1) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,X0_50) ),
% 2.70/0.99      inference(instantiation,[status(thm)],[c_710]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1521,plain,
% 2.70/0.99      ( ~ v1_funct_2(sK3,sK1,sK2)
% 2.70/0.99      | ~ v1_funct_2(sK4,sK2,sK1)
% 2.70/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.70/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 2.70/0.99      | ~ v1_funct_1(sK3)
% 2.70/0.99      | ~ v1_funct_1(sK4)
% 2.70/0.99      | k2_relset_1(sK2,sK1,sK4) = sK1
% 2.70/0.99      | k6_partfun1(sK1) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
% 2.70/0.99      inference(instantiation,[status(thm)],[c_1490]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1786,plain,
% 2.70/0.99      ( k2_relset_1(sK2,sK1,sK4) = sK1 ),
% 2.70/0.99      inference(global_propositional_subsumption,
% 2.70/0.99                [status(thm)],
% 2.70/0.99                [c_1783,c_32,c_31,c_30,c_29,c_28,c_27,c_709,c_1521,
% 2.70/0.99                 c_1560]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_2239,plain,
% 2.70/0.99      ( k2_relat_1(sK4) = sK1 ),
% 2.70/0.99      inference(light_normalisation,[status(thm)],[c_2231,c_1786]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_13,plain,
% 2.70/0.99      ( v5_relat_1(X0,X1)
% 2.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.70/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_18,plain,
% 2.70/0.99      ( v2_funct_2(X0,k2_relat_1(X0))
% 2.70/0.99      | ~ v5_relat_1(X0,k2_relat_1(X0))
% 2.70/0.99      | ~ v1_relat_1(X0) ),
% 2.70/0.99      inference(cnf_transformation,[],[f90]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_403,plain,
% 2.70/0.99      ( v2_funct_2(X0,k2_relat_1(X0))
% 2.70/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 2.70/0.99      | ~ v1_relat_1(X0)
% 2.70/0.99      | X0 != X1
% 2.70/0.99      | k2_relat_1(X0) != X3 ),
% 2.70/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_18]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_404,plain,
% 2.70/0.99      ( v2_funct_2(X0,k2_relat_1(X0))
% 2.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
% 2.70/0.99      | ~ v1_relat_1(X0) ),
% 2.70/0.99      inference(unflattening,[status(thm)],[c_403]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_12,plain,
% 2.70/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.70/0.99      | v1_relat_1(X0) ),
% 2.70/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_414,plain,
% 2.70/0.99      ( v2_funct_2(X0,k2_relat_1(X0))
% 2.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0)))) ),
% 2.70/0.99      inference(forward_subsumption_resolution,
% 2.70/0.99                [status(thm)],
% 2.70/0.99                [c_404,c_12]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_25,negated_conjecture,
% 2.70/0.99      ( ~ v2_funct_2(sK4,sK1) | ~ v2_funct_1(sK3) ),
% 2.70/0.99      inference(cnf_transformation,[],[f85]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_429,plain,
% 2.70/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
% 2.70/0.99      | ~ v2_funct_1(sK3)
% 2.70/0.99      | k2_relat_1(X0) != sK1
% 2.70/0.99      | sK4 != X0 ),
% 2.70/0.99      inference(resolution_lifted,[status(thm)],[c_414,c_25]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_430,plain,
% 2.70/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK4))))
% 2.70/0.99      | ~ v2_funct_1(sK3)
% 2.70/0.99      | k2_relat_1(sK4) != sK1 ),
% 2.70/0.99      inference(unflattening,[status(thm)],[c_429]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_711,plain,
% 2.70/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_50,k2_relat_1(sK4))))
% 2.70/0.99      | ~ v2_funct_1(sK3)
% 2.70/0.99      | k2_relat_1(sK4) != sK1 ),
% 2.70/0.99      inference(subtyping,[status(esa)],[c_430]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_731,plain,
% 2.70/0.99      ( ~ v2_funct_1(sK3) | sP0_iProver_split | k2_relat_1(sK4) != sK1 ),
% 2.70/0.99      inference(splitting,
% 2.70/0.99                [splitting(split),new_symbols(definition,[])],
% 2.70/0.99                [c_711]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1188,plain,
% 2.70/0.99      ( k2_relat_1(sK4) != sK1
% 2.70/0.99      | v2_funct_1(sK3) != iProver_top
% 2.70/0.99      | sP0_iProver_split = iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_731]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_2907,plain,
% 2.70/0.99      ( sK1 != sK1
% 2.70/0.99      | v2_funct_1(sK3) != iProver_top
% 2.70/0.99      | sP0_iProver_split = iProver_top ),
% 2.70/0.99      inference(demodulation,[status(thm)],[c_2239,c_1188]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_2908,plain,
% 2.70/0.99      ( v2_funct_1(sK3) != iProver_top
% 2.70/0.99      | sP0_iProver_split = iProver_top ),
% 2.70/0.99      inference(equality_resolution_simp,[status(thm)],[c_2907]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_730,plain,
% 2.70/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_50,k2_relat_1(sK4))))
% 2.70/0.99      | ~ sP0_iProver_split ),
% 2.70/0.99      inference(splitting,
% 2.70/0.99                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.70/0.99                [c_711]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1189,plain,
% 2.70/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_50,k2_relat_1(sK4)))) != iProver_top
% 2.70/0.99      | sP0_iProver_split != iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_730]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_2906,plain,
% 2.70/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_50,sK1))) != iProver_top
% 2.70/0.99      | sP0_iProver_split != iProver_top ),
% 2.70/0.99      inference(demodulation,[status(thm)],[c_2239,c_1189]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_3158,plain,
% 2.70/0.99      ( sP0_iProver_split != iProver_top ),
% 2.70/0.99      inference(superposition,[status(thm)],[c_1180,c_2906]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_3325,plain,
% 2.70/0.99      ( sK1 = k1_xboole_0 ),
% 2.70/0.99      inference(global_propositional_subsumption,
% 2.70/0.99                [status(thm)],
% 2.70/0.99                [c_2622,c_33,c_34,c_35,c_36,c_37,c_38,c_85,c_2908,c_3158]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_716,negated_conjecture,
% 2.70/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 2.70/0.99      inference(subtyping,[status(esa)],[c_30]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1183,plain,
% 2.70/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_716]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_3335,plain,
% 2.70/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) = iProver_top ),
% 2.70/0.99      inference(demodulation,[status(thm)],[c_3325,c_1183]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_0,plain,
% 2.70/0.99      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 2.70/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_4,plain,
% 2.70/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.70/0.99      | ~ r2_hidden(X2,X0)
% 2.70/0.99      | ~ v1_xboole_0(X1) ),
% 2.70/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_367,plain,
% 2.70/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.70/0.99      | ~ v1_xboole_0(X1)
% 2.70/0.99      | v1_xboole_0(X2)
% 2.70/0.99      | X0 != X2
% 2.70/0.99      | sK0(X2) != X3 ),
% 2.70/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_4]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_368,plain,
% 2.70/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.70/0.99      | ~ v1_xboole_0(X1)
% 2.70/0.99      | v1_xboole_0(X0) ),
% 2.70/0.99      inference(unflattening,[status(thm)],[c_367]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_712,plain,
% 2.70/0.99      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(X1_50))
% 2.70/0.99      | ~ v1_xboole_0(X1_50)
% 2.70/0.99      | v1_xboole_0(X0_50) ),
% 2.70/0.99      inference(subtyping,[status(esa)],[c_368]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1187,plain,
% 2.70/0.99      ( m1_subset_1(X0_50,k1_zfmisc_1(X1_50)) != iProver_top
% 2.70/0.99      | v1_xboole_0(X1_50) != iProver_top
% 2.70/0.99      | v1_xboole_0(X0_50) = iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_712]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_4025,plain,
% 2.70/0.99      ( v1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK2)) != iProver_top
% 2.70/0.99      | v1_xboole_0(sK3) = iProver_top ),
% 2.70/0.99      inference(superposition,[status(thm)],[c_3335,c_1187]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_7,plain,
% 2.70/0.99      ( v2_funct_1(X0)
% 2.70/0.99      | ~ v1_funct_1(X0)
% 2.70/0.99      | ~ v1_relat_1(X0)
% 2.70/0.99      | ~ v1_xboole_0(X0) ),
% 2.70/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_6,plain,
% 2.70/0.99      ( v1_funct_1(X0) | ~ v1_xboole_0(X0) ),
% 2.70/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_5,plain,
% 2.70/0.99      ( v1_relat_1(X0) | ~ v1_xboole_0(X0) ),
% 2.70/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_200,plain,
% 2.70/0.99      ( v2_funct_1(X0) | ~ v1_xboole_0(X0) ),
% 2.70/0.99      inference(global_propositional_subsumption,
% 2.70/0.99                [status(thm)],
% 2.70/0.99                [c_7,c_6,c_5]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_713,plain,
% 2.70/0.99      ( v2_funct_1(X0_50) | ~ v1_xboole_0(X0_50) ),
% 2.70/0.99      inference(subtyping,[status(esa)],[c_200]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1393,plain,
% 2.70/0.99      ( v2_funct_1(sK3) | ~ v1_xboole_0(sK3) ),
% 2.70/0.99      inference(instantiation,[status(thm)],[c_713]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1394,plain,
% 2.70/0.99      ( v2_funct_1(sK3) = iProver_top | v1_xboole_0(sK3) != iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_1393]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_4736,plain,
% 2.70/0.99      ( v1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK2)) != iProver_top ),
% 2.70/0.99      inference(global_propositional_subsumption,
% 2.70/0.99                [status(thm)],
% 2.70/0.99                [c_4025,c_1394,c_2908,c_3158]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_4741,plain,
% 2.70/0.99      ( v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.70/0.99      inference(superposition,[status(thm)],[c_1171,c_4736]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_2,plain,
% 2.70/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 2.70/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_103,plain,
% 2.70/0.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(contradiction,plain,
% 2.70/0.99      ( $false ),
% 2.70/0.99      inference(minisat,[status(thm)],[c_4741,c_103]) ).
% 2.70/0.99  
% 2.70/0.99  
% 2.70/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.70/0.99  
% 2.70/0.99  ------                               Statistics
% 2.70/0.99  
% 2.70/0.99  ------ General
% 2.70/0.99  
% 2.70/0.99  abstr_ref_over_cycles:                  0
% 2.70/0.99  abstr_ref_under_cycles:                 0
% 2.70/0.99  gc_basic_clause_elim:                   0
% 2.70/0.99  forced_gc_time:                         0
% 2.70/0.99  parsing_time:                           0.014
% 2.70/0.99  unif_index_cands_time:                  0.
% 2.70/0.99  unif_index_add_time:                    0.
% 2.70/0.99  orderings_time:                         0.
% 2.70/0.99  out_proof_time:                         0.01
% 2.70/0.99  total_time:                             0.196
% 2.70/0.99  num_of_symbols:                         56
% 2.70/0.99  num_of_terms:                           5830
% 2.70/0.99  
% 2.70/0.99  ------ Preprocessing
% 2.70/0.99  
% 2.70/0.99  num_of_splits:                          1
% 2.70/0.99  num_of_split_atoms:                     1
% 2.70/0.99  num_of_reused_defs:                     0
% 2.70/0.99  num_eq_ax_congr_red:                    11
% 2.70/0.99  num_of_sem_filtered_clauses:            1
% 2.70/0.99  num_of_subtypes:                        2
% 2.70/0.99  monotx_restored_types:                  0
% 2.70/0.99  sat_num_of_epr_types:                   0
% 2.70/0.99  sat_num_of_non_cyclic_types:            0
% 2.70/0.99  sat_guarded_non_collapsed_types:        1
% 2.70/0.99  num_pure_diseq_elim:                    0
% 2.70/0.99  simp_replaced_by:                       0
% 2.70/0.99  res_preprocessed:                       128
% 2.70/0.99  prep_upred:                             0
% 2.70/0.99  prep_unflattend:                        21
% 2.70/0.99  smt_new_axioms:                         0
% 2.70/0.99  pred_elim_cands:                        5
% 2.70/0.99  pred_elim:                              5
% 2.70/0.99  pred_elim_cl:                           9
% 2.70/0.99  pred_elim_cycles:                       7
% 2.70/0.99  merged_defs:                            0
% 2.70/0.99  merged_defs_ncl:                        0
% 2.70/0.99  bin_hyper_res:                          0
% 2.70/0.99  prep_cycles:                            4
% 2.70/0.99  pred_elim_time:                         0.005
% 2.70/0.99  splitting_time:                         0.
% 2.70/0.99  sem_filter_time:                        0.
% 2.70/0.99  monotx_time:                            0.
% 2.70/0.99  subtype_inf_time:                       0.
% 2.70/0.99  
% 2.70/0.99  ------ Problem properties
% 2.70/0.99  
% 2.70/0.99  clauses:                                23
% 2.70/0.99  conjectures:                            6
% 2.70/0.99  epr:                                    7
% 2.70/0.99  horn:                                   22
% 2.70/0.99  ground:                                 9
% 2.70/0.99  unary:                                  9
% 2.70/0.99  binary:                                 6
% 2.70/0.99  lits:                                   70
% 2.70/0.99  lits_eq:                                8
% 2.70/0.99  fd_pure:                                0
% 2.70/0.99  fd_pseudo:                              0
% 2.70/0.99  fd_cond:                                1
% 2.70/0.99  fd_pseudo_cond:                         0
% 2.70/0.99  ac_symbols:                             0
% 2.70/0.99  
% 2.70/0.99  ------ Propositional Solver
% 2.70/0.99  
% 2.70/0.99  prop_solver_calls:                      29
% 2.70/0.99  prop_fast_solver_calls:                 903
% 2.70/0.99  smt_solver_calls:                       0
% 2.70/0.99  smt_fast_solver_calls:                  0
% 2.70/0.99  prop_num_of_clauses:                    2110
% 2.70/0.99  prop_preprocess_simplified:             6626
% 2.70/0.99  prop_fo_subsumed:                       23
% 2.70/0.99  prop_solver_time:                       0.
% 2.70/0.99  smt_solver_time:                        0.
% 2.70/0.99  smt_fast_solver_time:                   0.
% 2.70/0.99  prop_fast_solver_time:                  0.
% 2.70/0.99  prop_unsat_core_time:                   0.
% 2.70/0.99  
% 2.70/0.99  ------ QBF
% 2.70/0.99  
% 2.70/0.99  qbf_q_res:                              0
% 2.70/0.99  qbf_num_tautologies:                    0
% 2.70/0.99  qbf_prep_cycles:                        0
% 2.70/0.99  
% 2.70/0.99  ------ BMC1
% 2.70/0.99  
% 2.70/0.99  bmc1_current_bound:                     -1
% 2.70/0.99  bmc1_last_solved_bound:                 -1
% 2.70/0.99  bmc1_unsat_core_size:                   -1
% 2.70/0.99  bmc1_unsat_core_parents_size:           -1
% 2.70/0.99  bmc1_merge_next_fun:                    0
% 2.70/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.70/0.99  
% 2.70/0.99  ------ Instantiation
% 2.70/0.99  
% 2.70/0.99  inst_num_of_clauses:                    681
% 2.70/0.99  inst_num_in_passive:                    488
% 2.70/0.99  inst_num_in_active:                     187
% 2.70/0.99  inst_num_in_unprocessed:                6
% 2.70/0.99  inst_num_of_loops:                      210
% 2.70/0.99  inst_num_of_learning_restarts:          0
% 2.70/0.99  inst_num_moves_active_passive:          21
% 2.70/0.99  inst_lit_activity:                      0
% 2.70/0.99  inst_lit_activity_moves:                1
% 2.70/0.99  inst_num_tautologies:                   0
% 2.70/0.99  inst_num_prop_implied:                  0
% 2.70/0.99  inst_num_existing_simplified:           0
% 2.70/0.99  inst_num_eq_res_simplified:             0
% 2.70/0.99  inst_num_child_elim:                    0
% 2.70/0.99  inst_num_of_dismatching_blockings:      9
% 2.70/0.99  inst_num_of_non_proper_insts:           314
% 2.70/0.99  inst_num_of_duplicates:                 0
% 2.70/0.99  inst_inst_num_from_inst_to_res:         0
% 2.70/0.99  inst_dismatching_checking_time:         0.
% 2.70/0.99  
% 2.70/0.99  ------ Resolution
% 2.70/0.99  
% 2.70/0.99  res_num_of_clauses:                     0
% 2.70/0.99  res_num_in_passive:                     0
% 2.70/0.99  res_num_in_active:                      0
% 2.70/0.99  res_num_of_loops:                       132
% 2.70/0.99  res_forward_subset_subsumed:            3
% 2.70/0.99  res_backward_subset_subsumed:           0
% 2.70/0.99  res_forward_subsumed:                   0
% 2.70/0.99  res_backward_subsumed:                  0
% 2.70/0.99  res_forward_subsumption_resolution:     3
% 2.70/0.99  res_backward_subsumption_resolution:    0
% 2.70/0.99  res_clause_to_clause_subsumption:       69
% 2.70/0.99  res_orphan_elimination:                 0
% 2.70/0.99  res_tautology_del:                      16
% 2.70/0.99  res_num_eq_res_simplified:              1
% 2.70/0.99  res_num_sel_changes:                    0
% 2.70/0.99  res_moves_from_active_to_pass:          0
% 2.70/0.99  
% 2.70/0.99  ------ Superposition
% 2.70/0.99  
% 2.70/0.99  sup_time_total:                         0.
% 2.70/0.99  sup_time_generating:                    0.
% 2.70/0.99  sup_time_sim_full:                      0.
% 2.70/0.99  sup_time_sim_immed:                     0.
% 2.70/0.99  
% 2.70/0.99  sup_num_of_clauses:                     40
% 2.70/0.99  sup_num_in_active:                      29
% 2.70/0.99  sup_num_in_passive:                     11
% 2.70/0.99  sup_num_of_loops:                       41
% 2.70/0.99  sup_fw_superposition:                   15
% 2.70/0.99  sup_bw_superposition:                   8
% 2.70/0.99  sup_immediate_simplified:               5
% 2.70/0.99  sup_given_eliminated:                   0
% 2.70/0.99  comparisons_done:                       0
% 2.70/0.99  comparisons_avoided:                    0
% 2.70/0.99  
% 2.70/0.99  ------ Simplifications
% 2.70/0.99  
% 2.70/0.99  
% 2.70/0.99  sim_fw_subset_subsumed:                 2
% 2.70/0.99  sim_bw_subset_subsumed:                 0
% 2.70/0.99  sim_fw_subsumed:                        2
% 2.70/0.99  sim_bw_subsumed:                        0
% 2.70/0.99  sim_fw_subsumption_res:                 0
% 2.70/0.99  sim_bw_subsumption_res:                 0
% 2.70/0.99  sim_tautology_del:                      0
% 2.70/0.99  sim_eq_tautology_del:                   1
% 2.70/0.99  sim_eq_res_simp:                        1
% 2.70/0.99  sim_fw_demodulated:                     0
% 2.70/0.99  sim_bw_demodulated:                     13
% 2.70/0.99  sim_light_normalised:                   2
% 2.70/0.99  sim_joinable_taut:                      0
% 2.70/0.99  sim_joinable_simp:                      0
% 2.70/0.99  sim_ac_normalised:                      0
% 2.70/0.99  sim_smt_subsumption:                    0
% 2.70/0.99  
%------------------------------------------------------------------------------

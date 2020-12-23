%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:01:54 EST 2020

% Result     : Theorem 2.99s
% Output     : CNFRefutation 2.99s
% Verified   : 
% Statistics : Number of formulae       :  160 ( 717 expanded)
%              Number of clauses        :   96 ( 242 expanded)
%              Number of leaves         :   19 ( 169 expanded)
%              Depth                    :   18
%              Number of atoms          :  562 (4488 expanded)
%              Number of equality atoms :  165 ( 385 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f28])).

fof(f54,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f24])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f15,conjecture,(
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

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f39,plain,(
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

fof(f38,plain,
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

fof(f40,plain,
    ( ( ~ v2_funct_2(sK3,sK0)
      | ~ v2_funct_1(sK2) )
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f35,f39,f38])).

fof(f66,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f40])).

fof(f11,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f55,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f60,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f62,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f40])).

fof(f63,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f65,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f40])).

fof(f14,axiom,(
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

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f58,plain,(
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
    inference(cnf_transformation,[],[f33])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f13,axiom,(
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

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f61,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f64,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f71,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f52])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f67,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f12,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f68,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f44,f56])).

cnf(c_625,plain,
    ( ~ v2_funct_1(X0_48)
    | v2_funct_1(X1_48)
    | X1_48 != X0_48 ),
    theory(equality)).

cnf(c_3414,plain,
    ( ~ v2_funct_1(X0_48)
    | v2_funct_1(sK2)
    | sK2 != X0_48 ),
    inference(instantiation,[status(thm)],[c_625])).

cnf(c_3416,plain,
    ( v2_funct_1(sK2)
    | ~ v2_funct_1(sK0)
    | sK2 != sK0 ),
    inference(instantiation,[status(thm)],[c_3414])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_610,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | ~ m1_subset_1(X3_48,k1_zfmisc_1(k2_zfmisc_1(X4_48,X5_48)))
    | m1_subset_1(k1_partfun1(X4_48,X5_48,X1_48,X2_48,X3_48,X0_48),k1_zfmisc_1(k2_zfmisc_1(X4_48,X2_48)))
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(X3_48) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1029,plain,
    ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48))) != iProver_top
    | m1_subset_1(X3_48,k1_zfmisc_1(k2_zfmisc_1(X4_48,X5_48))) != iProver_top
    | m1_subset_1(k1_partfun1(X4_48,X5_48,X1_48,X2_48,X3_48,X0_48),k1_zfmisc_1(k2_zfmisc_1(X4_48,X2_48))) = iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(X3_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_610])).

cnf(c_9,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_19,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_388,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_19])).

cnf(c_389,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_388])).

cnf(c_14,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_44,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_391,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_389,c_44])).

cnf(c_597,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_391])).

cnf(c_1043,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_597])).

cnf(c_2121,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1029,c_1043])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_26,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_28,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_29,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_31,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2370,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2121,c_26,c_28,c_29,c_31])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v2_funct_1(k1_partfun1(X1,X2,X2,X4,X0,X3))
    | k1_xboole_0 = X4 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_606,plain,
    ( ~ v1_funct_2(X0_48,X1_48,X2_48)
    | ~ v1_funct_2(X3_48,X2_48,X4_48)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | ~ m1_subset_1(X3_48,k1_zfmisc_1(k2_zfmisc_1(X2_48,X4_48)))
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(X3_48)
    | v2_funct_1(X0_48)
    | ~ v2_funct_1(k1_partfun1(X1_48,X2_48,X2_48,X4_48,X0_48,X3_48))
    | k1_xboole_0 = X4_48 ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1033,plain,
    ( k1_xboole_0 = X0_48
    | v1_funct_2(X1_48,X2_48,X3_48) != iProver_top
    | v1_funct_2(X4_48,X3_48,X0_48) != iProver_top
    | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_48,X3_48))) != iProver_top
    | m1_subset_1(X4_48,k1_zfmisc_1(k2_zfmisc_1(X3_48,X0_48))) != iProver_top
    | v1_funct_1(X1_48) != iProver_top
    | v1_funct_1(X4_48) != iProver_top
    | v2_funct_1(X1_48) = iProver_top
    | v2_funct_1(k1_partfun1(X2_48,X3_48,X3_48,X0_48,X1_48,X4_48)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_606])).

cnf(c_2396,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2370,c_1033])).

cnf(c_608,plain,
    ( m1_subset_1(k6_partfun1(X0_48),k1_zfmisc_1(k2_zfmisc_1(X0_48,X0_48))) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1031,plain,
    ( m1_subset_1(k6_partfun1(X0_48),k1_zfmisc_1(k2_zfmisc_1(X0_48,X0_48))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_608])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_612,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | ~ v1_xboole_0(X1_48)
    | v1_xboole_0(X0_48) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1027,plain,
    ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48))) != iProver_top
    | v1_xboole_0(X1_48) != iProver_top
    | v1_xboole_0(X0_48) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_612])).

cnf(c_2051,plain,
    ( v1_xboole_0(X0_48) != iProver_top
    | v1_xboole_0(k6_partfun1(X0_48)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1031,c_1027])).

cnf(c_2066,plain,
    ( ~ v1_xboole_0(X0_48)
    | v1_xboole_0(k6_partfun1(X0_48)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2051])).

cnf(c_2068,plain,
    ( v1_xboole_0(k6_partfun1(sK0))
    | ~ v1_xboole_0(sK0) ),
    inference(instantiation,[status(thm)],[c_2066])).

cnf(c_602,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1037,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_602])).

cnf(c_2050,plain,
    ( v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1037,c_1027])).

cnf(c_2065,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_xboole_0(sK0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2050])).

cnf(c_605,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1034,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_605])).

cnf(c_15,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_402,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X2,X1,X3) = X1
    | k6_partfun1(X1) != k6_partfun1(sK0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_19])).

cnf(c_403,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X0)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0
    | k6_partfun1(sK0) != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_402])).

cnf(c_477,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_403])).

cnf(c_596,plain,
    ( ~ v1_funct_2(X0_48,X1_48,sK0)
    | ~ v1_funct_2(X2_48,sK0,X1_48)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,sK0)))
    | ~ m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(sK0,X1_48)))
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(X2_48)
    | k1_partfun1(sK0,X1_48,X1_48,sK0,X2_48,X0_48) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1_48,sK0,X0_48) = sK0 ),
    inference(subtyping,[status(esa)],[c_477])).

cnf(c_1044,plain,
    ( k1_partfun1(sK0,X0_48,X0_48,sK0,X1_48,X2_48) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X0_48,sK0,X2_48) = sK0
    | v1_funct_2(X2_48,X0_48,sK0) != iProver_top
    | v1_funct_2(X1_48,sK0,X0_48) != iProver_top
    | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,sK0))) != iProver_top
    | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_48))) != iProver_top
    | v1_funct_1(X2_48) != iProver_top
    | v1_funct_1(X1_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_596])).

cnf(c_1930,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1044])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_611,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | k2_relset_1(X1_48,X2_48,X0_48) = k2_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1028,plain,
    ( k2_relset_1(X0_48,X1_48,X2_48) = k2_relat_1(X2_48)
    | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_611])).

cnf(c_1613,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1034,c_1028])).

cnf(c_1931,plain,
    ( k2_relat_1(sK3) = sK0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1930,c_1613])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_27,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_21,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_30,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1934,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1931,c_26,c_27,c_28,c_29,c_30,c_31])).

cnf(c_5,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_10,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_306,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X0)
    | X0 != X1
    | k2_relat_1(X0) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_10])).

cnf(c_307,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_306])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_317,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0)))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_307,c_4])).

cnf(c_18,negated_conjecture,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_332,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
    | ~ v2_funct_1(sK2)
    | k2_relat_1(X0) != sK0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_317,c_18])).

cnf(c_333,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3))))
    | ~ v2_funct_1(sK2)
    | k2_relat_1(sK3) != sK0 ),
    inference(unflattening,[status(thm)],[c_332])).

cnf(c_599,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_48,k2_relat_1(sK3))))
    | ~ v2_funct_1(sK2)
    | k2_relat_1(sK3) != sK0 ),
    inference(subtyping,[status(esa)],[c_333])).

cnf(c_616,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_48,k2_relat_1(sK3))))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_599])).

cnf(c_1041,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_48,k2_relat_1(sK3)))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_616])).

cnf(c_1938,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_48,sK0))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(demodulation,[status(thm)],[c_1934,c_1041])).

cnf(c_2007,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_1034,c_1938])).

cnf(c_2008,plain,
    ( ~ sP0_iProver_split ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2007])).

cnf(c_617,plain,
    ( ~ v2_funct_1(sK2)
    | sP0_iProver_split
    | k2_relat_1(sK3) != sK0 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_599])).

cnf(c_1040,plain,
    ( k2_relat_1(sK3) != sK0
    | v2_funct_1(sK2) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_617])).

cnf(c_1939,plain,
    ( sK0 != sK0
    | v2_funct_1(sK2) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_1934,c_1040])).

cnf(c_1940,plain,
    ( v2_funct_1(sK2) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_1939])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_614,plain,
    ( ~ v1_xboole_0(X0_48)
    | ~ v1_xboole_0(X1_48)
    | X1_48 = X0_48 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1624,plain,
    ( ~ v1_xboole_0(X0_48)
    | ~ v1_xboole_0(sK2)
    | sK2 = X0_48 ),
    inference(instantiation,[status(thm)],[c_614])).

cnf(c_1626,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ v1_xboole_0(sK0)
    | sK2 = sK0 ),
    inference(instantiation,[status(thm)],[c_1624])).

cnf(c_1495,plain,
    ( ~ v1_xboole_0(X0_48)
    | ~ v1_xboole_0(k6_partfun1(X1_48))
    | X0_48 = k6_partfun1(X1_48) ),
    inference(instantiation,[status(thm)],[c_614])).

cnf(c_1497,plain,
    ( ~ v1_xboole_0(k6_partfun1(sK0))
    | ~ v1_xboole_0(sK0)
    | sK0 = k6_partfun1(sK0) ),
    inference(instantiation,[status(thm)],[c_1495])).

cnf(c_623,plain,
    ( ~ v1_xboole_0(X0_48)
    | v1_xboole_0(X1_48)
    | X1_48 != X0_48 ),
    theory(equality)).

cnf(c_1354,plain,
    ( v1_xboole_0(X0_48)
    | ~ v1_xboole_0(k1_xboole_0)
    | X0_48 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_623])).

cnf(c_1356,plain,
    ( v1_xboole_0(sK0)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1354])).

cnf(c_1240,plain,
    ( v2_funct_1(X0_48)
    | ~ v2_funct_1(k6_partfun1(X1_48))
    | X0_48 != k6_partfun1(X1_48) ),
    inference(instantiation,[status(thm)],[c_625])).

cnf(c_1242,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | v2_funct_1(sK0)
    | sK0 != k6_partfun1(sK0) ),
    inference(instantiation,[status(thm)],[c_1240])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_2,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_77,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_79,plain,
    ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_77])).

cnf(c_78,plain,
    ( v2_funct_1(k6_partfun1(sK0)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3416,c_2396,c_2068,c_2065,c_2008,c_2007,c_1940,c_1931,c_1626,c_1497,c_1356,c_1242,c_617,c_0,c_79,c_78,c_31,c_30,c_29,c_28,c_27,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:01:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.99/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.99/0.99  
% 2.99/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.99/0.99  
% 2.99/0.99  ------  iProver source info
% 2.99/0.99  
% 2.99/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.99/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.99/0.99  git: non_committed_changes: false
% 2.99/0.99  git: last_make_outside_of_git: false
% 2.99/0.99  
% 2.99/0.99  ------ 
% 2.99/0.99  
% 2.99/0.99  ------ Input Options
% 2.99/0.99  
% 2.99/0.99  --out_options                           all
% 2.99/0.99  --tptp_safe_out                         true
% 2.99/0.99  --problem_path                          ""
% 2.99/0.99  --include_path                          ""
% 2.99/0.99  --clausifier                            res/vclausify_rel
% 2.99/0.99  --clausifier_options                    --mode clausify
% 2.99/0.99  --stdin                                 false
% 2.99/0.99  --stats_out                             all
% 2.99/0.99  
% 2.99/0.99  ------ General Options
% 2.99/0.99  
% 2.99/0.99  --fof                                   false
% 2.99/0.99  --time_out_real                         305.
% 2.99/0.99  --time_out_virtual                      -1.
% 2.99/0.99  --symbol_type_check                     false
% 2.99/0.99  --clausify_out                          false
% 2.99/0.99  --sig_cnt_out                           false
% 2.99/0.99  --trig_cnt_out                          false
% 2.99/0.99  --trig_cnt_out_tolerance                1.
% 2.99/0.99  --trig_cnt_out_sk_spl                   false
% 2.99/0.99  --abstr_cl_out                          false
% 2.99/0.99  
% 2.99/0.99  ------ Global Options
% 2.99/0.99  
% 2.99/0.99  --schedule                              default
% 2.99/0.99  --add_important_lit                     false
% 2.99/0.99  --prop_solver_per_cl                    1000
% 2.99/0.99  --min_unsat_core                        false
% 2.99/0.99  --soft_assumptions                      false
% 2.99/0.99  --soft_lemma_size                       3
% 2.99/0.99  --prop_impl_unit_size                   0
% 2.99/0.99  --prop_impl_unit                        []
% 2.99/0.99  --share_sel_clauses                     true
% 2.99/0.99  --reset_solvers                         false
% 2.99/0.99  --bc_imp_inh                            [conj_cone]
% 2.99/0.99  --conj_cone_tolerance                   3.
% 2.99/0.99  --extra_neg_conj                        none
% 2.99/0.99  --large_theory_mode                     true
% 2.99/0.99  --prolific_symb_bound                   200
% 2.99/0.99  --lt_threshold                          2000
% 2.99/0.99  --clause_weak_htbl                      true
% 2.99/0.99  --gc_record_bc_elim                     false
% 2.99/0.99  
% 2.99/0.99  ------ Preprocessing Options
% 2.99/0.99  
% 2.99/0.99  --preprocessing_flag                    true
% 2.99/0.99  --time_out_prep_mult                    0.1
% 2.99/0.99  --splitting_mode                        input
% 2.99/0.99  --splitting_grd                         true
% 2.99/0.99  --splitting_cvd                         false
% 2.99/0.99  --splitting_cvd_svl                     false
% 2.99/0.99  --splitting_nvd                         32
% 2.99/0.99  --sub_typing                            true
% 2.99/0.99  --prep_gs_sim                           true
% 2.99/0.99  --prep_unflatten                        true
% 2.99/0.99  --prep_res_sim                          true
% 2.99/0.99  --prep_upred                            true
% 2.99/0.99  --prep_sem_filter                       exhaustive
% 2.99/0.99  --prep_sem_filter_out                   false
% 2.99/0.99  --pred_elim                             true
% 2.99/0.99  --res_sim_input                         true
% 2.99/0.99  --eq_ax_congr_red                       true
% 2.99/0.99  --pure_diseq_elim                       true
% 2.99/0.99  --brand_transform                       false
% 2.99/0.99  --non_eq_to_eq                          false
% 2.99/0.99  --prep_def_merge                        true
% 2.99/0.99  --prep_def_merge_prop_impl              false
% 2.99/0.99  --prep_def_merge_mbd                    true
% 2.99/0.99  --prep_def_merge_tr_red                 false
% 2.99/0.99  --prep_def_merge_tr_cl                  false
% 2.99/0.99  --smt_preprocessing                     true
% 2.99/0.99  --smt_ac_axioms                         fast
% 2.99/0.99  --preprocessed_out                      false
% 2.99/0.99  --preprocessed_stats                    false
% 2.99/0.99  
% 2.99/0.99  ------ Abstraction refinement Options
% 2.99/0.99  
% 2.99/0.99  --abstr_ref                             []
% 2.99/0.99  --abstr_ref_prep                        false
% 2.99/0.99  --abstr_ref_until_sat                   false
% 2.99/0.99  --abstr_ref_sig_restrict                funpre
% 2.99/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.99/0.99  --abstr_ref_under                       []
% 2.99/0.99  
% 2.99/0.99  ------ SAT Options
% 2.99/0.99  
% 2.99/0.99  --sat_mode                              false
% 2.99/0.99  --sat_fm_restart_options                ""
% 2.99/0.99  --sat_gr_def                            false
% 2.99/0.99  --sat_epr_types                         true
% 2.99/0.99  --sat_non_cyclic_types                  false
% 2.99/0.99  --sat_finite_models                     false
% 2.99/0.99  --sat_fm_lemmas                         false
% 2.99/0.99  --sat_fm_prep                           false
% 2.99/0.99  --sat_fm_uc_incr                        true
% 2.99/0.99  --sat_out_model                         small
% 2.99/0.99  --sat_out_clauses                       false
% 2.99/0.99  
% 2.99/0.99  ------ QBF Options
% 2.99/0.99  
% 2.99/0.99  --qbf_mode                              false
% 2.99/0.99  --qbf_elim_univ                         false
% 2.99/0.99  --qbf_dom_inst                          none
% 2.99/0.99  --qbf_dom_pre_inst                      false
% 2.99/0.99  --qbf_sk_in                             false
% 2.99/0.99  --qbf_pred_elim                         true
% 2.99/0.99  --qbf_split                             512
% 2.99/0.99  
% 2.99/0.99  ------ BMC1 Options
% 2.99/0.99  
% 2.99/0.99  --bmc1_incremental                      false
% 2.99/0.99  --bmc1_axioms                           reachable_all
% 2.99/0.99  --bmc1_min_bound                        0
% 2.99/0.99  --bmc1_max_bound                        -1
% 2.99/0.99  --bmc1_max_bound_default                -1
% 2.99/0.99  --bmc1_symbol_reachability              true
% 2.99/0.99  --bmc1_property_lemmas                  false
% 2.99/0.99  --bmc1_k_induction                      false
% 2.99/0.99  --bmc1_non_equiv_states                 false
% 2.99/0.99  --bmc1_deadlock                         false
% 2.99/0.99  --bmc1_ucm                              false
% 2.99/0.99  --bmc1_add_unsat_core                   none
% 2.99/0.99  --bmc1_unsat_core_children              false
% 2.99/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.99/0.99  --bmc1_out_stat                         full
% 2.99/0.99  --bmc1_ground_init                      false
% 2.99/0.99  --bmc1_pre_inst_next_state              false
% 2.99/0.99  --bmc1_pre_inst_state                   false
% 2.99/0.99  --bmc1_pre_inst_reach_state             false
% 2.99/0.99  --bmc1_out_unsat_core                   false
% 2.99/0.99  --bmc1_aig_witness_out                  false
% 2.99/0.99  --bmc1_verbose                          false
% 2.99/0.99  --bmc1_dump_clauses_tptp                false
% 2.99/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.99/0.99  --bmc1_dump_file                        -
% 2.99/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.99/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.99/0.99  --bmc1_ucm_extend_mode                  1
% 2.99/0.99  --bmc1_ucm_init_mode                    2
% 2.99/0.99  --bmc1_ucm_cone_mode                    none
% 2.99/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.99/0.99  --bmc1_ucm_relax_model                  4
% 2.99/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.99/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.99/0.99  --bmc1_ucm_layered_model                none
% 2.99/0.99  --bmc1_ucm_max_lemma_size               10
% 2.99/0.99  
% 2.99/0.99  ------ AIG Options
% 2.99/0.99  
% 2.99/0.99  --aig_mode                              false
% 2.99/0.99  
% 2.99/0.99  ------ Instantiation Options
% 2.99/0.99  
% 2.99/0.99  --instantiation_flag                    true
% 2.99/0.99  --inst_sos_flag                         false
% 2.99/0.99  --inst_sos_phase                        true
% 2.99/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.99/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.99/0.99  --inst_lit_sel_side                     num_symb
% 2.99/0.99  --inst_solver_per_active                1400
% 2.99/0.99  --inst_solver_calls_frac                1.
% 2.99/0.99  --inst_passive_queue_type               priority_queues
% 2.99/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.99/0.99  --inst_passive_queues_freq              [25;2]
% 2.99/0.99  --inst_dismatching                      true
% 2.99/0.99  --inst_eager_unprocessed_to_passive     true
% 2.99/0.99  --inst_prop_sim_given                   true
% 2.99/0.99  --inst_prop_sim_new                     false
% 2.99/0.99  --inst_subs_new                         false
% 2.99/0.99  --inst_eq_res_simp                      false
% 2.99/0.99  --inst_subs_given                       false
% 2.99/0.99  --inst_orphan_elimination               true
% 2.99/0.99  --inst_learning_loop_flag               true
% 2.99/0.99  --inst_learning_start                   3000
% 2.99/0.99  --inst_learning_factor                  2
% 2.99/0.99  --inst_start_prop_sim_after_learn       3
% 2.99/0.99  --inst_sel_renew                        solver
% 2.99/0.99  --inst_lit_activity_flag                true
% 2.99/0.99  --inst_restr_to_given                   false
% 2.99/0.99  --inst_activity_threshold               500
% 2.99/0.99  --inst_out_proof                        true
% 2.99/0.99  
% 2.99/0.99  ------ Resolution Options
% 2.99/0.99  
% 2.99/0.99  --resolution_flag                       true
% 2.99/0.99  --res_lit_sel                           adaptive
% 2.99/0.99  --res_lit_sel_side                      none
% 2.99/0.99  --res_ordering                          kbo
% 2.99/0.99  --res_to_prop_solver                    active
% 2.99/0.99  --res_prop_simpl_new                    false
% 2.99/0.99  --res_prop_simpl_given                  true
% 2.99/0.99  --res_passive_queue_type                priority_queues
% 2.99/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.99/0.99  --res_passive_queues_freq               [15;5]
% 2.99/0.99  --res_forward_subs                      full
% 2.99/0.99  --res_backward_subs                     full
% 2.99/0.99  --res_forward_subs_resolution           true
% 2.99/0.99  --res_backward_subs_resolution          true
% 2.99/0.99  --res_orphan_elimination                true
% 2.99/0.99  --res_time_limit                        2.
% 2.99/0.99  --res_out_proof                         true
% 2.99/0.99  
% 2.99/0.99  ------ Superposition Options
% 2.99/0.99  
% 2.99/0.99  --superposition_flag                    true
% 2.99/0.99  --sup_passive_queue_type                priority_queues
% 2.99/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.99/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.99/0.99  --demod_completeness_check              fast
% 2.99/0.99  --demod_use_ground                      true
% 2.99/0.99  --sup_to_prop_solver                    passive
% 2.99/0.99  --sup_prop_simpl_new                    true
% 2.99/0.99  --sup_prop_simpl_given                  true
% 2.99/0.99  --sup_fun_splitting                     false
% 2.99/0.99  --sup_smt_interval                      50000
% 2.99/0.99  
% 2.99/0.99  ------ Superposition Simplification Setup
% 2.99/0.99  
% 2.99/0.99  --sup_indices_passive                   []
% 2.99/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.99/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.99/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.99/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.99/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.99/0.99  --sup_full_bw                           [BwDemod]
% 2.99/0.99  --sup_immed_triv                        [TrivRules]
% 2.99/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.99/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.99/0.99  --sup_immed_bw_main                     []
% 2.99/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.99/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.99/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.99/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.99/0.99  
% 2.99/0.99  ------ Combination Options
% 2.99/0.99  
% 2.99/0.99  --comb_res_mult                         3
% 2.99/0.99  --comb_sup_mult                         2
% 2.99/0.99  --comb_inst_mult                        10
% 2.99/0.99  
% 2.99/0.99  ------ Debug Options
% 2.99/0.99  
% 2.99/0.99  --dbg_backtrace                         false
% 2.99/0.99  --dbg_dump_prop_clauses                 false
% 2.99/0.99  --dbg_dump_prop_clauses_file            -
% 2.99/0.99  --dbg_out_stat                          false
% 2.99/0.99  ------ Parsing...
% 2.99/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.99/0.99  
% 2.99/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 2.99/0.99  
% 2.99/0.99  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.99/0.99  
% 2.99/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.99/0.99  ------ Proving...
% 2.99/0.99  ------ Problem Properties 
% 2.99/0.99  
% 2.99/0.99  
% 2.99/0.99  clauses                                 21
% 2.99/0.99  conjectures                             6
% 2.99/0.99  EPR                                     6
% 2.99/0.99  Horn                                    20
% 2.99/0.99  unary                                   9
% 2.99/0.99  binary                                  3
% 2.99/0.99  lits                                    67
% 2.99/0.99  lits eq                                 9
% 2.99/0.99  fd_pure                                 0
% 2.99/0.99  fd_pseudo                               0
% 2.99/0.99  fd_cond                                 1
% 2.99/0.99  fd_pseudo_cond                          1
% 2.99/0.99  AC symbols                              0
% 2.99/0.99  
% 2.99/0.99  ------ Schedule dynamic 5 is on 
% 2.99/0.99  
% 2.99/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.99/0.99  
% 2.99/0.99  
% 2.99/0.99  ------ 
% 2.99/0.99  Current options:
% 2.99/0.99  ------ 
% 2.99/0.99  
% 2.99/0.99  ------ Input Options
% 2.99/0.99  
% 2.99/0.99  --out_options                           all
% 2.99/0.99  --tptp_safe_out                         true
% 2.99/0.99  --problem_path                          ""
% 2.99/0.99  --include_path                          ""
% 2.99/0.99  --clausifier                            res/vclausify_rel
% 2.99/0.99  --clausifier_options                    --mode clausify
% 2.99/0.99  --stdin                                 false
% 2.99/0.99  --stats_out                             all
% 2.99/0.99  
% 2.99/0.99  ------ General Options
% 2.99/0.99  
% 2.99/0.99  --fof                                   false
% 2.99/0.99  --time_out_real                         305.
% 2.99/0.99  --time_out_virtual                      -1.
% 2.99/0.99  --symbol_type_check                     false
% 2.99/0.99  --clausify_out                          false
% 2.99/0.99  --sig_cnt_out                           false
% 2.99/0.99  --trig_cnt_out                          false
% 2.99/0.99  --trig_cnt_out_tolerance                1.
% 2.99/0.99  --trig_cnt_out_sk_spl                   false
% 2.99/0.99  --abstr_cl_out                          false
% 2.99/0.99  
% 2.99/0.99  ------ Global Options
% 2.99/0.99  
% 2.99/0.99  --schedule                              default
% 2.99/0.99  --add_important_lit                     false
% 2.99/0.99  --prop_solver_per_cl                    1000
% 2.99/0.99  --min_unsat_core                        false
% 2.99/0.99  --soft_assumptions                      false
% 2.99/0.99  --soft_lemma_size                       3
% 2.99/0.99  --prop_impl_unit_size                   0
% 2.99/0.99  --prop_impl_unit                        []
% 2.99/0.99  --share_sel_clauses                     true
% 2.99/0.99  --reset_solvers                         false
% 2.99/0.99  --bc_imp_inh                            [conj_cone]
% 2.99/0.99  --conj_cone_tolerance                   3.
% 2.99/0.99  --extra_neg_conj                        none
% 2.99/0.99  --large_theory_mode                     true
% 2.99/0.99  --prolific_symb_bound                   200
% 2.99/0.99  --lt_threshold                          2000
% 2.99/0.99  --clause_weak_htbl                      true
% 2.99/0.99  --gc_record_bc_elim                     false
% 2.99/0.99  
% 2.99/0.99  ------ Preprocessing Options
% 2.99/0.99  
% 2.99/0.99  --preprocessing_flag                    true
% 2.99/0.99  --time_out_prep_mult                    0.1
% 2.99/0.99  --splitting_mode                        input
% 2.99/0.99  --splitting_grd                         true
% 2.99/0.99  --splitting_cvd                         false
% 2.99/0.99  --splitting_cvd_svl                     false
% 2.99/0.99  --splitting_nvd                         32
% 2.99/0.99  --sub_typing                            true
% 2.99/0.99  --prep_gs_sim                           true
% 2.99/0.99  --prep_unflatten                        true
% 2.99/0.99  --prep_res_sim                          true
% 2.99/0.99  --prep_upred                            true
% 2.99/0.99  --prep_sem_filter                       exhaustive
% 2.99/0.99  --prep_sem_filter_out                   false
% 2.99/0.99  --pred_elim                             true
% 2.99/0.99  --res_sim_input                         true
% 2.99/0.99  --eq_ax_congr_red                       true
% 2.99/0.99  --pure_diseq_elim                       true
% 2.99/0.99  --brand_transform                       false
% 2.99/0.99  --non_eq_to_eq                          false
% 2.99/0.99  --prep_def_merge                        true
% 2.99/0.99  --prep_def_merge_prop_impl              false
% 2.99/0.99  --prep_def_merge_mbd                    true
% 2.99/0.99  --prep_def_merge_tr_red                 false
% 2.99/0.99  --prep_def_merge_tr_cl                  false
% 2.99/0.99  --smt_preprocessing                     true
% 2.99/0.99  --smt_ac_axioms                         fast
% 2.99/0.99  --preprocessed_out                      false
% 2.99/0.99  --preprocessed_stats                    false
% 2.99/0.99  
% 2.99/0.99  ------ Abstraction refinement Options
% 2.99/0.99  
% 2.99/0.99  --abstr_ref                             []
% 2.99/0.99  --abstr_ref_prep                        false
% 2.99/0.99  --abstr_ref_until_sat                   false
% 2.99/0.99  --abstr_ref_sig_restrict                funpre
% 2.99/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.99/0.99  --abstr_ref_under                       []
% 2.99/0.99  
% 2.99/0.99  ------ SAT Options
% 2.99/0.99  
% 2.99/0.99  --sat_mode                              false
% 2.99/0.99  --sat_fm_restart_options                ""
% 2.99/0.99  --sat_gr_def                            false
% 2.99/0.99  --sat_epr_types                         true
% 2.99/0.99  --sat_non_cyclic_types                  false
% 2.99/0.99  --sat_finite_models                     false
% 2.99/0.99  --sat_fm_lemmas                         false
% 2.99/0.99  --sat_fm_prep                           false
% 2.99/0.99  --sat_fm_uc_incr                        true
% 2.99/0.99  --sat_out_model                         small
% 2.99/0.99  --sat_out_clauses                       false
% 2.99/0.99  
% 2.99/0.99  ------ QBF Options
% 2.99/0.99  
% 2.99/0.99  --qbf_mode                              false
% 2.99/0.99  --qbf_elim_univ                         false
% 2.99/0.99  --qbf_dom_inst                          none
% 2.99/0.99  --qbf_dom_pre_inst                      false
% 2.99/0.99  --qbf_sk_in                             false
% 2.99/0.99  --qbf_pred_elim                         true
% 2.99/0.99  --qbf_split                             512
% 2.99/0.99  
% 2.99/0.99  ------ BMC1 Options
% 2.99/0.99  
% 2.99/0.99  --bmc1_incremental                      false
% 2.99/0.99  --bmc1_axioms                           reachable_all
% 2.99/0.99  --bmc1_min_bound                        0
% 2.99/0.99  --bmc1_max_bound                        -1
% 2.99/0.99  --bmc1_max_bound_default                -1
% 2.99/0.99  --bmc1_symbol_reachability              true
% 2.99/0.99  --bmc1_property_lemmas                  false
% 2.99/0.99  --bmc1_k_induction                      false
% 2.99/0.99  --bmc1_non_equiv_states                 false
% 2.99/0.99  --bmc1_deadlock                         false
% 2.99/0.99  --bmc1_ucm                              false
% 2.99/0.99  --bmc1_add_unsat_core                   none
% 2.99/0.99  --bmc1_unsat_core_children              false
% 2.99/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.99/0.99  --bmc1_out_stat                         full
% 2.99/0.99  --bmc1_ground_init                      false
% 2.99/0.99  --bmc1_pre_inst_next_state              false
% 2.99/0.99  --bmc1_pre_inst_state                   false
% 2.99/0.99  --bmc1_pre_inst_reach_state             false
% 2.99/0.99  --bmc1_out_unsat_core                   false
% 2.99/0.99  --bmc1_aig_witness_out                  false
% 2.99/0.99  --bmc1_verbose                          false
% 2.99/0.99  --bmc1_dump_clauses_tptp                false
% 2.99/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.99/0.99  --bmc1_dump_file                        -
% 2.99/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.99/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.99/0.99  --bmc1_ucm_extend_mode                  1
% 2.99/0.99  --bmc1_ucm_init_mode                    2
% 2.99/0.99  --bmc1_ucm_cone_mode                    none
% 2.99/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.99/0.99  --bmc1_ucm_relax_model                  4
% 2.99/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.99/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.99/0.99  --bmc1_ucm_layered_model                none
% 2.99/0.99  --bmc1_ucm_max_lemma_size               10
% 2.99/0.99  
% 2.99/0.99  ------ AIG Options
% 2.99/0.99  
% 2.99/0.99  --aig_mode                              false
% 2.99/0.99  
% 2.99/0.99  ------ Instantiation Options
% 2.99/0.99  
% 2.99/0.99  --instantiation_flag                    true
% 2.99/0.99  --inst_sos_flag                         false
% 2.99/0.99  --inst_sos_phase                        true
% 2.99/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.99/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.99/0.99  --inst_lit_sel_side                     none
% 2.99/0.99  --inst_solver_per_active                1400
% 2.99/0.99  --inst_solver_calls_frac                1.
% 2.99/0.99  --inst_passive_queue_type               priority_queues
% 2.99/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.99/0.99  --inst_passive_queues_freq              [25;2]
% 2.99/0.99  --inst_dismatching                      true
% 2.99/0.99  --inst_eager_unprocessed_to_passive     true
% 2.99/0.99  --inst_prop_sim_given                   true
% 2.99/0.99  --inst_prop_sim_new                     false
% 2.99/0.99  --inst_subs_new                         false
% 2.99/0.99  --inst_eq_res_simp                      false
% 2.99/0.99  --inst_subs_given                       false
% 2.99/0.99  --inst_orphan_elimination               true
% 2.99/0.99  --inst_learning_loop_flag               true
% 2.99/0.99  --inst_learning_start                   3000
% 2.99/0.99  --inst_learning_factor                  2
% 2.99/0.99  --inst_start_prop_sim_after_learn       3
% 2.99/0.99  --inst_sel_renew                        solver
% 2.99/0.99  --inst_lit_activity_flag                true
% 2.99/0.99  --inst_restr_to_given                   false
% 2.99/0.99  --inst_activity_threshold               500
% 2.99/0.99  --inst_out_proof                        true
% 2.99/0.99  
% 2.99/0.99  ------ Resolution Options
% 2.99/0.99  
% 2.99/0.99  --resolution_flag                       false
% 2.99/0.99  --res_lit_sel                           adaptive
% 2.99/0.99  --res_lit_sel_side                      none
% 2.99/0.99  --res_ordering                          kbo
% 2.99/0.99  --res_to_prop_solver                    active
% 2.99/0.99  --res_prop_simpl_new                    false
% 2.99/0.99  --res_prop_simpl_given                  true
% 2.99/0.99  --res_passive_queue_type                priority_queues
% 2.99/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.99/0.99  --res_passive_queues_freq               [15;5]
% 2.99/0.99  --res_forward_subs                      full
% 2.99/0.99  --res_backward_subs                     full
% 2.99/0.99  --res_forward_subs_resolution           true
% 2.99/0.99  --res_backward_subs_resolution          true
% 2.99/0.99  --res_orphan_elimination                true
% 2.99/0.99  --res_time_limit                        2.
% 2.99/0.99  --res_out_proof                         true
% 2.99/0.99  
% 2.99/0.99  ------ Superposition Options
% 2.99/0.99  
% 2.99/0.99  --superposition_flag                    true
% 2.99/0.99  --sup_passive_queue_type                priority_queues
% 2.99/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.99/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.99/0.99  --demod_completeness_check              fast
% 2.99/0.99  --demod_use_ground                      true
% 2.99/0.99  --sup_to_prop_solver                    passive
% 2.99/0.99  --sup_prop_simpl_new                    true
% 2.99/0.99  --sup_prop_simpl_given                  true
% 2.99/0.99  --sup_fun_splitting                     false
% 2.99/0.99  --sup_smt_interval                      50000
% 2.99/0.99  
% 2.99/0.99  ------ Superposition Simplification Setup
% 2.99/0.99  
% 2.99/0.99  --sup_indices_passive                   []
% 2.99/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.99/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.99/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.99/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.99/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.99/0.99  --sup_full_bw                           [BwDemod]
% 2.99/0.99  --sup_immed_triv                        [TrivRules]
% 2.99/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.99/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.99/0.99  --sup_immed_bw_main                     []
% 2.99/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.99/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.99/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.99/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.99/0.99  
% 2.99/0.99  ------ Combination Options
% 2.99/0.99  
% 2.99/0.99  --comb_res_mult                         3
% 2.99/0.99  --comb_sup_mult                         2
% 2.99/0.99  --comb_inst_mult                        10
% 2.99/0.99  
% 2.99/0.99  ------ Debug Options
% 2.99/0.99  
% 2.99/0.99  --dbg_backtrace                         false
% 2.99/0.99  --dbg_dump_prop_clauses                 false
% 2.99/0.99  --dbg_dump_prop_clauses_file            -
% 2.99/0.99  --dbg_out_stat                          false
% 2.99/0.99  
% 2.99/0.99  
% 2.99/0.99  
% 2.99/0.99  
% 2.99/0.99  ------ Proving...
% 2.99/0.99  
% 2.99/0.99  
% 2.99/0.99  % SZS status Theorem for theBenchmark.p
% 2.99/0.99  
% 2.99/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.99/0.99  
% 2.99/0.99  fof(f10,axiom,(
% 2.99/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 2.99/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.99/0.99  
% 2.99/0.99  fof(f28,plain,(
% 2.99/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.99/0.99    inference(ennf_transformation,[],[f10])).
% 2.99/0.99  
% 2.99/0.99  fof(f29,plain,(
% 2.99/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.99/0.99    inference(flattening,[],[f28])).
% 2.99/0.99  
% 2.99/0.99  fof(f54,plain,(
% 2.99/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.99/0.99    inference(cnf_transformation,[],[f29])).
% 2.99/0.99  
% 2.99/0.99  fof(f8,axiom,(
% 2.99/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.99/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.99/0.99  
% 2.99/0.99  fof(f24,plain,(
% 2.99/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.99/0.99    inference(ennf_transformation,[],[f8])).
% 2.99/0.99  
% 2.99/0.99  fof(f25,plain,(
% 2.99/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.99/0.99    inference(flattening,[],[f24])).
% 2.99/0.99  
% 2.99/0.99  fof(f36,plain,(
% 2.99/0.99    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.99/0.99    inference(nnf_transformation,[],[f25])).
% 2.99/0.99  
% 2.99/0.99  fof(f49,plain,(
% 2.99/0.99    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.99/0.99    inference(cnf_transformation,[],[f36])).
% 2.99/0.99  
% 2.99/0.99  fof(f15,conjecture,(
% 2.99/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 2.99/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.99/0.99  
% 2.99/0.99  fof(f16,negated_conjecture,(
% 2.99/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 2.99/0.99    inference(negated_conjecture,[],[f15])).
% 2.99/0.99  
% 2.99/0.99  fof(f34,plain,(
% 2.99/0.99    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.99/0.99    inference(ennf_transformation,[],[f16])).
% 2.99/0.99  
% 2.99/0.99  fof(f35,plain,(
% 2.99/0.99    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.99/0.99    inference(flattening,[],[f34])).
% 2.99/0.99  
% 2.99/0.99  fof(f39,plain,(
% 2.99/0.99    ( ! [X2,X0,X1] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((~v2_funct_2(sK3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 2.99/0.99    introduced(choice_axiom,[])).
% 2.99/0.99  
% 2.99/0.99  fof(f38,plain,(
% 2.99/0.99    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 2.99/0.99    introduced(choice_axiom,[])).
% 2.99/0.99  
% 2.99/0.99  fof(f40,plain,(
% 2.99/0.99    ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 2.99/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f35,f39,f38])).
% 2.99/0.99  
% 2.99/0.99  fof(f66,plain,(
% 2.99/0.99    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.99/0.99    inference(cnf_transformation,[],[f40])).
% 2.99/0.99  
% 2.99/0.99  fof(f11,axiom,(
% 2.99/0.99    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 2.99/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.99/0.99  
% 2.99/0.99  fof(f17,plain,(
% 2.99/0.99    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 2.99/0.99    inference(pure_predicate_removal,[],[f11])).
% 2.99/0.99  
% 2.99/0.99  fof(f55,plain,(
% 2.99/0.99    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.99/0.99    inference(cnf_transformation,[],[f17])).
% 2.99/0.99  
% 2.99/0.99  fof(f60,plain,(
% 2.99/0.99    v1_funct_1(sK2)),
% 2.99/0.99    inference(cnf_transformation,[],[f40])).
% 2.99/0.99  
% 2.99/0.99  fof(f62,plain,(
% 2.99/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.99/0.99    inference(cnf_transformation,[],[f40])).
% 2.99/0.99  
% 2.99/0.99  fof(f63,plain,(
% 2.99/0.99    v1_funct_1(sK3)),
% 2.99/0.99    inference(cnf_transformation,[],[f40])).
% 2.99/0.99  
% 2.99/0.99  fof(f65,plain,(
% 2.99/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.99/0.99    inference(cnf_transformation,[],[f40])).
% 2.99/0.99  
% 2.99/0.99  fof(f14,axiom,(
% 2.99/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 2.99/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.99/0.99  
% 2.99/0.99  fof(f32,plain,(
% 2.99/0.99    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.99/0.99    inference(ennf_transformation,[],[f14])).
% 2.99/0.99  
% 2.99/0.99  fof(f33,plain,(
% 2.99/0.99    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.99/0.99    inference(flattening,[],[f32])).
% 2.99/0.99  
% 2.99/0.99  fof(f58,plain,(
% 2.99/0.99    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X3) | k1_xboole_0 = X2 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.99/0.99    inference(cnf_transformation,[],[f33])).
% 2.99/0.99  
% 2.99/0.99  fof(f6,axiom,(
% 2.99/0.99    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 2.99/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.99/0.99  
% 2.99/0.99  fof(f22,plain,(
% 2.99/0.99    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 2.99/0.99    inference(ennf_transformation,[],[f6])).
% 2.99/0.99  
% 2.99/0.99  fof(f47,plain,(
% 2.99/0.99    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 2.99/0.99    inference(cnf_transformation,[],[f22])).
% 2.99/0.99  
% 2.99/0.99  fof(f13,axiom,(
% 2.99/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 2.99/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.99/0.99  
% 2.99/0.99  fof(f30,plain,(
% 2.99/0.99    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.99/0.99    inference(ennf_transformation,[],[f13])).
% 2.99/0.99  
% 2.99/0.99  fof(f31,plain,(
% 2.99/0.99    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.99/0.99    inference(flattening,[],[f30])).
% 2.99/0.99  
% 2.99/0.99  fof(f57,plain,(
% 2.99/0.99    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.99/0.99    inference(cnf_transformation,[],[f31])).
% 2.99/0.99  
% 2.99/0.99  fof(f7,axiom,(
% 2.99/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 2.99/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.99/0.99  
% 2.99/0.99  fof(f23,plain,(
% 2.99/0.99    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.99/0.99    inference(ennf_transformation,[],[f7])).
% 2.99/0.99  
% 2.99/0.99  fof(f48,plain,(
% 2.99/0.99    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.99/0.99    inference(cnf_transformation,[],[f23])).
% 2.99/0.99  
% 2.99/0.99  fof(f61,plain,(
% 2.99/0.99    v1_funct_2(sK2,sK0,sK1)),
% 2.99/0.99    inference(cnf_transformation,[],[f40])).
% 2.99/0.99  
% 2.99/0.99  fof(f64,plain,(
% 2.99/0.99    v1_funct_2(sK3,sK1,sK0)),
% 2.99/0.99    inference(cnf_transformation,[],[f40])).
% 2.99/0.99  
% 2.99/0.99  fof(f5,axiom,(
% 2.99/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.99/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.99/0.99  
% 2.99/0.99  fof(f18,plain,(
% 2.99/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 2.99/0.99    inference(pure_predicate_removal,[],[f5])).
% 2.99/0.99  
% 2.99/0.99  fof(f21,plain,(
% 2.99/0.99    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.99/0.99    inference(ennf_transformation,[],[f18])).
% 2.99/0.99  
% 2.99/0.99  fof(f46,plain,(
% 2.99/0.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.99/0.99    inference(cnf_transformation,[],[f21])).
% 2.99/0.99  
% 2.99/0.99  fof(f9,axiom,(
% 2.99/0.99    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 2.99/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.99/0.99  
% 2.99/0.99  fof(f26,plain,(
% 2.99/0.99    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.99/0.99    inference(ennf_transformation,[],[f9])).
% 2.99/0.99  
% 2.99/0.99  fof(f27,plain,(
% 2.99/0.99    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.99/0.99    inference(flattening,[],[f26])).
% 2.99/0.99  
% 2.99/0.99  fof(f37,plain,(
% 2.99/0.99    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.99/0.99    inference(nnf_transformation,[],[f27])).
% 2.99/0.99  
% 2.99/0.99  fof(f52,plain,(
% 2.99/0.99    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.99/0.99    inference(cnf_transformation,[],[f37])).
% 2.99/0.99  
% 2.99/0.99  fof(f71,plain,(
% 2.99/0.99    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.99/0.99    inference(equality_resolution,[],[f52])).
% 2.99/0.99  
% 2.99/0.99  fof(f4,axiom,(
% 2.99/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.99/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.99/0.99  
% 2.99/0.99  fof(f20,plain,(
% 2.99/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.99/0.99    inference(ennf_transformation,[],[f4])).
% 2.99/0.99  
% 2.99/0.99  fof(f45,plain,(
% 2.99/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.99/0.99    inference(cnf_transformation,[],[f20])).
% 2.99/0.99  
% 2.99/0.99  fof(f67,plain,(
% 2.99/0.99    ~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)),
% 2.99/0.99    inference(cnf_transformation,[],[f40])).
% 2.99/0.99  
% 2.99/0.99  fof(f2,axiom,(
% 2.99/0.99    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 2.99/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.99/0.99  
% 2.99/0.99  fof(f19,plain,(
% 2.99/0.99    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 2.99/0.99    inference(ennf_transformation,[],[f2])).
% 2.99/0.99  
% 2.99/0.99  fof(f42,plain,(
% 2.99/0.99    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 2.99/0.99    inference(cnf_transformation,[],[f19])).
% 2.99/0.99  
% 2.99/0.99  fof(f1,axiom,(
% 2.99/0.99    v1_xboole_0(k1_xboole_0)),
% 2.99/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.99/0.99  
% 2.99/0.99  fof(f41,plain,(
% 2.99/0.99    v1_xboole_0(k1_xboole_0)),
% 2.99/0.99    inference(cnf_transformation,[],[f1])).
% 2.99/0.99  
% 2.99/0.99  fof(f3,axiom,(
% 2.99/0.99    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.99/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.99/0.99  
% 2.99/0.99  fof(f44,plain,(
% 2.99/0.99    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 2.99/0.99    inference(cnf_transformation,[],[f3])).
% 2.99/0.99  
% 2.99/0.99  fof(f12,axiom,(
% 2.99/0.99    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.99/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.99/0.99  
% 2.99/0.99  fof(f56,plain,(
% 2.99/0.99    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.99/0.99    inference(cnf_transformation,[],[f12])).
% 2.99/0.99  
% 2.99/0.99  fof(f68,plain,(
% 2.99/0.99    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 2.99/0.99    inference(definition_unfolding,[],[f44,f56])).
% 2.99/0.99  
% 2.99/0.99  cnf(c_625,plain,
% 2.99/0.99      ( ~ v2_funct_1(X0_48) | v2_funct_1(X1_48) | X1_48 != X0_48 ),
% 2.99/0.99      theory(equality) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_3414,plain,
% 2.99/0.99      ( ~ v2_funct_1(X0_48) | v2_funct_1(sK2) | sK2 != X0_48 ),
% 2.99/0.99      inference(instantiation,[status(thm)],[c_625]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_3416,plain,
% 2.99/0.99      ( v2_funct_1(sK2) | ~ v2_funct_1(sK0) | sK2 != sK0 ),
% 2.99/0.99      inference(instantiation,[status(thm)],[c_3414]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_12,plain,
% 2.99/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.99/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 2.99/0.99      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 2.99/0.99      | ~ v1_funct_1(X0)
% 2.99/0.99      | ~ v1_funct_1(X3) ),
% 2.99/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_610,plain,
% 2.99/0.99      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
% 2.99/0.99      | ~ m1_subset_1(X3_48,k1_zfmisc_1(k2_zfmisc_1(X4_48,X5_48)))
% 2.99/0.99      | m1_subset_1(k1_partfun1(X4_48,X5_48,X1_48,X2_48,X3_48,X0_48),k1_zfmisc_1(k2_zfmisc_1(X4_48,X2_48)))
% 2.99/0.99      | ~ v1_funct_1(X0_48)
% 2.99/0.99      | ~ v1_funct_1(X3_48) ),
% 2.99/0.99      inference(subtyping,[status(esa)],[c_12]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1029,plain,
% 2.99/0.99      ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48))) != iProver_top
% 2.99/0.99      | m1_subset_1(X3_48,k1_zfmisc_1(k2_zfmisc_1(X4_48,X5_48))) != iProver_top
% 2.99/0.99      | m1_subset_1(k1_partfun1(X4_48,X5_48,X1_48,X2_48,X3_48,X0_48),k1_zfmisc_1(k2_zfmisc_1(X4_48,X2_48))) = iProver_top
% 2.99/0.99      | v1_funct_1(X0_48) != iProver_top
% 2.99/0.99      | v1_funct_1(X3_48) != iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_610]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_9,plain,
% 2.99/0.99      ( ~ r2_relset_1(X0,X1,X2,X3)
% 2.99/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.99/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.99/0.99      | X3 = X2 ),
% 2.99/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_19,negated_conjecture,
% 2.99/0.99      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 2.99/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_388,plain,
% 2.99/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.99/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.99/0.99      | X3 = X0
% 2.99/0.99      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 2.99/0.99      | k6_partfun1(sK0) != X3
% 2.99/0.99      | sK0 != X2
% 2.99/0.99      | sK0 != X1 ),
% 2.99/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_19]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_389,plain,
% 2.99/0.99      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.99/0.99      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.99/0.99      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 2.99/0.99      inference(unflattening,[status(thm)],[c_388]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_14,plain,
% 2.99/0.99      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 2.99/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_44,plain,
% 2.99/0.99      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 2.99/0.99      inference(instantiation,[status(thm)],[c_14]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_391,plain,
% 2.99/0.99      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.99/0.99      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 2.99/0.99      inference(global_propositional_subsumption,
% 2.99/0.99                [status(thm)],
% 2.99/0.99                [c_389,c_44]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_597,plain,
% 2.99/0.99      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.99/0.99      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 2.99/0.99      inference(subtyping,[status(esa)],[c_391]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1043,plain,
% 2.99/0.99      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 2.99/0.99      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_597]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_2121,plain,
% 2.99/0.99      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
% 2.99/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.99/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.99/0.99      | v1_funct_1(sK2) != iProver_top
% 2.99/0.99      | v1_funct_1(sK3) != iProver_top ),
% 2.99/0.99      inference(superposition,[status(thm)],[c_1029,c_1043]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_25,negated_conjecture,
% 2.99/0.99      ( v1_funct_1(sK2) ),
% 2.99/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_26,plain,
% 2.99/0.99      ( v1_funct_1(sK2) = iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_23,negated_conjecture,
% 2.99/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.99/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_28,plain,
% 2.99/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_22,negated_conjecture,
% 2.99/0.99      ( v1_funct_1(sK3) ),
% 2.99/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_29,plain,
% 2.99/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_20,negated_conjecture,
% 2.99/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 2.99/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_31,plain,
% 2.99/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_2370,plain,
% 2.99/0.99      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
% 2.99/0.99      inference(global_propositional_subsumption,
% 2.99/0.99                [status(thm)],
% 2.99/0.99                [c_2121,c_26,c_28,c_29,c_31]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_17,plain,
% 2.99/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.99/0.99      | ~ v1_funct_2(X3,X2,X4)
% 2.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.99/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
% 2.99/0.99      | ~ v1_funct_1(X3)
% 2.99/0.99      | ~ v1_funct_1(X0)
% 2.99/0.99      | v2_funct_1(X0)
% 2.99/0.99      | ~ v2_funct_1(k1_partfun1(X1,X2,X2,X4,X0,X3))
% 2.99/0.99      | k1_xboole_0 = X4 ),
% 2.99/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_606,plain,
% 2.99/0.99      ( ~ v1_funct_2(X0_48,X1_48,X2_48)
% 2.99/0.99      | ~ v1_funct_2(X3_48,X2_48,X4_48)
% 2.99/0.99      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
% 2.99/0.99      | ~ m1_subset_1(X3_48,k1_zfmisc_1(k2_zfmisc_1(X2_48,X4_48)))
% 2.99/0.99      | ~ v1_funct_1(X0_48)
% 2.99/0.99      | ~ v1_funct_1(X3_48)
% 2.99/0.99      | v2_funct_1(X0_48)
% 2.99/0.99      | ~ v2_funct_1(k1_partfun1(X1_48,X2_48,X2_48,X4_48,X0_48,X3_48))
% 2.99/0.99      | k1_xboole_0 = X4_48 ),
% 2.99/0.99      inference(subtyping,[status(esa)],[c_17]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1033,plain,
% 2.99/0.99      ( k1_xboole_0 = X0_48
% 2.99/0.99      | v1_funct_2(X1_48,X2_48,X3_48) != iProver_top
% 2.99/0.99      | v1_funct_2(X4_48,X3_48,X0_48) != iProver_top
% 2.99/0.99      | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_48,X3_48))) != iProver_top
% 2.99/0.99      | m1_subset_1(X4_48,k1_zfmisc_1(k2_zfmisc_1(X3_48,X0_48))) != iProver_top
% 2.99/0.99      | v1_funct_1(X1_48) != iProver_top
% 2.99/0.99      | v1_funct_1(X4_48) != iProver_top
% 2.99/0.99      | v2_funct_1(X1_48) = iProver_top
% 2.99/0.99      | v2_funct_1(k1_partfun1(X2_48,X3_48,X3_48,X0_48,X1_48,X4_48)) != iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_606]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_2396,plain,
% 2.99/0.99      ( sK0 = k1_xboole_0
% 2.99/0.99      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 2.99/0.99      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 2.99/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.99/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.99/0.99      | v1_funct_1(sK2) != iProver_top
% 2.99/0.99      | v1_funct_1(sK3) != iProver_top
% 2.99/0.99      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 2.99/0.99      | v2_funct_1(sK2) = iProver_top ),
% 2.99/0.99      inference(superposition,[status(thm)],[c_2370,c_1033]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_608,plain,
% 2.99/0.99      ( m1_subset_1(k6_partfun1(X0_48),k1_zfmisc_1(k2_zfmisc_1(X0_48,X0_48))) ),
% 2.99/0.99      inference(subtyping,[status(esa)],[c_14]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1031,plain,
% 2.99/0.99      ( m1_subset_1(k6_partfun1(X0_48),k1_zfmisc_1(k2_zfmisc_1(X0_48,X0_48))) = iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_608]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_6,plain,
% 2.99/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.99/0.99      | ~ v1_xboole_0(X1)
% 2.99/0.99      | v1_xboole_0(X0) ),
% 2.99/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_612,plain,
% 2.99/0.99      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
% 2.99/0.99      | ~ v1_xboole_0(X1_48)
% 2.99/0.99      | v1_xboole_0(X0_48) ),
% 2.99/0.99      inference(subtyping,[status(esa)],[c_6]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1027,plain,
% 2.99/0.99      ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48))) != iProver_top
% 2.99/0.99      | v1_xboole_0(X1_48) != iProver_top
% 2.99/0.99      | v1_xboole_0(X0_48) = iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_612]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_2051,plain,
% 2.99/0.99      ( v1_xboole_0(X0_48) != iProver_top
% 2.99/0.99      | v1_xboole_0(k6_partfun1(X0_48)) = iProver_top ),
% 2.99/0.99      inference(superposition,[status(thm)],[c_1031,c_1027]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_2066,plain,
% 2.99/0.99      ( ~ v1_xboole_0(X0_48) | v1_xboole_0(k6_partfun1(X0_48)) ),
% 2.99/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_2051]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_2068,plain,
% 2.99/0.99      ( v1_xboole_0(k6_partfun1(sK0)) | ~ v1_xboole_0(sK0) ),
% 2.99/0.99      inference(instantiation,[status(thm)],[c_2066]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_602,negated_conjecture,
% 2.99/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.99/0.99      inference(subtyping,[status(esa)],[c_23]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1037,plain,
% 2.99/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_602]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_2050,plain,
% 2.99/0.99      ( v1_xboole_0(sK2) = iProver_top
% 2.99/0.99      | v1_xboole_0(sK0) != iProver_top ),
% 2.99/0.99      inference(superposition,[status(thm)],[c_1037,c_1027]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_2065,plain,
% 2.99/0.99      ( v1_xboole_0(sK2) | ~ v1_xboole_0(sK0) ),
% 2.99/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_2050]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_605,negated_conjecture,
% 2.99/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 2.99/0.99      inference(subtyping,[status(esa)],[c_20]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1034,plain,
% 2.99/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_605]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_15,plain,
% 2.99/0.99      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 2.99/0.99      | ~ v1_funct_2(X2,X0,X1)
% 2.99/0.99      | ~ v1_funct_2(X3,X1,X0)
% 2.99/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.99/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.99/0.99      | ~ v1_funct_1(X2)
% 2.99/0.99      | ~ v1_funct_1(X3)
% 2.99/0.99      | k2_relset_1(X1,X0,X3) = X0 ),
% 2.99/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_402,plain,
% 2.99/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.99/0.99      | ~ v1_funct_2(X3,X2,X1)
% 2.99/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.99/0.99      | ~ v1_funct_1(X3)
% 2.99/0.99      | ~ v1_funct_1(X0)
% 2.99/0.99      | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 2.99/0.99      | k2_relset_1(X2,X1,X3) = X1
% 2.99/0.99      | k6_partfun1(X1) != k6_partfun1(sK0)
% 2.99/0.99      | sK0 != X1 ),
% 2.99/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_19]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_403,plain,
% 2.99/0.99      ( ~ v1_funct_2(X0,X1,sK0)
% 2.99/0.99      | ~ v1_funct_2(X2,sK0,X1)
% 2.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 2.99/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 2.99/0.99      | ~ v1_funct_1(X2)
% 2.99/0.99      | ~ v1_funct_1(X0)
% 2.99/0.99      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 2.99/0.99      | k2_relset_1(X1,sK0,X0) = sK0
% 2.99/0.99      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 2.99/0.99      inference(unflattening,[status(thm)],[c_402]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_477,plain,
% 2.99/0.99      ( ~ v1_funct_2(X0,X1,sK0)
% 2.99/0.99      | ~ v1_funct_2(X2,sK0,X1)
% 2.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 2.99/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 2.99/0.99      | ~ v1_funct_1(X0)
% 2.99/0.99      | ~ v1_funct_1(X2)
% 2.99/0.99      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 2.99/0.99      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 2.99/0.99      inference(equality_resolution_simp,[status(thm)],[c_403]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_596,plain,
% 2.99/0.99      ( ~ v1_funct_2(X0_48,X1_48,sK0)
% 2.99/0.99      | ~ v1_funct_2(X2_48,sK0,X1_48)
% 2.99/0.99      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,sK0)))
% 2.99/0.99      | ~ m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(sK0,X1_48)))
% 2.99/0.99      | ~ v1_funct_1(X0_48)
% 2.99/0.99      | ~ v1_funct_1(X2_48)
% 2.99/0.99      | k1_partfun1(sK0,X1_48,X1_48,sK0,X2_48,X0_48) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 2.99/0.99      | k2_relset_1(X1_48,sK0,X0_48) = sK0 ),
% 2.99/0.99      inference(subtyping,[status(esa)],[c_477]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1044,plain,
% 2.99/0.99      ( k1_partfun1(sK0,X0_48,X0_48,sK0,X1_48,X2_48) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 2.99/0.99      | k2_relset_1(X0_48,sK0,X2_48) = sK0
% 2.99/0.99      | v1_funct_2(X2_48,X0_48,sK0) != iProver_top
% 2.99/0.99      | v1_funct_2(X1_48,sK0,X0_48) != iProver_top
% 2.99/0.99      | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,sK0))) != iProver_top
% 2.99/0.99      | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_48))) != iProver_top
% 2.99/0.99      | v1_funct_1(X2_48) != iProver_top
% 2.99/0.99      | v1_funct_1(X1_48) != iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_596]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1930,plain,
% 2.99/0.99      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 2.99/0.99      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 2.99/0.99      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 2.99/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.99/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.99/0.99      | v1_funct_1(sK2) != iProver_top
% 2.99/0.99      | v1_funct_1(sK3) != iProver_top ),
% 2.99/0.99      inference(equality_resolution,[status(thm)],[c_1044]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_7,plain,
% 2.99/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.99/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.99/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_611,plain,
% 2.99/0.99      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
% 2.99/0.99      | k2_relset_1(X1_48,X2_48,X0_48) = k2_relat_1(X0_48) ),
% 2.99/0.99      inference(subtyping,[status(esa)],[c_7]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1028,plain,
% 2.99/0.99      ( k2_relset_1(X0_48,X1_48,X2_48) = k2_relat_1(X2_48)
% 2.99/0.99      | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_611]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1613,plain,
% 2.99/0.99      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 2.99/0.99      inference(superposition,[status(thm)],[c_1034,c_1028]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1931,plain,
% 2.99/0.99      ( k2_relat_1(sK3) = sK0
% 2.99/0.99      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 2.99/0.99      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 2.99/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.99/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.99/0.99      | v1_funct_1(sK2) != iProver_top
% 2.99/0.99      | v1_funct_1(sK3) != iProver_top ),
% 2.99/0.99      inference(demodulation,[status(thm)],[c_1930,c_1613]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_24,negated_conjecture,
% 2.99/0.99      ( v1_funct_2(sK2,sK0,sK1) ),
% 2.99/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_27,plain,
% 2.99/0.99      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_21,negated_conjecture,
% 2.99/0.99      ( v1_funct_2(sK3,sK1,sK0) ),
% 2.99/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_30,plain,
% 2.99/0.99      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1934,plain,
% 2.99/0.99      ( k2_relat_1(sK3) = sK0 ),
% 2.99/0.99      inference(global_propositional_subsumption,
% 2.99/0.99                [status(thm)],
% 2.99/0.99                [c_1931,c_26,c_27,c_28,c_29,c_30,c_31]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_5,plain,
% 2.99/0.99      ( v5_relat_1(X0,X1)
% 2.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.99/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_10,plain,
% 2.99/0.99      ( v2_funct_2(X0,k2_relat_1(X0))
% 2.99/0.99      | ~ v5_relat_1(X0,k2_relat_1(X0))
% 2.99/0.99      | ~ v1_relat_1(X0) ),
% 2.99/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_306,plain,
% 2.99/0.99      ( v2_funct_2(X0,k2_relat_1(X0))
% 2.99/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 2.99/0.99      | ~ v1_relat_1(X0)
% 2.99/0.99      | X0 != X1
% 2.99/0.99      | k2_relat_1(X0) != X3 ),
% 2.99/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_10]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_307,plain,
% 2.99/0.99      ( v2_funct_2(X0,k2_relat_1(X0))
% 2.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
% 2.99/0.99      | ~ v1_relat_1(X0) ),
% 2.99/0.99      inference(unflattening,[status(thm)],[c_306]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_4,plain,
% 2.99/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.99/0.99      | v1_relat_1(X0) ),
% 2.99/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_317,plain,
% 2.99/0.99      ( v2_funct_2(X0,k2_relat_1(X0))
% 2.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0)))) ),
% 2.99/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_307,c_4]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_18,negated_conjecture,
% 2.99/0.99      ( ~ v2_funct_2(sK3,sK0) | ~ v2_funct_1(sK2) ),
% 2.99/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_332,plain,
% 2.99/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
% 2.99/0.99      | ~ v2_funct_1(sK2)
% 2.99/0.99      | k2_relat_1(X0) != sK0
% 2.99/0.99      | sK3 != X0 ),
% 2.99/0.99      inference(resolution_lifted,[status(thm)],[c_317,c_18]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_333,plain,
% 2.99/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3))))
% 2.99/0.99      | ~ v2_funct_1(sK2)
% 2.99/0.99      | k2_relat_1(sK3) != sK0 ),
% 2.99/0.99      inference(unflattening,[status(thm)],[c_332]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_599,plain,
% 2.99/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_48,k2_relat_1(sK3))))
% 2.99/0.99      | ~ v2_funct_1(sK2)
% 2.99/0.99      | k2_relat_1(sK3) != sK0 ),
% 2.99/0.99      inference(subtyping,[status(esa)],[c_333]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_616,plain,
% 2.99/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_48,k2_relat_1(sK3))))
% 2.99/0.99      | ~ sP0_iProver_split ),
% 2.99/0.99      inference(splitting,
% 2.99/0.99                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.99/0.99                [c_599]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1041,plain,
% 2.99/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_48,k2_relat_1(sK3)))) != iProver_top
% 2.99/0.99      | sP0_iProver_split != iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_616]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1938,plain,
% 2.99/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_48,sK0))) != iProver_top
% 2.99/0.99      | sP0_iProver_split != iProver_top ),
% 2.99/0.99      inference(demodulation,[status(thm)],[c_1934,c_1041]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_2007,plain,
% 2.99/0.99      ( sP0_iProver_split != iProver_top ),
% 2.99/0.99      inference(superposition,[status(thm)],[c_1034,c_1938]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_2008,plain,
% 2.99/0.99      ( ~ sP0_iProver_split ),
% 2.99/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_2007]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_617,plain,
% 2.99/0.99      ( ~ v2_funct_1(sK2) | sP0_iProver_split | k2_relat_1(sK3) != sK0 ),
% 2.99/0.99      inference(splitting,
% 2.99/0.99                [splitting(split),new_symbols(definition,[])],
% 2.99/0.99                [c_599]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1040,plain,
% 2.99/0.99      ( k2_relat_1(sK3) != sK0
% 2.99/0.99      | v2_funct_1(sK2) != iProver_top
% 2.99/0.99      | sP0_iProver_split = iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_617]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1939,plain,
% 2.99/0.99      ( sK0 != sK0
% 2.99/0.99      | v2_funct_1(sK2) != iProver_top
% 2.99/0.99      | sP0_iProver_split = iProver_top ),
% 2.99/0.99      inference(demodulation,[status(thm)],[c_1934,c_1040]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1940,plain,
% 2.99/0.99      ( v2_funct_1(sK2) != iProver_top
% 2.99/0.99      | sP0_iProver_split = iProver_top ),
% 2.99/0.99      inference(equality_resolution_simp,[status(thm)],[c_1939]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1,plain,
% 2.99/0.99      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X1 = X0 ),
% 2.99/0.99      inference(cnf_transformation,[],[f42]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_614,plain,
% 2.99/0.99      ( ~ v1_xboole_0(X0_48) | ~ v1_xboole_0(X1_48) | X1_48 = X0_48 ),
% 2.99/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1624,plain,
% 2.99/0.99      ( ~ v1_xboole_0(X0_48) | ~ v1_xboole_0(sK2) | sK2 = X0_48 ),
% 2.99/0.99      inference(instantiation,[status(thm)],[c_614]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1626,plain,
% 2.99/0.99      ( ~ v1_xboole_0(sK2) | ~ v1_xboole_0(sK0) | sK2 = sK0 ),
% 2.99/0.99      inference(instantiation,[status(thm)],[c_1624]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1495,plain,
% 2.99/0.99      ( ~ v1_xboole_0(X0_48)
% 2.99/0.99      | ~ v1_xboole_0(k6_partfun1(X1_48))
% 2.99/0.99      | X0_48 = k6_partfun1(X1_48) ),
% 2.99/0.99      inference(instantiation,[status(thm)],[c_614]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1497,plain,
% 2.99/0.99      ( ~ v1_xboole_0(k6_partfun1(sK0))
% 2.99/0.99      | ~ v1_xboole_0(sK0)
% 2.99/0.99      | sK0 = k6_partfun1(sK0) ),
% 2.99/0.99      inference(instantiation,[status(thm)],[c_1495]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_623,plain,
% 2.99/0.99      ( ~ v1_xboole_0(X0_48) | v1_xboole_0(X1_48) | X1_48 != X0_48 ),
% 2.99/0.99      theory(equality) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1354,plain,
% 2.99/0.99      ( v1_xboole_0(X0_48)
% 2.99/0.99      | ~ v1_xboole_0(k1_xboole_0)
% 2.99/0.99      | X0_48 != k1_xboole_0 ),
% 2.99/0.99      inference(instantiation,[status(thm)],[c_623]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1356,plain,
% 2.99/0.99      ( v1_xboole_0(sK0)
% 2.99/0.99      | ~ v1_xboole_0(k1_xboole_0)
% 2.99/0.99      | sK0 != k1_xboole_0 ),
% 2.99/0.99      inference(instantiation,[status(thm)],[c_1354]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1240,plain,
% 2.99/0.99      ( v2_funct_1(X0_48)
% 2.99/0.99      | ~ v2_funct_1(k6_partfun1(X1_48))
% 2.99/0.99      | X0_48 != k6_partfun1(X1_48) ),
% 2.99/0.99      inference(instantiation,[status(thm)],[c_625]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_1242,plain,
% 2.99/0.99      ( ~ v2_funct_1(k6_partfun1(sK0))
% 2.99/0.99      | v2_funct_1(sK0)
% 2.99/0.99      | sK0 != k6_partfun1(sK0) ),
% 2.99/0.99      inference(instantiation,[status(thm)],[c_1240]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_0,plain,
% 2.99/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 2.99/0.99      inference(cnf_transformation,[],[f41]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_2,plain,
% 2.99/0.99      ( v2_funct_1(k6_partfun1(X0)) ),
% 2.99/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_77,plain,
% 2.99/0.99      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 2.99/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_79,plain,
% 2.99/0.99      ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
% 2.99/0.99      inference(instantiation,[status(thm)],[c_77]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(c_78,plain,
% 2.99/0.99      ( v2_funct_1(k6_partfun1(sK0)) ),
% 2.99/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 2.99/0.99  
% 2.99/0.99  cnf(contradiction,plain,
% 2.99/0.99      ( $false ),
% 2.99/0.99      inference(minisat,
% 2.99/0.99                [status(thm)],
% 2.99/0.99                [c_3416,c_2396,c_2068,c_2065,c_2008,c_2007,c_1940,c_1931,
% 2.99/0.99                 c_1626,c_1497,c_1356,c_1242,c_617,c_0,c_79,c_78,c_31,
% 2.99/0.99                 c_30,c_29,c_28,c_27,c_26]) ).
% 2.99/0.99  
% 2.99/0.99  
% 2.99/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.99/0.99  
% 2.99/0.99  ------                               Statistics
% 2.99/0.99  
% 2.99/0.99  ------ General
% 2.99/0.99  
% 2.99/0.99  abstr_ref_over_cycles:                  0
% 2.99/0.99  abstr_ref_under_cycles:                 0
% 2.99/0.99  gc_basic_clause_elim:                   0
% 2.99/0.99  forced_gc_time:                         0
% 2.99/0.99  parsing_time:                           0.01
% 2.99/0.99  unif_index_cands_time:                  0.
% 2.99/0.99  unif_index_add_time:                    0.
% 2.99/0.99  orderings_time:                         0.
% 2.99/0.99  out_proof_time:                         0.01
% 2.99/0.99  total_time:                             0.178
% 2.99/0.99  num_of_symbols:                         52
% 2.99/0.99  num_of_terms:                           6481
% 2.99/0.99  
% 2.99/0.99  ------ Preprocessing
% 2.99/0.99  
% 2.99/0.99  num_of_splits:                          1
% 2.99/0.99  num_of_split_atoms:                     1
% 2.99/0.99  num_of_reused_defs:                     0
% 2.99/0.99  num_eq_ax_congr_red:                    9
% 2.99/0.99  num_of_sem_filtered_clauses:            1
% 2.99/0.99  num_of_subtypes:                        3
% 2.99/0.99  monotx_restored_types:                  1
% 2.99/0.99  sat_num_of_epr_types:                   0
% 2.99/0.99  sat_num_of_non_cyclic_types:            0
% 2.99/0.99  sat_guarded_non_collapsed_types:        1
% 2.99/0.99  num_pure_diseq_elim:                    0
% 2.99/0.99  simp_replaced_by:                       0
% 2.99/0.99  res_preprocessed:                       119
% 2.99/0.99  prep_upred:                             0
% 2.99/0.99  prep_unflattend:                        17
% 2.99/0.99  smt_new_axioms:                         0
% 2.99/0.99  pred_elim_cands:                        5
% 2.99/0.99  pred_elim:                              4
% 2.99/0.99  pred_elim_cl:                           6
% 2.99/0.99  pred_elim_cycles:                       6
% 2.99/0.99  merged_defs:                            0
% 2.99/0.99  merged_defs_ncl:                        0
% 2.99/0.99  bin_hyper_res:                          0
% 2.99/0.99  prep_cycles:                            4
% 2.99/0.99  pred_elim_time:                         0.005
% 2.99/0.99  splitting_time:                         0.
% 2.99/0.99  sem_filter_time:                        0.
% 2.99/0.99  monotx_time:                            0.
% 2.99/0.99  subtype_inf_time:                       0.001
% 2.99/0.99  
% 2.99/0.99  ------ Problem properties
% 2.99/0.99  
% 2.99/0.99  clauses:                                21
% 2.99/0.99  conjectures:                            6
% 2.99/0.99  epr:                                    6
% 2.99/0.99  horn:                                   20
% 2.99/0.99  ground:                                 9
% 2.99/0.99  unary:                                  9
% 2.99/0.99  binary:                                 3
% 2.99/0.99  lits:                                   67
% 2.99/0.99  lits_eq:                                9
% 2.99/0.99  fd_pure:                                0
% 2.99/0.99  fd_pseudo:                              0
% 2.99/0.99  fd_cond:                                1
% 2.99/0.99  fd_pseudo_cond:                         1
% 2.99/0.99  ac_symbols:                             0
% 2.99/0.99  
% 2.99/0.99  ------ Propositional Solver
% 2.99/0.99  
% 2.99/0.99  prop_solver_calls:                      26
% 2.99/0.99  prop_fast_solver_calls:                 882
% 2.99/0.99  smt_solver_calls:                       0
% 2.99/0.99  smt_fast_solver_calls:                  0
% 2.99/0.99  prop_num_of_clauses:                    1417
% 2.99/0.99  prop_preprocess_simplified:             4531
% 2.99/0.99  prop_fo_subsumed:                       25
% 2.99/0.99  prop_solver_time:                       0.
% 2.99/0.99  smt_solver_time:                        0.
% 2.99/0.99  smt_fast_solver_time:                   0.
% 2.99/0.99  prop_fast_solver_time:                  0.
% 2.99/0.99  prop_unsat_core_time:                   0.
% 2.99/0.99  
% 2.99/0.99  ------ QBF
% 2.99/0.99  
% 2.99/0.99  qbf_q_res:                              0
% 2.99/0.99  qbf_num_tautologies:                    0
% 2.99/0.99  qbf_prep_cycles:                        0
% 2.99/0.99  
% 2.99/0.99  ------ BMC1
% 2.99/0.99  
% 2.99/0.99  bmc1_current_bound:                     -1
% 2.99/0.99  bmc1_last_solved_bound:                 -1
% 2.99/0.99  bmc1_unsat_core_size:                   -1
% 2.99/0.99  bmc1_unsat_core_parents_size:           -1
% 2.99/0.99  bmc1_merge_next_fun:                    0
% 2.99/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.99/0.99  
% 2.99/0.99  ------ Instantiation
% 2.99/0.99  
% 2.99/0.99  inst_num_of_clauses:                    366
% 2.99/0.99  inst_num_in_passive:                    124
% 2.99/0.99  inst_num_in_active:                     199
% 2.99/0.99  inst_num_in_unprocessed:                42
% 2.99/0.99  inst_num_of_loops:                      245
% 2.99/0.99  inst_num_of_learning_restarts:          0
% 2.99/0.99  inst_num_moves_active_passive:          42
% 2.99/0.99  inst_lit_activity:                      0
% 2.99/0.99  inst_lit_activity_moves:                0
% 2.99/0.99  inst_num_tautologies:                   0
% 2.99/0.99  inst_num_prop_implied:                  0
% 2.99/0.99  inst_num_existing_simplified:           0
% 2.99/0.99  inst_num_eq_res_simplified:             0
% 2.99/0.99  inst_num_child_elim:                    0
% 2.99/0.99  inst_num_of_dismatching_blockings:      6
% 2.99/0.99  inst_num_of_non_proper_insts:           257
% 2.99/0.99  inst_num_of_duplicates:                 0
% 2.99/0.99  inst_inst_num_from_inst_to_res:         0
% 2.99/0.99  inst_dismatching_checking_time:         0.
% 2.99/0.99  
% 2.99/0.99  ------ Resolution
% 2.99/0.99  
% 2.99/0.99  res_num_of_clauses:                     0
% 2.99/0.99  res_num_in_passive:                     0
% 2.99/0.99  res_num_in_active:                      0
% 2.99/0.99  res_num_of_loops:                       123
% 2.99/0.99  res_forward_subset_subsumed:            17
% 2.99/0.99  res_backward_subset_subsumed:           0
% 2.99/0.99  res_forward_subsumed:                   0
% 2.99/0.99  res_backward_subsumed:                  0
% 2.99/0.99  res_forward_subsumption_resolution:     3
% 2.99/0.99  res_backward_subsumption_resolution:    0
% 2.99/0.99  res_clause_to_clause_subsumption:       64
% 2.99/0.99  res_orphan_elimination:                 0
% 2.99/0.99  res_tautology_del:                      12
% 2.99/0.99  res_num_eq_res_simplified:              1
% 2.99/0.99  res_num_sel_changes:                    0
% 2.99/0.99  res_moves_from_active_to_pass:          0
% 2.99/0.99  
% 2.99/0.99  ------ Superposition
% 2.99/0.99  
% 2.99/0.99  sup_time_total:                         0.
% 2.99/0.99  sup_time_generating:                    0.
% 2.99/0.99  sup_time_sim_full:                      0.
% 2.99/0.99  sup_time_sim_immed:                     0.
% 2.99/0.99  
% 2.99/0.99  sup_num_of_clauses:                     33
% 2.99/0.99  sup_num_in_active:                      22
% 2.99/0.99  sup_num_in_passive:                     11
% 2.99/0.99  sup_num_of_loops:                       48
% 2.99/0.99  sup_fw_superposition:                   11
% 2.99/0.99  sup_bw_superposition:                   15
% 2.99/0.99  sup_immediate_simplified:               6
% 2.99/0.99  sup_given_eliminated:                   1
% 2.99/0.99  comparisons_done:                       0
% 2.99/0.99  comparisons_avoided:                    0
% 2.99/0.99  
% 2.99/0.99  ------ Simplifications
% 2.99/0.99  
% 2.99/0.99  
% 2.99/0.99  sim_fw_subset_subsumed:                 3
% 2.99/0.99  sim_bw_subset_subsumed:                 0
% 2.99/0.99  sim_fw_subsumed:                        2
% 2.99/0.99  sim_bw_subsumed:                        0
% 2.99/0.99  sim_fw_subsumption_res:                 0
% 2.99/0.99  sim_bw_subsumption_res:                 0
% 2.99/0.99  sim_tautology_del:                      0
% 2.99/0.99  sim_eq_tautology_del:                   4
% 2.99/0.99  sim_eq_res_simp:                        1
% 2.99/0.99  sim_fw_demodulated:                     1
% 2.99/0.99  sim_bw_demodulated:                     26
% 2.99/0.99  sim_light_normalised:                   0
% 2.99/0.99  sim_joinable_taut:                      0
% 2.99/0.99  sim_joinable_simp:                      0
% 2.99/0.99  sim_ac_normalised:                      0
% 2.99/0.99  sim_smt_subsumption:                    0
% 2.99/0.99  
%------------------------------------------------------------------------------

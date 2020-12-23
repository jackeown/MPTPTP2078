%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:01:51 EST 2020

% Result     : Theorem 2.67s
% Output     : CNFRefutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :  167 ( 781 expanded)
%              Number of clauses        :   96 ( 242 expanded)
%              Number of leaves         :   21 ( 193 expanded)
%              Depth                    :   21
%              Number of atoms          :  548 (4896 expanded)
%              Number of equality atoms :  194 ( 414 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
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
    inference(ennf_transformation,[],[f12])).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f28])).

fof(f59,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f24])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f16,conjecture,(
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

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

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
    inference(ennf_transformation,[],[f17])).

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

fof(f41,plain,(
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

fof(f40,plain,
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

fof(f42,plain,
    ( ( ~ v2_funct_2(sK3,sK0)
      | ~ v2_funct_1(sK2) )
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f35,f41,f40])).

fof(f70,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f42])).

fof(f10,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f13,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f73,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f55,f60])).

fof(f64,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f66,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f42])).

fof(f67,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f69,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f42])).

fof(f15,axiom,(
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
    inference(ennf_transformation,[],[f15])).

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

fof(f62,plain,(
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

fof(f65,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f68,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f14,axiom,(
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
    inference(ennf_transformation,[],[f14])).

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

fof(f61,plain,(
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
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f11,axiom,(
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
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f77,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f57])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f71,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f5,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f72,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f49,f60])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f36])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f75,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f46])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f74,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f47])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f44,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1040,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_11,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_21,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_420,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_21])).

cnf(c_421,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_420])).

cnf(c_12,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_429,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_421,c_12])).

cnf(c_1027,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_429])).

cnf(c_2637,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1040,c_1027])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_28,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_30,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_31,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_33,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3259,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2637,c_28,c_30,c_31,c_33])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v2_funct_1(X3)
    | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1037,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | v1_funct_2(X3,X4,X2) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v2_funct_1(X3) = iProver_top
    | v2_funct_1(k1_partfun1(X4,X2,X2,X0,X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3286,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3259,c_1037])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_29,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_23,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_32,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1036,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1042,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2050,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1036,c_1042])).

cnf(c_17,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_433,plain,
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
    inference(resolution_lifted,[status(thm)],[c_17,c_21])).

cnf(c_434,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0
    | k6_partfun1(sK0) != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_433])).

cnf(c_508,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_434])).

cnf(c_1026,plain,
    ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X0,sK0,X2) = sK0
    | v1_funct_2(X2,X0,sK0) != iProver_top
    | v1_funct_2(X1,sK0,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_508])).

cnf(c_1805,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1026])).

cnf(c_1887,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1805,c_28,c_29,c_30,c_31,c_32,c_33])).

cnf(c_2065,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_2050,c_1887])).

cnf(c_8,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_13,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_338,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X0)
    | X0 != X1
    | k2_relat_1(X0) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_13])).

cnf(c_339,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_338])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_349,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0)))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_339,c_7])).

cnf(c_20,negated_conjecture,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_364,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
    | ~ v2_funct_1(sK2)
    | k2_relat_1(X0) != sK0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_349,c_20])).

cnf(c_365,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3))))
    | ~ v2_funct_1(sK2)
    | k2_relat_1(sK3) != sK0 ),
    inference(unflattening,[status(thm)],[c_364])).

cnf(c_629,plain,
    ( ~ v2_funct_1(sK2)
    | sP0_iProver_split
    | k2_relat_1(sK3) != sK0 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_365])).

cnf(c_1029,plain,
    ( k2_relat_1(sK3) != sK0
    | v2_funct_1(sK2) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_629])).

cnf(c_2152,plain,
    ( sK0 != sK0
    | v2_funct_1(sK2) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_2065,c_1029])).

cnf(c_2153,plain,
    ( v2_funct_1(sK2) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2152])).

cnf(c_628,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3))))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_365])).

cnf(c_1030,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3)))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_628])).

cnf(c_2151,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(demodulation,[status(thm)],[c_2065,c_1030])).

cnf(c_2198,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_1036,c_2151])).

cnf(c_3456,plain,
    ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3286,c_28,c_29,c_30,c_31,c_32,c_33,c_2153,c_2198])).

cnf(c_3457,plain,
    ( sK0 = k1_xboole_0
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3456])).

cnf(c_6,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1043,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3462,plain,
    ( sK0 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3457,c_1043])).

cnf(c_1033,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3472,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3462,c_1033])).

cnf(c_3,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_3480,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3472,c_3])).

cnf(c_638,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2708,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(sK2)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_638])).

cnf(c_2710,plain,
    ( v2_funct_1(sK2)
    | ~ v2_funct_1(k1_xboole_0)
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2708])).

cnf(c_632,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1742,plain,
    ( X0 != X1
    | sK2 != X1
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_632])).

cnf(c_2400,plain,
    ( X0 != sK2
    | sK2 = X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1742])).

cnf(c_2401,plain,
    ( sK2 != sK2
    | sK2 = k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_2400])).

cnf(c_2204,plain,
    ( ~ sP0_iProver_split ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2198])).

cnf(c_2165,plain,
    ( ~ v2_funct_1(sK2)
    | sP0_iProver_split ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2153])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2000,plain,
    ( ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(k6_partfun1(X0)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2002,plain,
    ( ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | v1_xboole_0(k6_partfun1(k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2000])).

cnf(c_2,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1041,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1892,plain,
    ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_1041])).

cnf(c_1894,plain,
    ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1892])).

cnf(c_1605,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1606,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1605])).

cnf(c_1608,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1606])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1535,plain,
    ( ~ v1_xboole_0(k6_partfun1(X0))
    | k1_xboole_0 = k6_partfun1(X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1540,plain,
    ( ~ v1_xboole_0(k6_partfun1(k1_xboole_0))
    | k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1535])).

cnf(c_631,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1411,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_631])).

cnf(c_1371,plain,
    ( ~ v1_xboole_0(sK2)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1375,plain,
    ( k1_xboole_0 = sK2
    | v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1371])).

cnf(c_1253,plain,
    ( v2_funct_1(X0)
    | ~ v2_funct_1(k6_partfun1(X1))
    | X0 != k6_partfun1(X1) ),
    inference(instantiation,[status(thm)],[c_638])).

cnf(c_1255,plain,
    ( ~ v2_funct_1(k6_partfun1(k1_xboole_0))
    | v2_funct_1(k1_xboole_0)
    | k1_xboole_0 != k6_partfun1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1253])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_84,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_76,plain,
    ( v2_funct_1(k6_partfun1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3480,c_2710,c_2401,c_2204,c_2165,c_2002,c_1894,c_1608,c_1540,c_1411,c_1375,c_1255,c_84,c_0,c_76])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:21:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.67/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.00  
% 2.67/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.67/1.00  
% 2.67/1.00  ------  iProver source info
% 2.67/1.00  
% 2.67/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.67/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.67/1.00  git: non_committed_changes: false
% 2.67/1.00  git: last_make_outside_of_git: false
% 2.67/1.00  
% 2.67/1.00  ------ 
% 2.67/1.00  
% 2.67/1.00  ------ Input Options
% 2.67/1.00  
% 2.67/1.00  --out_options                           all
% 2.67/1.00  --tptp_safe_out                         true
% 2.67/1.00  --problem_path                          ""
% 2.67/1.00  --include_path                          ""
% 2.67/1.00  --clausifier                            res/vclausify_rel
% 2.67/1.00  --clausifier_options                    --mode clausify
% 2.67/1.00  --stdin                                 false
% 2.67/1.00  --stats_out                             all
% 2.67/1.00  
% 2.67/1.00  ------ General Options
% 2.67/1.00  
% 2.67/1.00  --fof                                   false
% 2.67/1.00  --time_out_real                         305.
% 2.67/1.00  --time_out_virtual                      -1.
% 2.67/1.00  --symbol_type_check                     false
% 2.67/1.00  --clausify_out                          false
% 2.67/1.00  --sig_cnt_out                           false
% 2.67/1.00  --trig_cnt_out                          false
% 2.67/1.00  --trig_cnt_out_tolerance                1.
% 2.67/1.00  --trig_cnt_out_sk_spl                   false
% 2.67/1.00  --abstr_cl_out                          false
% 2.67/1.00  
% 2.67/1.00  ------ Global Options
% 2.67/1.00  
% 2.67/1.00  --schedule                              default
% 2.67/1.00  --add_important_lit                     false
% 2.67/1.00  --prop_solver_per_cl                    1000
% 2.67/1.00  --min_unsat_core                        false
% 2.67/1.00  --soft_assumptions                      false
% 2.67/1.00  --soft_lemma_size                       3
% 2.67/1.00  --prop_impl_unit_size                   0
% 2.67/1.00  --prop_impl_unit                        []
% 2.67/1.00  --share_sel_clauses                     true
% 2.67/1.00  --reset_solvers                         false
% 2.67/1.00  --bc_imp_inh                            [conj_cone]
% 2.67/1.00  --conj_cone_tolerance                   3.
% 2.67/1.00  --extra_neg_conj                        none
% 2.67/1.00  --large_theory_mode                     true
% 2.67/1.00  --prolific_symb_bound                   200
% 2.67/1.00  --lt_threshold                          2000
% 2.67/1.00  --clause_weak_htbl                      true
% 2.67/1.00  --gc_record_bc_elim                     false
% 2.67/1.00  
% 2.67/1.00  ------ Preprocessing Options
% 2.67/1.00  
% 2.67/1.00  --preprocessing_flag                    true
% 2.67/1.00  --time_out_prep_mult                    0.1
% 2.67/1.00  --splitting_mode                        input
% 2.67/1.00  --splitting_grd                         true
% 2.67/1.00  --splitting_cvd                         false
% 2.67/1.00  --splitting_cvd_svl                     false
% 2.67/1.00  --splitting_nvd                         32
% 2.67/1.00  --sub_typing                            true
% 2.67/1.00  --prep_gs_sim                           true
% 2.67/1.00  --prep_unflatten                        true
% 2.67/1.00  --prep_res_sim                          true
% 2.67/1.00  --prep_upred                            true
% 2.67/1.00  --prep_sem_filter                       exhaustive
% 2.67/1.00  --prep_sem_filter_out                   false
% 2.67/1.00  --pred_elim                             true
% 2.67/1.00  --res_sim_input                         true
% 2.67/1.00  --eq_ax_congr_red                       true
% 2.67/1.00  --pure_diseq_elim                       true
% 2.67/1.00  --brand_transform                       false
% 2.67/1.00  --non_eq_to_eq                          false
% 2.67/1.00  --prep_def_merge                        true
% 2.67/1.00  --prep_def_merge_prop_impl              false
% 2.67/1.00  --prep_def_merge_mbd                    true
% 2.67/1.00  --prep_def_merge_tr_red                 false
% 2.67/1.00  --prep_def_merge_tr_cl                  false
% 2.67/1.00  --smt_preprocessing                     true
% 2.67/1.00  --smt_ac_axioms                         fast
% 2.67/1.00  --preprocessed_out                      false
% 2.67/1.00  --preprocessed_stats                    false
% 2.67/1.00  
% 2.67/1.00  ------ Abstraction refinement Options
% 2.67/1.00  
% 2.67/1.00  --abstr_ref                             []
% 2.67/1.00  --abstr_ref_prep                        false
% 2.67/1.00  --abstr_ref_until_sat                   false
% 2.67/1.00  --abstr_ref_sig_restrict                funpre
% 2.67/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.67/1.00  --abstr_ref_under                       []
% 2.67/1.00  
% 2.67/1.00  ------ SAT Options
% 2.67/1.00  
% 2.67/1.00  --sat_mode                              false
% 2.67/1.00  --sat_fm_restart_options                ""
% 2.67/1.00  --sat_gr_def                            false
% 2.67/1.00  --sat_epr_types                         true
% 2.67/1.00  --sat_non_cyclic_types                  false
% 2.67/1.00  --sat_finite_models                     false
% 2.67/1.00  --sat_fm_lemmas                         false
% 2.67/1.00  --sat_fm_prep                           false
% 2.67/1.00  --sat_fm_uc_incr                        true
% 2.67/1.00  --sat_out_model                         small
% 2.67/1.00  --sat_out_clauses                       false
% 2.67/1.00  
% 2.67/1.00  ------ QBF Options
% 2.67/1.00  
% 2.67/1.00  --qbf_mode                              false
% 2.67/1.00  --qbf_elim_univ                         false
% 2.67/1.00  --qbf_dom_inst                          none
% 2.67/1.00  --qbf_dom_pre_inst                      false
% 2.67/1.00  --qbf_sk_in                             false
% 2.67/1.00  --qbf_pred_elim                         true
% 2.67/1.00  --qbf_split                             512
% 2.67/1.00  
% 2.67/1.00  ------ BMC1 Options
% 2.67/1.00  
% 2.67/1.00  --bmc1_incremental                      false
% 2.67/1.00  --bmc1_axioms                           reachable_all
% 2.67/1.00  --bmc1_min_bound                        0
% 2.67/1.00  --bmc1_max_bound                        -1
% 2.67/1.00  --bmc1_max_bound_default                -1
% 2.67/1.00  --bmc1_symbol_reachability              true
% 2.67/1.00  --bmc1_property_lemmas                  false
% 2.67/1.00  --bmc1_k_induction                      false
% 2.67/1.00  --bmc1_non_equiv_states                 false
% 2.67/1.00  --bmc1_deadlock                         false
% 2.67/1.00  --bmc1_ucm                              false
% 2.67/1.00  --bmc1_add_unsat_core                   none
% 2.67/1.00  --bmc1_unsat_core_children              false
% 2.67/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.67/1.00  --bmc1_out_stat                         full
% 2.67/1.00  --bmc1_ground_init                      false
% 2.67/1.00  --bmc1_pre_inst_next_state              false
% 2.67/1.00  --bmc1_pre_inst_state                   false
% 2.67/1.00  --bmc1_pre_inst_reach_state             false
% 2.67/1.00  --bmc1_out_unsat_core                   false
% 2.67/1.00  --bmc1_aig_witness_out                  false
% 2.67/1.00  --bmc1_verbose                          false
% 2.67/1.00  --bmc1_dump_clauses_tptp                false
% 2.67/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.67/1.00  --bmc1_dump_file                        -
% 2.67/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.67/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.67/1.00  --bmc1_ucm_extend_mode                  1
% 2.67/1.00  --bmc1_ucm_init_mode                    2
% 2.67/1.00  --bmc1_ucm_cone_mode                    none
% 2.67/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.67/1.00  --bmc1_ucm_relax_model                  4
% 2.67/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.67/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.67/1.00  --bmc1_ucm_layered_model                none
% 2.67/1.00  --bmc1_ucm_max_lemma_size               10
% 2.67/1.00  
% 2.67/1.00  ------ AIG Options
% 2.67/1.00  
% 2.67/1.00  --aig_mode                              false
% 2.67/1.00  
% 2.67/1.00  ------ Instantiation Options
% 2.67/1.00  
% 2.67/1.00  --instantiation_flag                    true
% 2.67/1.00  --inst_sos_flag                         false
% 2.67/1.00  --inst_sos_phase                        true
% 2.67/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.67/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.67/1.00  --inst_lit_sel_side                     num_symb
% 2.67/1.00  --inst_solver_per_active                1400
% 2.67/1.00  --inst_solver_calls_frac                1.
% 2.67/1.00  --inst_passive_queue_type               priority_queues
% 2.67/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.67/1.00  --inst_passive_queues_freq              [25;2]
% 2.67/1.00  --inst_dismatching                      true
% 2.67/1.00  --inst_eager_unprocessed_to_passive     true
% 2.67/1.00  --inst_prop_sim_given                   true
% 2.67/1.00  --inst_prop_sim_new                     false
% 2.67/1.00  --inst_subs_new                         false
% 2.67/1.00  --inst_eq_res_simp                      false
% 2.67/1.00  --inst_subs_given                       false
% 2.67/1.00  --inst_orphan_elimination               true
% 2.67/1.00  --inst_learning_loop_flag               true
% 2.67/1.00  --inst_learning_start                   3000
% 2.67/1.00  --inst_learning_factor                  2
% 2.67/1.00  --inst_start_prop_sim_after_learn       3
% 2.67/1.00  --inst_sel_renew                        solver
% 2.67/1.00  --inst_lit_activity_flag                true
% 2.67/1.00  --inst_restr_to_given                   false
% 2.67/1.00  --inst_activity_threshold               500
% 2.67/1.00  --inst_out_proof                        true
% 2.67/1.00  
% 2.67/1.00  ------ Resolution Options
% 2.67/1.00  
% 2.67/1.00  --resolution_flag                       true
% 2.67/1.00  --res_lit_sel                           adaptive
% 2.67/1.00  --res_lit_sel_side                      none
% 2.67/1.00  --res_ordering                          kbo
% 2.67/1.00  --res_to_prop_solver                    active
% 2.67/1.00  --res_prop_simpl_new                    false
% 2.67/1.00  --res_prop_simpl_given                  true
% 2.67/1.00  --res_passive_queue_type                priority_queues
% 2.67/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.67/1.00  --res_passive_queues_freq               [15;5]
% 2.67/1.00  --res_forward_subs                      full
% 2.67/1.00  --res_backward_subs                     full
% 2.67/1.00  --res_forward_subs_resolution           true
% 2.67/1.00  --res_backward_subs_resolution          true
% 2.67/1.00  --res_orphan_elimination                true
% 2.67/1.00  --res_time_limit                        2.
% 2.67/1.00  --res_out_proof                         true
% 2.67/1.00  
% 2.67/1.00  ------ Superposition Options
% 2.67/1.00  
% 2.67/1.00  --superposition_flag                    true
% 2.67/1.00  --sup_passive_queue_type                priority_queues
% 2.67/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.67/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.67/1.00  --demod_completeness_check              fast
% 2.67/1.00  --demod_use_ground                      true
% 2.67/1.00  --sup_to_prop_solver                    passive
% 2.67/1.00  --sup_prop_simpl_new                    true
% 2.67/1.00  --sup_prop_simpl_given                  true
% 2.67/1.00  --sup_fun_splitting                     false
% 2.67/1.00  --sup_smt_interval                      50000
% 2.67/1.00  
% 2.67/1.00  ------ Superposition Simplification Setup
% 2.67/1.00  
% 2.67/1.00  --sup_indices_passive                   []
% 2.67/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.67/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/1.00  --sup_full_bw                           [BwDemod]
% 2.67/1.00  --sup_immed_triv                        [TrivRules]
% 2.67/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.67/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/1.00  --sup_immed_bw_main                     []
% 2.67/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.67/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.67/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.67/1.00  
% 2.67/1.00  ------ Combination Options
% 2.67/1.00  
% 2.67/1.00  --comb_res_mult                         3
% 2.67/1.00  --comb_sup_mult                         2
% 2.67/1.00  --comb_inst_mult                        10
% 2.67/1.00  
% 2.67/1.00  ------ Debug Options
% 2.67/1.00  
% 2.67/1.00  --dbg_backtrace                         false
% 2.67/1.00  --dbg_dump_prop_clauses                 false
% 2.67/1.00  --dbg_dump_prop_clauses_file            -
% 2.67/1.00  --dbg_out_stat                          false
% 2.67/1.00  ------ Parsing...
% 2.67/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.67/1.00  
% 2.67/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.67/1.00  
% 2.67/1.00  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.67/1.00  
% 2.67/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.67/1.00  ------ Proving...
% 2.67/1.00  ------ Problem Properties 
% 2.67/1.00  
% 2.67/1.00  
% 2.67/1.00  clauses                                 24
% 2.67/1.00  conjectures                             6
% 2.67/1.00  EPR                                     6
% 2.67/1.00  Horn                                    22
% 2.67/1.00  unary                                   11
% 2.67/1.00  binary                                  4
% 2.67/1.00  lits                                    71
% 2.67/1.00  lits eq                                 14
% 2.67/1.00  fd_pure                                 0
% 2.67/1.00  fd_pseudo                               0
% 2.67/1.00  fd_cond                                 3
% 2.67/1.00  fd_pseudo_cond                          0
% 2.67/1.00  AC symbols                              0
% 2.67/1.00  
% 2.67/1.00  ------ Schedule dynamic 5 is on 
% 2.67/1.00  
% 2.67/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.67/1.00  
% 2.67/1.00  
% 2.67/1.00  ------ 
% 2.67/1.00  Current options:
% 2.67/1.00  ------ 
% 2.67/1.00  
% 2.67/1.00  ------ Input Options
% 2.67/1.00  
% 2.67/1.00  --out_options                           all
% 2.67/1.00  --tptp_safe_out                         true
% 2.67/1.00  --problem_path                          ""
% 2.67/1.00  --include_path                          ""
% 2.67/1.00  --clausifier                            res/vclausify_rel
% 2.67/1.00  --clausifier_options                    --mode clausify
% 2.67/1.00  --stdin                                 false
% 2.67/1.00  --stats_out                             all
% 2.67/1.00  
% 2.67/1.00  ------ General Options
% 2.67/1.00  
% 2.67/1.00  --fof                                   false
% 2.67/1.00  --time_out_real                         305.
% 2.67/1.00  --time_out_virtual                      -1.
% 2.67/1.00  --symbol_type_check                     false
% 2.67/1.00  --clausify_out                          false
% 2.67/1.00  --sig_cnt_out                           false
% 2.67/1.00  --trig_cnt_out                          false
% 2.67/1.00  --trig_cnt_out_tolerance                1.
% 2.67/1.00  --trig_cnt_out_sk_spl                   false
% 2.67/1.00  --abstr_cl_out                          false
% 2.67/1.00  
% 2.67/1.00  ------ Global Options
% 2.67/1.00  
% 2.67/1.00  --schedule                              default
% 2.67/1.00  --add_important_lit                     false
% 2.67/1.00  --prop_solver_per_cl                    1000
% 2.67/1.00  --min_unsat_core                        false
% 2.67/1.00  --soft_assumptions                      false
% 2.67/1.00  --soft_lemma_size                       3
% 2.67/1.00  --prop_impl_unit_size                   0
% 2.67/1.00  --prop_impl_unit                        []
% 2.67/1.00  --share_sel_clauses                     true
% 2.67/1.00  --reset_solvers                         false
% 2.67/1.00  --bc_imp_inh                            [conj_cone]
% 2.67/1.00  --conj_cone_tolerance                   3.
% 2.67/1.00  --extra_neg_conj                        none
% 2.67/1.00  --large_theory_mode                     true
% 2.67/1.00  --prolific_symb_bound                   200
% 2.67/1.00  --lt_threshold                          2000
% 2.67/1.00  --clause_weak_htbl                      true
% 2.67/1.00  --gc_record_bc_elim                     false
% 2.67/1.00  
% 2.67/1.00  ------ Preprocessing Options
% 2.67/1.00  
% 2.67/1.00  --preprocessing_flag                    true
% 2.67/1.00  --time_out_prep_mult                    0.1
% 2.67/1.00  --splitting_mode                        input
% 2.67/1.00  --splitting_grd                         true
% 2.67/1.00  --splitting_cvd                         false
% 2.67/1.00  --splitting_cvd_svl                     false
% 2.67/1.00  --splitting_nvd                         32
% 2.67/1.00  --sub_typing                            true
% 2.67/1.00  --prep_gs_sim                           true
% 2.67/1.00  --prep_unflatten                        true
% 2.67/1.00  --prep_res_sim                          true
% 2.67/1.00  --prep_upred                            true
% 2.67/1.00  --prep_sem_filter                       exhaustive
% 2.67/1.00  --prep_sem_filter_out                   false
% 2.67/1.00  --pred_elim                             true
% 2.67/1.00  --res_sim_input                         true
% 2.67/1.00  --eq_ax_congr_red                       true
% 2.67/1.00  --pure_diseq_elim                       true
% 2.67/1.00  --brand_transform                       false
% 2.67/1.00  --non_eq_to_eq                          false
% 2.67/1.00  --prep_def_merge                        true
% 2.67/1.00  --prep_def_merge_prop_impl              false
% 2.67/1.00  --prep_def_merge_mbd                    true
% 2.67/1.00  --prep_def_merge_tr_red                 false
% 2.67/1.00  --prep_def_merge_tr_cl                  false
% 2.67/1.00  --smt_preprocessing                     true
% 2.67/1.00  --smt_ac_axioms                         fast
% 2.67/1.00  --preprocessed_out                      false
% 2.67/1.00  --preprocessed_stats                    false
% 2.67/1.00  
% 2.67/1.00  ------ Abstraction refinement Options
% 2.67/1.00  
% 2.67/1.00  --abstr_ref                             []
% 2.67/1.00  --abstr_ref_prep                        false
% 2.67/1.00  --abstr_ref_until_sat                   false
% 2.67/1.00  --abstr_ref_sig_restrict                funpre
% 2.67/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.67/1.00  --abstr_ref_under                       []
% 2.67/1.00  
% 2.67/1.00  ------ SAT Options
% 2.67/1.00  
% 2.67/1.00  --sat_mode                              false
% 2.67/1.00  --sat_fm_restart_options                ""
% 2.67/1.00  --sat_gr_def                            false
% 2.67/1.00  --sat_epr_types                         true
% 2.67/1.00  --sat_non_cyclic_types                  false
% 2.67/1.00  --sat_finite_models                     false
% 2.67/1.00  --sat_fm_lemmas                         false
% 2.67/1.00  --sat_fm_prep                           false
% 2.67/1.00  --sat_fm_uc_incr                        true
% 2.67/1.00  --sat_out_model                         small
% 2.67/1.00  --sat_out_clauses                       false
% 2.67/1.00  
% 2.67/1.00  ------ QBF Options
% 2.67/1.00  
% 2.67/1.00  --qbf_mode                              false
% 2.67/1.00  --qbf_elim_univ                         false
% 2.67/1.00  --qbf_dom_inst                          none
% 2.67/1.00  --qbf_dom_pre_inst                      false
% 2.67/1.00  --qbf_sk_in                             false
% 2.67/1.00  --qbf_pred_elim                         true
% 2.67/1.00  --qbf_split                             512
% 2.67/1.00  
% 2.67/1.00  ------ BMC1 Options
% 2.67/1.00  
% 2.67/1.00  --bmc1_incremental                      false
% 2.67/1.00  --bmc1_axioms                           reachable_all
% 2.67/1.00  --bmc1_min_bound                        0
% 2.67/1.00  --bmc1_max_bound                        -1
% 2.67/1.00  --bmc1_max_bound_default                -1
% 2.67/1.00  --bmc1_symbol_reachability              true
% 2.67/1.00  --bmc1_property_lemmas                  false
% 2.67/1.00  --bmc1_k_induction                      false
% 2.67/1.00  --bmc1_non_equiv_states                 false
% 2.67/1.00  --bmc1_deadlock                         false
% 2.67/1.00  --bmc1_ucm                              false
% 2.67/1.00  --bmc1_add_unsat_core                   none
% 2.67/1.00  --bmc1_unsat_core_children              false
% 2.67/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.67/1.00  --bmc1_out_stat                         full
% 2.67/1.00  --bmc1_ground_init                      false
% 2.67/1.00  --bmc1_pre_inst_next_state              false
% 2.67/1.00  --bmc1_pre_inst_state                   false
% 2.67/1.00  --bmc1_pre_inst_reach_state             false
% 2.67/1.00  --bmc1_out_unsat_core                   false
% 2.67/1.00  --bmc1_aig_witness_out                  false
% 2.67/1.00  --bmc1_verbose                          false
% 2.67/1.00  --bmc1_dump_clauses_tptp                false
% 2.67/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.67/1.00  --bmc1_dump_file                        -
% 2.67/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.67/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.67/1.00  --bmc1_ucm_extend_mode                  1
% 2.67/1.00  --bmc1_ucm_init_mode                    2
% 2.67/1.00  --bmc1_ucm_cone_mode                    none
% 2.67/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.67/1.00  --bmc1_ucm_relax_model                  4
% 2.67/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.67/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.67/1.00  --bmc1_ucm_layered_model                none
% 2.67/1.00  --bmc1_ucm_max_lemma_size               10
% 2.67/1.00  
% 2.67/1.00  ------ AIG Options
% 2.67/1.00  
% 2.67/1.00  --aig_mode                              false
% 2.67/1.00  
% 2.67/1.00  ------ Instantiation Options
% 2.67/1.00  
% 2.67/1.00  --instantiation_flag                    true
% 2.67/1.00  --inst_sos_flag                         false
% 2.67/1.00  --inst_sos_phase                        true
% 2.67/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.67/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.67/1.00  --inst_lit_sel_side                     none
% 2.67/1.00  --inst_solver_per_active                1400
% 2.67/1.00  --inst_solver_calls_frac                1.
% 2.67/1.00  --inst_passive_queue_type               priority_queues
% 2.67/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.67/1.00  --inst_passive_queues_freq              [25;2]
% 2.67/1.00  --inst_dismatching                      true
% 2.67/1.00  --inst_eager_unprocessed_to_passive     true
% 2.67/1.00  --inst_prop_sim_given                   true
% 2.67/1.00  --inst_prop_sim_new                     false
% 2.67/1.00  --inst_subs_new                         false
% 2.67/1.00  --inst_eq_res_simp                      false
% 2.67/1.00  --inst_subs_given                       false
% 2.67/1.00  --inst_orphan_elimination               true
% 2.67/1.00  --inst_learning_loop_flag               true
% 2.67/1.00  --inst_learning_start                   3000
% 2.67/1.00  --inst_learning_factor                  2
% 2.67/1.00  --inst_start_prop_sim_after_learn       3
% 2.67/1.00  --inst_sel_renew                        solver
% 2.67/1.00  --inst_lit_activity_flag                true
% 2.67/1.00  --inst_restr_to_given                   false
% 2.67/1.00  --inst_activity_threshold               500
% 2.67/1.00  --inst_out_proof                        true
% 2.67/1.00  
% 2.67/1.00  ------ Resolution Options
% 2.67/1.00  
% 2.67/1.00  --resolution_flag                       false
% 2.67/1.00  --res_lit_sel                           adaptive
% 2.67/1.00  --res_lit_sel_side                      none
% 2.67/1.00  --res_ordering                          kbo
% 2.67/1.00  --res_to_prop_solver                    active
% 2.67/1.00  --res_prop_simpl_new                    false
% 2.67/1.00  --res_prop_simpl_given                  true
% 2.67/1.00  --res_passive_queue_type                priority_queues
% 2.67/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.67/1.00  --res_passive_queues_freq               [15;5]
% 2.67/1.00  --res_forward_subs                      full
% 2.67/1.00  --res_backward_subs                     full
% 2.67/1.00  --res_forward_subs_resolution           true
% 2.67/1.00  --res_backward_subs_resolution          true
% 2.67/1.00  --res_orphan_elimination                true
% 2.67/1.00  --res_time_limit                        2.
% 2.67/1.00  --res_out_proof                         true
% 2.67/1.00  
% 2.67/1.00  ------ Superposition Options
% 2.67/1.00  
% 2.67/1.00  --superposition_flag                    true
% 2.67/1.00  --sup_passive_queue_type                priority_queues
% 2.67/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.67/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.67/1.00  --demod_completeness_check              fast
% 2.67/1.00  --demod_use_ground                      true
% 2.67/1.00  --sup_to_prop_solver                    passive
% 2.67/1.00  --sup_prop_simpl_new                    true
% 2.67/1.00  --sup_prop_simpl_given                  true
% 2.67/1.00  --sup_fun_splitting                     false
% 2.67/1.00  --sup_smt_interval                      50000
% 2.67/1.00  
% 2.67/1.00  ------ Superposition Simplification Setup
% 2.67/1.00  
% 2.67/1.00  --sup_indices_passive                   []
% 2.67/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.67/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/1.00  --sup_full_bw                           [BwDemod]
% 2.67/1.00  --sup_immed_triv                        [TrivRules]
% 2.67/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.67/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/1.00  --sup_immed_bw_main                     []
% 2.67/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.67/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.67/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.67/1.00  
% 2.67/1.00  ------ Combination Options
% 2.67/1.00  
% 2.67/1.00  --comb_res_mult                         3
% 2.67/1.00  --comb_sup_mult                         2
% 2.67/1.00  --comb_inst_mult                        10
% 2.67/1.00  
% 2.67/1.00  ------ Debug Options
% 2.67/1.00  
% 2.67/1.00  --dbg_backtrace                         false
% 2.67/1.00  --dbg_dump_prop_clauses                 false
% 2.67/1.00  --dbg_dump_prop_clauses_file            -
% 2.67/1.00  --dbg_out_stat                          false
% 2.67/1.00  
% 2.67/1.00  
% 2.67/1.00  
% 2.67/1.00  
% 2.67/1.00  ------ Proving...
% 2.67/1.00  
% 2.67/1.00  
% 2.67/1.00  % SZS status Theorem for theBenchmark.p
% 2.67/1.00  
% 2.67/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.67/1.00  
% 2.67/1.00  fof(f12,axiom,(
% 2.67/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 2.67/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/1.00  
% 2.67/1.00  fof(f28,plain,(
% 2.67/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.67/1.00    inference(ennf_transformation,[],[f12])).
% 2.67/1.00  
% 2.67/1.00  fof(f29,plain,(
% 2.67/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.67/1.00    inference(flattening,[],[f28])).
% 2.67/1.00  
% 2.67/1.00  fof(f59,plain,(
% 2.67/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.67/1.00    inference(cnf_transformation,[],[f29])).
% 2.67/1.00  
% 2.67/1.00  fof(f9,axiom,(
% 2.67/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.67/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/1.00  
% 2.67/1.00  fof(f24,plain,(
% 2.67/1.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.67/1.00    inference(ennf_transformation,[],[f9])).
% 2.67/1.00  
% 2.67/1.00  fof(f25,plain,(
% 2.67/1.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.67/1.00    inference(flattening,[],[f24])).
% 2.67/1.00  
% 2.67/1.00  fof(f38,plain,(
% 2.67/1.00    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.67/1.00    inference(nnf_transformation,[],[f25])).
% 2.67/1.00  
% 2.67/1.00  fof(f53,plain,(
% 2.67/1.00    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.67/1.00    inference(cnf_transformation,[],[f38])).
% 2.67/1.00  
% 2.67/1.00  fof(f16,conjecture,(
% 2.67/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 2.67/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/1.00  
% 2.67/1.00  fof(f17,negated_conjecture,(
% 2.67/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 2.67/1.00    inference(negated_conjecture,[],[f16])).
% 2.67/1.00  
% 2.67/1.00  fof(f34,plain,(
% 2.67/1.00    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.67/1.00    inference(ennf_transformation,[],[f17])).
% 2.67/1.00  
% 2.67/1.00  fof(f35,plain,(
% 2.67/1.00    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.67/1.00    inference(flattening,[],[f34])).
% 2.67/1.00  
% 2.67/1.00  fof(f41,plain,(
% 2.67/1.00    ( ! [X2,X0,X1] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((~v2_funct_2(sK3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 2.67/1.00    introduced(choice_axiom,[])).
% 2.67/1.00  
% 2.67/1.00  fof(f40,plain,(
% 2.67/1.00    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 2.67/1.00    introduced(choice_axiom,[])).
% 2.67/1.00  
% 2.67/1.00  fof(f42,plain,(
% 2.67/1.00    ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 2.67/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f35,f41,f40])).
% 2.67/1.00  
% 2.67/1.00  fof(f70,plain,(
% 2.67/1.00    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.67/1.00    inference(cnf_transformation,[],[f42])).
% 2.67/1.00  
% 2.67/1.00  fof(f10,axiom,(
% 2.67/1.00    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 2.67/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/1.00  
% 2.67/1.00  fof(f55,plain,(
% 2.67/1.00    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.67/1.00    inference(cnf_transformation,[],[f10])).
% 2.67/1.00  
% 2.67/1.00  fof(f13,axiom,(
% 2.67/1.00    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.67/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/1.00  
% 2.67/1.00  fof(f60,plain,(
% 2.67/1.00    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.67/1.00    inference(cnf_transformation,[],[f13])).
% 2.67/1.00  
% 2.67/1.00  fof(f73,plain,(
% 2.67/1.00    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.67/1.00    inference(definition_unfolding,[],[f55,f60])).
% 2.67/1.00  
% 2.67/1.00  fof(f64,plain,(
% 2.67/1.00    v1_funct_1(sK2)),
% 2.67/1.00    inference(cnf_transformation,[],[f42])).
% 2.67/1.00  
% 2.67/1.00  fof(f66,plain,(
% 2.67/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.67/1.00    inference(cnf_transformation,[],[f42])).
% 2.67/1.00  
% 2.67/1.00  fof(f67,plain,(
% 2.67/1.00    v1_funct_1(sK3)),
% 2.67/1.00    inference(cnf_transformation,[],[f42])).
% 2.67/1.00  
% 2.67/1.00  fof(f69,plain,(
% 2.67/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.67/1.00    inference(cnf_transformation,[],[f42])).
% 2.67/1.00  
% 2.67/1.00  fof(f15,axiom,(
% 2.67/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 2.67/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/1.00  
% 2.67/1.00  fof(f32,plain,(
% 2.67/1.00    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.67/1.00    inference(ennf_transformation,[],[f15])).
% 2.67/1.00  
% 2.67/1.00  fof(f33,plain,(
% 2.67/1.00    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.67/1.00    inference(flattening,[],[f32])).
% 2.67/1.00  
% 2.67/1.00  fof(f62,plain,(
% 2.67/1.00    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X3) | k1_xboole_0 = X2 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.67/1.00    inference(cnf_transformation,[],[f33])).
% 2.67/1.00  
% 2.67/1.00  fof(f65,plain,(
% 2.67/1.00    v1_funct_2(sK2,sK0,sK1)),
% 2.67/1.00    inference(cnf_transformation,[],[f42])).
% 2.67/1.00  
% 2.67/1.00  fof(f68,plain,(
% 2.67/1.00    v1_funct_2(sK3,sK1,sK0)),
% 2.67/1.00    inference(cnf_transformation,[],[f42])).
% 2.67/1.00  
% 2.67/1.00  fof(f8,axiom,(
% 2.67/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 2.67/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/1.00  
% 2.67/1.00  fof(f23,plain,(
% 2.67/1.00    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.67/1.00    inference(ennf_transformation,[],[f8])).
% 2.67/1.00  
% 2.67/1.00  fof(f52,plain,(
% 2.67/1.00    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.67/1.00    inference(cnf_transformation,[],[f23])).
% 2.67/1.00  
% 2.67/1.00  fof(f14,axiom,(
% 2.67/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 2.67/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/1.00  
% 2.67/1.00  fof(f30,plain,(
% 2.67/1.00    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.67/1.00    inference(ennf_transformation,[],[f14])).
% 2.67/1.00  
% 2.67/1.00  fof(f31,plain,(
% 2.67/1.00    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.67/1.00    inference(flattening,[],[f30])).
% 2.67/1.00  
% 2.67/1.00  fof(f61,plain,(
% 2.67/1.00    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.67/1.00    inference(cnf_transformation,[],[f31])).
% 2.67/1.00  
% 2.67/1.00  fof(f7,axiom,(
% 2.67/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.67/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/1.00  
% 2.67/1.00  fof(f18,plain,(
% 2.67/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 2.67/1.00    inference(pure_predicate_removal,[],[f7])).
% 2.67/1.00  
% 2.67/1.00  fof(f22,plain,(
% 2.67/1.00    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.67/1.00    inference(ennf_transformation,[],[f18])).
% 2.67/1.00  
% 2.67/1.00  fof(f51,plain,(
% 2.67/1.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.67/1.00    inference(cnf_transformation,[],[f22])).
% 2.67/1.00  
% 2.67/1.00  fof(f11,axiom,(
% 2.67/1.00    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 2.67/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/1.00  
% 2.67/1.00  fof(f26,plain,(
% 2.67/1.00    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.67/1.00    inference(ennf_transformation,[],[f11])).
% 2.67/1.00  
% 2.67/1.00  fof(f27,plain,(
% 2.67/1.00    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.67/1.00    inference(flattening,[],[f26])).
% 2.67/1.00  
% 2.67/1.00  fof(f39,plain,(
% 2.67/1.00    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.67/1.00    inference(nnf_transformation,[],[f27])).
% 2.67/1.00  
% 2.67/1.00  fof(f57,plain,(
% 2.67/1.00    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.67/1.00    inference(cnf_transformation,[],[f39])).
% 2.67/1.00  
% 2.67/1.00  fof(f77,plain,(
% 2.67/1.00    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.67/1.00    inference(equality_resolution,[],[f57])).
% 2.67/1.00  
% 2.67/1.00  fof(f6,axiom,(
% 2.67/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.67/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/1.00  
% 2.67/1.00  fof(f21,plain,(
% 2.67/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.67/1.00    inference(ennf_transformation,[],[f6])).
% 2.67/1.00  
% 2.67/1.00  fof(f50,plain,(
% 2.67/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.67/1.00    inference(cnf_transformation,[],[f21])).
% 2.67/1.00  
% 2.67/1.00  fof(f71,plain,(
% 2.67/1.00    ~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)),
% 2.67/1.00    inference(cnf_transformation,[],[f42])).
% 2.67/1.00  
% 2.67/1.00  fof(f5,axiom,(
% 2.67/1.00    ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 2.67/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/1.00  
% 2.67/1.00  fof(f49,plain,(
% 2.67/1.00    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 2.67/1.00    inference(cnf_transformation,[],[f5])).
% 2.67/1.00  
% 2.67/1.00  fof(f72,plain,(
% 2.67/1.00    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 2.67/1.00    inference(definition_unfolding,[],[f49,f60])).
% 2.67/1.00  
% 2.67/1.00  fof(f3,axiom,(
% 2.67/1.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.67/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/1.00  
% 2.67/1.00  fof(f36,plain,(
% 2.67/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.67/1.00    inference(nnf_transformation,[],[f3])).
% 2.67/1.00  
% 2.67/1.00  fof(f37,plain,(
% 2.67/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.67/1.00    inference(flattening,[],[f36])).
% 2.67/1.00  
% 2.67/1.00  fof(f46,plain,(
% 2.67/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.67/1.00    inference(cnf_transformation,[],[f37])).
% 2.67/1.00  
% 2.67/1.00  fof(f75,plain,(
% 2.67/1.00    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.67/1.00    inference(equality_resolution,[],[f46])).
% 2.67/1.00  
% 2.67/1.00  fof(f4,axiom,(
% 2.67/1.00    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 2.67/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/1.00  
% 2.67/1.00  fof(f20,plain,(
% 2.67/1.00    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 2.67/1.00    inference(ennf_transformation,[],[f4])).
% 2.67/1.00  
% 2.67/1.00  fof(f48,plain,(
% 2.67/1.00    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 2.67/1.00    inference(cnf_transformation,[],[f20])).
% 2.67/1.00  
% 2.67/1.00  fof(f47,plain,(
% 2.67/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 2.67/1.00    inference(cnf_transformation,[],[f37])).
% 2.67/1.00  
% 2.67/1.00  fof(f74,plain,(
% 2.67/1.00    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.67/1.00    inference(equality_resolution,[],[f47])).
% 2.67/1.00  
% 2.67/1.00  fof(f2,axiom,(
% 2.67/1.00    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.67/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/1.00  
% 2.67/1.00  fof(f19,plain,(
% 2.67/1.00    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.67/1.00    inference(ennf_transformation,[],[f2])).
% 2.67/1.00  
% 2.67/1.00  fof(f44,plain,(
% 2.67/1.00    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.67/1.00    inference(cnf_transformation,[],[f19])).
% 2.67/1.00  
% 2.67/1.00  fof(f1,axiom,(
% 2.67/1.00    v1_xboole_0(k1_xboole_0)),
% 2.67/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/1.00  
% 2.67/1.00  fof(f43,plain,(
% 2.67/1.00    v1_xboole_0(k1_xboole_0)),
% 2.67/1.00    inference(cnf_transformation,[],[f1])).
% 2.67/1.00  
% 2.67/1.00  cnf(c_15,plain,
% 2.67/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.67/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 2.67/1.00      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 2.67/1.00      | ~ v1_funct_1(X0)
% 2.67/1.00      | ~ v1_funct_1(X3) ),
% 2.67/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1040,plain,
% 2.67/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.67/1.00      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 2.67/1.00      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 2.67/1.00      | v1_funct_1(X0) != iProver_top
% 2.67/1.00      | v1_funct_1(X3) != iProver_top ),
% 2.67/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_11,plain,
% 2.67/1.00      ( ~ r2_relset_1(X0,X1,X2,X3)
% 2.67/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.67/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.67/1.00      | X3 = X2 ),
% 2.67/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_21,negated_conjecture,
% 2.67/1.00      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 2.67/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_420,plain,
% 2.67/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.67/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.67/1.00      | X3 = X0
% 2.67/1.00      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 2.67/1.00      | k6_partfun1(sK0) != X3
% 2.67/1.00      | sK0 != X2
% 2.67/1.00      | sK0 != X1 ),
% 2.67/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_21]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_421,plain,
% 2.67/1.00      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.67/1.00      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.67/1.00      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 2.67/1.00      inference(unflattening,[status(thm)],[c_420]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_12,plain,
% 2.67/1.00      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 2.67/1.00      inference(cnf_transformation,[],[f73]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_429,plain,
% 2.67/1.00      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.67/1.00      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 2.67/1.00      inference(forward_subsumption_resolution,
% 2.67/1.00                [status(thm)],
% 2.67/1.00                [c_421,c_12]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1027,plain,
% 2.67/1.00      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 2.67/1.00      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 2.67/1.00      inference(predicate_to_equality,[status(thm)],[c_429]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_2637,plain,
% 2.67/1.00      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
% 2.67/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.67/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.67/1.00      | v1_funct_1(sK2) != iProver_top
% 2.67/1.00      | v1_funct_1(sK3) != iProver_top ),
% 2.67/1.00      inference(superposition,[status(thm)],[c_1040,c_1027]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_27,negated_conjecture,
% 2.67/1.00      ( v1_funct_1(sK2) ),
% 2.67/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_28,plain,
% 2.67/1.00      ( v1_funct_1(sK2) = iProver_top ),
% 2.67/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_25,negated_conjecture,
% 2.67/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.67/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_30,plain,
% 2.67/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.67/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_24,negated_conjecture,
% 2.67/1.00      ( v1_funct_1(sK3) ),
% 2.67/1.00      inference(cnf_transformation,[],[f67]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_31,plain,
% 2.67/1.00      ( v1_funct_1(sK3) = iProver_top ),
% 2.67/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_22,negated_conjecture,
% 2.67/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 2.67/1.00      inference(cnf_transformation,[],[f69]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_33,plain,
% 2.67/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 2.67/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_3259,plain,
% 2.67/1.00      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
% 2.67/1.00      inference(global_propositional_subsumption,
% 2.67/1.00                [status(thm)],
% 2.67/1.00                [c_2637,c_28,c_30,c_31,c_33]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_19,plain,
% 2.67/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.67/1.00      | ~ v1_funct_2(X3,X4,X1)
% 2.67/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 2.67/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.67/1.00      | ~ v1_funct_1(X0)
% 2.67/1.00      | ~ v1_funct_1(X3)
% 2.67/1.00      | v2_funct_1(X3)
% 2.67/1.00      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 2.67/1.00      | k1_xboole_0 = X2 ),
% 2.67/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1037,plain,
% 2.67/1.00      ( k1_xboole_0 = X0
% 2.67/1.00      | v1_funct_2(X1,X2,X0) != iProver_top
% 2.67/1.00      | v1_funct_2(X3,X4,X2) != iProver_top
% 2.67/1.00      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
% 2.67/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 2.67/1.00      | v1_funct_1(X1) != iProver_top
% 2.67/1.00      | v1_funct_1(X3) != iProver_top
% 2.67/1.00      | v2_funct_1(X3) = iProver_top
% 2.67/1.00      | v2_funct_1(k1_partfun1(X4,X2,X2,X0,X3,X1)) != iProver_top ),
% 2.67/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_3286,plain,
% 2.67/1.00      ( sK0 = k1_xboole_0
% 2.67/1.00      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 2.67/1.00      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 2.67/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.67/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.67/1.00      | v1_funct_1(sK2) != iProver_top
% 2.67/1.00      | v1_funct_1(sK3) != iProver_top
% 2.67/1.00      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 2.67/1.00      | v2_funct_1(sK2) = iProver_top ),
% 2.67/1.00      inference(superposition,[status(thm)],[c_3259,c_1037]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_26,negated_conjecture,
% 2.67/1.00      ( v1_funct_2(sK2,sK0,sK1) ),
% 2.67/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_29,plain,
% 2.67/1.00      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 2.67/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_23,negated_conjecture,
% 2.67/1.00      ( v1_funct_2(sK3,sK1,sK0) ),
% 2.67/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_32,plain,
% 2.67/1.00      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 2.67/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1036,plain,
% 2.67/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 2.67/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_9,plain,
% 2.67/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.67/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.67/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1042,plain,
% 2.67/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.67/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.67/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_2050,plain,
% 2.67/1.00      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 2.67/1.00      inference(superposition,[status(thm)],[c_1036,c_1042]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_17,plain,
% 2.67/1.00      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 2.67/1.00      | ~ v1_funct_2(X2,X0,X1)
% 2.67/1.00      | ~ v1_funct_2(X3,X1,X0)
% 2.67/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.67/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.67/1.00      | ~ v1_funct_1(X2)
% 2.67/1.00      | ~ v1_funct_1(X3)
% 2.67/1.00      | k2_relset_1(X1,X0,X3) = X0 ),
% 2.67/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_433,plain,
% 2.67/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.67/1.00      | ~ v1_funct_2(X3,X2,X1)
% 2.67/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.67/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.67/1.00      | ~ v1_funct_1(X0)
% 2.67/1.00      | ~ v1_funct_1(X3)
% 2.67/1.00      | k1_partfun1(X2,X1,X1,X2,X3,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 2.67/1.00      | k2_relset_1(X1,X2,X0) = X2
% 2.67/1.00      | k6_partfun1(X2) != k6_partfun1(sK0)
% 2.67/1.00      | sK0 != X2 ),
% 2.67/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_21]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_434,plain,
% 2.67/1.00      ( ~ v1_funct_2(X0,X1,sK0)
% 2.67/1.00      | ~ v1_funct_2(X2,sK0,X1)
% 2.67/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 2.67/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 2.67/1.00      | ~ v1_funct_1(X0)
% 2.67/1.00      | ~ v1_funct_1(X2)
% 2.67/1.00      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 2.67/1.00      | k2_relset_1(X1,sK0,X0) = sK0
% 2.67/1.00      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 2.67/1.00      inference(unflattening,[status(thm)],[c_433]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_508,plain,
% 2.67/1.00      ( ~ v1_funct_2(X0,X1,sK0)
% 2.67/1.00      | ~ v1_funct_2(X2,sK0,X1)
% 2.67/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 2.67/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 2.67/1.00      | ~ v1_funct_1(X0)
% 2.67/1.00      | ~ v1_funct_1(X2)
% 2.67/1.00      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 2.67/1.00      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 2.67/1.00      inference(equality_resolution_simp,[status(thm)],[c_434]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1026,plain,
% 2.67/1.00      ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 2.67/1.00      | k2_relset_1(X0,sK0,X2) = sK0
% 2.67/1.00      | v1_funct_2(X2,X0,sK0) != iProver_top
% 2.67/1.00      | v1_funct_2(X1,sK0,X0) != iProver_top
% 2.67/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 2.67/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 2.67/1.00      | v1_funct_1(X2) != iProver_top
% 2.67/1.00      | v1_funct_1(X1) != iProver_top ),
% 2.67/1.00      inference(predicate_to_equality,[status(thm)],[c_508]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1805,plain,
% 2.67/1.00      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 2.67/1.00      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 2.67/1.00      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 2.67/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.67/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.67/1.00      | v1_funct_1(sK2) != iProver_top
% 2.67/1.00      | v1_funct_1(sK3) != iProver_top ),
% 2.67/1.00      inference(equality_resolution,[status(thm)],[c_1026]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1887,plain,
% 2.67/1.00      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 2.67/1.00      inference(global_propositional_subsumption,
% 2.67/1.00                [status(thm)],
% 2.67/1.00                [c_1805,c_28,c_29,c_30,c_31,c_32,c_33]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_2065,plain,
% 2.67/1.00      ( k2_relat_1(sK3) = sK0 ),
% 2.67/1.00      inference(light_normalisation,[status(thm)],[c_2050,c_1887]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_8,plain,
% 2.67/1.00      ( v5_relat_1(X0,X1)
% 2.67/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.67/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_13,plain,
% 2.67/1.00      ( v2_funct_2(X0,k2_relat_1(X0))
% 2.67/1.00      | ~ v5_relat_1(X0,k2_relat_1(X0))
% 2.67/1.00      | ~ v1_relat_1(X0) ),
% 2.67/1.00      inference(cnf_transformation,[],[f77]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_338,plain,
% 2.67/1.00      ( v2_funct_2(X0,k2_relat_1(X0))
% 2.67/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 2.67/1.00      | ~ v1_relat_1(X0)
% 2.67/1.00      | X0 != X1
% 2.67/1.00      | k2_relat_1(X0) != X3 ),
% 2.67/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_13]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_339,plain,
% 2.67/1.00      ( v2_funct_2(X0,k2_relat_1(X0))
% 2.67/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
% 2.67/1.00      | ~ v1_relat_1(X0) ),
% 2.67/1.00      inference(unflattening,[status(thm)],[c_338]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_7,plain,
% 2.67/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.67/1.00      | v1_relat_1(X0) ),
% 2.67/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_349,plain,
% 2.67/1.00      ( v2_funct_2(X0,k2_relat_1(X0))
% 2.67/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0)))) ),
% 2.67/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_339,c_7]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_20,negated_conjecture,
% 2.67/1.00      ( ~ v2_funct_2(sK3,sK0) | ~ v2_funct_1(sK2) ),
% 2.67/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_364,plain,
% 2.67/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
% 2.67/1.00      | ~ v2_funct_1(sK2)
% 2.67/1.00      | k2_relat_1(X0) != sK0
% 2.67/1.00      | sK3 != X0 ),
% 2.67/1.00      inference(resolution_lifted,[status(thm)],[c_349,c_20]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_365,plain,
% 2.67/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3))))
% 2.67/1.00      | ~ v2_funct_1(sK2)
% 2.67/1.00      | k2_relat_1(sK3) != sK0 ),
% 2.67/1.00      inference(unflattening,[status(thm)],[c_364]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_629,plain,
% 2.67/1.00      ( ~ v2_funct_1(sK2) | sP0_iProver_split | k2_relat_1(sK3) != sK0 ),
% 2.67/1.00      inference(splitting,
% 2.67/1.00                [splitting(split),new_symbols(definition,[])],
% 2.67/1.00                [c_365]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1029,plain,
% 2.67/1.00      ( k2_relat_1(sK3) != sK0
% 2.67/1.00      | v2_funct_1(sK2) != iProver_top
% 2.67/1.00      | sP0_iProver_split = iProver_top ),
% 2.67/1.00      inference(predicate_to_equality,[status(thm)],[c_629]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_2152,plain,
% 2.67/1.00      ( sK0 != sK0
% 2.67/1.00      | v2_funct_1(sK2) != iProver_top
% 2.67/1.00      | sP0_iProver_split = iProver_top ),
% 2.67/1.00      inference(demodulation,[status(thm)],[c_2065,c_1029]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_2153,plain,
% 2.67/1.00      ( v2_funct_1(sK2) != iProver_top
% 2.67/1.00      | sP0_iProver_split = iProver_top ),
% 2.67/1.00      inference(equality_resolution_simp,[status(thm)],[c_2152]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_628,plain,
% 2.67/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3))))
% 2.67/1.00      | ~ sP0_iProver_split ),
% 2.67/1.00      inference(splitting,
% 2.67/1.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.67/1.00                [c_365]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1030,plain,
% 2.67/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3)))) != iProver_top
% 2.67/1.00      | sP0_iProver_split != iProver_top ),
% 2.67/1.00      inference(predicate_to_equality,[status(thm)],[c_628]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_2151,plain,
% 2.67/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 2.67/1.00      | sP0_iProver_split != iProver_top ),
% 2.67/1.00      inference(demodulation,[status(thm)],[c_2065,c_1030]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_2198,plain,
% 2.67/1.00      ( sP0_iProver_split != iProver_top ),
% 2.67/1.00      inference(superposition,[status(thm)],[c_1036,c_2151]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_3456,plain,
% 2.67/1.00      ( v2_funct_1(k6_partfun1(sK0)) != iProver_top | sK0 = k1_xboole_0 ),
% 2.67/1.00      inference(global_propositional_subsumption,
% 2.67/1.00                [status(thm)],
% 2.67/1.00                [c_3286,c_28,c_29,c_30,c_31,c_32,c_33,c_2153,c_2198]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_3457,plain,
% 2.67/1.00      ( sK0 = k1_xboole_0 | v2_funct_1(k6_partfun1(sK0)) != iProver_top ),
% 2.67/1.00      inference(renaming,[status(thm)],[c_3456]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_6,plain,
% 2.67/1.00      ( v2_funct_1(k6_partfun1(X0)) ),
% 2.67/1.00      inference(cnf_transformation,[],[f72]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1043,plain,
% 2.67/1.00      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 2.67/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_3462,plain,
% 2.67/1.00      ( sK0 = k1_xboole_0 ),
% 2.67/1.00      inference(forward_subsumption_resolution,
% 2.67/1.00                [status(thm)],
% 2.67/1.00                [c_3457,c_1043]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1033,plain,
% 2.67/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.67/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_3472,plain,
% 2.67/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) = iProver_top ),
% 2.67/1.00      inference(demodulation,[status(thm)],[c_3462,c_1033]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_3,plain,
% 2.67/1.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.67/1.00      inference(cnf_transformation,[],[f75]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_3480,plain,
% 2.67/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.67/1.00      inference(demodulation,[status(thm)],[c_3472,c_3]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_638,plain,
% 2.67/1.00      ( ~ v2_funct_1(X0) | v2_funct_1(X1) | X1 != X0 ),
% 2.67/1.00      theory(equality) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_2708,plain,
% 2.67/1.00      ( ~ v2_funct_1(X0) | v2_funct_1(sK2) | sK2 != X0 ),
% 2.67/1.00      inference(instantiation,[status(thm)],[c_638]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_2710,plain,
% 2.67/1.00      ( v2_funct_1(sK2)
% 2.67/1.00      | ~ v2_funct_1(k1_xboole_0)
% 2.67/1.00      | sK2 != k1_xboole_0 ),
% 2.67/1.00      inference(instantiation,[status(thm)],[c_2708]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_632,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1742,plain,
% 2.67/1.00      ( X0 != X1 | sK2 != X1 | sK2 = X0 ),
% 2.67/1.00      inference(instantiation,[status(thm)],[c_632]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_2400,plain,
% 2.67/1.00      ( X0 != sK2 | sK2 = X0 | sK2 != sK2 ),
% 2.67/1.00      inference(instantiation,[status(thm)],[c_1742]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_2401,plain,
% 2.67/1.00      ( sK2 != sK2 | sK2 = k1_xboole_0 | k1_xboole_0 != sK2 ),
% 2.67/1.00      inference(instantiation,[status(thm)],[c_2400]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_2204,plain,
% 2.67/1.00      ( ~ sP0_iProver_split ),
% 2.67/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_2198]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_2165,plain,
% 2.67/1.00      ( ~ v2_funct_1(sK2) | sP0_iProver_split ),
% 2.67/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_2153]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_5,plain,
% 2.67/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.67/1.00      | ~ v1_xboole_0(X1)
% 2.67/1.00      | v1_xboole_0(X0) ),
% 2.67/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_2000,plain,
% 2.67/1.00      ( ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(X1))
% 2.67/1.00      | ~ v1_xboole_0(X1)
% 2.67/1.00      | v1_xboole_0(k6_partfun1(X0)) ),
% 2.67/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_2002,plain,
% 2.67/1.00      ( ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
% 2.67/1.00      | v1_xboole_0(k6_partfun1(k1_xboole_0))
% 2.67/1.00      | ~ v1_xboole_0(k1_xboole_0) ),
% 2.67/1.00      inference(instantiation,[status(thm)],[c_2000]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_2,plain,
% 2.67/1.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.67/1.00      inference(cnf_transformation,[],[f74]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1041,plain,
% 2.67/1.00      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 2.67/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1892,plain,
% 2.67/1.00      ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.67/1.00      inference(superposition,[status(thm)],[c_2,c_1041]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1894,plain,
% 2.67/1.00      ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
% 2.67/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1892]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1605,plain,
% 2.67/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
% 2.67/1.00      | ~ v1_xboole_0(X0)
% 2.67/1.00      | v1_xboole_0(sK2) ),
% 2.67/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1606,plain,
% 2.67/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top
% 2.67/1.00      | v1_xboole_0(X0) != iProver_top
% 2.67/1.00      | v1_xboole_0(sK2) = iProver_top ),
% 2.67/1.00      inference(predicate_to_equality,[status(thm)],[c_1605]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1608,plain,
% 2.67/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.67/1.00      | v1_xboole_0(sK2) = iProver_top
% 2.67/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.67/1.00      inference(instantiation,[status(thm)],[c_1606]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1,plain,
% 2.67/1.00      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 2.67/1.00      inference(cnf_transformation,[],[f44]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1535,plain,
% 2.67/1.00      ( ~ v1_xboole_0(k6_partfun1(X0)) | k1_xboole_0 = k6_partfun1(X0) ),
% 2.67/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1540,plain,
% 2.67/1.00      ( ~ v1_xboole_0(k6_partfun1(k1_xboole_0))
% 2.67/1.00      | k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
% 2.67/1.00      inference(instantiation,[status(thm)],[c_1535]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_631,plain,( X0 = X0 ),theory(equality) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1411,plain,
% 2.67/1.00      ( sK2 = sK2 ),
% 2.67/1.00      inference(instantiation,[status(thm)],[c_631]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1371,plain,
% 2.67/1.00      ( ~ v1_xboole_0(sK2) | k1_xboole_0 = sK2 ),
% 2.67/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1375,plain,
% 2.67/1.00      ( k1_xboole_0 = sK2 | v1_xboole_0(sK2) != iProver_top ),
% 2.67/1.00      inference(predicate_to_equality,[status(thm)],[c_1371]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1253,plain,
% 2.67/1.00      ( v2_funct_1(X0)
% 2.67/1.00      | ~ v2_funct_1(k6_partfun1(X1))
% 2.67/1.00      | X0 != k6_partfun1(X1) ),
% 2.67/1.00      inference(instantiation,[status(thm)],[c_638]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1255,plain,
% 2.67/1.00      ( ~ v2_funct_1(k6_partfun1(k1_xboole_0))
% 2.67/1.00      | v2_funct_1(k1_xboole_0)
% 2.67/1.00      | k1_xboole_0 != k6_partfun1(k1_xboole_0) ),
% 2.67/1.00      inference(instantiation,[status(thm)],[c_1253]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_0,plain,
% 2.67/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 2.67/1.00      inference(cnf_transformation,[],[f43]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_84,plain,
% 2.67/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.67/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_76,plain,
% 2.67/1.00      ( v2_funct_1(k6_partfun1(k1_xboole_0)) ),
% 2.67/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(contradiction,plain,
% 2.67/1.00      ( $false ),
% 2.67/1.00      inference(minisat,
% 2.67/1.00                [status(thm)],
% 2.67/1.00                [c_3480,c_2710,c_2401,c_2204,c_2165,c_2002,c_1894,c_1608,
% 2.67/1.00                 c_1540,c_1411,c_1375,c_1255,c_84,c_0,c_76]) ).
% 2.67/1.00  
% 2.67/1.00  
% 2.67/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.67/1.00  
% 2.67/1.00  ------                               Statistics
% 2.67/1.00  
% 2.67/1.00  ------ General
% 2.67/1.00  
% 2.67/1.00  abstr_ref_over_cycles:                  0
% 2.67/1.00  abstr_ref_under_cycles:                 0
% 2.67/1.00  gc_basic_clause_elim:                   0
% 2.67/1.00  forced_gc_time:                         0
% 2.67/1.00  parsing_time:                           0.014
% 2.67/1.00  unif_index_cands_time:                  0.
% 2.67/1.00  unif_index_add_time:                    0.
% 2.67/1.00  orderings_time:                         0.
% 2.67/1.00  out_proof_time:                         0.008
% 2.67/1.00  total_time:                             0.215
% 2.67/1.00  num_of_symbols:                         52
% 2.67/1.00  num_of_terms:                           4915
% 2.67/1.00  
% 2.67/1.00  ------ Preprocessing
% 2.67/1.00  
% 2.67/1.00  num_of_splits:                          1
% 2.67/1.00  num_of_split_atoms:                     1
% 2.67/1.00  num_of_reused_defs:                     0
% 2.67/1.00  num_eq_ax_congr_red:                    10
% 2.67/1.00  num_of_sem_filtered_clauses:            1
% 2.67/1.00  num_of_subtypes:                        0
% 2.67/1.00  monotx_restored_types:                  0
% 2.67/1.00  sat_num_of_epr_types:                   0
% 2.67/1.00  sat_num_of_non_cyclic_types:            0
% 2.67/1.00  sat_guarded_non_collapsed_types:        0
% 2.67/1.00  num_pure_diseq_elim:                    0
% 2.67/1.00  simp_replaced_by:                       0
% 2.67/1.00  res_preprocessed:                       126
% 2.67/1.00  prep_upred:                             0
% 2.67/1.00  prep_unflattend:                        17
% 2.67/1.00  smt_new_axioms:                         0
% 2.67/1.00  pred_elim_cands:                        5
% 2.67/1.00  pred_elim:                              4
% 2.67/1.00  pred_elim_cl:                           5
% 2.67/1.00  pred_elim_cycles:                       7
% 2.67/1.00  merged_defs:                            0
% 2.67/1.00  merged_defs_ncl:                        0
% 2.67/1.00  bin_hyper_res:                          0
% 2.67/1.00  prep_cycles:                            4
% 2.67/1.00  pred_elim_time:                         0.009
% 2.67/1.00  splitting_time:                         0.
% 2.67/1.00  sem_filter_time:                        0.
% 2.67/1.00  monotx_time:                            0.001
% 2.67/1.00  subtype_inf_time:                       0.
% 2.67/1.00  
% 2.67/1.00  ------ Problem properties
% 2.67/1.00  
% 2.67/1.00  clauses:                                24
% 2.67/1.00  conjectures:                            6
% 2.67/1.00  epr:                                    6
% 2.67/1.00  horn:                                   22
% 2.67/1.00  ground:                                 9
% 2.67/1.00  unary:                                  11
% 2.67/1.00  binary:                                 4
% 2.67/1.00  lits:                                   71
% 2.67/1.00  lits_eq:                                14
% 2.67/1.00  fd_pure:                                0
% 2.67/1.00  fd_pseudo:                              0
% 2.67/1.00  fd_cond:                                3
% 2.67/1.00  fd_pseudo_cond:                         0
% 2.67/1.00  ac_symbols:                             0
% 2.67/1.00  
% 2.67/1.00  ------ Propositional Solver
% 2.67/1.00  
% 2.67/1.00  prop_solver_calls:                      27
% 2.67/1.00  prop_fast_solver_calls:                 905
% 2.67/1.00  smt_solver_calls:                       0
% 2.67/1.00  smt_fast_solver_calls:                  0
% 2.67/1.00  prop_num_of_clauses:                    1360
% 2.67/1.00  prop_preprocess_simplified:             4588
% 2.67/1.00  prop_fo_subsumed:                       23
% 2.67/1.00  prop_solver_time:                       0.
% 2.67/1.00  smt_solver_time:                        0.
% 2.67/1.00  smt_fast_solver_time:                   0.
% 2.67/1.00  prop_fast_solver_time:                  0.
% 2.67/1.00  prop_unsat_core_time:                   0.
% 2.67/1.00  
% 2.67/1.00  ------ QBF
% 2.67/1.00  
% 2.67/1.00  qbf_q_res:                              0
% 2.67/1.00  qbf_num_tautologies:                    0
% 2.67/1.00  qbf_prep_cycles:                        0
% 2.67/1.00  
% 2.67/1.00  ------ BMC1
% 2.67/1.00  
% 2.67/1.00  bmc1_current_bound:                     -1
% 2.67/1.00  bmc1_last_solved_bound:                 -1
% 2.67/1.00  bmc1_unsat_core_size:                   -1
% 2.67/1.00  bmc1_unsat_core_parents_size:           -1
% 2.67/1.00  bmc1_merge_next_fun:                    0
% 2.67/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.67/1.00  
% 2.67/1.00  ------ Instantiation
% 2.67/1.00  
% 2.67/1.00  inst_num_of_clauses:                    440
% 2.67/1.00  inst_num_in_passive:                    116
% 2.67/1.00  inst_num_in_active:                     210
% 2.67/1.00  inst_num_in_unprocessed:                114
% 2.67/1.00  inst_num_of_loops:                      220
% 2.67/1.00  inst_num_of_learning_restarts:          0
% 2.67/1.00  inst_num_moves_active_passive:          8
% 2.67/1.00  inst_lit_activity:                      0
% 2.67/1.00  inst_lit_activity_moves:                0
% 2.67/1.00  inst_num_tautologies:                   0
% 2.67/1.00  inst_num_prop_implied:                  0
% 2.67/1.00  inst_num_existing_simplified:           0
% 2.67/1.00  inst_num_eq_res_simplified:             0
% 2.67/1.00  inst_num_child_elim:                    0
% 2.67/1.00  inst_num_of_dismatching_blockings:      16
% 2.67/1.00  inst_num_of_non_proper_insts:           278
% 2.67/1.00  inst_num_of_duplicates:                 0
% 2.67/1.00  inst_inst_num_from_inst_to_res:         0
% 2.67/1.00  inst_dismatching_checking_time:         0.
% 2.67/1.00  
% 2.67/1.00  ------ Resolution
% 2.67/1.00  
% 2.67/1.00  res_num_of_clauses:                     0
% 2.67/1.00  res_num_in_passive:                     0
% 2.67/1.00  res_num_in_active:                      0
% 2.67/1.00  res_num_of_loops:                       130
% 2.67/1.00  res_forward_subset_subsumed:            14
% 2.67/1.00  res_backward_subset_subsumed:           0
% 2.67/1.00  res_forward_subsumed:                   0
% 2.67/1.00  res_backward_subsumed:                  0
% 2.67/1.00  res_forward_subsumption_resolution:     4
% 2.67/1.00  res_backward_subsumption_resolution:    0
% 2.67/1.00  res_clause_to_clause_subsumption:       95
% 2.67/1.00  res_orphan_elimination:                 0
% 2.67/1.00  res_tautology_del:                      24
% 2.67/1.00  res_num_eq_res_simplified:              1
% 2.67/1.00  res_num_sel_changes:                    0
% 2.67/1.00  res_moves_from_active_to_pass:          0
% 2.67/1.00  
% 2.67/1.00  ------ Superposition
% 2.67/1.00  
% 2.67/1.00  sup_time_total:                         0.
% 2.67/1.00  sup_time_generating:                    0.
% 2.67/1.00  sup_time_sim_full:                      0.
% 2.67/1.00  sup_time_sim_immed:                     0.
% 2.67/1.00  
% 2.67/1.00  sup_num_of_clauses:                     45
% 2.67/1.00  sup_num_in_active:                      25
% 2.67/1.00  sup_num_in_passive:                     20
% 2.67/1.00  sup_num_of_loops:                       42
% 2.67/1.00  sup_fw_superposition:                   21
% 2.67/1.00  sup_bw_superposition:                   11
% 2.67/1.00  sup_immediate_simplified:               9
% 2.67/1.00  sup_given_eliminated:                   1
% 2.67/1.00  comparisons_done:                       0
% 2.67/1.00  comparisons_avoided:                    0
% 2.67/1.00  
% 2.67/1.00  ------ Simplifications
% 2.67/1.00  
% 2.67/1.00  
% 2.67/1.00  sim_fw_subset_subsumed:                 0
% 2.67/1.00  sim_bw_subset_subsumed:                 0
% 2.67/1.00  sim_fw_subsumed:                        1
% 2.67/1.00  sim_bw_subsumed:                        2
% 2.67/1.00  sim_fw_subsumption_res:                 1
% 2.67/1.00  sim_bw_subsumption_res:                 0
% 2.67/1.00  sim_tautology_del:                      0
% 2.67/1.00  sim_eq_tautology_del:                   3
% 2.67/1.00  sim_eq_res_simp:                        1
% 2.67/1.00  sim_fw_demodulated:                     7
% 2.67/1.00  sim_bw_demodulated:                     16
% 2.67/1.00  sim_light_normalised:                   2
% 2.67/1.00  sim_joinable_taut:                      0
% 2.67/1.00  sim_joinable_simp:                      0
% 2.67/1.00  sim_ac_normalised:                      0
% 2.67/1.00  sim_smt_subsumption:                    0
% 2.67/1.00  
%------------------------------------------------------------------------------

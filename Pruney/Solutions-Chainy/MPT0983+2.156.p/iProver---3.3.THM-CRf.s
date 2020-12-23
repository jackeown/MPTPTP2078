%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:18 EST 2020

% Result     : Theorem 3.06s
% Output     : CNFRefutation 3.06s
% Verified   : 
% Statistics : Number of formulae       :  192 ( 889 expanded)
%              Number of clauses        :  115 ( 287 expanded)
%              Number of leaves         :   22 ( 213 expanded)
%              Depth                    :   22
%              Number of atoms          :  630 (5399 expanded)
%              Number of equality atoms :  240 ( 522 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
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

fof(f19,negated_conjecture,(
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
    inference(negated_conjecture,[],[f18])).

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
    inference(ennf_transformation,[],[f19])).

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

fof(f44,plain,(
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

fof(f43,plain,
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

fof(f45,plain,
    ( ( ~ v2_funct_2(sK3,sK0)
      | ~ v2_funct_1(sK2) )
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f35,f44,f43])).

fof(f77,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f45])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f28])).

fof(f67,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f24])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f78,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f45])).

fof(f12,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f15,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f82,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f63,f68])).

fof(f72,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f74,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f45])).

fof(f75,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f17,axiom,(
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
    inference(ennf_transformation,[],[f17])).

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

fof(f70,plain,(
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

fof(f73,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f76,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f8,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f81,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f58,f68])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f16,axiom,(
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
    inference(ennf_transformation,[],[f16])).

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

fof(f69,plain,(
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

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f88,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f65])).

fof(f79,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f38])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f86,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f51])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

fof(f48,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f7,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f80,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f57,f68])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1498,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1507,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2667,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1498,c_1507])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_223,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_224,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_223])).

cnf(c_293,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_9,c_224])).

cnf(c_1492,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_293])).

cnf(c_4961,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2667,c_1492])).

cnf(c_10,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1506,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_5074,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4961,c_1506])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1502,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_16,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_26,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_516,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_26])).

cnf(c_517,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_516])).

cnf(c_17,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_525,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_517,c_17])).

cnf(c_1488,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_525])).

cnf(c_3900,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1502,c_1488])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1508,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2789,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | r1_tarski(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k2_zfmisc_1(sK0,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1508,c_1488])).

cnf(c_2806,plain,
    ( ~ r1_tarski(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k2_zfmisc_1(sK0,sK0))
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2789])).

cnf(c_1984,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_3158,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | r1_tarski(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k2_zfmisc_1(sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_1984])).

cnf(c_1825,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_partfun1(X1,X2,X3,X4,X0,sK3),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_2071,plain,
    ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1825])).

cnf(c_2484,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,X0,X1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2071])).

cnf(c_3663,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2484])).

cnf(c_4255,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3900,c_32,c_30,c_29,c_27,c_2806,c_3158,c_3663])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v2_funct_1(X3)
    | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1499,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | v1_funct_2(X3,X4,X2) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v2_funct_1(X3) = iProver_top
    | v2_funct_1(k1_partfun1(X4,X2,X2,X0,X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4282,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4255,c_1499])).

cnf(c_33,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_34,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_35,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_36,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_37,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_38,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_4406,plain,
    ( sK0 = k1_xboole_0
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4282,c_33,c_34,c_35,c_36,c_37,c_38])).

cnf(c_12,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1505,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4413,plain,
    ( sK0 = k1_xboole_0
    | v2_funct_1(sK2) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4406,c_1505])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1504,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3067,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1498,c_1504])).

cnf(c_22,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_529,plain,
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
    inference(resolution_lifted,[status(thm)],[c_22,c_26])).

cnf(c_530,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0
    | k6_partfun1(sK0) != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_529])).

cnf(c_608,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_530])).

cnf(c_1487,plain,
    ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X0,sK0,X2) = sK0
    | v1_funct_2(X2,X0,sK0) != iProver_top
    | v1_funct_2(X1,sK0,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_608])).

cnf(c_2256,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1487])).

cnf(c_2347,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2256,c_33,c_34,c_35,c_36,c_37,c_38])).

cnf(c_3082,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_3067,c_2347])).

cnf(c_13,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_18,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_25,negated_conjecture,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_435,plain,
    ( ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) != sK0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_25])).

cnf(c_436,plain,
    ( ~ v5_relat_1(sK3,k2_relat_1(sK3))
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) != sK0 ),
    inference(unflattening,[status(thm)],[c_435])).

cnf(c_456,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) != X2
    | k2_relat_1(sK3) != sK0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_436])).

cnf(c_457,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3))))
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) != sK0 ),
    inference(unflattening,[status(thm)],[c_456])).

cnf(c_818,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | sP0_iProver_split
    | k2_relat_1(sK3) != sK0 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_457])).

cnf(c_1490,plain,
    ( k2_relat_1(sK3) != sK0
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_818])).

cnf(c_3395,plain,
    ( sK0 != sK0
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_3082,c_1490])).

cnf(c_3401,plain,
    ( v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3395])).

cnf(c_817,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3))))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_457])).

cnf(c_1491,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3)))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_817])).

cnf(c_2788,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(X0,k2_relat_1(sK3))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_1508,c_1491])).

cnf(c_3394,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(X0,sK0)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(demodulation,[status(thm)],[c_3082,c_2788])).

cnf(c_3746,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_2667,c_3394])).

cnf(c_3818,plain,
    ( v1_relat_1(sK3) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3401,c_3746])).

cnf(c_3819,plain,
    ( v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_3818])).

cnf(c_4415,plain,
    ( sK0 = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4413,c_3819])).

cnf(c_5076,plain,
    ( sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5074,c_4415])).

cnf(c_1495,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_5157,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5076,c_1495])).

cnf(c_5,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_5165,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5157,c_5])).

cnf(c_2761,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
    | r1_tarski(sK2,X0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2762,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(sK2,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2761])).

cnf(c_2764,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(sK2,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2762])).

cnf(c_828,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2517,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(sK2)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_828])).

cnf(c_2518,plain,
    ( sK2 != X0
    | v2_funct_1(X0) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2517])).

cnf(c_2520,plain,
    ( sK2 != k1_xboole_0
    | v2_funct_1(sK2) = iProver_top
    | v2_funct_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2518])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2233,plain,
    ( ~ r1_tarski(X0,sK2)
    | ~ r1_tarski(sK2,X0)
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2234,plain,
    ( sK2 = X0
    | r1_tarski(X0,sK2) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2233])).

cnf(c_2236,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(sK2,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2234])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2203,plain,
    ( r1_tarski(k1_xboole_0,sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2206,plain,
    ( r1_tarski(k1_xboole_0,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2203])).

cnf(c_821,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1979,plain,
    ( X0 != X1
    | X0 = k6_partfun1(X2)
    | k6_partfun1(X2) != X1 ),
    inference(instantiation,[status(thm)],[c_821])).

cnf(c_1980,plain,
    ( k6_partfun1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k6_partfun1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1979])).

cnf(c_1752,plain,
    ( v2_funct_1(X0)
    | ~ v2_funct_1(k6_partfun1(X1))
    | X0 != k6_partfun1(X1) ),
    inference(instantiation,[status(thm)],[c_828])).

cnf(c_1753,plain,
    ( X0 != k6_partfun1(X1)
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k6_partfun1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1752])).

cnf(c_1755,plain,
    ( k1_xboole_0 != k6_partfun1(k1_xboole_0)
    | v2_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top
    | v2_funct_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1753])).

cnf(c_91,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_6,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_90,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_11,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_77,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_79,plain,
    ( v2_funct_1(k6_partfun1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_77])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5165,c_5074,c_3746,c_3401,c_2764,c_2520,c_2236,c_2206,c_1980,c_1755,c_91,c_90,c_11,c_79])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 16:50:19 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.06/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/0.98  
% 3.06/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.06/0.98  
% 3.06/0.98  ------  iProver source info
% 3.06/0.98  
% 3.06/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.06/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.06/0.98  git: non_committed_changes: false
% 3.06/0.98  git: last_make_outside_of_git: false
% 3.06/0.98  
% 3.06/0.98  ------ 
% 3.06/0.98  
% 3.06/0.98  ------ Input Options
% 3.06/0.98  
% 3.06/0.98  --out_options                           all
% 3.06/0.98  --tptp_safe_out                         true
% 3.06/0.98  --problem_path                          ""
% 3.06/0.98  --include_path                          ""
% 3.06/0.98  --clausifier                            res/vclausify_rel
% 3.06/0.98  --clausifier_options                    --mode clausify
% 3.06/0.98  --stdin                                 false
% 3.06/0.98  --stats_out                             all
% 3.06/0.98  
% 3.06/0.98  ------ General Options
% 3.06/0.98  
% 3.06/0.98  --fof                                   false
% 3.06/0.98  --time_out_real                         305.
% 3.06/0.98  --time_out_virtual                      -1.
% 3.06/0.98  --symbol_type_check                     false
% 3.06/0.98  --clausify_out                          false
% 3.06/0.98  --sig_cnt_out                           false
% 3.06/0.98  --trig_cnt_out                          false
% 3.06/0.98  --trig_cnt_out_tolerance                1.
% 3.06/0.98  --trig_cnt_out_sk_spl                   false
% 3.06/0.98  --abstr_cl_out                          false
% 3.06/0.98  
% 3.06/0.98  ------ Global Options
% 3.06/0.98  
% 3.06/0.98  --schedule                              default
% 3.06/0.98  --add_important_lit                     false
% 3.06/0.98  --prop_solver_per_cl                    1000
% 3.06/0.98  --min_unsat_core                        false
% 3.06/0.98  --soft_assumptions                      false
% 3.06/0.98  --soft_lemma_size                       3
% 3.06/0.98  --prop_impl_unit_size                   0
% 3.06/0.98  --prop_impl_unit                        []
% 3.06/0.98  --share_sel_clauses                     true
% 3.06/0.98  --reset_solvers                         false
% 3.06/0.98  --bc_imp_inh                            [conj_cone]
% 3.06/0.98  --conj_cone_tolerance                   3.
% 3.06/0.98  --extra_neg_conj                        none
% 3.06/0.98  --large_theory_mode                     true
% 3.06/0.98  --prolific_symb_bound                   200
% 3.06/0.98  --lt_threshold                          2000
% 3.06/0.98  --clause_weak_htbl                      true
% 3.06/0.98  --gc_record_bc_elim                     false
% 3.06/0.98  
% 3.06/0.98  ------ Preprocessing Options
% 3.06/0.98  
% 3.06/0.98  --preprocessing_flag                    true
% 3.06/0.98  --time_out_prep_mult                    0.1
% 3.06/0.98  --splitting_mode                        input
% 3.06/0.98  --splitting_grd                         true
% 3.06/0.98  --splitting_cvd                         false
% 3.06/0.98  --splitting_cvd_svl                     false
% 3.06/0.98  --splitting_nvd                         32
% 3.06/0.98  --sub_typing                            true
% 3.06/0.98  --prep_gs_sim                           true
% 3.06/0.98  --prep_unflatten                        true
% 3.06/0.98  --prep_res_sim                          true
% 3.06/0.98  --prep_upred                            true
% 3.06/0.98  --prep_sem_filter                       exhaustive
% 3.06/0.98  --prep_sem_filter_out                   false
% 3.06/0.98  --pred_elim                             true
% 3.06/0.98  --res_sim_input                         true
% 3.06/0.98  --eq_ax_congr_red                       true
% 3.06/0.98  --pure_diseq_elim                       true
% 3.06/0.98  --brand_transform                       false
% 3.06/0.98  --non_eq_to_eq                          false
% 3.06/0.98  --prep_def_merge                        true
% 3.06/0.98  --prep_def_merge_prop_impl              false
% 3.06/0.98  --prep_def_merge_mbd                    true
% 3.06/0.98  --prep_def_merge_tr_red                 false
% 3.06/0.98  --prep_def_merge_tr_cl                  false
% 3.06/0.98  --smt_preprocessing                     true
% 3.06/0.98  --smt_ac_axioms                         fast
% 3.06/0.98  --preprocessed_out                      false
% 3.06/0.98  --preprocessed_stats                    false
% 3.06/0.98  
% 3.06/0.98  ------ Abstraction refinement Options
% 3.06/0.98  
% 3.06/0.98  --abstr_ref                             []
% 3.06/0.98  --abstr_ref_prep                        false
% 3.06/0.98  --abstr_ref_until_sat                   false
% 3.06/0.98  --abstr_ref_sig_restrict                funpre
% 3.06/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.06/0.98  --abstr_ref_under                       []
% 3.06/0.98  
% 3.06/0.98  ------ SAT Options
% 3.06/0.98  
% 3.06/0.98  --sat_mode                              false
% 3.06/0.98  --sat_fm_restart_options                ""
% 3.06/0.98  --sat_gr_def                            false
% 3.06/0.98  --sat_epr_types                         true
% 3.06/0.98  --sat_non_cyclic_types                  false
% 3.06/0.98  --sat_finite_models                     false
% 3.06/0.98  --sat_fm_lemmas                         false
% 3.06/0.98  --sat_fm_prep                           false
% 3.06/0.98  --sat_fm_uc_incr                        true
% 3.06/0.98  --sat_out_model                         small
% 3.06/0.98  --sat_out_clauses                       false
% 3.06/0.98  
% 3.06/0.98  ------ QBF Options
% 3.06/0.98  
% 3.06/0.98  --qbf_mode                              false
% 3.06/0.98  --qbf_elim_univ                         false
% 3.06/0.98  --qbf_dom_inst                          none
% 3.06/0.98  --qbf_dom_pre_inst                      false
% 3.06/0.98  --qbf_sk_in                             false
% 3.06/0.98  --qbf_pred_elim                         true
% 3.06/0.98  --qbf_split                             512
% 3.06/0.98  
% 3.06/0.98  ------ BMC1 Options
% 3.06/0.98  
% 3.06/0.98  --bmc1_incremental                      false
% 3.06/0.98  --bmc1_axioms                           reachable_all
% 3.06/0.98  --bmc1_min_bound                        0
% 3.06/0.98  --bmc1_max_bound                        -1
% 3.06/0.98  --bmc1_max_bound_default                -1
% 3.06/0.98  --bmc1_symbol_reachability              true
% 3.06/0.98  --bmc1_property_lemmas                  false
% 3.06/0.98  --bmc1_k_induction                      false
% 3.06/0.98  --bmc1_non_equiv_states                 false
% 3.06/0.98  --bmc1_deadlock                         false
% 3.06/0.98  --bmc1_ucm                              false
% 3.06/0.98  --bmc1_add_unsat_core                   none
% 3.06/0.98  --bmc1_unsat_core_children              false
% 3.06/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.06/0.98  --bmc1_out_stat                         full
% 3.06/0.98  --bmc1_ground_init                      false
% 3.06/0.98  --bmc1_pre_inst_next_state              false
% 3.06/0.98  --bmc1_pre_inst_state                   false
% 3.06/0.98  --bmc1_pre_inst_reach_state             false
% 3.06/0.98  --bmc1_out_unsat_core                   false
% 3.06/0.98  --bmc1_aig_witness_out                  false
% 3.06/0.98  --bmc1_verbose                          false
% 3.06/0.98  --bmc1_dump_clauses_tptp                false
% 3.06/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.06/0.98  --bmc1_dump_file                        -
% 3.06/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.06/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.06/0.98  --bmc1_ucm_extend_mode                  1
% 3.06/0.98  --bmc1_ucm_init_mode                    2
% 3.06/0.98  --bmc1_ucm_cone_mode                    none
% 3.06/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.06/0.98  --bmc1_ucm_relax_model                  4
% 3.06/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.06/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.06/0.98  --bmc1_ucm_layered_model                none
% 3.06/0.98  --bmc1_ucm_max_lemma_size               10
% 3.06/0.98  
% 3.06/0.98  ------ AIG Options
% 3.06/0.98  
% 3.06/0.98  --aig_mode                              false
% 3.06/0.98  
% 3.06/0.98  ------ Instantiation Options
% 3.06/0.98  
% 3.06/0.98  --instantiation_flag                    true
% 3.06/0.98  --inst_sos_flag                         false
% 3.06/0.98  --inst_sos_phase                        true
% 3.06/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.06/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.06/0.98  --inst_lit_sel_side                     num_symb
% 3.06/0.98  --inst_solver_per_active                1400
% 3.06/0.98  --inst_solver_calls_frac                1.
% 3.06/0.98  --inst_passive_queue_type               priority_queues
% 3.06/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.06/0.98  --inst_passive_queues_freq              [25;2]
% 3.06/0.98  --inst_dismatching                      true
% 3.06/0.98  --inst_eager_unprocessed_to_passive     true
% 3.06/0.98  --inst_prop_sim_given                   true
% 3.06/0.98  --inst_prop_sim_new                     false
% 3.06/0.98  --inst_subs_new                         false
% 3.06/0.98  --inst_eq_res_simp                      false
% 3.06/0.98  --inst_subs_given                       false
% 3.06/0.98  --inst_orphan_elimination               true
% 3.06/0.98  --inst_learning_loop_flag               true
% 3.06/0.98  --inst_learning_start                   3000
% 3.06/0.98  --inst_learning_factor                  2
% 3.06/0.98  --inst_start_prop_sim_after_learn       3
% 3.06/0.98  --inst_sel_renew                        solver
% 3.06/0.98  --inst_lit_activity_flag                true
% 3.06/0.98  --inst_restr_to_given                   false
% 3.06/0.98  --inst_activity_threshold               500
% 3.06/0.98  --inst_out_proof                        true
% 3.06/0.98  
% 3.06/0.98  ------ Resolution Options
% 3.06/0.98  
% 3.06/0.98  --resolution_flag                       true
% 3.06/0.98  --res_lit_sel                           adaptive
% 3.06/0.98  --res_lit_sel_side                      none
% 3.06/0.98  --res_ordering                          kbo
% 3.06/0.98  --res_to_prop_solver                    active
% 3.06/0.98  --res_prop_simpl_new                    false
% 3.06/0.98  --res_prop_simpl_given                  true
% 3.06/0.98  --res_passive_queue_type                priority_queues
% 3.06/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.06/0.98  --res_passive_queues_freq               [15;5]
% 3.06/0.98  --res_forward_subs                      full
% 3.06/0.98  --res_backward_subs                     full
% 3.06/0.98  --res_forward_subs_resolution           true
% 3.06/0.98  --res_backward_subs_resolution          true
% 3.06/0.98  --res_orphan_elimination                true
% 3.06/0.98  --res_time_limit                        2.
% 3.06/0.98  --res_out_proof                         true
% 3.06/0.98  
% 3.06/0.98  ------ Superposition Options
% 3.06/0.98  
% 3.06/0.98  --superposition_flag                    true
% 3.06/0.98  --sup_passive_queue_type                priority_queues
% 3.06/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.06/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.06/0.98  --demod_completeness_check              fast
% 3.06/0.98  --demod_use_ground                      true
% 3.06/0.98  --sup_to_prop_solver                    passive
% 3.06/0.98  --sup_prop_simpl_new                    true
% 3.06/0.98  --sup_prop_simpl_given                  true
% 3.06/0.98  --sup_fun_splitting                     false
% 3.06/0.98  --sup_smt_interval                      50000
% 3.06/0.98  
% 3.06/0.98  ------ Superposition Simplification Setup
% 3.06/0.98  
% 3.06/0.98  --sup_indices_passive                   []
% 3.06/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.06/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.06/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.06/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.06/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.06/0.98  --sup_full_bw                           [BwDemod]
% 3.06/0.98  --sup_immed_triv                        [TrivRules]
% 3.06/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.06/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.06/0.98  --sup_immed_bw_main                     []
% 3.06/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.06/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.06/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.06/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.06/0.98  
% 3.06/0.98  ------ Combination Options
% 3.06/0.98  
% 3.06/0.98  --comb_res_mult                         3
% 3.06/0.98  --comb_sup_mult                         2
% 3.06/0.98  --comb_inst_mult                        10
% 3.06/0.98  
% 3.06/0.98  ------ Debug Options
% 3.06/0.98  
% 3.06/0.98  --dbg_backtrace                         false
% 3.06/0.98  --dbg_dump_prop_clauses                 false
% 3.06/0.98  --dbg_dump_prop_clauses_file            -
% 3.06/0.98  --dbg_out_stat                          false
% 3.06/0.98  ------ Parsing...
% 3.06/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.06/0.98  
% 3.06/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.06/0.98  
% 3.06/0.98  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.06/0.98  
% 3.06/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.06/0.98  ------ Proving...
% 3.06/0.98  ------ Problem Properties 
% 3.06/0.98  
% 3.06/0.98  
% 3.06/0.98  clauses                                 29
% 3.06/0.98  conjectures                             6
% 3.06/0.98  EPR                                     8
% 3.06/0.98  Horn                                    27
% 3.06/0.98  unary                                   14
% 3.06/0.98  binary                                  5
% 3.06/0.98  lits                                    80
% 3.06/0.98  lits eq                                 15
% 3.06/0.98  fd_pure                                 0
% 3.06/0.98  fd_pseudo                               0
% 3.06/0.98  fd_cond                                 2
% 3.06/0.98  fd_pseudo_cond                          1
% 3.06/0.98  AC symbols                              0
% 3.06/0.98  
% 3.06/0.98  ------ Schedule dynamic 5 is on 
% 3.06/0.98  
% 3.06/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.06/0.98  
% 3.06/0.98  
% 3.06/0.98  ------ 
% 3.06/0.98  Current options:
% 3.06/0.98  ------ 
% 3.06/0.98  
% 3.06/0.98  ------ Input Options
% 3.06/0.98  
% 3.06/0.98  --out_options                           all
% 3.06/0.98  --tptp_safe_out                         true
% 3.06/0.98  --problem_path                          ""
% 3.06/0.98  --include_path                          ""
% 3.06/0.98  --clausifier                            res/vclausify_rel
% 3.06/0.98  --clausifier_options                    --mode clausify
% 3.06/0.98  --stdin                                 false
% 3.06/0.98  --stats_out                             all
% 3.06/0.98  
% 3.06/0.98  ------ General Options
% 3.06/0.98  
% 3.06/0.98  --fof                                   false
% 3.06/0.98  --time_out_real                         305.
% 3.06/0.98  --time_out_virtual                      -1.
% 3.06/0.98  --symbol_type_check                     false
% 3.06/0.98  --clausify_out                          false
% 3.06/0.98  --sig_cnt_out                           false
% 3.06/0.98  --trig_cnt_out                          false
% 3.06/0.98  --trig_cnt_out_tolerance                1.
% 3.06/0.98  --trig_cnt_out_sk_spl                   false
% 3.06/0.98  --abstr_cl_out                          false
% 3.06/0.98  
% 3.06/0.98  ------ Global Options
% 3.06/0.98  
% 3.06/0.98  --schedule                              default
% 3.06/0.98  --add_important_lit                     false
% 3.06/0.98  --prop_solver_per_cl                    1000
% 3.06/0.98  --min_unsat_core                        false
% 3.06/0.98  --soft_assumptions                      false
% 3.06/0.98  --soft_lemma_size                       3
% 3.06/0.98  --prop_impl_unit_size                   0
% 3.06/0.98  --prop_impl_unit                        []
% 3.06/0.98  --share_sel_clauses                     true
% 3.06/0.98  --reset_solvers                         false
% 3.06/0.98  --bc_imp_inh                            [conj_cone]
% 3.06/0.98  --conj_cone_tolerance                   3.
% 3.06/0.98  --extra_neg_conj                        none
% 3.06/0.98  --large_theory_mode                     true
% 3.06/0.98  --prolific_symb_bound                   200
% 3.06/0.98  --lt_threshold                          2000
% 3.06/0.98  --clause_weak_htbl                      true
% 3.06/0.98  --gc_record_bc_elim                     false
% 3.06/0.98  
% 3.06/0.98  ------ Preprocessing Options
% 3.06/0.98  
% 3.06/0.98  --preprocessing_flag                    true
% 3.06/0.98  --time_out_prep_mult                    0.1
% 3.06/0.98  --splitting_mode                        input
% 3.06/0.98  --splitting_grd                         true
% 3.06/0.98  --splitting_cvd                         false
% 3.06/0.98  --splitting_cvd_svl                     false
% 3.06/0.98  --splitting_nvd                         32
% 3.06/0.98  --sub_typing                            true
% 3.06/0.98  --prep_gs_sim                           true
% 3.06/0.98  --prep_unflatten                        true
% 3.06/0.98  --prep_res_sim                          true
% 3.06/0.98  --prep_upred                            true
% 3.06/0.98  --prep_sem_filter                       exhaustive
% 3.06/0.98  --prep_sem_filter_out                   false
% 3.06/0.98  --pred_elim                             true
% 3.06/0.98  --res_sim_input                         true
% 3.06/0.98  --eq_ax_congr_red                       true
% 3.06/0.98  --pure_diseq_elim                       true
% 3.06/0.98  --brand_transform                       false
% 3.06/0.98  --non_eq_to_eq                          false
% 3.06/0.98  --prep_def_merge                        true
% 3.06/0.98  --prep_def_merge_prop_impl              false
% 3.06/0.98  --prep_def_merge_mbd                    true
% 3.06/0.98  --prep_def_merge_tr_red                 false
% 3.06/0.98  --prep_def_merge_tr_cl                  false
% 3.06/0.98  --smt_preprocessing                     true
% 3.06/0.98  --smt_ac_axioms                         fast
% 3.06/0.98  --preprocessed_out                      false
% 3.06/0.98  --preprocessed_stats                    false
% 3.06/0.98  
% 3.06/0.98  ------ Abstraction refinement Options
% 3.06/0.98  
% 3.06/0.98  --abstr_ref                             []
% 3.06/0.98  --abstr_ref_prep                        false
% 3.06/0.98  --abstr_ref_until_sat                   false
% 3.06/0.98  --abstr_ref_sig_restrict                funpre
% 3.06/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.06/0.98  --abstr_ref_under                       []
% 3.06/0.98  
% 3.06/0.98  ------ SAT Options
% 3.06/0.98  
% 3.06/0.98  --sat_mode                              false
% 3.06/0.98  --sat_fm_restart_options                ""
% 3.06/0.98  --sat_gr_def                            false
% 3.06/0.98  --sat_epr_types                         true
% 3.06/0.98  --sat_non_cyclic_types                  false
% 3.06/0.98  --sat_finite_models                     false
% 3.06/0.98  --sat_fm_lemmas                         false
% 3.06/0.98  --sat_fm_prep                           false
% 3.06/0.98  --sat_fm_uc_incr                        true
% 3.06/0.98  --sat_out_model                         small
% 3.06/0.98  --sat_out_clauses                       false
% 3.06/0.98  
% 3.06/0.98  ------ QBF Options
% 3.06/0.98  
% 3.06/0.98  --qbf_mode                              false
% 3.06/0.98  --qbf_elim_univ                         false
% 3.06/0.98  --qbf_dom_inst                          none
% 3.06/0.98  --qbf_dom_pre_inst                      false
% 3.06/0.98  --qbf_sk_in                             false
% 3.06/0.98  --qbf_pred_elim                         true
% 3.06/0.98  --qbf_split                             512
% 3.06/0.98  
% 3.06/0.98  ------ BMC1 Options
% 3.06/0.98  
% 3.06/0.98  --bmc1_incremental                      false
% 3.06/0.98  --bmc1_axioms                           reachable_all
% 3.06/0.98  --bmc1_min_bound                        0
% 3.06/0.98  --bmc1_max_bound                        -1
% 3.06/0.98  --bmc1_max_bound_default                -1
% 3.06/0.98  --bmc1_symbol_reachability              true
% 3.06/0.98  --bmc1_property_lemmas                  false
% 3.06/0.98  --bmc1_k_induction                      false
% 3.06/0.98  --bmc1_non_equiv_states                 false
% 3.06/0.98  --bmc1_deadlock                         false
% 3.06/0.98  --bmc1_ucm                              false
% 3.06/0.98  --bmc1_add_unsat_core                   none
% 3.06/0.98  --bmc1_unsat_core_children              false
% 3.06/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.06/0.98  --bmc1_out_stat                         full
% 3.06/0.98  --bmc1_ground_init                      false
% 3.06/0.98  --bmc1_pre_inst_next_state              false
% 3.06/0.98  --bmc1_pre_inst_state                   false
% 3.06/0.98  --bmc1_pre_inst_reach_state             false
% 3.06/0.98  --bmc1_out_unsat_core                   false
% 3.06/0.98  --bmc1_aig_witness_out                  false
% 3.06/0.98  --bmc1_verbose                          false
% 3.06/0.98  --bmc1_dump_clauses_tptp                false
% 3.06/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.06/0.98  --bmc1_dump_file                        -
% 3.06/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.06/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.06/0.98  --bmc1_ucm_extend_mode                  1
% 3.06/0.98  --bmc1_ucm_init_mode                    2
% 3.06/0.98  --bmc1_ucm_cone_mode                    none
% 3.06/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.06/0.98  --bmc1_ucm_relax_model                  4
% 3.06/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.06/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.06/0.98  --bmc1_ucm_layered_model                none
% 3.06/0.98  --bmc1_ucm_max_lemma_size               10
% 3.06/0.98  
% 3.06/0.98  ------ AIG Options
% 3.06/0.98  
% 3.06/0.98  --aig_mode                              false
% 3.06/0.98  
% 3.06/0.98  ------ Instantiation Options
% 3.06/0.98  
% 3.06/0.98  --instantiation_flag                    true
% 3.06/0.98  --inst_sos_flag                         false
% 3.06/0.98  --inst_sos_phase                        true
% 3.06/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.06/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.06/0.98  --inst_lit_sel_side                     none
% 3.06/0.98  --inst_solver_per_active                1400
% 3.06/0.98  --inst_solver_calls_frac                1.
% 3.06/0.98  --inst_passive_queue_type               priority_queues
% 3.06/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.06/0.98  --inst_passive_queues_freq              [25;2]
% 3.06/0.98  --inst_dismatching                      true
% 3.06/0.98  --inst_eager_unprocessed_to_passive     true
% 3.06/0.98  --inst_prop_sim_given                   true
% 3.06/0.98  --inst_prop_sim_new                     false
% 3.06/0.98  --inst_subs_new                         false
% 3.06/0.98  --inst_eq_res_simp                      false
% 3.06/0.98  --inst_subs_given                       false
% 3.06/0.98  --inst_orphan_elimination               true
% 3.06/0.98  --inst_learning_loop_flag               true
% 3.06/0.98  --inst_learning_start                   3000
% 3.06/0.98  --inst_learning_factor                  2
% 3.06/0.98  --inst_start_prop_sim_after_learn       3
% 3.06/0.98  --inst_sel_renew                        solver
% 3.06/0.98  --inst_lit_activity_flag                true
% 3.06/0.98  --inst_restr_to_given                   false
% 3.06/0.98  --inst_activity_threshold               500
% 3.06/0.98  --inst_out_proof                        true
% 3.06/0.98  
% 3.06/0.98  ------ Resolution Options
% 3.06/0.98  
% 3.06/0.98  --resolution_flag                       false
% 3.06/0.98  --res_lit_sel                           adaptive
% 3.06/0.98  --res_lit_sel_side                      none
% 3.06/0.98  --res_ordering                          kbo
% 3.06/0.98  --res_to_prop_solver                    active
% 3.06/0.98  --res_prop_simpl_new                    false
% 3.06/0.98  --res_prop_simpl_given                  true
% 3.06/0.98  --res_passive_queue_type                priority_queues
% 3.06/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.06/0.98  --res_passive_queues_freq               [15;5]
% 3.06/0.98  --res_forward_subs                      full
% 3.06/0.98  --res_backward_subs                     full
% 3.06/0.98  --res_forward_subs_resolution           true
% 3.06/0.98  --res_backward_subs_resolution          true
% 3.06/0.98  --res_orphan_elimination                true
% 3.06/0.98  --res_time_limit                        2.
% 3.06/0.98  --res_out_proof                         true
% 3.06/0.98  
% 3.06/0.98  ------ Superposition Options
% 3.06/0.98  
% 3.06/0.98  --superposition_flag                    true
% 3.06/0.98  --sup_passive_queue_type                priority_queues
% 3.06/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.06/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.06/0.98  --demod_completeness_check              fast
% 3.06/0.98  --demod_use_ground                      true
% 3.06/0.98  --sup_to_prop_solver                    passive
% 3.06/0.98  --sup_prop_simpl_new                    true
% 3.06/0.98  --sup_prop_simpl_given                  true
% 3.06/0.98  --sup_fun_splitting                     false
% 3.06/0.98  --sup_smt_interval                      50000
% 3.06/0.98  
% 3.06/0.98  ------ Superposition Simplification Setup
% 3.06/0.98  
% 3.06/0.98  --sup_indices_passive                   []
% 3.06/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.06/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.06/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.06/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.06/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.06/0.98  --sup_full_bw                           [BwDemod]
% 3.06/0.98  --sup_immed_triv                        [TrivRules]
% 3.06/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.06/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.06/0.98  --sup_immed_bw_main                     []
% 3.06/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.06/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.06/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.06/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.06/0.98  
% 3.06/0.98  ------ Combination Options
% 3.06/0.98  
% 3.06/0.98  --comb_res_mult                         3
% 3.06/0.98  --comb_sup_mult                         2
% 3.06/0.98  --comb_inst_mult                        10
% 3.06/0.98  
% 3.06/0.98  ------ Debug Options
% 3.06/0.98  
% 3.06/0.98  --dbg_backtrace                         false
% 3.06/0.98  --dbg_dump_prop_clauses                 false
% 3.06/0.98  --dbg_dump_prop_clauses_file            -
% 3.06/0.98  --dbg_out_stat                          false
% 3.06/0.98  
% 3.06/0.98  
% 3.06/0.98  
% 3.06/0.98  
% 3.06/0.98  ------ Proving...
% 3.06/0.98  
% 3.06/0.98  
% 3.06/0.98  % SZS status Theorem for theBenchmark.p
% 3.06/0.98  
% 3.06/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.06/0.98  
% 3.06/0.98  fof(f18,conjecture,(
% 3.06/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.06/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/0.98  
% 3.06/0.98  fof(f19,negated_conjecture,(
% 3.06/0.98    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.06/0.98    inference(negated_conjecture,[],[f18])).
% 3.06/0.98  
% 3.06/0.98  fof(f34,plain,(
% 3.06/0.98    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.06/0.98    inference(ennf_transformation,[],[f19])).
% 3.06/0.98  
% 3.06/0.98  fof(f35,plain,(
% 3.06/0.98    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.06/0.98    inference(flattening,[],[f34])).
% 3.06/0.98  
% 3.06/0.98  fof(f44,plain,(
% 3.06/0.98    ( ! [X2,X0,X1] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((~v2_funct_2(sK3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 3.06/0.98    introduced(choice_axiom,[])).
% 3.06/0.98  
% 3.06/0.98  fof(f43,plain,(
% 3.06/0.98    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 3.06/0.98    introduced(choice_axiom,[])).
% 3.06/0.98  
% 3.06/0.98  fof(f45,plain,(
% 3.06/0.98    ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 3.06/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f35,f44,f43])).
% 3.06/0.98  
% 3.06/0.98  fof(f77,plain,(
% 3.06/0.98    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 3.06/0.98    inference(cnf_transformation,[],[f45])).
% 3.06/0.98  
% 3.06/0.98  fof(f4,axiom,(
% 3.06/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.06/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/0.98  
% 3.06/0.98  fof(f40,plain,(
% 3.06/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.06/0.98    inference(nnf_transformation,[],[f4])).
% 3.06/0.98  
% 3.06/0.98  fof(f53,plain,(
% 3.06/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.06/0.98    inference(cnf_transformation,[],[f40])).
% 3.06/0.98  
% 3.06/0.98  fof(f5,axiom,(
% 3.06/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.06/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/0.98  
% 3.06/0.98  fof(f21,plain,(
% 3.06/0.98    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.06/0.98    inference(ennf_transformation,[],[f5])).
% 3.06/0.98  
% 3.06/0.98  fof(f55,plain,(
% 3.06/0.98    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.06/0.98    inference(cnf_transformation,[],[f21])).
% 3.06/0.98  
% 3.06/0.98  fof(f54,plain,(
% 3.06/0.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.06/0.98    inference(cnf_transformation,[],[f40])).
% 3.06/0.98  
% 3.06/0.98  fof(f6,axiom,(
% 3.06/0.98    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.06/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/0.98  
% 3.06/0.98  fof(f56,plain,(
% 3.06/0.98    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.06/0.98    inference(cnf_transformation,[],[f6])).
% 3.06/0.98  
% 3.06/0.98  fof(f14,axiom,(
% 3.06/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 3.06/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/0.98  
% 3.06/0.98  fof(f28,plain,(
% 3.06/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.06/0.98    inference(ennf_transformation,[],[f14])).
% 3.06/0.98  
% 3.06/0.98  fof(f29,plain,(
% 3.06/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.06/0.98    inference(flattening,[],[f28])).
% 3.06/0.98  
% 3.06/0.98  fof(f67,plain,(
% 3.06/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.06/0.98    inference(cnf_transformation,[],[f29])).
% 3.06/0.98  
% 3.06/0.98  fof(f11,axiom,(
% 3.06/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.06/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/0.98  
% 3.06/0.98  fof(f24,plain,(
% 3.06/0.98    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.06/0.98    inference(ennf_transformation,[],[f11])).
% 3.06/0.98  
% 3.06/0.98  fof(f25,plain,(
% 3.06/0.98    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.06/0.98    inference(flattening,[],[f24])).
% 3.06/0.98  
% 3.06/0.98  fof(f41,plain,(
% 3.06/0.98    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.06/0.98    inference(nnf_transformation,[],[f25])).
% 3.06/0.98  
% 3.06/0.98  fof(f61,plain,(
% 3.06/0.98    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.06/0.98    inference(cnf_transformation,[],[f41])).
% 3.06/0.98  
% 3.06/0.98  fof(f78,plain,(
% 3.06/0.98    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 3.06/0.98    inference(cnf_transformation,[],[f45])).
% 3.06/0.98  
% 3.06/0.98  fof(f12,axiom,(
% 3.06/0.98    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.06/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/0.98  
% 3.06/0.98  fof(f63,plain,(
% 3.06/0.98    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.06/0.98    inference(cnf_transformation,[],[f12])).
% 3.06/0.98  
% 3.06/0.98  fof(f15,axiom,(
% 3.06/0.98    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.06/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/0.98  
% 3.06/0.98  fof(f68,plain,(
% 3.06/0.98    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.06/0.98    inference(cnf_transformation,[],[f15])).
% 3.06/0.98  
% 3.06/0.98  fof(f82,plain,(
% 3.06/0.98    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.06/0.98    inference(definition_unfolding,[],[f63,f68])).
% 3.06/0.98  
% 3.06/0.98  fof(f72,plain,(
% 3.06/0.98    v1_funct_1(sK2)),
% 3.06/0.98    inference(cnf_transformation,[],[f45])).
% 3.06/0.98  
% 3.06/0.98  fof(f74,plain,(
% 3.06/0.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.06/0.98    inference(cnf_transformation,[],[f45])).
% 3.06/0.98  
% 3.06/0.98  fof(f75,plain,(
% 3.06/0.98    v1_funct_1(sK3)),
% 3.06/0.98    inference(cnf_transformation,[],[f45])).
% 3.06/0.98  
% 3.06/0.98  fof(f17,axiom,(
% 3.06/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 3.06/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/0.98  
% 3.06/0.98  fof(f32,plain,(
% 3.06/0.98    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.06/0.98    inference(ennf_transformation,[],[f17])).
% 3.06/0.98  
% 3.06/0.98  fof(f33,plain,(
% 3.06/0.98    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.06/0.98    inference(flattening,[],[f32])).
% 3.06/0.98  
% 3.06/0.98  fof(f70,plain,(
% 3.06/0.98    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X3) | k1_xboole_0 = X2 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.06/0.98    inference(cnf_transformation,[],[f33])).
% 3.06/0.98  
% 3.06/0.98  fof(f73,plain,(
% 3.06/0.98    v1_funct_2(sK2,sK0,sK1)),
% 3.06/0.98    inference(cnf_transformation,[],[f45])).
% 3.06/0.98  
% 3.06/0.98  fof(f76,plain,(
% 3.06/0.98    v1_funct_2(sK3,sK1,sK0)),
% 3.06/0.98    inference(cnf_transformation,[],[f45])).
% 3.06/0.98  
% 3.06/0.98  fof(f8,axiom,(
% 3.06/0.98    ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 3.06/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/0.98  
% 3.06/0.98  fof(f58,plain,(
% 3.06/0.98    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 3.06/0.98    inference(cnf_transformation,[],[f8])).
% 3.06/0.98  
% 3.06/0.98  fof(f81,plain,(
% 3.06/0.98    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 3.06/0.98    inference(definition_unfolding,[],[f58,f68])).
% 3.06/0.98  
% 3.06/0.98  fof(f10,axiom,(
% 3.06/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 3.06/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/0.98  
% 3.06/0.98  fof(f23,plain,(
% 3.06/0.98    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.06/0.98    inference(ennf_transformation,[],[f10])).
% 3.06/0.98  
% 3.06/0.98  fof(f60,plain,(
% 3.06/0.98    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.06/0.98    inference(cnf_transformation,[],[f23])).
% 3.06/0.98  
% 3.06/0.98  fof(f16,axiom,(
% 3.06/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 3.06/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/0.98  
% 3.06/0.98  fof(f30,plain,(
% 3.06/0.98    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.06/0.98    inference(ennf_transformation,[],[f16])).
% 3.06/0.98  
% 3.06/0.98  fof(f31,plain,(
% 3.06/0.98    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.06/0.98    inference(flattening,[],[f30])).
% 3.06/0.98  
% 3.06/0.98  fof(f69,plain,(
% 3.06/0.98    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.06/0.98    inference(cnf_transformation,[],[f31])).
% 3.06/0.98  
% 3.06/0.98  fof(f9,axiom,(
% 3.06/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.06/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/0.98  
% 3.06/0.98  fof(f20,plain,(
% 3.06/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.06/0.98    inference(pure_predicate_removal,[],[f9])).
% 3.06/0.98  
% 3.06/0.98  fof(f22,plain,(
% 3.06/0.98    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.06/0.98    inference(ennf_transformation,[],[f20])).
% 3.06/0.98  
% 3.06/0.98  fof(f59,plain,(
% 3.06/0.98    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.06/0.98    inference(cnf_transformation,[],[f22])).
% 3.06/0.98  
% 3.06/0.98  fof(f13,axiom,(
% 3.06/0.98    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.06/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/0.98  
% 3.06/0.98  fof(f26,plain,(
% 3.06/0.98    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.06/0.98    inference(ennf_transformation,[],[f13])).
% 3.06/0.98  
% 3.06/0.98  fof(f27,plain,(
% 3.06/0.98    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.06/0.98    inference(flattening,[],[f26])).
% 3.06/0.98  
% 3.06/0.98  fof(f42,plain,(
% 3.06/0.98    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.06/0.98    inference(nnf_transformation,[],[f27])).
% 3.06/0.98  
% 3.06/0.98  fof(f65,plain,(
% 3.06/0.98    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.06/0.98    inference(cnf_transformation,[],[f42])).
% 3.06/0.98  
% 3.06/0.98  fof(f88,plain,(
% 3.06/0.98    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.06/0.98    inference(equality_resolution,[],[f65])).
% 3.06/0.98  
% 3.06/0.98  fof(f79,plain,(
% 3.06/0.98    ~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)),
% 3.06/0.98    inference(cnf_transformation,[],[f45])).
% 3.06/0.98  
% 3.06/0.98  fof(f3,axiom,(
% 3.06/0.98    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.06/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/0.98  
% 3.06/0.98  fof(f38,plain,(
% 3.06/0.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.06/0.98    inference(nnf_transformation,[],[f3])).
% 3.06/0.98  
% 3.06/0.98  fof(f39,plain,(
% 3.06/0.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.06/0.98    inference(flattening,[],[f38])).
% 3.06/0.98  
% 3.06/0.98  fof(f51,plain,(
% 3.06/0.98    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.06/0.98    inference(cnf_transformation,[],[f39])).
% 3.06/0.98  
% 3.06/0.98  fof(f86,plain,(
% 3.06/0.98    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.06/0.98    inference(equality_resolution,[],[f51])).
% 3.06/0.98  
% 3.06/0.98  fof(f1,axiom,(
% 3.06/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.06/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/0.98  
% 3.06/0.98  fof(f36,plain,(
% 3.06/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.06/0.98    inference(nnf_transformation,[],[f1])).
% 3.06/0.98  
% 3.06/0.98  fof(f37,plain,(
% 3.06/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.06/0.98    inference(flattening,[],[f36])).
% 3.06/0.98  
% 3.06/0.98  fof(f48,plain,(
% 3.06/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.06/0.98    inference(cnf_transformation,[],[f37])).
% 3.06/0.98  
% 3.06/0.98  fof(f2,axiom,(
% 3.06/0.98    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.06/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/0.98  
% 3.06/0.98  fof(f49,plain,(
% 3.06/0.98    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.06/0.98    inference(cnf_transformation,[],[f2])).
% 3.06/0.98  
% 3.06/0.98  fof(f50,plain,(
% 3.06/0.98    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.06/0.98    inference(cnf_transformation,[],[f39])).
% 3.06/0.98  
% 3.06/0.98  fof(f7,axiom,(
% 3.06/0.98    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 3.06/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/0.98  
% 3.06/0.98  fof(f57,plain,(
% 3.06/0.98    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 3.06/0.98    inference(cnf_transformation,[],[f7])).
% 3.06/0.98  
% 3.06/0.98  fof(f80,plain,(
% 3.06/0.98    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 3.06/0.98    inference(definition_unfolding,[],[f57,f68])).
% 3.06/0.98  
% 3.06/0.98  cnf(c_27,negated_conjecture,
% 3.06/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 3.06/0.98      inference(cnf_transformation,[],[f77]) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_1498,plain,
% 3.06/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.06/0.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_8,plain,
% 3.06/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.06/0.98      inference(cnf_transformation,[],[f53]) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_1507,plain,
% 3.06/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.06/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 3.06/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_2667,plain,
% 3.06/0.98      ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK0)) = iProver_top ),
% 3.06/0.98      inference(superposition,[status(thm)],[c_1498,c_1507]) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_9,plain,
% 3.06/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.06/0.98      | ~ v1_relat_1(X1)
% 3.06/0.98      | v1_relat_1(X0) ),
% 3.06/0.98      inference(cnf_transformation,[],[f55]) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_7,plain,
% 3.06/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.06/0.98      inference(cnf_transformation,[],[f54]) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_223,plain,
% 3.06/0.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.06/0.98      inference(prop_impl,[status(thm)],[c_7]) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_224,plain,
% 3.06/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.06/0.98      inference(renaming,[status(thm)],[c_223]) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_293,plain,
% 3.06/0.98      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.06/0.98      inference(bin_hyper_res,[status(thm)],[c_9,c_224]) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_1492,plain,
% 3.06/0.98      ( r1_tarski(X0,X1) != iProver_top
% 3.06/0.98      | v1_relat_1(X1) != iProver_top
% 3.06/0.98      | v1_relat_1(X0) = iProver_top ),
% 3.06/0.98      inference(predicate_to_equality,[status(thm)],[c_293]) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_4961,plain,
% 3.06/0.98      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 3.06/0.98      | v1_relat_1(sK3) = iProver_top ),
% 3.06/0.98      inference(superposition,[status(thm)],[c_2667,c_1492]) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_10,plain,
% 3.06/0.98      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.06/0.98      inference(cnf_transformation,[],[f56]) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_1506,plain,
% 3.06/0.98      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.06/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_5074,plain,
% 3.06/0.98      ( v1_relat_1(sK3) = iProver_top ),
% 3.06/0.98      inference(forward_subsumption_resolution,
% 3.06/0.98                [status(thm)],
% 3.06/0.98                [c_4961,c_1506]) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_20,plain,
% 3.06/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.06/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.06/0.98      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.06/0.98      | ~ v1_funct_1(X0)
% 3.06/0.98      | ~ v1_funct_1(X3) ),
% 3.06/0.98      inference(cnf_transformation,[],[f67]) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_1502,plain,
% 3.06/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.06/0.98      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 3.06/0.98      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 3.06/0.98      | v1_funct_1(X0) != iProver_top
% 3.06/0.98      | v1_funct_1(X3) != iProver_top ),
% 3.06/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_16,plain,
% 3.06/0.98      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.06/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.06/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.06/0.99      | X3 = X2 ),
% 3.06/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_26,negated_conjecture,
% 3.06/0.99      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 3.06/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_516,plain,
% 3.06/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.06/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.06/0.99      | X3 = X0
% 3.06/0.99      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 3.06/0.99      | k6_partfun1(sK0) != X3
% 3.06/0.99      | sK0 != X2
% 3.06/0.99      | sK0 != X1 ),
% 3.06/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_26]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_517,plain,
% 3.06/0.99      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.06/0.99      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.06/0.99      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.06/0.99      inference(unflattening,[status(thm)],[c_516]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_17,plain,
% 3.06/0.99      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.06/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_525,plain,
% 3.06/0.99      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.06/0.99      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.06/0.99      inference(forward_subsumption_resolution,
% 3.06/0.99                [status(thm)],
% 3.06/0.99                [c_517,c_17]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_1488,plain,
% 3.06/0.99      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.06/0.99      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.06/0.99      inference(predicate_to_equality,[status(thm)],[c_525]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_3900,plain,
% 3.06/0.99      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
% 3.06/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.06/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.06/0.99      | v1_funct_1(sK2) != iProver_top
% 3.06/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.06/0.99      inference(superposition,[status(thm)],[c_1502,c_1488]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_32,negated_conjecture,
% 3.06/0.99      ( v1_funct_1(sK2) ),
% 3.06/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_30,negated_conjecture,
% 3.06/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.06/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_29,negated_conjecture,
% 3.06/0.99      ( v1_funct_1(sK3) ),
% 3.06/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_1508,plain,
% 3.06/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.06/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 3.06/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_2789,plain,
% 3.06/0.99      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
% 3.06/0.99      | r1_tarski(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k2_zfmisc_1(sK0,sK0)) != iProver_top ),
% 3.06/0.99      inference(superposition,[status(thm)],[c_1508,c_1488]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_2806,plain,
% 3.06/0.99      ( ~ r1_tarski(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k2_zfmisc_1(sK0,sK0))
% 3.06/0.99      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
% 3.06/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_2789]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_1984,plain,
% 3.06/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.06/0.99      | r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
% 3.06/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_3158,plain,
% 3.06/0.99      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.06/0.99      | r1_tarski(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k2_zfmisc_1(sK0,sK0)) ),
% 3.06/0.99      inference(instantiation,[status(thm)],[c_1984]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_1825,plain,
% 3.06/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.06/0.99      | m1_subset_1(k1_partfun1(X1,X2,X3,X4,X0,sK3),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
% 3.06/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 3.06/0.99      | ~ v1_funct_1(X0)
% 3.06/0.99      | ~ v1_funct_1(sK3) ),
% 3.06/0.99      inference(instantiation,[status(thm)],[c_20]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_2071,plain,
% 3.06/0.99      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
% 3.06/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.06/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.06/0.99      | ~ v1_funct_1(sK2)
% 3.06/0.99      | ~ v1_funct_1(sK3) ),
% 3.06/0.99      inference(instantiation,[status(thm)],[c_1825]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_2484,plain,
% 3.06/0.99      ( m1_subset_1(k1_partfun1(sK0,sK1,X0,X1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 3.06/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.06/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.06/0.99      | ~ v1_funct_1(sK2)
% 3.06/0.99      | ~ v1_funct_1(sK3) ),
% 3.06/0.99      inference(instantiation,[status(thm)],[c_2071]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_3663,plain,
% 3.06/0.99      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.06/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.06/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.06/0.99      | ~ v1_funct_1(sK2)
% 3.06/0.99      | ~ v1_funct_1(sK3) ),
% 3.06/0.99      inference(instantiation,[status(thm)],[c_2484]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_4255,plain,
% 3.06/0.99      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
% 3.06/0.99      inference(global_propositional_subsumption,
% 3.06/0.99                [status(thm)],
% 3.06/0.99                [c_3900,c_32,c_30,c_29,c_27,c_2806,c_3158,c_3663]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_24,plain,
% 3.06/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.06/0.99      | ~ v1_funct_2(X3,X4,X1)
% 3.06/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 3.06/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.06/0.99      | ~ v1_funct_1(X0)
% 3.06/0.99      | ~ v1_funct_1(X3)
% 3.06/0.99      | v2_funct_1(X3)
% 3.06/0.99      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 3.06/0.99      | k1_xboole_0 = X2 ),
% 3.06/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_1499,plain,
% 3.06/0.99      ( k1_xboole_0 = X0
% 3.06/0.99      | v1_funct_2(X1,X2,X0) != iProver_top
% 3.06/0.99      | v1_funct_2(X3,X4,X2) != iProver_top
% 3.06/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
% 3.06/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 3.06/0.99      | v1_funct_1(X1) != iProver_top
% 3.06/0.99      | v1_funct_1(X3) != iProver_top
% 3.06/0.99      | v2_funct_1(X3) = iProver_top
% 3.06/0.99      | v2_funct_1(k1_partfun1(X4,X2,X2,X0,X3,X1)) != iProver_top ),
% 3.06/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_4282,plain,
% 3.06/0.99      ( sK0 = k1_xboole_0
% 3.06/0.99      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 3.06/0.99      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 3.06/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.06/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.06/0.99      | v1_funct_1(sK2) != iProver_top
% 3.06/0.99      | v1_funct_1(sK3) != iProver_top
% 3.06/0.99      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 3.06/0.99      | v2_funct_1(sK2) = iProver_top ),
% 3.06/0.99      inference(superposition,[status(thm)],[c_4255,c_1499]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_33,plain,
% 3.06/0.99      ( v1_funct_1(sK2) = iProver_top ),
% 3.06/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_31,negated_conjecture,
% 3.06/0.99      ( v1_funct_2(sK2,sK0,sK1) ),
% 3.06/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_34,plain,
% 3.06/0.99      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 3.06/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_35,plain,
% 3.06/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.06/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_36,plain,
% 3.06/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 3.06/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_28,negated_conjecture,
% 3.06/0.99      ( v1_funct_2(sK3,sK1,sK0) ),
% 3.06/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_37,plain,
% 3.06/0.99      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 3.06/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_38,plain,
% 3.06/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.06/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_4406,plain,
% 3.06/0.99      ( sK0 = k1_xboole_0
% 3.06/0.99      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 3.06/0.99      | v2_funct_1(sK2) = iProver_top ),
% 3.06/0.99      inference(global_propositional_subsumption,
% 3.06/0.99                [status(thm)],
% 3.06/0.99                [c_4282,c_33,c_34,c_35,c_36,c_37,c_38]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_12,plain,
% 3.06/0.99      ( v2_funct_1(k6_partfun1(X0)) ),
% 3.06/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_1505,plain,
% 3.06/0.99      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 3.06/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_4413,plain,
% 3.06/0.99      ( sK0 = k1_xboole_0 | v2_funct_1(sK2) = iProver_top ),
% 3.06/0.99      inference(forward_subsumption_resolution,
% 3.06/0.99                [status(thm)],
% 3.06/0.99                [c_4406,c_1505]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_14,plain,
% 3.06/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.06/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.06/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_1504,plain,
% 3.06/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.06/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.06/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_3067,plain,
% 3.06/0.99      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 3.06/0.99      inference(superposition,[status(thm)],[c_1498,c_1504]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_22,plain,
% 3.06/0.99      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.06/0.99      | ~ v1_funct_2(X2,X0,X1)
% 3.06/0.99      | ~ v1_funct_2(X3,X1,X0)
% 3.06/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.06/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.06/0.99      | ~ v1_funct_1(X2)
% 3.06/0.99      | ~ v1_funct_1(X3)
% 3.06/0.99      | k2_relset_1(X1,X0,X3) = X0 ),
% 3.06/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_529,plain,
% 3.06/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.06/0.99      | ~ v1_funct_2(X3,X2,X1)
% 3.06/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.06/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.06/0.99      | ~ v1_funct_1(X0)
% 3.06/0.99      | ~ v1_funct_1(X3)
% 3.06/0.99      | k1_partfun1(X2,X1,X1,X2,X3,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.06/0.99      | k2_relset_1(X1,X2,X0) = X2
% 3.06/0.99      | k6_partfun1(X2) != k6_partfun1(sK0)
% 3.06/0.99      | sK0 != X2 ),
% 3.06/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_26]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_530,plain,
% 3.06/0.99      ( ~ v1_funct_2(X0,X1,sK0)
% 3.06/0.99      | ~ v1_funct_2(X2,sK0,X1)
% 3.06/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 3.06/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 3.06/0.99      | ~ v1_funct_1(X0)
% 3.06/0.99      | ~ v1_funct_1(X2)
% 3.06/0.99      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.06/0.99      | k2_relset_1(X1,sK0,X0) = sK0
% 3.06/0.99      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 3.06/0.99      inference(unflattening,[status(thm)],[c_529]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_608,plain,
% 3.06/0.99      ( ~ v1_funct_2(X0,X1,sK0)
% 3.06/0.99      | ~ v1_funct_2(X2,sK0,X1)
% 3.06/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 3.06/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 3.06/0.99      | ~ v1_funct_1(X0)
% 3.06/0.99      | ~ v1_funct_1(X2)
% 3.06/0.99      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.06/0.99      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 3.06/0.99      inference(equality_resolution_simp,[status(thm)],[c_530]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_1487,plain,
% 3.06/0.99      ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.06/0.99      | k2_relset_1(X0,sK0,X2) = sK0
% 3.06/0.99      | v1_funct_2(X2,X0,sK0) != iProver_top
% 3.06/0.99      | v1_funct_2(X1,sK0,X0) != iProver_top
% 3.06/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 3.06/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 3.06/0.99      | v1_funct_1(X2) != iProver_top
% 3.06/0.99      | v1_funct_1(X1) != iProver_top ),
% 3.06/0.99      inference(predicate_to_equality,[status(thm)],[c_608]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_2256,plain,
% 3.06/0.99      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 3.06/0.99      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 3.06/0.99      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 3.06/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.06/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.06/0.99      | v1_funct_1(sK2) != iProver_top
% 3.06/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.06/0.99      inference(equality_resolution,[status(thm)],[c_1487]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_2347,plain,
% 3.06/0.99      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 3.06/0.99      inference(global_propositional_subsumption,
% 3.06/0.99                [status(thm)],
% 3.06/0.99                [c_2256,c_33,c_34,c_35,c_36,c_37,c_38]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_3082,plain,
% 3.06/0.99      ( k2_relat_1(sK3) = sK0 ),
% 3.06/0.99      inference(light_normalisation,[status(thm)],[c_3067,c_2347]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_13,plain,
% 3.06/0.99      ( v5_relat_1(X0,X1)
% 3.06/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.06/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_18,plain,
% 3.06/0.99      ( v2_funct_2(X0,k2_relat_1(X0))
% 3.06/0.99      | ~ v5_relat_1(X0,k2_relat_1(X0))
% 3.06/0.99      | ~ v1_relat_1(X0) ),
% 3.06/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_25,negated_conjecture,
% 3.06/0.99      ( ~ v2_funct_2(sK3,sK0) | ~ v2_funct_1(sK2) ),
% 3.06/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_435,plain,
% 3.06/0.99      ( ~ v5_relat_1(X0,k2_relat_1(X0))
% 3.06/0.99      | ~ v2_funct_1(sK2)
% 3.06/0.99      | ~ v1_relat_1(X0)
% 3.06/0.99      | k2_relat_1(X0) != sK0
% 3.06/0.99      | sK3 != X0 ),
% 3.06/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_25]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_436,plain,
% 3.06/0.99      ( ~ v5_relat_1(sK3,k2_relat_1(sK3))
% 3.06/0.99      | ~ v2_funct_1(sK2)
% 3.06/0.99      | ~ v1_relat_1(sK3)
% 3.06/0.99      | k2_relat_1(sK3) != sK0 ),
% 3.06/0.99      inference(unflattening,[status(thm)],[c_435]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_456,plain,
% 3.06/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.06/0.99      | ~ v2_funct_1(sK2)
% 3.06/0.99      | ~ v1_relat_1(sK3)
% 3.06/0.99      | k2_relat_1(sK3) != X2
% 3.06/0.99      | k2_relat_1(sK3) != sK0
% 3.06/0.99      | sK3 != X0 ),
% 3.06/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_436]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_457,plain,
% 3.06/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3))))
% 3.06/0.99      | ~ v2_funct_1(sK2)
% 3.06/0.99      | ~ v1_relat_1(sK3)
% 3.06/0.99      | k2_relat_1(sK3) != sK0 ),
% 3.06/0.99      inference(unflattening,[status(thm)],[c_456]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_818,plain,
% 3.06/0.99      ( ~ v2_funct_1(sK2)
% 3.06/0.99      | ~ v1_relat_1(sK3)
% 3.06/0.99      | sP0_iProver_split
% 3.06/0.99      | k2_relat_1(sK3) != sK0 ),
% 3.06/0.99      inference(splitting,
% 3.06/0.99                [splitting(split),new_symbols(definition,[])],
% 3.06/0.99                [c_457]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_1490,plain,
% 3.06/0.99      ( k2_relat_1(sK3) != sK0
% 3.06/0.99      | v2_funct_1(sK2) != iProver_top
% 3.06/0.99      | v1_relat_1(sK3) != iProver_top
% 3.06/0.99      | sP0_iProver_split = iProver_top ),
% 3.06/0.99      inference(predicate_to_equality,[status(thm)],[c_818]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_3395,plain,
% 3.06/0.99      ( sK0 != sK0
% 3.06/0.99      | v2_funct_1(sK2) != iProver_top
% 3.06/0.99      | v1_relat_1(sK3) != iProver_top
% 3.06/0.99      | sP0_iProver_split = iProver_top ),
% 3.06/0.99      inference(demodulation,[status(thm)],[c_3082,c_1490]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_3401,plain,
% 3.06/0.99      ( v2_funct_1(sK2) != iProver_top
% 3.06/0.99      | v1_relat_1(sK3) != iProver_top
% 3.06/0.99      | sP0_iProver_split = iProver_top ),
% 3.06/0.99      inference(equality_resolution_simp,[status(thm)],[c_3395]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_817,plain,
% 3.06/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3))))
% 3.06/0.99      | ~ sP0_iProver_split ),
% 3.06/0.99      inference(splitting,
% 3.06/0.99                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 3.06/0.99                [c_457]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_1491,plain,
% 3.06/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3)))) != iProver_top
% 3.06/0.99      | sP0_iProver_split != iProver_top ),
% 3.06/0.99      inference(predicate_to_equality,[status(thm)],[c_817]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_2788,plain,
% 3.06/0.99      ( r1_tarski(sK3,k2_zfmisc_1(X0,k2_relat_1(sK3))) != iProver_top
% 3.06/0.99      | sP0_iProver_split != iProver_top ),
% 3.06/0.99      inference(superposition,[status(thm)],[c_1508,c_1491]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_3394,plain,
% 3.06/0.99      ( r1_tarski(sK3,k2_zfmisc_1(X0,sK0)) != iProver_top
% 3.06/0.99      | sP0_iProver_split != iProver_top ),
% 3.06/0.99      inference(demodulation,[status(thm)],[c_3082,c_2788]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_3746,plain,
% 3.06/0.99      ( sP0_iProver_split != iProver_top ),
% 3.06/0.99      inference(superposition,[status(thm)],[c_2667,c_3394]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_3818,plain,
% 3.06/0.99      ( v1_relat_1(sK3) != iProver_top | v2_funct_1(sK2) != iProver_top ),
% 3.06/0.99      inference(global_propositional_subsumption,
% 3.06/0.99                [status(thm)],
% 3.06/0.99                [c_3401,c_3746]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_3819,plain,
% 3.06/0.99      ( v2_funct_1(sK2) != iProver_top | v1_relat_1(sK3) != iProver_top ),
% 3.06/0.99      inference(renaming,[status(thm)],[c_3818]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_4415,plain,
% 3.06/0.99      ( sK0 = k1_xboole_0 | v1_relat_1(sK3) != iProver_top ),
% 3.06/0.99      inference(superposition,[status(thm)],[c_4413,c_3819]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_5076,plain,
% 3.06/0.99      ( sK0 = k1_xboole_0 ),
% 3.06/0.99      inference(superposition,[status(thm)],[c_5074,c_4415]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_1495,plain,
% 3.06/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.06/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_5157,plain,
% 3.06/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) = iProver_top ),
% 3.06/0.99      inference(demodulation,[status(thm)],[c_5076,c_1495]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_5,plain,
% 3.06/0.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.06/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_5165,plain,
% 3.06/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.06/0.99      inference(demodulation,[status(thm)],[c_5157,c_5]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_2761,plain,
% 3.06/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0)) | r1_tarski(sK2,X0) ),
% 3.06/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_2762,plain,
% 3.06/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top
% 3.06/0.99      | r1_tarski(sK2,X0) = iProver_top ),
% 3.06/0.99      inference(predicate_to_equality,[status(thm)],[c_2761]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_2764,plain,
% 3.06/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.06/0.99      | r1_tarski(sK2,k1_xboole_0) = iProver_top ),
% 3.06/0.99      inference(instantiation,[status(thm)],[c_2762]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_828,plain,
% 3.06/0.99      ( ~ v2_funct_1(X0) | v2_funct_1(X1) | X1 != X0 ),
% 3.06/0.99      theory(equality) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_2517,plain,
% 3.06/0.99      ( ~ v2_funct_1(X0) | v2_funct_1(sK2) | sK2 != X0 ),
% 3.06/0.99      inference(instantiation,[status(thm)],[c_828]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_2518,plain,
% 3.06/0.99      ( sK2 != X0
% 3.06/0.99      | v2_funct_1(X0) != iProver_top
% 3.06/0.99      | v2_funct_1(sK2) = iProver_top ),
% 3.06/0.99      inference(predicate_to_equality,[status(thm)],[c_2517]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_2520,plain,
% 3.06/0.99      ( sK2 != k1_xboole_0
% 3.06/0.99      | v2_funct_1(sK2) = iProver_top
% 3.06/0.99      | v2_funct_1(k1_xboole_0) != iProver_top ),
% 3.06/0.99      inference(instantiation,[status(thm)],[c_2518]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_0,plain,
% 3.06/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.06/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_2233,plain,
% 3.06/0.99      ( ~ r1_tarski(X0,sK2) | ~ r1_tarski(sK2,X0) | sK2 = X0 ),
% 3.06/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_2234,plain,
% 3.06/0.99      ( sK2 = X0
% 3.06/0.99      | r1_tarski(X0,sK2) != iProver_top
% 3.06/0.99      | r1_tarski(sK2,X0) != iProver_top ),
% 3.06/0.99      inference(predicate_to_equality,[status(thm)],[c_2233]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_2236,plain,
% 3.06/0.99      ( sK2 = k1_xboole_0
% 3.06/0.99      | r1_tarski(sK2,k1_xboole_0) != iProver_top
% 3.06/0.99      | r1_tarski(k1_xboole_0,sK2) != iProver_top ),
% 3.06/0.99      inference(instantiation,[status(thm)],[c_2234]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_3,plain,
% 3.06/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 3.06/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_2203,plain,
% 3.06/0.99      ( r1_tarski(k1_xboole_0,sK2) ),
% 3.06/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_2206,plain,
% 3.06/0.99      ( r1_tarski(k1_xboole_0,sK2) = iProver_top ),
% 3.06/0.99      inference(predicate_to_equality,[status(thm)],[c_2203]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_821,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_1979,plain,
% 3.06/0.99      ( X0 != X1 | X0 = k6_partfun1(X2) | k6_partfun1(X2) != X1 ),
% 3.06/0.99      inference(instantiation,[status(thm)],[c_821]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_1980,plain,
% 3.06/0.99      ( k6_partfun1(k1_xboole_0) != k1_xboole_0
% 3.06/0.99      | k1_xboole_0 = k6_partfun1(k1_xboole_0)
% 3.06/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.06/0.99      inference(instantiation,[status(thm)],[c_1979]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_1752,plain,
% 3.06/0.99      ( v2_funct_1(X0)
% 3.06/0.99      | ~ v2_funct_1(k6_partfun1(X1))
% 3.06/0.99      | X0 != k6_partfun1(X1) ),
% 3.06/0.99      inference(instantiation,[status(thm)],[c_828]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_1753,plain,
% 3.06/0.99      ( X0 != k6_partfun1(X1)
% 3.06/0.99      | v2_funct_1(X0) = iProver_top
% 3.06/0.99      | v2_funct_1(k6_partfun1(X1)) != iProver_top ),
% 3.06/0.99      inference(predicate_to_equality,[status(thm)],[c_1752]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_1755,plain,
% 3.06/0.99      ( k1_xboole_0 != k6_partfun1(k1_xboole_0)
% 3.06/0.99      | v2_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top
% 3.06/0.99      | v2_funct_1(k1_xboole_0) = iProver_top ),
% 3.06/0.99      inference(instantiation,[status(thm)],[c_1753]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_91,plain,
% 3.06/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.06/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_6,plain,
% 3.06/0.99      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.06/0.99      | k1_xboole_0 = X1
% 3.06/0.99      | k1_xboole_0 = X0 ),
% 3.06/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_90,plain,
% 3.06/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.06/0.99      | k1_xboole_0 = k1_xboole_0 ),
% 3.06/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_11,plain,
% 3.06/0.99      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 3.06/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_77,plain,
% 3.06/0.99      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 3.06/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_79,plain,
% 3.06/0.99      ( v2_funct_1(k6_partfun1(k1_xboole_0)) = iProver_top ),
% 3.06/0.99      inference(instantiation,[status(thm)],[c_77]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(contradiction,plain,
% 3.06/0.99      ( $false ),
% 3.06/0.99      inference(minisat,
% 3.06/0.99                [status(thm)],
% 3.06/0.99                [c_5165,c_5074,c_3746,c_3401,c_2764,c_2520,c_2236,c_2206,
% 3.06/0.99                 c_1980,c_1755,c_91,c_90,c_11,c_79]) ).
% 3.06/0.99  
% 3.06/0.99  
% 3.06/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.06/0.99  
% 3.06/0.99  ------                               Statistics
% 3.06/0.99  
% 3.06/0.99  ------ General
% 3.06/0.99  
% 3.06/0.99  abstr_ref_over_cycles:                  0
% 3.06/0.99  abstr_ref_under_cycles:                 0
% 3.06/0.99  gc_basic_clause_elim:                   0
% 3.06/0.99  forced_gc_time:                         0
% 3.06/0.99  parsing_time:                           0.01
% 3.06/0.99  unif_index_cands_time:                  0.
% 3.06/0.99  unif_index_add_time:                    0.
% 3.06/0.99  orderings_time:                         0.
% 3.06/0.99  out_proof_time:                         0.01
% 3.06/0.99  total_time:                             0.188
% 3.06/0.99  num_of_symbols:                         52
% 3.06/0.99  num_of_terms:                           6270
% 3.06/0.99  
% 3.06/0.99  ------ Preprocessing
% 3.06/0.99  
% 3.06/0.99  num_of_splits:                          1
% 3.06/0.99  num_of_split_atoms:                     1
% 3.06/0.99  num_of_reused_defs:                     0
% 3.06/0.99  num_eq_ax_congr_red:                    12
% 3.06/0.99  num_of_sem_filtered_clauses:            1
% 3.06/0.99  num_of_subtypes:                        0
% 3.06/0.99  monotx_restored_types:                  0
% 3.06/0.99  sat_num_of_epr_types:                   0
% 3.06/0.99  sat_num_of_non_cyclic_types:            0
% 3.06/0.99  sat_guarded_non_collapsed_types:        0
% 3.06/0.99  num_pure_diseq_elim:                    0
% 3.06/0.99  simp_replaced_by:                       0
% 3.06/0.99  res_preprocessed:                       147
% 3.06/0.99  prep_upred:                             0
% 3.06/0.99  prep_unflattend:                        19
% 3.06/0.99  smt_new_axioms:                         0
% 3.06/0.99  pred_elim_cands:                        6
% 3.06/0.99  pred_elim:                              3
% 3.06/0.99  pred_elim_cl:                           4
% 3.06/0.99  pred_elim_cycles:                       6
% 3.06/0.99  merged_defs:                            8
% 3.06/0.99  merged_defs_ncl:                        0
% 3.06/0.99  bin_hyper_res:                          9
% 3.06/0.99  prep_cycles:                            4
% 3.06/0.99  pred_elim_time:                         0.006
% 3.06/0.99  splitting_time:                         0.
% 3.06/0.99  sem_filter_time:                        0.
% 3.06/0.99  monotx_time:                            0.001
% 3.06/0.99  subtype_inf_time:                       0.
% 3.06/0.99  
% 3.06/0.99  ------ Problem properties
% 3.06/0.99  
% 3.06/0.99  clauses:                                29
% 3.06/0.99  conjectures:                            6
% 3.06/0.99  epr:                                    8
% 3.06/0.99  horn:                                   27
% 3.06/0.99  ground:                                 9
% 3.06/0.99  unary:                                  14
% 3.06/0.99  binary:                                 5
% 3.06/0.99  lits:                                   80
% 3.06/0.99  lits_eq:                                15
% 3.06/0.99  fd_pure:                                0
% 3.06/0.99  fd_pseudo:                              0
% 3.06/0.99  fd_cond:                                2
% 3.06/0.99  fd_pseudo_cond:                         1
% 3.06/0.99  ac_symbols:                             0
% 3.06/0.99  
% 3.06/0.99  ------ Propositional Solver
% 3.06/0.99  
% 3.06/0.99  prop_solver_calls:                      26
% 3.06/0.99  prop_fast_solver_calls:                 1042
% 3.06/0.99  smt_solver_calls:                       0
% 3.06/0.99  smt_fast_solver_calls:                  0
% 3.06/0.99  prop_num_of_clauses:                    1814
% 3.06/0.99  prop_preprocess_simplified:             5658
% 3.06/0.99  prop_fo_subsumed:                       22
% 3.06/0.99  prop_solver_time:                       0.
% 3.06/0.99  smt_solver_time:                        0.
% 3.06/0.99  smt_fast_solver_time:                   0.
% 3.06/0.99  prop_fast_solver_time:                  0.
% 3.06/0.99  prop_unsat_core_time:                   0.
% 3.06/0.99  
% 3.06/0.99  ------ QBF
% 3.06/0.99  
% 3.06/0.99  qbf_q_res:                              0
% 3.06/0.99  qbf_num_tautologies:                    0
% 3.06/0.99  qbf_prep_cycles:                        0
% 3.06/0.99  
% 3.06/0.99  ------ BMC1
% 3.06/0.99  
% 3.06/0.99  bmc1_current_bound:                     -1
% 3.06/0.99  bmc1_last_solved_bound:                 -1
% 3.06/0.99  bmc1_unsat_core_size:                   -1
% 3.06/0.99  bmc1_unsat_core_parents_size:           -1
% 3.06/0.99  bmc1_merge_next_fun:                    0
% 3.06/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.06/0.99  
% 3.06/0.99  ------ Instantiation
% 3.06/0.99  
% 3.06/0.99  inst_num_of_clauses:                    561
% 3.06/0.99  inst_num_in_passive:                    49
% 3.06/0.99  inst_num_in_active:                     332
% 3.06/0.99  inst_num_in_unprocessed:                180
% 3.06/0.99  inst_num_of_loops:                      350
% 3.06/0.99  inst_num_of_learning_restarts:          0
% 3.06/0.99  inst_num_moves_active_passive:          15
% 3.06/0.99  inst_lit_activity:                      0
% 3.06/0.99  inst_lit_activity_moves:                0
% 3.06/0.99  inst_num_tautologies:                   0
% 3.06/0.99  inst_num_prop_implied:                  0
% 3.06/0.99  inst_num_existing_simplified:           0
% 3.06/0.99  inst_num_eq_res_simplified:             0
% 3.06/0.99  inst_num_child_elim:                    0
% 3.06/0.99  inst_num_of_dismatching_blockings:      102
% 3.06/0.99  inst_num_of_non_proper_insts:           639
% 3.06/0.99  inst_num_of_duplicates:                 0
% 3.06/0.99  inst_inst_num_from_inst_to_res:         0
% 3.06/0.99  inst_dismatching_checking_time:         0.
% 3.06/0.99  
% 3.06/0.99  ------ Resolution
% 3.06/0.99  
% 3.06/0.99  res_num_of_clauses:                     0
% 3.06/0.99  res_num_in_passive:                     0
% 3.06/0.99  res_num_in_active:                      0
% 3.06/0.99  res_num_of_loops:                       151
% 3.06/0.99  res_forward_subset_subsumed:            30
% 3.06/0.99  res_backward_subset_subsumed:           0
% 3.06/0.99  res_forward_subsumed:                   0
% 3.06/0.99  res_backward_subsumed:                  0
% 3.06/0.99  res_forward_subsumption_resolution:     2
% 3.06/0.99  res_backward_subsumption_resolution:    0
% 3.06/0.99  res_clause_to_clause_subsumption:       244
% 3.06/0.99  res_orphan_elimination:                 0
% 3.06/0.99  res_tautology_del:                      45
% 3.06/0.99  res_num_eq_res_simplified:              1
% 3.06/0.99  res_num_sel_changes:                    0
% 3.06/0.99  res_moves_from_active_to_pass:          0
% 3.06/0.99  
% 3.06/0.99  ------ Superposition
% 3.06/0.99  
% 3.06/0.99  sup_time_total:                         0.
% 3.06/0.99  sup_time_generating:                    0.
% 3.06/0.99  sup_time_sim_full:                      0.
% 3.06/0.99  sup_time_sim_immed:                     0.
% 3.06/0.99  
% 3.06/0.99  sup_num_of_clauses:                     63
% 3.06/0.99  sup_num_in_active:                      45
% 3.06/0.99  sup_num_in_passive:                     18
% 3.06/0.99  sup_num_of_loops:                       68
% 3.06/0.99  sup_fw_superposition:                   60
% 3.06/0.99  sup_bw_superposition:                   20
% 3.06/0.99  sup_immediate_simplified:               24
% 3.06/0.99  sup_given_eliminated:                   1
% 3.06/0.99  comparisons_done:                       0
% 3.06/0.99  comparisons_avoided:                    0
% 3.06/0.99  
% 3.06/0.99  ------ Simplifications
% 3.06/0.99  
% 3.06/0.99  
% 3.06/0.99  sim_fw_subset_subsumed:                 1
% 3.06/0.99  sim_bw_subset_subsumed:                 3
% 3.06/0.99  sim_fw_subsumed:                        3
% 3.06/0.99  sim_bw_subsumed:                        1
% 3.06/0.99  sim_fw_subsumption_res:                 3
% 3.06/0.99  sim_bw_subsumption_res:                 0
% 3.06/0.99  sim_tautology_del:                      2
% 3.06/0.99  sim_eq_tautology_del:                   8
% 3.06/0.99  sim_eq_res_simp:                        1
% 3.06/0.99  sim_fw_demodulated:                     13
% 3.06/0.99  sim_bw_demodulated:                     19
% 3.06/0.99  sim_light_normalised:                   11
% 3.06/0.99  sim_joinable_taut:                      0
% 3.06/0.99  sim_joinable_simp:                      0
% 3.06/0.99  sim_ac_normalised:                      0
% 3.06/0.99  sim_smt_subsumption:                    0
% 3.06/0.99  
%------------------------------------------------------------------------------

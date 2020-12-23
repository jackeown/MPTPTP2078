%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:01:55 EST 2020

% Result     : Theorem 2.97s
% Output     : CNFRefutation 2.97s
% Verified   : 
% Statistics : Number of formulae       :  162 (1241 expanded)
%              Number of clauses        :   98 ( 398 expanded)
%              Number of leaves         :   18 ( 299 expanded)
%              Depth                    :   22
%              Number of atoms          :  542 (7937 expanded)
%              Number of equality atoms :  177 ( 641 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f12,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f69,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f50,f55])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f41,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f67,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f43,f55])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f27])).

fof(f54,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f23])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f33,plain,(
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
    inference(flattening,[],[f33])).

fof(f38,plain,(
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

fof(f37,plain,
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

fof(f39,plain,
    ( ( ~ v2_funct_2(sK3,sK0)
      | ~ v2_funct_1(sK2) )
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f34,f38,f37])).

fof(f65,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f39])).

fof(f59,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f61,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f39])).

fof(f62,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f64,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f39])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
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
    inference(flattening,[],[f31])).

fof(f57,plain,(
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
    inference(cnf_transformation,[],[f32])).

fof(f60,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f63,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f39])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
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
    inference(flattening,[],[f29])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f66,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_617,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1030,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_617])).

cnf(c_10,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_612,plain,
    ( m1_subset_1(k6_partfun1(X0_48),k1_zfmisc_1(k2_zfmisc_1(X0_48,X0_48))) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1035,plain,
    ( m1_subset_1(k6_partfun1(X0_48),k1_zfmisc_1(k2_zfmisc_1(X0_48,X0_48))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_612])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_614,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | ~ v1_xboole_0(X1_48)
    | v1_xboole_0(X0_48) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1033,plain,
    ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48))) != iProver_top
    | v1_xboole_0(X1_48) != iProver_top
    | v1_xboole_0(X0_48) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_614])).

cnf(c_2023,plain,
    ( v1_xboole_0(X0_48) != iProver_top
    | v1_xboole_0(k6_partfun1(X0_48)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1035,c_1033])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_616,plain,
    ( ~ v1_xboole_0(X0_48)
    | k1_xboole_0 = X0_48 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1031,plain,
    ( k1_xboole_0 = X0_48
    | v1_xboole_0(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_616])).

cnf(c_3448,plain,
    ( k6_partfun1(X0_48) = k1_xboole_0
    | v1_xboole_0(X0_48) != iProver_top ),
    inference(superposition,[status(thm)],[c_2023,c_1031])).

cnf(c_3495,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1030,c_3448])).

cnf(c_2,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_615,plain,
    ( v2_funct_1(k6_partfun1(X0_48)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1032,plain,
    ( v2_funct_1(k6_partfun1(X0_48)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_615])).

cnf(c_3510,plain,
    ( v2_funct_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3495,c_1032])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_611,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | ~ m1_subset_1(X3_48,k1_zfmisc_1(k2_zfmisc_1(X4_48,X5_48)))
    | m1_subset_1(k1_partfun1(X4_48,X5_48,X1_48,X2_48,X3_48,X0_48),k1_zfmisc_1(k2_zfmisc_1(X4_48,X2_48)))
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(X3_48) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1036,plain,
    ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48))) != iProver_top
    | m1_subset_1(X3_48,k1_zfmisc_1(k2_zfmisc_1(X4_48,X5_48))) != iProver_top
    | m1_subset_1(k1_partfun1(X4_48,X5_48,X1_48,X2_48,X3_48,X0_48),k1_zfmisc_1(k2_zfmisc_1(X4_48,X2_48))) = iProver_top
    | v1_funct_1(X3_48) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_611])).

cnf(c_9,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_19,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_389,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_19])).

cnf(c_390,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_389])).

cnf(c_56,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_392,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_390,c_56])).

cnf(c_599,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_392])).

cnf(c_1049,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_599])).

cnf(c_2083,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1036,c_1049])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_26,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_28,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_29,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_31,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2338,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2083,c_26,c_28,c_29,c_31])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v2_funct_1(X3)
    | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_608,plain,
    ( ~ v1_funct_2(X0_48,X1_48,X2_48)
    | ~ v1_funct_2(X3_48,X4_48,X1_48)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | ~ m1_subset_1(X3_48,k1_zfmisc_1(k2_zfmisc_1(X4_48,X1_48)))
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(X3_48)
    | v2_funct_1(X3_48)
    | ~ v2_funct_1(k1_partfun1(X4_48,X1_48,X1_48,X2_48,X3_48,X0_48))
    | k1_xboole_0 = X2_48 ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1039,plain,
    ( k1_xboole_0 = X0_48
    | v1_funct_2(X1_48,X2_48,X0_48) != iProver_top
    | v1_funct_2(X3_48,X4_48,X2_48) != iProver_top
    | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_48,X0_48))) != iProver_top
    | m1_subset_1(X3_48,k1_zfmisc_1(k2_zfmisc_1(X4_48,X2_48))) != iProver_top
    | v1_funct_1(X3_48) != iProver_top
    | v1_funct_1(X1_48) != iProver_top
    | v2_funct_1(X3_48) = iProver_top
    | v2_funct_1(k1_partfun1(X4_48,X2_48,X2_48,X0_48,X3_48,X1_48)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_608])).

cnf(c_2364,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2338,c_1039])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_27,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_21,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_30,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_77,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_79,plain,
    ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_77])).

cnf(c_15,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_403,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X2,X1,X3) = X1
    | k6_partfun1(X1) != k6_partfun1(sK0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_19])).

cnf(c_404,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X0)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0
    | k6_partfun1(sK0) != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_403])).

cnf(c_478,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_404])).

cnf(c_598,plain,
    ( ~ v1_funct_2(X0_48,X1_48,sK0)
    | ~ v1_funct_2(X2_48,sK0,X1_48)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,sK0)))
    | ~ m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(sK0,X1_48)))
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(X2_48)
    | k1_partfun1(sK0,X1_48,X1_48,sK0,X2_48,X0_48) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1_48,sK0,X0_48) = sK0 ),
    inference(subtyping,[status(esa)],[c_478])).

cnf(c_1050,plain,
    ( k1_partfun1(sK0,X0_48,X0_48,sK0,X1_48,X2_48) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X0_48,sK0,X2_48) = sK0
    | v1_funct_2(X2_48,X0_48,sK0) != iProver_top
    | v1_funct_2(X1_48,sK0,X0_48) != iProver_top
    | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,sK0))) != iProver_top
    | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_48))) != iProver_top
    | v1_funct_1(X2_48) != iProver_top
    | v1_funct_1(X1_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_598])).

cnf(c_1895,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1050])).

cnf(c_607,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1040,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_607])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_613,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | k2_relset_1(X1_48,X2_48,X0_48) = k2_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1034,plain,
    ( k2_relset_1(X0_48,X1_48,X2_48) = k2_relat_1(X2_48)
    | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_613])).

cnf(c_1580,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1040,c_1034])).

cnf(c_1896,plain,
    ( k2_relat_1(sK3) = sK0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1895,c_1580])).

cnf(c_1899,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1896,c_26,c_27,c_28,c_29,c_30,c_31])).

cnf(c_5,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_11,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_307,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X0)
    | X0 != X1
    | k2_relat_1(X0) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_11])).

cnf(c_308,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_307])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_318,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0)))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_308,c_4])).

cnf(c_18,negated_conjecture,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_333,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
    | ~ v2_funct_1(sK2)
    | k2_relat_1(X0) != sK0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_318,c_18])).

cnf(c_334,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3))))
    | ~ v2_funct_1(sK2)
    | k2_relat_1(sK3) != sK0 ),
    inference(unflattening,[status(thm)],[c_333])).

cnf(c_601,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_48,k2_relat_1(sK3))))
    | ~ v2_funct_1(sK2)
    | k2_relat_1(sK3) != sK0 ),
    inference(subtyping,[status(esa)],[c_334])).

cnf(c_619,plain,
    ( ~ v2_funct_1(sK2)
    | sP0_iProver_split
    | k2_relat_1(sK3) != sK0 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_601])).

cnf(c_1046,plain,
    ( k2_relat_1(sK3) != sK0
    | v2_funct_1(sK2) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_619])).

cnf(c_1904,plain,
    ( sK0 != sK0
    | v2_funct_1(sK2) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_1899,c_1046])).

cnf(c_1905,plain,
    ( v2_funct_1(sK2) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_1904])).

cnf(c_618,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_48,k2_relat_1(sK3))))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_601])).

cnf(c_1047,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_48,k2_relat_1(sK3)))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_618])).

cnf(c_1903,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_48,sK0))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(demodulation,[status(thm)],[c_1899,c_1047])).

cnf(c_1968,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_1040,c_1903])).

cnf(c_2984,plain,
    ( sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2364,c_26,c_27,c_28,c_29,c_30,c_31,c_79,c_1905,c_1968])).

cnf(c_604,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1043,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_604])).

cnf(c_2022,plain,
    ( v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1043,c_1033])).

cnf(c_2990,plain,
    ( v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2984,c_2022])).

cnf(c_83,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_625,plain,
    ( ~ v1_xboole_0(X0_48)
    | v1_xboole_0(X1_48)
    | X1_48 != X0_48 ),
    theory(equality)).

cnf(c_1361,plain,
    ( v1_xboole_0(X0_48)
    | ~ v1_xboole_0(k1_xboole_0)
    | X0_48 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_625])).

cnf(c_1362,plain,
    ( X0_48 != k1_xboole_0
    | v1_xboole_0(X0_48) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1361])).

cnf(c_1364,plain,
    ( sK0 != k1_xboole_0
    | v1_xboole_0(sK0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1362])).

cnf(c_3132,plain,
    ( v1_xboole_0(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2990,c_26,c_27,c_28,c_29,c_30,c_31,c_79,c_83,c_1364,c_1905,c_1968,c_2022,c_2364])).

cnf(c_3137,plain,
    ( sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3132,c_1031])).

cnf(c_2401,plain,
    ( v2_funct_1(sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1905,c_1968])).

cnf(c_3143,plain,
    ( v2_funct_1(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3137,c_2401])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3510,c_3143])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:47:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 2.97/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.97/0.99  
% 2.97/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.97/0.99  
% 2.97/0.99  ------  iProver source info
% 2.97/0.99  
% 2.97/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.97/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.97/0.99  git: non_committed_changes: false
% 2.97/0.99  git: last_make_outside_of_git: false
% 2.97/0.99  
% 2.97/0.99  ------ 
% 2.97/0.99  
% 2.97/0.99  ------ Input Options
% 2.97/0.99  
% 2.97/0.99  --out_options                           all
% 2.97/0.99  --tptp_safe_out                         true
% 2.97/0.99  --problem_path                          ""
% 2.97/0.99  --include_path                          ""
% 2.97/0.99  --clausifier                            res/vclausify_rel
% 2.97/0.99  --clausifier_options                    --mode clausify
% 2.97/0.99  --stdin                                 false
% 2.97/0.99  --stats_out                             all
% 2.97/0.99  
% 2.97/0.99  ------ General Options
% 2.97/0.99  
% 2.97/0.99  --fof                                   false
% 2.97/0.99  --time_out_real                         305.
% 2.97/0.99  --time_out_virtual                      -1.
% 2.97/0.99  --symbol_type_check                     false
% 2.97/0.99  --clausify_out                          false
% 2.97/0.99  --sig_cnt_out                           false
% 2.97/0.99  --trig_cnt_out                          false
% 2.97/0.99  --trig_cnt_out_tolerance                1.
% 2.97/0.99  --trig_cnt_out_sk_spl                   false
% 2.97/0.99  --abstr_cl_out                          false
% 2.97/0.99  
% 2.97/0.99  ------ Global Options
% 2.97/0.99  
% 2.97/0.99  --schedule                              default
% 2.97/0.99  --add_important_lit                     false
% 2.97/0.99  --prop_solver_per_cl                    1000
% 2.97/0.99  --min_unsat_core                        false
% 2.97/0.99  --soft_assumptions                      false
% 2.97/0.99  --soft_lemma_size                       3
% 2.97/0.99  --prop_impl_unit_size                   0
% 2.97/0.99  --prop_impl_unit                        []
% 2.97/0.99  --share_sel_clauses                     true
% 2.97/0.99  --reset_solvers                         false
% 2.97/0.99  --bc_imp_inh                            [conj_cone]
% 2.97/0.99  --conj_cone_tolerance                   3.
% 2.97/0.99  --extra_neg_conj                        none
% 2.97/0.99  --large_theory_mode                     true
% 2.97/0.99  --prolific_symb_bound                   200
% 2.97/0.99  --lt_threshold                          2000
% 2.97/0.99  --clause_weak_htbl                      true
% 2.97/0.99  --gc_record_bc_elim                     false
% 2.97/0.99  
% 2.97/0.99  ------ Preprocessing Options
% 2.97/0.99  
% 2.97/0.99  --preprocessing_flag                    true
% 2.97/0.99  --time_out_prep_mult                    0.1
% 2.97/0.99  --splitting_mode                        input
% 2.97/0.99  --splitting_grd                         true
% 2.97/0.99  --splitting_cvd                         false
% 2.97/0.99  --splitting_cvd_svl                     false
% 2.97/0.99  --splitting_nvd                         32
% 2.97/0.99  --sub_typing                            true
% 2.97/0.99  --prep_gs_sim                           true
% 2.97/0.99  --prep_unflatten                        true
% 2.97/0.99  --prep_res_sim                          true
% 2.97/0.99  --prep_upred                            true
% 2.97/0.99  --prep_sem_filter                       exhaustive
% 2.97/0.99  --prep_sem_filter_out                   false
% 2.97/0.99  --pred_elim                             true
% 2.97/0.99  --res_sim_input                         true
% 2.97/0.99  --eq_ax_congr_red                       true
% 2.97/0.99  --pure_diseq_elim                       true
% 2.97/0.99  --brand_transform                       false
% 2.97/0.99  --non_eq_to_eq                          false
% 2.97/0.99  --prep_def_merge                        true
% 2.97/0.99  --prep_def_merge_prop_impl              false
% 2.97/0.99  --prep_def_merge_mbd                    true
% 2.97/0.99  --prep_def_merge_tr_red                 false
% 2.97/0.99  --prep_def_merge_tr_cl                  false
% 2.97/0.99  --smt_preprocessing                     true
% 2.97/0.99  --smt_ac_axioms                         fast
% 2.97/0.99  --preprocessed_out                      false
% 2.97/0.99  --preprocessed_stats                    false
% 2.97/0.99  
% 2.97/0.99  ------ Abstraction refinement Options
% 2.97/0.99  
% 2.97/0.99  --abstr_ref                             []
% 2.97/0.99  --abstr_ref_prep                        false
% 2.97/0.99  --abstr_ref_until_sat                   false
% 2.97/0.99  --abstr_ref_sig_restrict                funpre
% 2.97/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.97/0.99  --abstr_ref_under                       []
% 2.97/0.99  
% 2.97/0.99  ------ SAT Options
% 2.97/0.99  
% 2.97/0.99  --sat_mode                              false
% 2.97/0.99  --sat_fm_restart_options                ""
% 2.97/0.99  --sat_gr_def                            false
% 2.97/0.99  --sat_epr_types                         true
% 2.97/0.99  --sat_non_cyclic_types                  false
% 2.97/0.99  --sat_finite_models                     false
% 2.97/0.99  --sat_fm_lemmas                         false
% 2.97/0.99  --sat_fm_prep                           false
% 2.97/0.99  --sat_fm_uc_incr                        true
% 2.97/0.99  --sat_out_model                         small
% 2.97/0.99  --sat_out_clauses                       false
% 2.97/0.99  
% 2.97/0.99  ------ QBF Options
% 2.97/0.99  
% 2.97/0.99  --qbf_mode                              false
% 2.97/0.99  --qbf_elim_univ                         false
% 2.97/0.99  --qbf_dom_inst                          none
% 2.97/0.99  --qbf_dom_pre_inst                      false
% 2.97/0.99  --qbf_sk_in                             false
% 2.97/0.99  --qbf_pred_elim                         true
% 2.97/0.99  --qbf_split                             512
% 2.97/0.99  
% 2.97/0.99  ------ BMC1 Options
% 2.97/0.99  
% 2.97/0.99  --bmc1_incremental                      false
% 2.97/0.99  --bmc1_axioms                           reachable_all
% 2.97/0.99  --bmc1_min_bound                        0
% 2.97/0.99  --bmc1_max_bound                        -1
% 2.97/0.99  --bmc1_max_bound_default                -1
% 2.97/0.99  --bmc1_symbol_reachability              true
% 2.97/0.99  --bmc1_property_lemmas                  false
% 2.97/0.99  --bmc1_k_induction                      false
% 2.97/0.99  --bmc1_non_equiv_states                 false
% 2.97/0.99  --bmc1_deadlock                         false
% 2.97/0.99  --bmc1_ucm                              false
% 2.97/0.99  --bmc1_add_unsat_core                   none
% 2.97/0.99  --bmc1_unsat_core_children              false
% 2.97/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.97/0.99  --bmc1_out_stat                         full
% 2.97/0.99  --bmc1_ground_init                      false
% 2.97/0.99  --bmc1_pre_inst_next_state              false
% 2.97/0.99  --bmc1_pre_inst_state                   false
% 2.97/0.99  --bmc1_pre_inst_reach_state             false
% 2.97/0.99  --bmc1_out_unsat_core                   false
% 2.97/0.99  --bmc1_aig_witness_out                  false
% 2.97/0.99  --bmc1_verbose                          false
% 2.97/0.99  --bmc1_dump_clauses_tptp                false
% 2.97/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.97/0.99  --bmc1_dump_file                        -
% 2.97/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.97/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.97/0.99  --bmc1_ucm_extend_mode                  1
% 2.97/0.99  --bmc1_ucm_init_mode                    2
% 2.97/0.99  --bmc1_ucm_cone_mode                    none
% 2.97/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.97/0.99  --bmc1_ucm_relax_model                  4
% 2.97/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.97/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.97/0.99  --bmc1_ucm_layered_model                none
% 2.97/0.99  --bmc1_ucm_max_lemma_size               10
% 2.97/0.99  
% 2.97/0.99  ------ AIG Options
% 2.97/0.99  
% 2.97/0.99  --aig_mode                              false
% 2.97/0.99  
% 2.97/0.99  ------ Instantiation Options
% 2.97/0.99  
% 2.97/0.99  --instantiation_flag                    true
% 2.97/0.99  --inst_sos_flag                         false
% 2.97/0.99  --inst_sos_phase                        true
% 2.97/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.97/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.97/0.99  --inst_lit_sel_side                     num_symb
% 2.97/0.99  --inst_solver_per_active                1400
% 2.97/0.99  --inst_solver_calls_frac                1.
% 2.97/0.99  --inst_passive_queue_type               priority_queues
% 2.97/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.97/0.99  --inst_passive_queues_freq              [25;2]
% 2.97/0.99  --inst_dismatching                      true
% 2.97/0.99  --inst_eager_unprocessed_to_passive     true
% 2.97/0.99  --inst_prop_sim_given                   true
% 2.97/0.99  --inst_prop_sim_new                     false
% 2.97/0.99  --inst_subs_new                         false
% 2.97/0.99  --inst_eq_res_simp                      false
% 2.97/0.99  --inst_subs_given                       false
% 2.97/0.99  --inst_orphan_elimination               true
% 2.97/0.99  --inst_learning_loop_flag               true
% 2.97/0.99  --inst_learning_start                   3000
% 2.97/0.99  --inst_learning_factor                  2
% 2.97/0.99  --inst_start_prop_sim_after_learn       3
% 2.97/0.99  --inst_sel_renew                        solver
% 2.97/0.99  --inst_lit_activity_flag                true
% 2.97/0.99  --inst_restr_to_given                   false
% 2.97/0.99  --inst_activity_threshold               500
% 2.97/0.99  --inst_out_proof                        true
% 2.97/0.99  
% 2.97/0.99  ------ Resolution Options
% 2.97/0.99  
% 2.97/0.99  --resolution_flag                       true
% 2.97/0.99  --res_lit_sel                           adaptive
% 2.97/0.99  --res_lit_sel_side                      none
% 2.97/0.99  --res_ordering                          kbo
% 2.97/0.99  --res_to_prop_solver                    active
% 2.97/0.99  --res_prop_simpl_new                    false
% 2.97/0.99  --res_prop_simpl_given                  true
% 2.97/0.99  --res_passive_queue_type                priority_queues
% 2.97/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.97/0.99  --res_passive_queues_freq               [15;5]
% 2.97/0.99  --res_forward_subs                      full
% 2.97/0.99  --res_backward_subs                     full
% 2.97/0.99  --res_forward_subs_resolution           true
% 2.97/0.99  --res_backward_subs_resolution          true
% 2.97/0.99  --res_orphan_elimination                true
% 2.97/0.99  --res_time_limit                        2.
% 2.97/0.99  --res_out_proof                         true
% 2.97/0.99  
% 2.97/0.99  ------ Superposition Options
% 2.97/0.99  
% 2.97/0.99  --superposition_flag                    true
% 2.97/0.99  --sup_passive_queue_type                priority_queues
% 2.97/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.97/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.97/0.99  --demod_completeness_check              fast
% 2.97/0.99  --demod_use_ground                      true
% 2.97/0.99  --sup_to_prop_solver                    passive
% 2.97/0.99  --sup_prop_simpl_new                    true
% 2.97/0.99  --sup_prop_simpl_given                  true
% 2.97/0.99  --sup_fun_splitting                     false
% 2.97/0.99  --sup_smt_interval                      50000
% 2.97/0.99  
% 2.97/0.99  ------ Superposition Simplification Setup
% 2.97/0.99  
% 2.97/0.99  --sup_indices_passive                   []
% 2.97/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.97/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/0.99  --sup_full_bw                           [BwDemod]
% 2.97/0.99  --sup_immed_triv                        [TrivRules]
% 2.97/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.97/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/0.99  --sup_immed_bw_main                     []
% 2.97/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.97/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/0.99  
% 2.97/0.99  ------ Combination Options
% 2.97/0.99  
% 2.97/0.99  --comb_res_mult                         3
% 2.97/0.99  --comb_sup_mult                         2
% 2.97/0.99  --comb_inst_mult                        10
% 2.97/0.99  
% 2.97/0.99  ------ Debug Options
% 2.97/0.99  
% 2.97/0.99  --dbg_backtrace                         false
% 2.97/0.99  --dbg_dump_prop_clauses                 false
% 2.97/0.99  --dbg_dump_prop_clauses_file            -
% 2.97/0.99  --dbg_out_stat                          false
% 2.97/0.99  ------ Parsing...
% 2.97/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.97/0.99  
% 2.97/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 2.97/0.99  
% 2.97/0.99  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.97/0.99  
% 2.97/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.97/0.99  ------ Proving...
% 2.97/0.99  ------ Problem Properties 
% 2.97/0.99  
% 2.97/0.99  
% 2.97/0.99  clauses                                 21
% 2.97/0.99  conjectures                             6
% 2.97/0.99  EPR                                     6
% 2.97/0.99  Horn                                    20
% 2.97/0.99  unary                                   9
% 2.97/0.99  binary                                  4
% 2.97/0.99  lits                                    66
% 2.97/0.99  lits eq                                 9
% 2.97/0.99  fd_pure                                 0
% 2.97/0.99  fd_pseudo                               0
% 2.97/0.99  fd_cond                                 2
% 2.97/0.99  fd_pseudo_cond                          0
% 2.97/0.99  AC symbols                              0
% 2.97/0.99  
% 2.97/0.99  ------ Schedule dynamic 5 is on 
% 2.97/0.99  
% 2.97/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.97/0.99  
% 2.97/0.99  
% 2.97/0.99  ------ 
% 2.97/0.99  Current options:
% 2.97/0.99  ------ 
% 2.97/0.99  
% 2.97/0.99  ------ Input Options
% 2.97/0.99  
% 2.97/0.99  --out_options                           all
% 2.97/0.99  --tptp_safe_out                         true
% 2.97/0.99  --problem_path                          ""
% 2.97/0.99  --include_path                          ""
% 2.97/0.99  --clausifier                            res/vclausify_rel
% 2.97/0.99  --clausifier_options                    --mode clausify
% 2.97/0.99  --stdin                                 false
% 2.97/0.99  --stats_out                             all
% 2.97/0.99  
% 2.97/0.99  ------ General Options
% 2.97/0.99  
% 2.97/0.99  --fof                                   false
% 2.97/0.99  --time_out_real                         305.
% 2.97/0.99  --time_out_virtual                      -1.
% 2.97/0.99  --symbol_type_check                     false
% 2.97/0.99  --clausify_out                          false
% 2.97/0.99  --sig_cnt_out                           false
% 2.97/0.99  --trig_cnt_out                          false
% 2.97/0.99  --trig_cnt_out_tolerance                1.
% 2.97/0.99  --trig_cnt_out_sk_spl                   false
% 2.97/0.99  --abstr_cl_out                          false
% 2.97/0.99  
% 2.97/0.99  ------ Global Options
% 2.97/0.99  
% 2.97/0.99  --schedule                              default
% 2.97/0.99  --add_important_lit                     false
% 2.97/0.99  --prop_solver_per_cl                    1000
% 2.97/0.99  --min_unsat_core                        false
% 2.97/0.99  --soft_assumptions                      false
% 2.97/0.99  --soft_lemma_size                       3
% 2.97/0.99  --prop_impl_unit_size                   0
% 2.97/0.99  --prop_impl_unit                        []
% 2.97/0.99  --share_sel_clauses                     true
% 2.97/0.99  --reset_solvers                         false
% 2.97/0.99  --bc_imp_inh                            [conj_cone]
% 2.97/0.99  --conj_cone_tolerance                   3.
% 2.97/0.99  --extra_neg_conj                        none
% 2.97/0.99  --large_theory_mode                     true
% 2.97/0.99  --prolific_symb_bound                   200
% 2.97/0.99  --lt_threshold                          2000
% 2.97/0.99  --clause_weak_htbl                      true
% 2.97/0.99  --gc_record_bc_elim                     false
% 2.97/0.99  
% 2.97/0.99  ------ Preprocessing Options
% 2.97/0.99  
% 2.97/0.99  --preprocessing_flag                    true
% 2.97/0.99  --time_out_prep_mult                    0.1
% 2.97/0.99  --splitting_mode                        input
% 2.97/0.99  --splitting_grd                         true
% 2.97/0.99  --splitting_cvd                         false
% 2.97/0.99  --splitting_cvd_svl                     false
% 2.97/0.99  --splitting_nvd                         32
% 2.97/0.99  --sub_typing                            true
% 2.97/0.99  --prep_gs_sim                           true
% 2.97/0.99  --prep_unflatten                        true
% 2.97/0.99  --prep_res_sim                          true
% 2.97/0.99  --prep_upred                            true
% 2.97/0.99  --prep_sem_filter                       exhaustive
% 2.97/0.99  --prep_sem_filter_out                   false
% 2.97/0.99  --pred_elim                             true
% 2.97/0.99  --res_sim_input                         true
% 2.97/1.00  --eq_ax_congr_red                       true
% 2.97/1.00  --pure_diseq_elim                       true
% 2.97/1.00  --brand_transform                       false
% 2.97/1.00  --non_eq_to_eq                          false
% 2.97/1.00  --prep_def_merge                        true
% 2.97/1.00  --prep_def_merge_prop_impl              false
% 2.97/1.00  --prep_def_merge_mbd                    true
% 2.97/1.00  --prep_def_merge_tr_red                 false
% 2.97/1.00  --prep_def_merge_tr_cl                  false
% 2.97/1.00  --smt_preprocessing                     true
% 2.97/1.00  --smt_ac_axioms                         fast
% 2.97/1.00  --preprocessed_out                      false
% 2.97/1.00  --preprocessed_stats                    false
% 2.97/1.00  
% 2.97/1.00  ------ Abstraction refinement Options
% 2.97/1.00  
% 2.97/1.00  --abstr_ref                             []
% 2.97/1.00  --abstr_ref_prep                        false
% 2.97/1.00  --abstr_ref_until_sat                   false
% 2.97/1.00  --abstr_ref_sig_restrict                funpre
% 2.97/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.97/1.00  --abstr_ref_under                       []
% 2.97/1.00  
% 2.97/1.00  ------ SAT Options
% 2.97/1.00  
% 2.97/1.00  --sat_mode                              false
% 2.97/1.00  --sat_fm_restart_options                ""
% 2.97/1.00  --sat_gr_def                            false
% 2.97/1.00  --sat_epr_types                         true
% 2.97/1.00  --sat_non_cyclic_types                  false
% 2.97/1.00  --sat_finite_models                     false
% 2.97/1.00  --sat_fm_lemmas                         false
% 2.97/1.00  --sat_fm_prep                           false
% 2.97/1.00  --sat_fm_uc_incr                        true
% 2.97/1.00  --sat_out_model                         small
% 2.97/1.00  --sat_out_clauses                       false
% 2.97/1.00  
% 2.97/1.00  ------ QBF Options
% 2.97/1.00  
% 2.97/1.00  --qbf_mode                              false
% 2.97/1.00  --qbf_elim_univ                         false
% 2.97/1.00  --qbf_dom_inst                          none
% 2.97/1.00  --qbf_dom_pre_inst                      false
% 2.97/1.00  --qbf_sk_in                             false
% 2.97/1.00  --qbf_pred_elim                         true
% 2.97/1.00  --qbf_split                             512
% 2.97/1.00  
% 2.97/1.00  ------ BMC1 Options
% 2.97/1.00  
% 2.97/1.00  --bmc1_incremental                      false
% 2.97/1.00  --bmc1_axioms                           reachable_all
% 2.97/1.00  --bmc1_min_bound                        0
% 2.97/1.00  --bmc1_max_bound                        -1
% 2.97/1.00  --bmc1_max_bound_default                -1
% 2.97/1.00  --bmc1_symbol_reachability              true
% 2.97/1.00  --bmc1_property_lemmas                  false
% 2.97/1.00  --bmc1_k_induction                      false
% 2.97/1.00  --bmc1_non_equiv_states                 false
% 2.97/1.00  --bmc1_deadlock                         false
% 2.97/1.00  --bmc1_ucm                              false
% 2.97/1.00  --bmc1_add_unsat_core                   none
% 2.97/1.00  --bmc1_unsat_core_children              false
% 2.97/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.97/1.00  --bmc1_out_stat                         full
% 2.97/1.00  --bmc1_ground_init                      false
% 2.97/1.00  --bmc1_pre_inst_next_state              false
% 2.97/1.00  --bmc1_pre_inst_state                   false
% 2.97/1.00  --bmc1_pre_inst_reach_state             false
% 2.97/1.00  --bmc1_out_unsat_core                   false
% 2.97/1.00  --bmc1_aig_witness_out                  false
% 2.97/1.00  --bmc1_verbose                          false
% 2.97/1.00  --bmc1_dump_clauses_tptp                false
% 2.97/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.97/1.00  --bmc1_dump_file                        -
% 2.97/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.97/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.97/1.00  --bmc1_ucm_extend_mode                  1
% 2.97/1.00  --bmc1_ucm_init_mode                    2
% 2.97/1.00  --bmc1_ucm_cone_mode                    none
% 2.97/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.97/1.00  --bmc1_ucm_relax_model                  4
% 2.97/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.97/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.97/1.00  --bmc1_ucm_layered_model                none
% 2.97/1.00  --bmc1_ucm_max_lemma_size               10
% 2.97/1.00  
% 2.97/1.00  ------ AIG Options
% 2.97/1.00  
% 2.97/1.00  --aig_mode                              false
% 2.97/1.00  
% 2.97/1.00  ------ Instantiation Options
% 2.97/1.00  
% 2.97/1.00  --instantiation_flag                    true
% 2.97/1.00  --inst_sos_flag                         false
% 2.97/1.00  --inst_sos_phase                        true
% 2.97/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.97/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.97/1.00  --inst_lit_sel_side                     none
% 2.97/1.00  --inst_solver_per_active                1400
% 2.97/1.00  --inst_solver_calls_frac                1.
% 2.97/1.00  --inst_passive_queue_type               priority_queues
% 2.97/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.97/1.00  --inst_passive_queues_freq              [25;2]
% 2.97/1.00  --inst_dismatching                      true
% 2.97/1.00  --inst_eager_unprocessed_to_passive     true
% 2.97/1.00  --inst_prop_sim_given                   true
% 2.97/1.00  --inst_prop_sim_new                     false
% 2.97/1.00  --inst_subs_new                         false
% 2.97/1.00  --inst_eq_res_simp                      false
% 2.97/1.00  --inst_subs_given                       false
% 2.97/1.00  --inst_orphan_elimination               true
% 2.97/1.00  --inst_learning_loop_flag               true
% 2.97/1.00  --inst_learning_start                   3000
% 2.97/1.00  --inst_learning_factor                  2
% 2.97/1.00  --inst_start_prop_sim_after_learn       3
% 2.97/1.00  --inst_sel_renew                        solver
% 2.97/1.00  --inst_lit_activity_flag                true
% 2.97/1.00  --inst_restr_to_given                   false
% 2.97/1.00  --inst_activity_threshold               500
% 2.97/1.00  --inst_out_proof                        true
% 2.97/1.00  
% 2.97/1.00  ------ Resolution Options
% 2.97/1.00  
% 2.97/1.00  --resolution_flag                       false
% 2.97/1.00  --res_lit_sel                           adaptive
% 2.97/1.00  --res_lit_sel_side                      none
% 2.97/1.00  --res_ordering                          kbo
% 2.97/1.00  --res_to_prop_solver                    active
% 2.97/1.00  --res_prop_simpl_new                    false
% 2.97/1.00  --res_prop_simpl_given                  true
% 2.97/1.00  --res_passive_queue_type                priority_queues
% 2.97/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.97/1.00  --res_passive_queues_freq               [15;5]
% 2.97/1.00  --res_forward_subs                      full
% 2.97/1.00  --res_backward_subs                     full
% 2.97/1.00  --res_forward_subs_resolution           true
% 2.97/1.00  --res_backward_subs_resolution          true
% 2.97/1.00  --res_orphan_elimination                true
% 2.97/1.00  --res_time_limit                        2.
% 2.97/1.00  --res_out_proof                         true
% 2.97/1.00  
% 2.97/1.00  ------ Superposition Options
% 2.97/1.00  
% 2.97/1.00  --superposition_flag                    true
% 2.97/1.00  --sup_passive_queue_type                priority_queues
% 2.97/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.97/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.97/1.00  --demod_completeness_check              fast
% 2.97/1.00  --demod_use_ground                      true
% 2.97/1.00  --sup_to_prop_solver                    passive
% 2.97/1.00  --sup_prop_simpl_new                    true
% 2.97/1.00  --sup_prop_simpl_given                  true
% 2.97/1.00  --sup_fun_splitting                     false
% 2.97/1.00  --sup_smt_interval                      50000
% 2.97/1.00  
% 2.97/1.00  ------ Superposition Simplification Setup
% 2.97/1.00  
% 2.97/1.00  --sup_indices_passive                   []
% 2.97/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.97/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/1.00  --sup_full_bw                           [BwDemod]
% 2.97/1.00  --sup_immed_triv                        [TrivRules]
% 2.97/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.97/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/1.00  --sup_immed_bw_main                     []
% 2.97/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.97/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/1.00  
% 2.97/1.00  ------ Combination Options
% 2.97/1.00  
% 2.97/1.00  --comb_res_mult                         3
% 2.97/1.00  --comb_sup_mult                         2
% 2.97/1.00  --comb_inst_mult                        10
% 2.97/1.00  
% 2.97/1.00  ------ Debug Options
% 2.97/1.00  
% 2.97/1.00  --dbg_backtrace                         false
% 2.97/1.00  --dbg_dump_prop_clauses                 false
% 2.97/1.00  --dbg_dump_prop_clauses_file            -
% 2.97/1.00  --dbg_out_stat                          false
% 2.97/1.00  
% 2.97/1.00  
% 2.97/1.00  
% 2.97/1.00  
% 2.97/1.00  ------ Proving...
% 2.97/1.00  
% 2.97/1.00  
% 2.97/1.00  % SZS status Theorem for theBenchmark.p
% 2.97/1.00  
% 2.97/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.97/1.00  
% 2.97/1.00  fof(f1,axiom,(
% 2.97/1.00    v1_xboole_0(k1_xboole_0)),
% 2.97/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f40,plain,(
% 2.97/1.00    v1_xboole_0(k1_xboole_0)),
% 2.97/1.00    inference(cnf_transformation,[],[f1])).
% 2.97/1.00  
% 2.97/1.00  fof(f9,axiom,(
% 2.97/1.00    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 2.97/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f50,plain,(
% 2.97/1.00    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.97/1.00    inference(cnf_transformation,[],[f9])).
% 2.97/1.00  
% 2.97/1.00  fof(f12,axiom,(
% 2.97/1.00    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.97/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f55,plain,(
% 2.97/1.00    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.97/1.00    inference(cnf_transformation,[],[f12])).
% 2.97/1.00  
% 2.97/1.00  fof(f69,plain,(
% 2.97/1.00    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.97/1.00    inference(definition_unfolding,[],[f50,f55])).
% 2.97/1.00  
% 2.97/1.00  fof(f6,axiom,(
% 2.97/1.00    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 2.97/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f21,plain,(
% 2.97/1.00    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 2.97/1.00    inference(ennf_transformation,[],[f6])).
% 2.97/1.00  
% 2.97/1.00  fof(f46,plain,(
% 2.97/1.00    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 2.97/1.00    inference(cnf_transformation,[],[f21])).
% 2.97/1.00  
% 2.97/1.00  fof(f2,axiom,(
% 2.97/1.00    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.97/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f18,plain,(
% 2.97/1.00    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.97/1.00    inference(ennf_transformation,[],[f2])).
% 2.97/1.00  
% 2.97/1.00  fof(f41,plain,(
% 2.97/1.00    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.97/1.00    inference(cnf_transformation,[],[f18])).
% 2.97/1.00  
% 2.97/1.00  fof(f3,axiom,(
% 2.97/1.00    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.97/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f43,plain,(
% 2.97/1.00    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 2.97/1.00    inference(cnf_transformation,[],[f3])).
% 2.97/1.00  
% 2.97/1.00  fof(f67,plain,(
% 2.97/1.00    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 2.97/1.00    inference(definition_unfolding,[],[f43,f55])).
% 2.97/1.00  
% 2.97/1.00  fof(f11,axiom,(
% 2.97/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 2.97/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f27,plain,(
% 2.97/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.97/1.00    inference(ennf_transformation,[],[f11])).
% 2.97/1.00  
% 2.97/1.00  fof(f28,plain,(
% 2.97/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.97/1.00    inference(flattening,[],[f27])).
% 2.97/1.00  
% 2.97/1.00  fof(f54,plain,(
% 2.97/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.97/1.00    inference(cnf_transformation,[],[f28])).
% 2.97/1.00  
% 2.97/1.00  fof(f8,axiom,(
% 2.97/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.97/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f23,plain,(
% 2.97/1.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.97/1.00    inference(ennf_transformation,[],[f8])).
% 2.97/1.00  
% 2.97/1.00  fof(f24,plain,(
% 2.97/1.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.97/1.00    inference(flattening,[],[f23])).
% 2.97/1.00  
% 2.97/1.00  fof(f35,plain,(
% 2.97/1.00    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.97/1.00    inference(nnf_transformation,[],[f24])).
% 2.97/1.00  
% 2.97/1.00  fof(f48,plain,(
% 2.97/1.00    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.97/1.00    inference(cnf_transformation,[],[f35])).
% 2.97/1.00  
% 2.97/1.00  fof(f15,conjecture,(
% 2.97/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 2.97/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f16,negated_conjecture,(
% 2.97/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 2.97/1.00    inference(negated_conjecture,[],[f15])).
% 2.97/1.00  
% 2.97/1.00  fof(f33,plain,(
% 2.97/1.00    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.97/1.00    inference(ennf_transformation,[],[f16])).
% 2.97/1.00  
% 2.97/1.00  fof(f34,plain,(
% 2.97/1.00    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.97/1.00    inference(flattening,[],[f33])).
% 2.97/1.00  
% 2.97/1.00  fof(f38,plain,(
% 2.97/1.00    ( ! [X2,X0,X1] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((~v2_funct_2(sK3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 2.97/1.00    introduced(choice_axiom,[])).
% 2.97/1.00  
% 2.97/1.00  fof(f37,plain,(
% 2.97/1.00    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 2.97/1.00    introduced(choice_axiom,[])).
% 2.97/1.00  
% 2.97/1.00  fof(f39,plain,(
% 2.97/1.00    ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 2.97/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f34,f38,f37])).
% 2.97/1.00  
% 2.97/1.00  fof(f65,plain,(
% 2.97/1.00    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.97/1.00    inference(cnf_transformation,[],[f39])).
% 2.97/1.00  
% 2.97/1.00  fof(f59,plain,(
% 2.97/1.00    v1_funct_1(sK2)),
% 2.97/1.00    inference(cnf_transformation,[],[f39])).
% 2.97/1.00  
% 2.97/1.00  fof(f61,plain,(
% 2.97/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.97/1.00    inference(cnf_transformation,[],[f39])).
% 2.97/1.00  
% 2.97/1.00  fof(f62,plain,(
% 2.97/1.00    v1_funct_1(sK3)),
% 2.97/1.00    inference(cnf_transformation,[],[f39])).
% 2.97/1.00  
% 2.97/1.00  fof(f64,plain,(
% 2.97/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.97/1.00    inference(cnf_transformation,[],[f39])).
% 2.97/1.00  
% 2.97/1.00  fof(f14,axiom,(
% 2.97/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 2.97/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f31,plain,(
% 2.97/1.00    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.97/1.00    inference(ennf_transformation,[],[f14])).
% 2.97/1.00  
% 2.97/1.00  fof(f32,plain,(
% 2.97/1.00    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.97/1.00    inference(flattening,[],[f31])).
% 2.97/1.00  
% 2.97/1.00  fof(f57,plain,(
% 2.97/1.00    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X3) | k1_xboole_0 = X2 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.97/1.00    inference(cnf_transformation,[],[f32])).
% 2.97/1.00  
% 2.97/1.00  fof(f60,plain,(
% 2.97/1.00    v1_funct_2(sK2,sK0,sK1)),
% 2.97/1.00    inference(cnf_transformation,[],[f39])).
% 2.97/1.00  
% 2.97/1.00  fof(f63,plain,(
% 2.97/1.00    v1_funct_2(sK3,sK1,sK0)),
% 2.97/1.00    inference(cnf_transformation,[],[f39])).
% 2.97/1.00  
% 2.97/1.00  fof(f13,axiom,(
% 2.97/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 2.97/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f29,plain,(
% 2.97/1.00    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.97/1.00    inference(ennf_transformation,[],[f13])).
% 2.97/1.00  
% 2.97/1.00  fof(f30,plain,(
% 2.97/1.00    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.97/1.00    inference(flattening,[],[f29])).
% 2.97/1.00  
% 2.97/1.00  fof(f56,plain,(
% 2.97/1.00    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.97/1.00    inference(cnf_transformation,[],[f30])).
% 2.97/1.00  
% 2.97/1.00  fof(f7,axiom,(
% 2.97/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 2.97/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f22,plain,(
% 2.97/1.00    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.97/1.00    inference(ennf_transformation,[],[f7])).
% 2.97/1.00  
% 2.97/1.00  fof(f47,plain,(
% 2.97/1.00    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.97/1.00    inference(cnf_transformation,[],[f22])).
% 2.97/1.00  
% 2.97/1.00  fof(f5,axiom,(
% 2.97/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.97/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f17,plain,(
% 2.97/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 2.97/1.00    inference(pure_predicate_removal,[],[f5])).
% 2.97/1.00  
% 2.97/1.00  fof(f20,plain,(
% 2.97/1.00    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.97/1.00    inference(ennf_transformation,[],[f17])).
% 2.97/1.00  
% 2.97/1.00  fof(f45,plain,(
% 2.97/1.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.97/1.00    inference(cnf_transformation,[],[f20])).
% 2.97/1.00  
% 2.97/1.00  fof(f10,axiom,(
% 2.97/1.00    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 2.97/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f25,plain,(
% 2.97/1.00    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.97/1.00    inference(ennf_transformation,[],[f10])).
% 2.97/1.00  
% 2.97/1.00  fof(f26,plain,(
% 2.97/1.00    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.97/1.00    inference(flattening,[],[f25])).
% 2.97/1.00  
% 2.97/1.00  fof(f36,plain,(
% 2.97/1.00    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.97/1.00    inference(nnf_transformation,[],[f26])).
% 2.97/1.00  
% 2.97/1.00  fof(f52,plain,(
% 2.97/1.00    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.97/1.00    inference(cnf_transformation,[],[f36])).
% 2.97/1.00  
% 2.97/1.00  fof(f71,plain,(
% 2.97/1.00    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.97/1.00    inference(equality_resolution,[],[f52])).
% 2.97/1.00  
% 2.97/1.00  fof(f4,axiom,(
% 2.97/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.97/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f19,plain,(
% 2.97/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.97/1.00    inference(ennf_transformation,[],[f4])).
% 2.97/1.00  
% 2.97/1.00  fof(f44,plain,(
% 2.97/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.97/1.00    inference(cnf_transformation,[],[f19])).
% 2.97/1.00  
% 2.97/1.00  fof(f66,plain,(
% 2.97/1.00    ~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)),
% 2.97/1.00    inference(cnf_transformation,[],[f39])).
% 2.97/1.00  
% 2.97/1.00  cnf(c_0,plain,
% 2.97/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 2.97/1.00      inference(cnf_transformation,[],[f40]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_617,plain,
% 2.97/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 2.97/1.00      inference(subtyping,[status(esa)],[c_0]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1030,plain,
% 2.97/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_617]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_10,plain,
% 2.97/1.00      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 2.97/1.00      inference(cnf_transformation,[],[f69]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_612,plain,
% 2.97/1.00      ( m1_subset_1(k6_partfun1(X0_48),k1_zfmisc_1(k2_zfmisc_1(X0_48,X0_48))) ),
% 2.97/1.00      inference(subtyping,[status(esa)],[c_10]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1035,plain,
% 2.97/1.00      ( m1_subset_1(k6_partfun1(X0_48),k1_zfmisc_1(k2_zfmisc_1(X0_48,X0_48))) = iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_612]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_6,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.97/1.00      | ~ v1_xboole_0(X1)
% 2.97/1.00      | v1_xboole_0(X0) ),
% 2.97/1.00      inference(cnf_transformation,[],[f46]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_614,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
% 2.97/1.00      | ~ v1_xboole_0(X1_48)
% 2.97/1.00      | v1_xboole_0(X0_48) ),
% 2.97/1.00      inference(subtyping,[status(esa)],[c_6]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1033,plain,
% 2.97/1.00      ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48))) != iProver_top
% 2.97/1.00      | v1_xboole_0(X1_48) != iProver_top
% 2.97/1.00      | v1_xboole_0(X0_48) = iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_614]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2023,plain,
% 2.97/1.00      ( v1_xboole_0(X0_48) != iProver_top
% 2.97/1.00      | v1_xboole_0(k6_partfun1(X0_48)) = iProver_top ),
% 2.97/1.00      inference(superposition,[status(thm)],[c_1035,c_1033]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1,plain,
% 2.97/1.00      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 2.97/1.00      inference(cnf_transformation,[],[f41]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_616,plain,
% 2.97/1.00      ( ~ v1_xboole_0(X0_48) | k1_xboole_0 = X0_48 ),
% 2.97/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1031,plain,
% 2.97/1.00      ( k1_xboole_0 = X0_48 | v1_xboole_0(X0_48) != iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_616]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_3448,plain,
% 2.97/1.00      ( k6_partfun1(X0_48) = k1_xboole_0
% 2.97/1.00      | v1_xboole_0(X0_48) != iProver_top ),
% 2.97/1.00      inference(superposition,[status(thm)],[c_2023,c_1031]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_3495,plain,
% 2.97/1.00      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 2.97/1.00      inference(superposition,[status(thm)],[c_1030,c_3448]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2,plain,
% 2.97/1.00      ( v2_funct_1(k6_partfun1(X0)) ),
% 2.97/1.00      inference(cnf_transformation,[],[f67]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_615,plain,
% 2.97/1.00      ( v2_funct_1(k6_partfun1(X0_48)) ),
% 2.97/1.00      inference(subtyping,[status(esa)],[c_2]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1032,plain,
% 2.97/1.00      ( v2_funct_1(k6_partfun1(X0_48)) = iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_615]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_3510,plain,
% 2.97/1.00      ( v2_funct_1(k1_xboole_0) = iProver_top ),
% 2.97/1.00      inference(superposition,[status(thm)],[c_3495,c_1032]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_13,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.97/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 2.97/1.00      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 2.97/1.00      | ~ v1_funct_1(X0)
% 2.97/1.00      | ~ v1_funct_1(X3) ),
% 2.97/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_611,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
% 2.97/1.00      | ~ m1_subset_1(X3_48,k1_zfmisc_1(k2_zfmisc_1(X4_48,X5_48)))
% 2.97/1.00      | m1_subset_1(k1_partfun1(X4_48,X5_48,X1_48,X2_48,X3_48,X0_48),k1_zfmisc_1(k2_zfmisc_1(X4_48,X2_48)))
% 2.97/1.00      | ~ v1_funct_1(X0_48)
% 2.97/1.00      | ~ v1_funct_1(X3_48) ),
% 2.97/1.00      inference(subtyping,[status(esa)],[c_13]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1036,plain,
% 2.97/1.00      ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48))) != iProver_top
% 2.97/1.00      | m1_subset_1(X3_48,k1_zfmisc_1(k2_zfmisc_1(X4_48,X5_48))) != iProver_top
% 2.97/1.00      | m1_subset_1(k1_partfun1(X4_48,X5_48,X1_48,X2_48,X3_48,X0_48),k1_zfmisc_1(k2_zfmisc_1(X4_48,X2_48))) = iProver_top
% 2.97/1.00      | v1_funct_1(X3_48) != iProver_top
% 2.97/1.00      | v1_funct_1(X0_48) != iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_611]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_9,plain,
% 2.97/1.00      ( ~ r2_relset_1(X0,X1,X2,X3)
% 2.97/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.97/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.97/1.00      | X3 = X2 ),
% 2.97/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_19,negated_conjecture,
% 2.97/1.00      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 2.97/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_389,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.97/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.97/1.00      | X3 = X0
% 2.97/1.00      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 2.97/1.00      | k6_partfun1(sK0) != X3
% 2.97/1.00      | sK0 != X2
% 2.97/1.00      | sK0 != X1 ),
% 2.97/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_19]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_390,plain,
% 2.97/1.00      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.97/1.00      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.97/1.00      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 2.97/1.00      inference(unflattening,[status(thm)],[c_389]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_56,plain,
% 2.97/1.00      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 2.97/1.00      inference(instantiation,[status(thm)],[c_10]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_392,plain,
% 2.97/1.00      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.97/1.00      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 2.97/1.00      inference(global_propositional_subsumption,
% 2.97/1.00                [status(thm)],
% 2.97/1.00                [c_390,c_56]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_599,plain,
% 2.97/1.00      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.97/1.00      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 2.97/1.00      inference(subtyping,[status(esa)],[c_392]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1049,plain,
% 2.97/1.00      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 2.97/1.00      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_599]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2083,plain,
% 2.97/1.00      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
% 2.97/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.97/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.97/1.00      | v1_funct_1(sK2) != iProver_top
% 2.97/1.00      | v1_funct_1(sK3) != iProver_top ),
% 2.97/1.00      inference(superposition,[status(thm)],[c_1036,c_1049]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_25,negated_conjecture,
% 2.97/1.00      ( v1_funct_1(sK2) ),
% 2.97/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_26,plain,
% 2.97/1.00      ( v1_funct_1(sK2) = iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_23,negated_conjecture,
% 2.97/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.97/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_28,plain,
% 2.97/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_22,negated_conjecture,
% 2.97/1.00      ( v1_funct_1(sK3) ),
% 2.97/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_29,plain,
% 2.97/1.00      ( v1_funct_1(sK3) = iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_20,negated_conjecture,
% 2.97/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 2.97/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_31,plain,
% 2.97/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2338,plain,
% 2.97/1.00      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
% 2.97/1.00      inference(global_propositional_subsumption,
% 2.97/1.00                [status(thm)],
% 2.97/1.00                [c_2083,c_26,c_28,c_29,c_31]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_17,plain,
% 2.97/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.97/1.00      | ~ v1_funct_2(X3,X4,X1)
% 2.97/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 2.97/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.97/1.00      | ~ v1_funct_1(X0)
% 2.97/1.00      | ~ v1_funct_1(X3)
% 2.97/1.00      | v2_funct_1(X3)
% 2.97/1.00      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 2.97/1.00      | k1_xboole_0 = X2 ),
% 2.97/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_608,plain,
% 2.97/1.00      ( ~ v1_funct_2(X0_48,X1_48,X2_48)
% 2.97/1.00      | ~ v1_funct_2(X3_48,X4_48,X1_48)
% 2.97/1.00      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
% 2.97/1.00      | ~ m1_subset_1(X3_48,k1_zfmisc_1(k2_zfmisc_1(X4_48,X1_48)))
% 2.97/1.00      | ~ v1_funct_1(X0_48)
% 2.97/1.00      | ~ v1_funct_1(X3_48)
% 2.97/1.00      | v2_funct_1(X3_48)
% 2.97/1.00      | ~ v2_funct_1(k1_partfun1(X4_48,X1_48,X1_48,X2_48,X3_48,X0_48))
% 2.97/1.00      | k1_xboole_0 = X2_48 ),
% 2.97/1.00      inference(subtyping,[status(esa)],[c_17]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1039,plain,
% 2.97/1.00      ( k1_xboole_0 = X0_48
% 2.97/1.00      | v1_funct_2(X1_48,X2_48,X0_48) != iProver_top
% 2.97/1.00      | v1_funct_2(X3_48,X4_48,X2_48) != iProver_top
% 2.97/1.00      | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_48,X0_48))) != iProver_top
% 2.97/1.00      | m1_subset_1(X3_48,k1_zfmisc_1(k2_zfmisc_1(X4_48,X2_48))) != iProver_top
% 2.97/1.00      | v1_funct_1(X3_48) != iProver_top
% 2.97/1.00      | v1_funct_1(X1_48) != iProver_top
% 2.97/1.00      | v2_funct_1(X3_48) = iProver_top
% 2.97/1.00      | v2_funct_1(k1_partfun1(X4_48,X2_48,X2_48,X0_48,X3_48,X1_48)) != iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_608]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2364,plain,
% 2.97/1.00      ( sK0 = k1_xboole_0
% 2.97/1.00      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 2.97/1.00      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 2.97/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.97/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.97/1.00      | v1_funct_1(sK2) != iProver_top
% 2.97/1.00      | v1_funct_1(sK3) != iProver_top
% 2.97/1.00      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 2.97/1.00      | v2_funct_1(sK2) = iProver_top ),
% 2.97/1.00      inference(superposition,[status(thm)],[c_2338,c_1039]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_24,negated_conjecture,
% 2.97/1.00      ( v1_funct_2(sK2,sK0,sK1) ),
% 2.97/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_27,plain,
% 2.97/1.00      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_21,negated_conjecture,
% 2.97/1.00      ( v1_funct_2(sK3,sK1,sK0) ),
% 2.97/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_30,plain,
% 2.97/1.00      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_77,plain,
% 2.97/1.00      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_79,plain,
% 2.97/1.00      ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
% 2.97/1.00      inference(instantiation,[status(thm)],[c_77]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_15,plain,
% 2.97/1.00      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 2.97/1.00      | ~ v1_funct_2(X2,X0,X1)
% 2.97/1.00      | ~ v1_funct_2(X3,X1,X0)
% 2.97/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.97/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.97/1.00      | ~ v1_funct_1(X2)
% 2.97/1.00      | ~ v1_funct_1(X3)
% 2.97/1.00      | k2_relset_1(X1,X0,X3) = X0 ),
% 2.97/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_403,plain,
% 2.97/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.97/1.00      | ~ v1_funct_2(X3,X2,X1)
% 2.97/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.97/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.97/1.00      | ~ v1_funct_1(X3)
% 2.97/1.00      | ~ v1_funct_1(X0)
% 2.97/1.00      | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 2.97/1.00      | k2_relset_1(X2,X1,X3) = X1
% 2.97/1.00      | k6_partfun1(X1) != k6_partfun1(sK0)
% 2.97/1.00      | sK0 != X1 ),
% 2.97/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_19]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_404,plain,
% 2.97/1.00      ( ~ v1_funct_2(X0,X1,sK0)
% 2.97/1.00      | ~ v1_funct_2(X2,sK0,X1)
% 2.97/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 2.97/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 2.97/1.00      | ~ v1_funct_1(X2)
% 2.97/1.00      | ~ v1_funct_1(X0)
% 2.97/1.00      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 2.97/1.00      | k2_relset_1(X1,sK0,X0) = sK0
% 2.97/1.00      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 2.97/1.00      inference(unflattening,[status(thm)],[c_403]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_478,plain,
% 2.97/1.00      ( ~ v1_funct_2(X0,X1,sK0)
% 2.97/1.00      | ~ v1_funct_2(X2,sK0,X1)
% 2.97/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 2.97/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 2.97/1.00      | ~ v1_funct_1(X0)
% 2.97/1.00      | ~ v1_funct_1(X2)
% 2.97/1.00      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 2.97/1.00      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 2.97/1.00      inference(equality_resolution_simp,[status(thm)],[c_404]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_598,plain,
% 2.97/1.00      ( ~ v1_funct_2(X0_48,X1_48,sK0)
% 2.97/1.00      | ~ v1_funct_2(X2_48,sK0,X1_48)
% 2.97/1.00      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,sK0)))
% 2.97/1.00      | ~ m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(sK0,X1_48)))
% 2.97/1.00      | ~ v1_funct_1(X0_48)
% 2.97/1.00      | ~ v1_funct_1(X2_48)
% 2.97/1.00      | k1_partfun1(sK0,X1_48,X1_48,sK0,X2_48,X0_48) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 2.97/1.00      | k2_relset_1(X1_48,sK0,X0_48) = sK0 ),
% 2.97/1.00      inference(subtyping,[status(esa)],[c_478]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1050,plain,
% 2.97/1.00      ( k1_partfun1(sK0,X0_48,X0_48,sK0,X1_48,X2_48) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 2.97/1.00      | k2_relset_1(X0_48,sK0,X2_48) = sK0
% 2.97/1.00      | v1_funct_2(X2_48,X0_48,sK0) != iProver_top
% 2.97/1.00      | v1_funct_2(X1_48,sK0,X0_48) != iProver_top
% 2.97/1.00      | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,sK0))) != iProver_top
% 2.97/1.00      | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_48))) != iProver_top
% 2.97/1.00      | v1_funct_1(X2_48) != iProver_top
% 2.97/1.00      | v1_funct_1(X1_48) != iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_598]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1895,plain,
% 2.97/1.00      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 2.97/1.00      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 2.97/1.00      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 2.97/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.97/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.97/1.00      | v1_funct_1(sK2) != iProver_top
% 2.97/1.00      | v1_funct_1(sK3) != iProver_top ),
% 2.97/1.00      inference(equality_resolution,[status(thm)],[c_1050]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_607,negated_conjecture,
% 2.97/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 2.97/1.00      inference(subtyping,[status(esa)],[c_20]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1040,plain,
% 2.97/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_607]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_7,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.97/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.97/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_613,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
% 2.97/1.00      | k2_relset_1(X1_48,X2_48,X0_48) = k2_relat_1(X0_48) ),
% 2.97/1.00      inference(subtyping,[status(esa)],[c_7]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1034,plain,
% 2.97/1.00      ( k2_relset_1(X0_48,X1_48,X2_48) = k2_relat_1(X2_48)
% 2.97/1.00      | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_613]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1580,plain,
% 2.97/1.00      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 2.97/1.00      inference(superposition,[status(thm)],[c_1040,c_1034]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1896,plain,
% 2.97/1.00      ( k2_relat_1(sK3) = sK0
% 2.97/1.00      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 2.97/1.00      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 2.97/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.97/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.97/1.00      | v1_funct_1(sK2) != iProver_top
% 2.97/1.00      | v1_funct_1(sK3) != iProver_top ),
% 2.97/1.00      inference(demodulation,[status(thm)],[c_1895,c_1580]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1899,plain,
% 2.97/1.00      ( k2_relat_1(sK3) = sK0 ),
% 2.97/1.00      inference(global_propositional_subsumption,
% 2.97/1.00                [status(thm)],
% 2.97/1.00                [c_1896,c_26,c_27,c_28,c_29,c_30,c_31]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_5,plain,
% 2.97/1.00      ( v5_relat_1(X0,X1)
% 2.97/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.97/1.00      inference(cnf_transformation,[],[f45]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_11,plain,
% 2.97/1.00      ( v2_funct_2(X0,k2_relat_1(X0))
% 2.97/1.00      | ~ v5_relat_1(X0,k2_relat_1(X0))
% 2.97/1.00      | ~ v1_relat_1(X0) ),
% 2.97/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_307,plain,
% 2.97/1.00      ( v2_funct_2(X0,k2_relat_1(X0))
% 2.97/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 2.97/1.00      | ~ v1_relat_1(X0)
% 2.97/1.00      | X0 != X1
% 2.97/1.00      | k2_relat_1(X0) != X3 ),
% 2.97/1.00      inference(resolution_lifted,[status(thm)],[c_5,c_11]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_308,plain,
% 2.97/1.00      ( v2_funct_2(X0,k2_relat_1(X0))
% 2.97/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
% 2.97/1.00      | ~ v1_relat_1(X0) ),
% 2.97/1.00      inference(unflattening,[status(thm)],[c_307]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_4,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.97/1.00      | v1_relat_1(X0) ),
% 2.97/1.00      inference(cnf_transformation,[],[f44]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_318,plain,
% 2.97/1.00      ( v2_funct_2(X0,k2_relat_1(X0))
% 2.97/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0)))) ),
% 2.97/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_308,c_4]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_18,negated_conjecture,
% 2.97/1.00      ( ~ v2_funct_2(sK3,sK0) | ~ v2_funct_1(sK2) ),
% 2.97/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_333,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
% 2.97/1.00      | ~ v2_funct_1(sK2)
% 2.97/1.00      | k2_relat_1(X0) != sK0
% 2.97/1.00      | sK3 != X0 ),
% 2.97/1.00      inference(resolution_lifted,[status(thm)],[c_318,c_18]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_334,plain,
% 2.97/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3))))
% 2.97/1.00      | ~ v2_funct_1(sK2)
% 2.97/1.00      | k2_relat_1(sK3) != sK0 ),
% 2.97/1.00      inference(unflattening,[status(thm)],[c_333]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_601,plain,
% 2.97/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_48,k2_relat_1(sK3))))
% 2.97/1.00      | ~ v2_funct_1(sK2)
% 2.97/1.00      | k2_relat_1(sK3) != sK0 ),
% 2.97/1.00      inference(subtyping,[status(esa)],[c_334]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_619,plain,
% 2.97/1.00      ( ~ v2_funct_1(sK2) | sP0_iProver_split | k2_relat_1(sK3) != sK0 ),
% 2.97/1.00      inference(splitting,
% 2.97/1.00                [splitting(split),new_symbols(definition,[])],
% 2.97/1.00                [c_601]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1046,plain,
% 2.97/1.00      ( k2_relat_1(sK3) != sK0
% 2.97/1.00      | v2_funct_1(sK2) != iProver_top
% 2.97/1.00      | sP0_iProver_split = iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_619]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1904,plain,
% 2.97/1.00      ( sK0 != sK0
% 2.97/1.00      | v2_funct_1(sK2) != iProver_top
% 2.97/1.00      | sP0_iProver_split = iProver_top ),
% 2.97/1.00      inference(demodulation,[status(thm)],[c_1899,c_1046]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1905,plain,
% 2.97/1.00      ( v2_funct_1(sK2) != iProver_top
% 2.97/1.00      | sP0_iProver_split = iProver_top ),
% 2.97/1.00      inference(equality_resolution_simp,[status(thm)],[c_1904]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_618,plain,
% 2.97/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_48,k2_relat_1(sK3))))
% 2.97/1.00      | ~ sP0_iProver_split ),
% 2.97/1.00      inference(splitting,
% 2.97/1.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.97/1.00                [c_601]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1047,plain,
% 2.97/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_48,k2_relat_1(sK3)))) != iProver_top
% 2.97/1.00      | sP0_iProver_split != iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_618]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1903,plain,
% 2.97/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_48,sK0))) != iProver_top
% 2.97/1.00      | sP0_iProver_split != iProver_top ),
% 2.97/1.00      inference(demodulation,[status(thm)],[c_1899,c_1047]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1968,plain,
% 2.97/1.00      ( sP0_iProver_split != iProver_top ),
% 2.97/1.00      inference(superposition,[status(thm)],[c_1040,c_1903]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2984,plain,
% 2.97/1.00      ( sK0 = k1_xboole_0 ),
% 2.97/1.00      inference(global_propositional_subsumption,
% 2.97/1.00                [status(thm)],
% 2.97/1.00                [c_2364,c_26,c_27,c_28,c_29,c_30,c_31,c_79,c_1905,c_1968]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_604,negated_conjecture,
% 2.97/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.97/1.00      inference(subtyping,[status(esa)],[c_23]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1043,plain,
% 2.97/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_604]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2022,plain,
% 2.97/1.00      ( v1_xboole_0(sK2) = iProver_top
% 2.97/1.00      | v1_xboole_0(sK0) != iProver_top ),
% 2.97/1.00      inference(superposition,[status(thm)],[c_1043,c_1033]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2990,plain,
% 2.97/1.00      ( v1_xboole_0(sK2) = iProver_top
% 2.97/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.97/1.00      inference(demodulation,[status(thm)],[c_2984,c_2022]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_83,plain,
% 2.97/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_625,plain,
% 2.97/1.00      ( ~ v1_xboole_0(X0_48) | v1_xboole_0(X1_48) | X1_48 != X0_48 ),
% 2.97/1.00      theory(equality) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1361,plain,
% 2.97/1.00      ( v1_xboole_0(X0_48)
% 2.97/1.00      | ~ v1_xboole_0(k1_xboole_0)
% 2.97/1.00      | X0_48 != k1_xboole_0 ),
% 2.97/1.00      inference(instantiation,[status(thm)],[c_625]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1362,plain,
% 2.97/1.00      ( X0_48 != k1_xboole_0
% 2.97/1.00      | v1_xboole_0(X0_48) = iProver_top
% 2.97/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_1361]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1364,plain,
% 2.97/1.00      ( sK0 != k1_xboole_0
% 2.97/1.00      | v1_xboole_0(sK0) = iProver_top
% 2.97/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.97/1.00      inference(instantiation,[status(thm)],[c_1362]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_3132,plain,
% 2.97/1.00      ( v1_xboole_0(sK2) = iProver_top ),
% 2.97/1.00      inference(global_propositional_subsumption,
% 2.97/1.00                [status(thm)],
% 2.97/1.00                [c_2990,c_26,c_27,c_28,c_29,c_30,c_31,c_79,c_83,c_1364,
% 2.97/1.00                 c_1905,c_1968,c_2022,c_2364]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_3137,plain,
% 2.97/1.00      ( sK2 = k1_xboole_0 ),
% 2.97/1.00      inference(superposition,[status(thm)],[c_3132,c_1031]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2401,plain,
% 2.97/1.00      ( v2_funct_1(sK2) != iProver_top ),
% 2.97/1.00      inference(global_propositional_subsumption,
% 2.97/1.00                [status(thm)],
% 2.97/1.00                [c_1905,c_1968]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_3143,plain,
% 2.97/1.00      ( v2_funct_1(k1_xboole_0) != iProver_top ),
% 2.97/1.00      inference(demodulation,[status(thm)],[c_3137,c_2401]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(contradiction,plain,
% 2.97/1.00      ( $false ),
% 2.97/1.00      inference(minisat,[status(thm)],[c_3510,c_3143]) ).
% 2.97/1.00  
% 2.97/1.00  
% 2.97/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.97/1.00  
% 2.97/1.00  ------                               Statistics
% 2.97/1.00  
% 2.97/1.00  ------ General
% 2.97/1.00  
% 2.97/1.00  abstr_ref_over_cycles:                  0
% 2.97/1.00  abstr_ref_under_cycles:                 0
% 2.97/1.00  gc_basic_clause_elim:                   0
% 2.97/1.00  forced_gc_time:                         0
% 2.97/1.00  parsing_time:                           0.01
% 2.97/1.00  unif_index_cands_time:                  0.
% 2.97/1.00  unif_index_add_time:                    0.
% 2.97/1.00  orderings_time:                         0.
% 2.97/1.00  out_proof_time:                         0.013
% 2.97/1.00  total_time:                             0.18
% 2.97/1.00  num_of_symbols:                         52
% 2.97/1.00  num_of_terms:                           6759
% 2.97/1.00  
% 2.97/1.00  ------ Preprocessing
% 2.97/1.00  
% 2.97/1.00  num_of_splits:                          1
% 2.97/1.00  num_of_split_atoms:                     1
% 2.97/1.00  num_of_reused_defs:                     0
% 2.97/1.00  num_eq_ax_congr_red:                    9
% 2.97/1.00  num_of_sem_filtered_clauses:            1
% 2.97/1.00  num_of_subtypes:                        3
% 2.97/1.00  monotx_restored_types:                  1
% 2.97/1.00  sat_num_of_epr_types:                   0
% 2.97/1.00  sat_num_of_non_cyclic_types:            0
% 2.97/1.00  sat_guarded_non_collapsed_types:        1
% 2.97/1.00  num_pure_diseq_elim:                    0
% 2.97/1.00  simp_replaced_by:                       0
% 2.97/1.00  res_preprocessed:                       119
% 2.97/1.00  prep_upred:                             0
% 2.97/1.00  prep_unflattend:                        17
% 2.97/1.00  smt_new_axioms:                         0
% 2.97/1.00  pred_elim_cands:                        5
% 2.97/1.00  pred_elim:                              4
% 2.97/1.00  pred_elim_cl:                           6
% 2.97/1.00  pred_elim_cycles:                       6
% 2.97/1.00  merged_defs:                            0
% 2.97/1.00  merged_defs_ncl:                        0
% 2.97/1.00  bin_hyper_res:                          0
% 2.97/1.00  prep_cycles:                            4
% 2.97/1.00  pred_elim_time:                         0.005
% 2.97/1.00  splitting_time:                         0.
% 2.97/1.00  sem_filter_time:                        0.
% 2.97/1.00  monotx_time:                            0.001
% 2.97/1.00  subtype_inf_time:                       0.002
% 2.97/1.00  
% 2.97/1.00  ------ Problem properties
% 2.97/1.00  
% 2.97/1.00  clauses:                                21
% 2.97/1.00  conjectures:                            6
% 2.97/1.00  epr:                                    6
% 2.97/1.00  horn:                                   20
% 2.97/1.00  ground:                                 9
% 2.97/1.00  unary:                                  9
% 2.97/1.00  binary:                                 4
% 2.97/1.00  lits:                                   66
% 2.97/1.00  lits_eq:                                9
% 2.97/1.00  fd_pure:                                0
% 2.97/1.00  fd_pseudo:                              0
% 2.97/1.00  fd_cond:                                2
% 2.97/1.00  fd_pseudo_cond:                         0
% 2.97/1.00  ac_symbols:                             0
% 2.97/1.00  
% 2.97/1.00  ------ Propositional Solver
% 2.97/1.00  
% 2.97/1.00  prop_solver_calls:                      26
% 2.97/1.00  prop_fast_solver_calls:                 876
% 2.97/1.00  smt_solver_calls:                       0
% 2.97/1.00  smt_fast_solver_calls:                  0
% 2.97/1.00  prop_num_of_clauses:                    1470
% 2.97/1.00  prop_preprocess_simplified:             4589
% 2.97/1.00  prop_fo_subsumed:                       25
% 2.97/1.00  prop_solver_time:                       0.
% 2.97/1.00  smt_solver_time:                        0.
% 2.97/1.00  smt_fast_solver_time:                   0.
% 2.97/1.00  prop_fast_solver_time:                  0.
% 2.97/1.00  prop_unsat_core_time:                   0.
% 2.97/1.00  
% 2.97/1.00  ------ QBF
% 2.97/1.00  
% 2.97/1.00  qbf_q_res:                              0
% 2.97/1.00  qbf_num_tautologies:                    0
% 2.97/1.00  qbf_prep_cycles:                        0
% 2.97/1.00  
% 2.97/1.00  ------ BMC1
% 2.97/1.00  
% 2.97/1.00  bmc1_current_bound:                     -1
% 2.97/1.00  bmc1_last_solved_bound:                 -1
% 2.97/1.00  bmc1_unsat_core_size:                   -1
% 2.97/1.00  bmc1_unsat_core_parents_size:           -1
% 2.97/1.00  bmc1_merge_next_fun:                    0
% 2.97/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.97/1.00  
% 2.97/1.00  ------ Instantiation
% 2.97/1.00  
% 2.97/1.00  inst_num_of_clauses:                    389
% 2.97/1.00  inst_num_in_passive:                    78
% 2.97/1.00  inst_num_in_active:                     234
% 2.97/1.00  inst_num_in_unprocessed:                77
% 2.97/1.00  inst_num_of_loops:                      250
% 2.97/1.00  inst_num_of_learning_restarts:          0
% 2.97/1.00  inst_num_moves_active_passive:          13
% 2.97/1.00  inst_lit_activity:                      0
% 2.97/1.00  inst_lit_activity_moves:                0
% 2.97/1.00  inst_num_tautologies:                   0
% 2.97/1.00  inst_num_prop_implied:                  0
% 2.97/1.00  inst_num_existing_simplified:           0
% 2.97/1.00  inst_num_eq_res_simplified:             0
% 2.97/1.00  inst_num_child_elim:                    0
% 2.97/1.00  inst_num_of_dismatching_blockings:      16
% 2.97/1.00  inst_num_of_non_proper_insts:           220
% 2.97/1.00  inst_num_of_duplicates:                 0
% 2.97/1.00  inst_inst_num_from_inst_to_res:         0
% 2.97/1.00  inst_dismatching_checking_time:         0.
% 2.97/1.00  
% 2.97/1.00  ------ Resolution
% 2.97/1.00  
% 2.97/1.00  res_num_of_clauses:                     0
% 2.97/1.00  res_num_in_passive:                     0
% 2.97/1.00  res_num_in_active:                      0
% 2.97/1.00  res_num_of_loops:                       123
% 2.97/1.00  res_forward_subset_subsumed:            19
% 2.97/1.00  res_backward_subset_subsumed:           0
% 2.97/1.00  res_forward_subsumed:                   0
% 2.97/1.00  res_backward_subsumed:                  0
% 2.97/1.00  res_forward_subsumption_resolution:     3
% 2.97/1.00  res_backward_subsumption_resolution:    0
% 2.97/1.00  res_clause_to_clause_subsumption:       70
% 2.97/1.00  res_orphan_elimination:                 0
% 2.97/1.00  res_tautology_del:                      12
% 2.97/1.00  res_num_eq_res_simplified:              1
% 2.97/1.00  res_num_sel_changes:                    0
% 2.97/1.00  res_moves_from_active_to_pass:          0
% 2.97/1.00  
% 2.97/1.00  ------ Superposition
% 2.97/1.00  
% 2.97/1.00  sup_time_total:                         0.
% 2.97/1.00  sup_time_generating:                    0.
% 2.97/1.00  sup_time_sim_full:                      0.
% 2.97/1.00  sup_time_sim_immed:                     0.
% 2.97/1.00  
% 2.97/1.00  sup_num_of_clauses:                     37
% 2.97/1.00  sup_num_in_active:                      26
% 2.97/1.00  sup_num_in_passive:                     11
% 2.97/1.00  sup_num_of_loops:                       49
% 2.97/1.00  sup_fw_superposition:                   11
% 2.97/1.00  sup_bw_superposition:                   18
% 2.97/1.00  sup_immediate_simplified:               3
% 2.97/1.00  sup_given_eliminated:                   0
% 2.97/1.00  comparisons_done:                       0
% 2.97/1.00  comparisons_avoided:                    0
% 2.97/1.00  
% 2.97/1.00  ------ Simplifications
% 2.97/1.00  
% 2.97/1.00  
% 2.97/1.00  sim_fw_subset_subsumed:                 1
% 2.97/1.00  sim_bw_subset_subsumed:                 0
% 2.97/1.00  sim_fw_subsumed:                        1
% 2.97/1.00  sim_bw_subsumed:                        0
% 2.97/1.00  sim_fw_subsumption_res:                 0
% 2.97/1.00  sim_bw_subsumption_res:                 0
% 2.97/1.00  sim_tautology_del:                      2
% 2.97/1.00  sim_eq_tautology_del:                   2
% 2.97/1.00  sim_eq_res_simp:                        1
% 2.97/1.00  sim_fw_demodulated:                     1
% 2.97/1.00  sim_bw_demodulated:                     24
% 2.97/1.00  sim_light_normalised:                   1
% 2.97/1.00  sim_joinable_taut:                      0
% 2.97/1.00  sim_joinable_simp:                      0
% 2.97/1.00  sim_ac_normalised:                      0
% 2.97/1.00  sim_smt_subsumption:                    0
% 2.97/1.00  
%------------------------------------------------------------------------------

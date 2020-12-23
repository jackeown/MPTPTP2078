%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:01:55 EST 2020

% Result     : Theorem 2.93s
% Output     : CNFRefutation 2.93s
% Verified   : 
% Statistics : Number of formulae       :  160 ( 721 expanded)
%              Number of clauses        :   96 ( 242 expanded)
%              Number of leaves         :   19 ( 171 expanded)
%              Depth                    :   18
%              Number of atoms          :  560 (4488 expanded)
%              Number of equality atoms :  165 ( 389 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f53,plain,(
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

fof(f47,plain,(
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

fof(f64,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f39])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f12,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f67,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f49,f54])).

fof(f58,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f60,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f39])).

fof(f61,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f63,plain,(
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

fof(f56,plain,(
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

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

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

fof(f55,plain,(
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

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f59,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f62,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f39])).

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

fof(f44,plain,(
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

fof(f51,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f69,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f51])).

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

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f65,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f66,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f42,f54])).

cnf(c_651,plain,
    ( ~ v2_funct_1(X0_48)
    | v2_funct_1(X1_48)
    | X1_48 != X0_48 ),
    theory(equality)).

cnf(c_3440,plain,
    ( ~ v2_funct_1(X0_48)
    | v2_funct_1(sK2)
    | sK2 != X0_48 ),
    inference(instantiation,[status(thm)],[c_651])).

cnf(c_3442,plain,
    ( v2_funct_1(sK2)
    | ~ v2_funct_1(sK0)
    | sK2 != sK0 ),
    inference(instantiation,[status(thm)],[c_3440])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_635,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | ~ m1_subset_1(X3_48,k1_zfmisc_1(k2_zfmisc_1(X4_48,X5_48)))
    | m1_subset_1(k1_partfun1(X4_48,X5_48,X1_48,X2_48,X3_48,X0_48),k1_zfmisc_1(k2_zfmisc_1(X4_48,X2_48)))
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(X3_48) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1056,plain,
    ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48))) != iProver_top
    | m1_subset_1(X3_48,k1_zfmisc_1(k2_zfmisc_1(X4_48,X5_48))) != iProver_top
    | m1_subset_1(k1_partfun1(X4_48,X5_48,X1_48,X2_48,X3_48,X0_48),k1_zfmisc_1(k2_zfmisc_1(X4_48,X2_48))) = iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(X3_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_635])).

cnf(c_8,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_18,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_414,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_18])).

cnf(c_415,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_414])).

cnf(c_9,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_55,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_417,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_415,c_55])).

cnf(c_623,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_417])).

cnf(c_1069,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_623])).

cnf(c_2147,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1056,c_1069])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_25,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_27,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_28,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_30,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2396,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2147,c_25,c_27,c_28,c_30])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v2_funct_1(k1_partfun1(X1,X2,X2,X4,X0,X3))
    | k1_xboole_0 = X4 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_632,plain,
    ( ~ v1_funct_2(X0_48,X1_48,X2_48)
    | ~ v1_funct_2(X3_48,X2_48,X4_48)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | ~ m1_subset_1(X3_48,k1_zfmisc_1(k2_zfmisc_1(X2_48,X4_48)))
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(X3_48)
    | v2_funct_1(X0_48)
    | ~ v2_funct_1(k1_partfun1(X1_48,X2_48,X2_48,X4_48,X0_48,X3_48))
    | k1_xboole_0 = X4_48 ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1059,plain,
    ( k1_xboole_0 = X0_48
    | v1_funct_2(X1_48,X2_48,X3_48) != iProver_top
    | v1_funct_2(X4_48,X3_48,X0_48) != iProver_top
    | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_48,X3_48))) != iProver_top
    | m1_subset_1(X4_48,k1_zfmisc_1(k2_zfmisc_1(X3_48,X0_48))) != iProver_top
    | v1_funct_1(X1_48) != iProver_top
    | v1_funct_1(X4_48) != iProver_top
    | v2_funct_1(X1_48) = iProver_top
    | v2_funct_1(k1_partfun1(X2_48,X3_48,X3_48,X0_48,X1_48,X4_48)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_632])).

cnf(c_2422,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2396,c_1059])).

cnf(c_636,plain,
    ( m1_subset_1(k6_partfun1(X0_48),k1_zfmisc_1(k2_zfmisc_1(X0_48,X0_48))) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1055,plain,
    ( m1_subset_1(k6_partfun1(X0_48),k1_zfmisc_1(k2_zfmisc_1(X0_48,X0_48))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_636])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_638,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | ~ v1_xboole_0(X1_48)
    | v1_xboole_0(X0_48) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1053,plain,
    ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48))) != iProver_top
    | v1_xboole_0(X1_48) != iProver_top
    | v1_xboole_0(X0_48) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_638])).

cnf(c_2077,plain,
    ( v1_xboole_0(X0_48) != iProver_top
    | v1_xboole_0(k6_partfun1(X0_48)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1055,c_1053])).

cnf(c_2092,plain,
    ( ~ v1_xboole_0(X0_48)
    | v1_xboole_0(k6_partfun1(X0_48)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2077])).

cnf(c_2094,plain,
    ( v1_xboole_0(k6_partfun1(sK0))
    | ~ v1_xboole_0(sK0) ),
    inference(instantiation,[status(thm)],[c_2092])).

cnf(c_628,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1063,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_628])).

cnf(c_2076,plain,
    ( v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1063,c_1053])).

cnf(c_2091,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_xboole_0(sK0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2076])).

cnf(c_631,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1060,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_631])).

cnf(c_14,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_428,plain,
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
    inference(resolution_lifted,[status(thm)],[c_14,c_18])).

cnf(c_429,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X0)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0
    | k6_partfun1(sK0) != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_428])).

cnf(c_503,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_429])).

cnf(c_622,plain,
    ( ~ v1_funct_2(X0_48,X1_48,sK0)
    | ~ v1_funct_2(X2_48,sK0,X1_48)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,sK0)))
    | ~ m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(sK0,X1_48)))
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(X2_48)
    | k1_partfun1(sK0,X1_48,X1_48,sK0,X2_48,X0_48) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1_48,sK0,X0_48) = sK0 ),
    inference(subtyping,[status(esa)],[c_503])).

cnf(c_1070,plain,
    ( k1_partfun1(sK0,X0_48,X0_48,sK0,X1_48,X2_48) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X0_48,sK0,X2_48) = sK0
    | v1_funct_2(X2_48,X0_48,sK0) != iProver_top
    | v1_funct_2(X1_48,sK0,X0_48) != iProver_top
    | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,sK0))) != iProver_top
    | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_48))) != iProver_top
    | v1_funct_1(X2_48) != iProver_top
    | v1_funct_1(X1_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_622])).

cnf(c_1956,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1070])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_637,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | k2_relset_1(X1_48,X2_48,X0_48) = k2_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1054,plain,
    ( k2_relset_1(X0_48,X1_48,X2_48) = k2_relat_1(X2_48)
    | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_637])).

cnf(c_1639,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1060,c_1054])).

cnf(c_1957,plain,
    ( k2_relat_1(sK3) = sK0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1956,c_1639])).

cnf(c_23,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_26,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_20,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_29,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1960,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1957,c_25,c_26,c_27,c_28,c_29,c_30])).

cnf(c_4,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_10,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_332,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X0)
    | X0 != X1
    | k2_relat_1(X0) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_10])).

cnf(c_333,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_332])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_343,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0)))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_333,c_3])).

cnf(c_17,negated_conjecture,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_358,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
    | ~ v2_funct_1(sK2)
    | k2_relat_1(X0) != sK0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_343,c_17])).

cnf(c_359,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3))))
    | ~ v2_funct_1(sK2)
    | k2_relat_1(sK3) != sK0 ),
    inference(unflattening,[status(thm)],[c_358])).

cnf(c_625,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_48,k2_relat_1(sK3))))
    | ~ v2_funct_1(sK2)
    | k2_relat_1(sK3) != sK0 ),
    inference(subtyping,[status(esa)],[c_359])).

cnf(c_642,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_48,k2_relat_1(sK3))))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_625])).

cnf(c_1067,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_48,k2_relat_1(sK3)))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_642])).

cnf(c_1964,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_48,sK0))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(demodulation,[status(thm)],[c_1960,c_1067])).

cnf(c_2033,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_1060,c_1964])).

cnf(c_2034,plain,
    ( ~ sP0_iProver_split ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2033])).

cnf(c_643,plain,
    ( ~ v2_funct_1(sK2)
    | sP0_iProver_split
    | k2_relat_1(sK3) != sK0 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_625])).

cnf(c_1066,plain,
    ( k2_relat_1(sK3) != sK0
    | v2_funct_1(sK2) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_643])).

cnf(c_1965,plain,
    ( sK0 != sK0
    | v2_funct_1(sK2) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_1960,c_1066])).

cnf(c_1966,plain,
    ( v2_funct_1(sK2) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_1965])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_640,plain,
    ( ~ v1_xboole_0(X0_48)
    | ~ v1_xboole_0(X1_48)
    | X1_48 = X0_48 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1650,plain,
    ( ~ v1_xboole_0(X0_48)
    | ~ v1_xboole_0(sK2)
    | sK2 = X0_48 ),
    inference(instantiation,[status(thm)],[c_640])).

cnf(c_1652,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ v1_xboole_0(sK0)
    | sK2 = sK0 ),
    inference(instantiation,[status(thm)],[c_1650])).

cnf(c_1521,plain,
    ( ~ v1_xboole_0(X0_48)
    | ~ v1_xboole_0(k6_partfun1(X1_48))
    | X0_48 = k6_partfun1(X1_48) ),
    inference(instantiation,[status(thm)],[c_640])).

cnf(c_1523,plain,
    ( ~ v1_xboole_0(k6_partfun1(sK0))
    | ~ v1_xboole_0(sK0)
    | sK0 = k6_partfun1(sK0) ),
    inference(instantiation,[status(thm)],[c_1521])).

cnf(c_649,plain,
    ( ~ v1_xboole_0(X0_48)
    | v1_xboole_0(X1_48)
    | X1_48 != X0_48 ),
    theory(equality)).

cnf(c_1380,plain,
    ( v1_xboole_0(X0_48)
    | ~ v1_xboole_0(k1_xboole_0)
    | X0_48 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_649])).

cnf(c_1382,plain,
    ( v1_xboole_0(sK0)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1380])).

cnf(c_1266,plain,
    ( v2_funct_1(X0_48)
    | ~ v2_funct_1(k6_partfun1(X1_48))
    | X0_48 != k6_partfun1(X1_48) ),
    inference(instantiation,[status(thm)],[c_651])).

cnf(c_1268,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | v2_funct_1(sK0)
    | sK0 != k6_partfun1(sK0) ),
    inference(instantiation,[status(thm)],[c_1266])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_2,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_73,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_75,plain,
    ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_73])).

cnf(c_74,plain,
    ( v2_funct_1(k6_partfun1(sK0)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3442,c_2422,c_2094,c_2091,c_2034,c_2033,c_1966,c_1957,c_1652,c_1523,c_1382,c_1268,c_643,c_0,c_75,c_74,c_30,c_29,c_28,c_27,c_26,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:52:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 2.93/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.93/0.98  
% 2.93/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.93/0.98  
% 2.93/0.98  ------  iProver source info
% 2.93/0.98  
% 2.93/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.93/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.93/0.98  git: non_committed_changes: false
% 2.93/0.98  git: last_make_outside_of_git: false
% 2.93/0.98  
% 2.93/0.98  ------ 
% 2.93/0.98  
% 2.93/0.98  ------ Input Options
% 2.93/0.98  
% 2.93/0.98  --out_options                           all
% 2.93/0.98  --tptp_safe_out                         true
% 2.93/0.98  --problem_path                          ""
% 2.93/0.98  --include_path                          ""
% 2.93/0.98  --clausifier                            res/vclausify_rel
% 2.93/0.98  --clausifier_options                    --mode clausify
% 2.93/0.98  --stdin                                 false
% 2.93/0.98  --stats_out                             all
% 2.93/0.98  
% 2.93/0.98  ------ General Options
% 2.93/0.98  
% 2.93/0.98  --fof                                   false
% 2.93/0.98  --time_out_real                         305.
% 2.93/0.98  --time_out_virtual                      -1.
% 2.93/0.98  --symbol_type_check                     false
% 2.93/0.98  --clausify_out                          false
% 2.93/0.98  --sig_cnt_out                           false
% 2.93/0.98  --trig_cnt_out                          false
% 2.93/0.98  --trig_cnt_out_tolerance                1.
% 2.93/0.98  --trig_cnt_out_sk_spl                   false
% 2.93/0.98  --abstr_cl_out                          false
% 2.93/0.98  
% 2.93/0.98  ------ Global Options
% 2.93/0.98  
% 2.93/0.98  --schedule                              default
% 2.93/0.98  --add_important_lit                     false
% 2.93/0.98  --prop_solver_per_cl                    1000
% 2.93/0.98  --min_unsat_core                        false
% 2.93/0.98  --soft_assumptions                      false
% 2.93/0.98  --soft_lemma_size                       3
% 2.93/0.98  --prop_impl_unit_size                   0
% 2.93/0.98  --prop_impl_unit                        []
% 2.93/0.98  --share_sel_clauses                     true
% 2.93/0.98  --reset_solvers                         false
% 2.93/0.98  --bc_imp_inh                            [conj_cone]
% 2.93/0.98  --conj_cone_tolerance                   3.
% 2.93/0.98  --extra_neg_conj                        none
% 2.93/0.98  --large_theory_mode                     true
% 2.93/0.98  --prolific_symb_bound                   200
% 2.93/0.98  --lt_threshold                          2000
% 2.93/0.98  --clause_weak_htbl                      true
% 2.93/0.98  --gc_record_bc_elim                     false
% 2.93/0.98  
% 2.93/0.98  ------ Preprocessing Options
% 2.93/0.98  
% 2.93/0.98  --preprocessing_flag                    true
% 2.93/0.98  --time_out_prep_mult                    0.1
% 2.93/0.98  --splitting_mode                        input
% 2.93/0.98  --splitting_grd                         true
% 2.93/0.98  --splitting_cvd                         false
% 2.93/0.98  --splitting_cvd_svl                     false
% 2.93/0.98  --splitting_nvd                         32
% 2.93/0.98  --sub_typing                            true
% 2.93/0.98  --prep_gs_sim                           true
% 2.93/0.98  --prep_unflatten                        true
% 2.93/0.98  --prep_res_sim                          true
% 2.93/0.98  --prep_upred                            true
% 2.93/0.98  --prep_sem_filter                       exhaustive
% 2.93/0.98  --prep_sem_filter_out                   false
% 2.93/0.98  --pred_elim                             true
% 2.93/0.98  --res_sim_input                         true
% 2.93/0.98  --eq_ax_congr_red                       true
% 2.93/0.98  --pure_diseq_elim                       true
% 2.93/0.98  --brand_transform                       false
% 2.93/0.98  --non_eq_to_eq                          false
% 2.93/0.98  --prep_def_merge                        true
% 2.93/0.98  --prep_def_merge_prop_impl              false
% 2.93/0.98  --prep_def_merge_mbd                    true
% 2.93/0.98  --prep_def_merge_tr_red                 false
% 2.93/0.98  --prep_def_merge_tr_cl                  false
% 2.93/0.98  --smt_preprocessing                     true
% 2.93/0.98  --smt_ac_axioms                         fast
% 2.93/0.98  --preprocessed_out                      false
% 2.93/0.98  --preprocessed_stats                    false
% 2.93/0.98  
% 2.93/0.98  ------ Abstraction refinement Options
% 2.93/0.98  
% 2.93/0.98  --abstr_ref                             []
% 2.93/0.98  --abstr_ref_prep                        false
% 2.93/0.98  --abstr_ref_until_sat                   false
% 2.93/0.98  --abstr_ref_sig_restrict                funpre
% 2.93/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.93/0.98  --abstr_ref_under                       []
% 2.93/0.98  
% 2.93/0.98  ------ SAT Options
% 2.93/0.98  
% 2.93/0.98  --sat_mode                              false
% 2.93/0.98  --sat_fm_restart_options                ""
% 2.93/0.98  --sat_gr_def                            false
% 2.93/0.98  --sat_epr_types                         true
% 2.93/0.98  --sat_non_cyclic_types                  false
% 2.93/0.98  --sat_finite_models                     false
% 2.93/0.98  --sat_fm_lemmas                         false
% 2.93/0.98  --sat_fm_prep                           false
% 2.93/0.98  --sat_fm_uc_incr                        true
% 2.93/0.98  --sat_out_model                         small
% 2.93/0.98  --sat_out_clauses                       false
% 2.93/0.98  
% 2.93/0.98  ------ QBF Options
% 2.93/0.98  
% 2.93/0.98  --qbf_mode                              false
% 2.93/0.98  --qbf_elim_univ                         false
% 2.93/0.98  --qbf_dom_inst                          none
% 2.93/0.98  --qbf_dom_pre_inst                      false
% 2.93/0.98  --qbf_sk_in                             false
% 2.93/0.98  --qbf_pred_elim                         true
% 2.93/0.98  --qbf_split                             512
% 2.93/0.98  
% 2.93/0.98  ------ BMC1 Options
% 2.93/0.98  
% 2.93/0.98  --bmc1_incremental                      false
% 2.93/0.98  --bmc1_axioms                           reachable_all
% 2.93/0.98  --bmc1_min_bound                        0
% 2.93/0.98  --bmc1_max_bound                        -1
% 2.93/0.98  --bmc1_max_bound_default                -1
% 2.93/0.98  --bmc1_symbol_reachability              true
% 2.93/0.98  --bmc1_property_lemmas                  false
% 2.93/0.98  --bmc1_k_induction                      false
% 2.93/0.98  --bmc1_non_equiv_states                 false
% 2.93/0.98  --bmc1_deadlock                         false
% 2.93/0.98  --bmc1_ucm                              false
% 2.93/0.98  --bmc1_add_unsat_core                   none
% 2.93/0.98  --bmc1_unsat_core_children              false
% 2.93/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.93/0.98  --bmc1_out_stat                         full
% 2.93/0.98  --bmc1_ground_init                      false
% 2.93/0.98  --bmc1_pre_inst_next_state              false
% 2.93/0.98  --bmc1_pre_inst_state                   false
% 2.93/0.98  --bmc1_pre_inst_reach_state             false
% 2.93/0.98  --bmc1_out_unsat_core                   false
% 2.93/0.98  --bmc1_aig_witness_out                  false
% 2.93/0.98  --bmc1_verbose                          false
% 2.93/0.98  --bmc1_dump_clauses_tptp                false
% 2.93/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.93/0.98  --bmc1_dump_file                        -
% 2.93/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.93/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.93/0.98  --bmc1_ucm_extend_mode                  1
% 2.93/0.98  --bmc1_ucm_init_mode                    2
% 2.93/0.98  --bmc1_ucm_cone_mode                    none
% 2.93/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.93/0.98  --bmc1_ucm_relax_model                  4
% 2.93/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.93/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.93/0.98  --bmc1_ucm_layered_model                none
% 2.93/0.98  --bmc1_ucm_max_lemma_size               10
% 2.93/0.98  
% 2.93/0.98  ------ AIG Options
% 2.93/0.98  
% 2.93/0.98  --aig_mode                              false
% 2.93/0.98  
% 2.93/0.98  ------ Instantiation Options
% 2.93/0.98  
% 2.93/0.98  --instantiation_flag                    true
% 2.93/0.98  --inst_sos_flag                         false
% 2.93/0.98  --inst_sos_phase                        true
% 2.93/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.93/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.93/0.98  --inst_lit_sel_side                     num_symb
% 2.93/0.98  --inst_solver_per_active                1400
% 2.93/0.98  --inst_solver_calls_frac                1.
% 2.93/0.98  --inst_passive_queue_type               priority_queues
% 2.93/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.93/0.98  --inst_passive_queues_freq              [25;2]
% 2.93/0.98  --inst_dismatching                      true
% 2.93/0.98  --inst_eager_unprocessed_to_passive     true
% 2.93/0.98  --inst_prop_sim_given                   true
% 2.93/0.98  --inst_prop_sim_new                     false
% 2.93/0.98  --inst_subs_new                         false
% 2.93/0.98  --inst_eq_res_simp                      false
% 2.93/0.98  --inst_subs_given                       false
% 2.93/0.98  --inst_orphan_elimination               true
% 2.93/0.98  --inst_learning_loop_flag               true
% 2.93/0.98  --inst_learning_start                   3000
% 2.93/0.98  --inst_learning_factor                  2
% 2.93/0.98  --inst_start_prop_sim_after_learn       3
% 2.93/0.98  --inst_sel_renew                        solver
% 2.93/0.98  --inst_lit_activity_flag                true
% 2.93/0.98  --inst_restr_to_given                   false
% 2.93/0.98  --inst_activity_threshold               500
% 2.93/0.98  --inst_out_proof                        true
% 2.93/0.98  
% 2.93/0.98  ------ Resolution Options
% 2.93/0.98  
% 2.93/0.98  --resolution_flag                       true
% 2.93/0.98  --res_lit_sel                           adaptive
% 2.93/0.98  --res_lit_sel_side                      none
% 2.93/0.98  --res_ordering                          kbo
% 2.93/0.98  --res_to_prop_solver                    active
% 2.93/0.98  --res_prop_simpl_new                    false
% 2.93/0.98  --res_prop_simpl_given                  true
% 2.93/0.98  --res_passive_queue_type                priority_queues
% 2.93/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.93/0.98  --res_passive_queues_freq               [15;5]
% 2.93/0.98  --res_forward_subs                      full
% 2.93/0.98  --res_backward_subs                     full
% 2.93/0.98  --res_forward_subs_resolution           true
% 2.93/0.98  --res_backward_subs_resolution          true
% 2.93/0.98  --res_orphan_elimination                true
% 2.93/0.98  --res_time_limit                        2.
% 2.93/0.98  --res_out_proof                         true
% 2.93/0.98  
% 2.93/0.98  ------ Superposition Options
% 2.93/0.98  
% 2.93/0.98  --superposition_flag                    true
% 2.93/0.98  --sup_passive_queue_type                priority_queues
% 2.93/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.93/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.93/0.98  --demod_completeness_check              fast
% 2.93/0.98  --demod_use_ground                      true
% 2.93/0.98  --sup_to_prop_solver                    passive
% 2.93/0.98  --sup_prop_simpl_new                    true
% 2.93/0.98  --sup_prop_simpl_given                  true
% 2.93/0.98  --sup_fun_splitting                     false
% 2.93/0.98  --sup_smt_interval                      50000
% 2.93/0.98  
% 2.93/0.98  ------ Superposition Simplification Setup
% 2.93/0.98  
% 2.93/0.98  --sup_indices_passive                   []
% 2.93/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.93/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.93/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.93/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.93/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.93/0.98  --sup_full_bw                           [BwDemod]
% 2.93/0.98  --sup_immed_triv                        [TrivRules]
% 2.93/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.93/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.93/0.98  --sup_immed_bw_main                     []
% 2.93/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.93/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.93/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.93/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.93/0.98  
% 2.93/0.98  ------ Combination Options
% 2.93/0.98  
% 2.93/0.98  --comb_res_mult                         3
% 2.93/0.98  --comb_sup_mult                         2
% 2.93/0.98  --comb_inst_mult                        10
% 2.93/0.98  
% 2.93/0.98  ------ Debug Options
% 2.93/0.98  
% 2.93/0.98  --dbg_backtrace                         false
% 2.93/0.98  --dbg_dump_prop_clauses                 false
% 2.93/0.98  --dbg_dump_prop_clauses_file            -
% 2.93/0.98  --dbg_out_stat                          false
% 2.93/0.98  ------ Parsing...
% 2.93/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.93/0.98  
% 2.93/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.93/0.98  
% 2.93/0.98  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.93/0.98  
% 2.93/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.93/0.98  ------ Proving...
% 2.93/0.98  ------ Problem Properties 
% 2.93/0.98  
% 2.93/0.98  
% 2.93/0.98  clauses                                 21
% 2.93/0.98  conjectures                             6
% 2.93/0.98  EPR                                     6
% 2.93/0.98  Horn                                    20
% 2.93/0.98  unary                                   9
% 2.93/0.98  binary                                  3
% 2.93/0.98  lits                                    67
% 2.93/0.98  lits eq                                 9
% 2.93/0.98  fd_pure                                 0
% 2.93/0.98  fd_pseudo                               0
% 2.93/0.98  fd_cond                                 1
% 2.93/0.98  fd_pseudo_cond                          1
% 2.93/0.98  AC symbols                              0
% 2.93/0.98  
% 2.93/0.98  ------ Schedule dynamic 5 is on 
% 2.93/0.98  
% 2.93/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.93/0.98  
% 2.93/0.98  
% 2.93/0.98  ------ 
% 2.93/0.98  Current options:
% 2.93/0.98  ------ 
% 2.93/0.98  
% 2.93/0.98  ------ Input Options
% 2.93/0.98  
% 2.93/0.98  --out_options                           all
% 2.93/0.98  --tptp_safe_out                         true
% 2.93/0.98  --problem_path                          ""
% 2.93/0.98  --include_path                          ""
% 2.93/0.98  --clausifier                            res/vclausify_rel
% 2.93/0.98  --clausifier_options                    --mode clausify
% 2.93/0.98  --stdin                                 false
% 2.93/0.98  --stats_out                             all
% 2.93/0.98  
% 2.93/0.98  ------ General Options
% 2.93/0.98  
% 2.93/0.98  --fof                                   false
% 2.93/0.98  --time_out_real                         305.
% 2.93/0.98  --time_out_virtual                      -1.
% 2.93/0.98  --symbol_type_check                     false
% 2.93/0.98  --clausify_out                          false
% 2.93/0.98  --sig_cnt_out                           false
% 2.93/0.98  --trig_cnt_out                          false
% 2.93/0.98  --trig_cnt_out_tolerance                1.
% 2.93/0.98  --trig_cnt_out_sk_spl                   false
% 2.93/0.98  --abstr_cl_out                          false
% 2.93/0.98  
% 2.93/0.98  ------ Global Options
% 2.93/0.98  
% 2.93/0.98  --schedule                              default
% 2.93/0.98  --add_important_lit                     false
% 2.93/0.98  --prop_solver_per_cl                    1000
% 2.93/0.98  --min_unsat_core                        false
% 2.93/0.98  --soft_assumptions                      false
% 2.93/0.98  --soft_lemma_size                       3
% 2.93/0.98  --prop_impl_unit_size                   0
% 2.93/0.98  --prop_impl_unit                        []
% 2.93/0.98  --share_sel_clauses                     true
% 2.93/0.98  --reset_solvers                         false
% 2.93/0.98  --bc_imp_inh                            [conj_cone]
% 2.93/0.98  --conj_cone_tolerance                   3.
% 2.93/0.98  --extra_neg_conj                        none
% 2.93/0.98  --large_theory_mode                     true
% 2.93/0.98  --prolific_symb_bound                   200
% 2.93/0.98  --lt_threshold                          2000
% 2.93/0.98  --clause_weak_htbl                      true
% 2.93/0.98  --gc_record_bc_elim                     false
% 2.93/0.98  
% 2.93/0.98  ------ Preprocessing Options
% 2.93/0.98  
% 2.93/0.98  --preprocessing_flag                    true
% 2.93/0.98  --time_out_prep_mult                    0.1
% 2.93/0.98  --splitting_mode                        input
% 2.93/0.98  --splitting_grd                         true
% 2.93/0.98  --splitting_cvd                         false
% 2.93/0.98  --splitting_cvd_svl                     false
% 2.93/0.98  --splitting_nvd                         32
% 2.93/0.98  --sub_typing                            true
% 2.93/0.98  --prep_gs_sim                           true
% 2.93/0.98  --prep_unflatten                        true
% 2.93/0.98  --prep_res_sim                          true
% 2.93/0.98  --prep_upred                            true
% 2.93/0.98  --prep_sem_filter                       exhaustive
% 2.93/0.98  --prep_sem_filter_out                   false
% 2.93/0.98  --pred_elim                             true
% 2.93/0.98  --res_sim_input                         true
% 2.93/0.98  --eq_ax_congr_red                       true
% 2.93/0.98  --pure_diseq_elim                       true
% 2.93/0.98  --brand_transform                       false
% 2.93/0.98  --non_eq_to_eq                          false
% 2.93/0.98  --prep_def_merge                        true
% 2.93/0.98  --prep_def_merge_prop_impl              false
% 2.93/0.98  --prep_def_merge_mbd                    true
% 2.93/0.98  --prep_def_merge_tr_red                 false
% 2.93/0.98  --prep_def_merge_tr_cl                  false
% 2.93/0.98  --smt_preprocessing                     true
% 2.93/0.98  --smt_ac_axioms                         fast
% 2.93/0.98  --preprocessed_out                      false
% 2.93/0.98  --preprocessed_stats                    false
% 2.93/0.98  
% 2.93/0.98  ------ Abstraction refinement Options
% 2.93/0.98  
% 2.93/0.98  --abstr_ref                             []
% 2.93/0.98  --abstr_ref_prep                        false
% 2.93/0.98  --abstr_ref_until_sat                   false
% 2.93/0.98  --abstr_ref_sig_restrict                funpre
% 2.93/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.93/0.98  --abstr_ref_under                       []
% 2.93/0.98  
% 2.93/0.98  ------ SAT Options
% 2.93/0.98  
% 2.93/0.98  --sat_mode                              false
% 2.93/0.98  --sat_fm_restart_options                ""
% 2.93/0.98  --sat_gr_def                            false
% 2.93/0.98  --sat_epr_types                         true
% 2.93/0.98  --sat_non_cyclic_types                  false
% 2.93/0.98  --sat_finite_models                     false
% 2.93/0.98  --sat_fm_lemmas                         false
% 2.93/0.98  --sat_fm_prep                           false
% 2.93/0.98  --sat_fm_uc_incr                        true
% 2.93/0.98  --sat_out_model                         small
% 2.93/0.98  --sat_out_clauses                       false
% 2.93/0.98  
% 2.93/0.98  ------ QBF Options
% 2.93/0.98  
% 2.93/0.98  --qbf_mode                              false
% 2.93/0.98  --qbf_elim_univ                         false
% 2.93/0.98  --qbf_dom_inst                          none
% 2.93/0.98  --qbf_dom_pre_inst                      false
% 2.93/0.98  --qbf_sk_in                             false
% 2.93/0.98  --qbf_pred_elim                         true
% 2.93/0.98  --qbf_split                             512
% 2.93/0.98  
% 2.93/0.98  ------ BMC1 Options
% 2.93/0.98  
% 2.93/0.98  --bmc1_incremental                      false
% 2.93/0.98  --bmc1_axioms                           reachable_all
% 2.93/0.98  --bmc1_min_bound                        0
% 2.93/0.98  --bmc1_max_bound                        -1
% 2.93/0.98  --bmc1_max_bound_default                -1
% 2.93/0.98  --bmc1_symbol_reachability              true
% 2.93/0.98  --bmc1_property_lemmas                  false
% 2.93/0.98  --bmc1_k_induction                      false
% 2.93/0.98  --bmc1_non_equiv_states                 false
% 2.93/0.98  --bmc1_deadlock                         false
% 2.93/0.98  --bmc1_ucm                              false
% 2.93/0.98  --bmc1_add_unsat_core                   none
% 2.93/0.98  --bmc1_unsat_core_children              false
% 2.93/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.93/0.98  --bmc1_out_stat                         full
% 2.93/0.98  --bmc1_ground_init                      false
% 2.93/0.98  --bmc1_pre_inst_next_state              false
% 2.93/0.98  --bmc1_pre_inst_state                   false
% 2.93/0.98  --bmc1_pre_inst_reach_state             false
% 2.93/0.98  --bmc1_out_unsat_core                   false
% 2.93/0.98  --bmc1_aig_witness_out                  false
% 2.93/0.98  --bmc1_verbose                          false
% 2.93/0.98  --bmc1_dump_clauses_tptp                false
% 2.93/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.93/0.98  --bmc1_dump_file                        -
% 2.93/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.93/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.93/0.98  --bmc1_ucm_extend_mode                  1
% 2.93/0.98  --bmc1_ucm_init_mode                    2
% 2.93/0.98  --bmc1_ucm_cone_mode                    none
% 2.93/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.93/0.98  --bmc1_ucm_relax_model                  4
% 2.93/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.93/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.93/0.98  --bmc1_ucm_layered_model                none
% 2.93/0.98  --bmc1_ucm_max_lemma_size               10
% 2.93/0.98  
% 2.93/0.98  ------ AIG Options
% 2.93/0.98  
% 2.93/0.98  --aig_mode                              false
% 2.93/0.98  
% 2.93/0.98  ------ Instantiation Options
% 2.93/0.98  
% 2.93/0.98  --instantiation_flag                    true
% 2.93/0.98  --inst_sos_flag                         false
% 2.93/0.98  --inst_sos_phase                        true
% 2.93/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.93/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.93/0.98  --inst_lit_sel_side                     none
% 2.93/0.98  --inst_solver_per_active                1400
% 2.93/0.98  --inst_solver_calls_frac                1.
% 2.93/0.98  --inst_passive_queue_type               priority_queues
% 2.93/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.93/0.98  --inst_passive_queues_freq              [25;2]
% 2.93/0.98  --inst_dismatching                      true
% 2.93/0.98  --inst_eager_unprocessed_to_passive     true
% 2.93/0.98  --inst_prop_sim_given                   true
% 2.93/0.98  --inst_prop_sim_new                     false
% 2.93/0.98  --inst_subs_new                         false
% 2.93/0.98  --inst_eq_res_simp                      false
% 2.93/0.98  --inst_subs_given                       false
% 2.93/0.98  --inst_orphan_elimination               true
% 2.93/0.98  --inst_learning_loop_flag               true
% 2.93/0.98  --inst_learning_start                   3000
% 2.93/0.98  --inst_learning_factor                  2
% 2.93/0.98  --inst_start_prop_sim_after_learn       3
% 2.93/0.98  --inst_sel_renew                        solver
% 2.93/0.98  --inst_lit_activity_flag                true
% 2.93/0.98  --inst_restr_to_given                   false
% 2.93/0.98  --inst_activity_threshold               500
% 2.93/0.98  --inst_out_proof                        true
% 2.93/0.98  
% 2.93/0.98  ------ Resolution Options
% 2.93/0.98  
% 2.93/0.98  --resolution_flag                       false
% 2.93/0.98  --res_lit_sel                           adaptive
% 2.93/0.98  --res_lit_sel_side                      none
% 2.93/0.98  --res_ordering                          kbo
% 2.93/0.98  --res_to_prop_solver                    active
% 2.93/0.98  --res_prop_simpl_new                    false
% 2.93/0.98  --res_prop_simpl_given                  true
% 2.93/0.98  --res_passive_queue_type                priority_queues
% 2.93/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.93/0.98  --res_passive_queues_freq               [15;5]
% 2.93/0.98  --res_forward_subs                      full
% 2.93/0.98  --res_backward_subs                     full
% 2.93/0.98  --res_forward_subs_resolution           true
% 2.93/0.98  --res_backward_subs_resolution          true
% 2.93/0.98  --res_orphan_elimination                true
% 2.93/0.98  --res_time_limit                        2.
% 2.93/0.98  --res_out_proof                         true
% 2.93/0.98  
% 2.93/0.98  ------ Superposition Options
% 2.93/0.98  
% 2.93/0.98  --superposition_flag                    true
% 2.93/0.98  --sup_passive_queue_type                priority_queues
% 2.93/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.93/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.93/0.98  --demod_completeness_check              fast
% 2.93/0.98  --demod_use_ground                      true
% 2.93/0.98  --sup_to_prop_solver                    passive
% 2.93/0.98  --sup_prop_simpl_new                    true
% 2.93/0.98  --sup_prop_simpl_given                  true
% 2.93/0.98  --sup_fun_splitting                     false
% 2.93/0.98  --sup_smt_interval                      50000
% 2.93/0.98  
% 2.93/0.98  ------ Superposition Simplification Setup
% 2.93/0.98  
% 2.93/0.98  --sup_indices_passive                   []
% 2.93/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.93/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.93/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.93/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.93/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.93/0.98  --sup_full_bw                           [BwDemod]
% 2.93/0.98  --sup_immed_triv                        [TrivRules]
% 2.93/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.93/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.93/0.98  --sup_immed_bw_main                     []
% 2.93/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.93/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.93/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.93/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.93/0.98  
% 2.93/0.98  ------ Combination Options
% 2.93/0.98  
% 2.93/0.98  --comb_res_mult                         3
% 2.93/0.98  --comb_sup_mult                         2
% 2.93/0.98  --comb_inst_mult                        10
% 2.93/0.98  
% 2.93/0.98  ------ Debug Options
% 2.93/0.98  
% 2.93/0.98  --dbg_backtrace                         false
% 2.93/0.98  --dbg_dump_prop_clauses                 false
% 2.93/0.98  --dbg_dump_prop_clauses_file            -
% 2.93/0.98  --dbg_out_stat                          false
% 2.93/0.98  
% 2.93/0.98  
% 2.93/0.98  
% 2.93/0.98  
% 2.93/0.98  ------ Proving...
% 2.93/0.98  
% 2.93/0.98  
% 2.93/0.98  % SZS status Theorem for theBenchmark.p
% 2.93/0.98  
% 2.93/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.93/0.98  
% 2.93/0.98  fof(f11,axiom,(
% 2.93/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 2.93/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.93/0.98  
% 2.93/0.98  fof(f27,plain,(
% 2.93/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.93/0.98    inference(ennf_transformation,[],[f11])).
% 2.93/0.98  
% 2.93/0.98  fof(f28,plain,(
% 2.93/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.93/0.98    inference(flattening,[],[f27])).
% 2.93/0.98  
% 2.93/0.98  fof(f53,plain,(
% 2.93/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.93/0.98    inference(cnf_transformation,[],[f28])).
% 2.93/0.98  
% 2.93/0.98  fof(f8,axiom,(
% 2.93/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.93/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.93/0.98  
% 2.93/0.98  fof(f23,plain,(
% 2.93/0.98    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.93/0.98    inference(ennf_transformation,[],[f8])).
% 2.93/0.98  
% 2.93/0.98  fof(f24,plain,(
% 2.93/0.98    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.93/0.98    inference(flattening,[],[f23])).
% 2.93/0.98  
% 2.93/0.98  fof(f35,plain,(
% 2.93/0.98    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.93/0.98    inference(nnf_transformation,[],[f24])).
% 2.93/0.98  
% 2.93/0.98  fof(f47,plain,(
% 2.93/0.98    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.93/0.98    inference(cnf_transformation,[],[f35])).
% 2.93/0.98  
% 2.93/0.98  fof(f15,conjecture,(
% 2.93/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 2.93/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.93/0.98  
% 2.93/0.98  fof(f16,negated_conjecture,(
% 2.93/0.98    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 2.93/0.98    inference(negated_conjecture,[],[f15])).
% 2.93/0.98  
% 2.93/0.98  fof(f33,plain,(
% 2.93/0.98    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.93/0.98    inference(ennf_transformation,[],[f16])).
% 2.93/0.98  
% 2.93/0.98  fof(f34,plain,(
% 2.93/0.98    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.93/0.98    inference(flattening,[],[f33])).
% 2.93/0.98  
% 2.93/0.98  fof(f38,plain,(
% 2.93/0.98    ( ! [X2,X0,X1] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((~v2_funct_2(sK3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 2.93/0.98    introduced(choice_axiom,[])).
% 2.93/0.98  
% 2.93/0.98  fof(f37,plain,(
% 2.93/0.98    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 2.93/0.98    introduced(choice_axiom,[])).
% 2.93/0.98  
% 2.93/0.98  fof(f39,plain,(
% 2.93/0.98    ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 2.93/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f34,f38,f37])).
% 2.93/0.98  
% 2.93/0.98  fof(f64,plain,(
% 2.93/0.98    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.93/0.98    inference(cnf_transformation,[],[f39])).
% 2.93/0.98  
% 2.93/0.98  fof(f9,axiom,(
% 2.93/0.98    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 2.93/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.93/0.98  
% 2.93/0.98  fof(f49,plain,(
% 2.93/0.98    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.93/0.98    inference(cnf_transformation,[],[f9])).
% 2.93/0.98  
% 2.93/0.98  fof(f12,axiom,(
% 2.93/0.98    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.93/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.93/0.98  
% 2.93/0.98  fof(f54,plain,(
% 2.93/0.98    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.93/0.98    inference(cnf_transformation,[],[f12])).
% 2.93/0.98  
% 2.93/0.98  fof(f67,plain,(
% 2.93/0.98    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.93/0.98    inference(definition_unfolding,[],[f49,f54])).
% 2.93/0.98  
% 2.93/0.98  fof(f58,plain,(
% 2.93/0.98    v1_funct_1(sK2)),
% 2.93/0.98    inference(cnf_transformation,[],[f39])).
% 2.93/0.98  
% 2.93/0.98  fof(f60,plain,(
% 2.93/0.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.93/0.98    inference(cnf_transformation,[],[f39])).
% 2.93/0.98  
% 2.93/0.98  fof(f61,plain,(
% 2.93/0.98    v1_funct_1(sK3)),
% 2.93/0.98    inference(cnf_transformation,[],[f39])).
% 2.93/0.98  
% 2.93/0.98  fof(f63,plain,(
% 2.93/0.98    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.93/0.98    inference(cnf_transformation,[],[f39])).
% 2.93/0.98  
% 2.93/0.98  fof(f14,axiom,(
% 2.93/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 2.93/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.93/0.98  
% 2.93/0.98  fof(f31,plain,(
% 2.93/0.98    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.93/0.98    inference(ennf_transformation,[],[f14])).
% 2.93/0.98  
% 2.93/0.98  fof(f32,plain,(
% 2.93/0.98    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.93/0.98    inference(flattening,[],[f31])).
% 2.93/0.98  
% 2.93/0.98  fof(f56,plain,(
% 2.93/0.98    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X3) | k1_xboole_0 = X2 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.93/0.98    inference(cnf_transformation,[],[f32])).
% 2.93/0.98  
% 2.93/0.98  fof(f6,axiom,(
% 2.93/0.98    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 2.93/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.93/0.98  
% 2.93/0.98  fof(f21,plain,(
% 2.93/0.98    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 2.93/0.98    inference(ennf_transformation,[],[f6])).
% 2.93/0.98  
% 2.93/0.98  fof(f45,plain,(
% 2.93/0.98    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 2.93/0.98    inference(cnf_transformation,[],[f21])).
% 2.93/0.98  
% 2.93/0.98  fof(f13,axiom,(
% 2.93/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 2.93/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.93/0.98  
% 2.93/0.98  fof(f29,plain,(
% 2.93/0.98    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.93/0.98    inference(ennf_transformation,[],[f13])).
% 2.93/0.98  
% 2.93/0.98  fof(f30,plain,(
% 2.93/0.98    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.93/0.98    inference(flattening,[],[f29])).
% 2.93/0.98  
% 2.93/0.98  fof(f55,plain,(
% 2.93/0.98    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.93/0.98    inference(cnf_transformation,[],[f30])).
% 2.93/0.98  
% 2.93/0.98  fof(f7,axiom,(
% 2.93/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 2.93/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.93/0.98  
% 2.93/0.98  fof(f22,plain,(
% 2.93/0.98    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.93/0.98    inference(ennf_transformation,[],[f7])).
% 2.93/0.98  
% 2.93/0.98  fof(f46,plain,(
% 2.93/0.98    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.93/0.98    inference(cnf_transformation,[],[f22])).
% 2.93/0.98  
% 2.93/0.98  fof(f59,plain,(
% 2.93/0.98    v1_funct_2(sK2,sK0,sK1)),
% 2.93/0.98    inference(cnf_transformation,[],[f39])).
% 2.93/0.98  
% 2.93/0.98  fof(f62,plain,(
% 2.93/0.98    v1_funct_2(sK3,sK1,sK0)),
% 2.93/0.98    inference(cnf_transformation,[],[f39])).
% 2.93/0.98  
% 2.93/0.98  fof(f5,axiom,(
% 2.93/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.93/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.93/0.98  
% 2.93/0.98  fof(f17,plain,(
% 2.93/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 2.93/0.98    inference(pure_predicate_removal,[],[f5])).
% 2.93/0.98  
% 2.93/0.98  fof(f20,plain,(
% 2.93/0.98    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.93/0.98    inference(ennf_transformation,[],[f17])).
% 2.93/0.98  
% 2.93/0.98  fof(f44,plain,(
% 2.93/0.98    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.93/0.98    inference(cnf_transformation,[],[f20])).
% 2.93/0.98  
% 2.93/0.98  fof(f10,axiom,(
% 2.93/0.98    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 2.93/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.93/0.98  
% 2.93/0.98  fof(f25,plain,(
% 2.93/0.98    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.93/0.98    inference(ennf_transformation,[],[f10])).
% 2.93/0.98  
% 2.93/0.98  fof(f26,plain,(
% 2.93/0.98    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.93/0.98    inference(flattening,[],[f25])).
% 2.93/0.98  
% 2.93/0.98  fof(f36,plain,(
% 2.93/0.98    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.93/0.98    inference(nnf_transformation,[],[f26])).
% 2.93/0.98  
% 2.93/0.98  fof(f51,plain,(
% 2.93/0.98    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.93/0.98    inference(cnf_transformation,[],[f36])).
% 2.93/0.98  
% 2.93/0.98  fof(f69,plain,(
% 2.93/0.98    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.93/0.98    inference(equality_resolution,[],[f51])).
% 2.93/0.98  
% 2.93/0.98  fof(f4,axiom,(
% 2.93/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.93/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.93/0.98  
% 2.93/0.98  fof(f19,plain,(
% 2.93/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.93/0.98    inference(ennf_transformation,[],[f4])).
% 2.93/0.98  
% 2.93/0.98  fof(f43,plain,(
% 2.93/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.93/0.98    inference(cnf_transformation,[],[f19])).
% 2.93/0.98  
% 2.93/0.98  fof(f65,plain,(
% 2.93/0.98    ~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)),
% 2.93/0.98    inference(cnf_transformation,[],[f39])).
% 2.93/0.98  
% 2.93/0.98  fof(f2,axiom,(
% 2.93/0.98    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 2.93/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.93/0.98  
% 2.93/0.98  fof(f18,plain,(
% 2.93/0.98    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 2.93/0.98    inference(ennf_transformation,[],[f2])).
% 2.93/0.98  
% 2.93/0.98  fof(f41,plain,(
% 2.93/0.98    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 2.93/0.98    inference(cnf_transformation,[],[f18])).
% 2.93/0.98  
% 2.93/0.98  fof(f1,axiom,(
% 2.93/0.98    v1_xboole_0(k1_xboole_0)),
% 2.93/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.93/0.98  
% 2.93/0.98  fof(f40,plain,(
% 2.93/0.98    v1_xboole_0(k1_xboole_0)),
% 2.93/0.98    inference(cnf_transformation,[],[f1])).
% 2.93/0.98  
% 2.93/0.98  fof(f3,axiom,(
% 2.93/0.98    ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 2.93/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.93/0.98  
% 2.93/0.98  fof(f42,plain,(
% 2.93/0.98    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 2.93/0.98    inference(cnf_transformation,[],[f3])).
% 2.93/0.98  
% 2.93/0.98  fof(f66,plain,(
% 2.93/0.98    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 2.93/0.98    inference(definition_unfolding,[],[f42,f54])).
% 2.93/0.98  
% 2.93/0.98  cnf(c_651,plain,
% 2.93/0.98      ( ~ v2_funct_1(X0_48) | v2_funct_1(X1_48) | X1_48 != X0_48 ),
% 2.93/0.98      theory(equality) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_3440,plain,
% 2.93/0.98      ( ~ v2_funct_1(X0_48) | v2_funct_1(sK2) | sK2 != X0_48 ),
% 2.93/0.98      inference(instantiation,[status(thm)],[c_651]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_3442,plain,
% 2.93/0.98      ( v2_funct_1(sK2) | ~ v2_funct_1(sK0) | sK2 != sK0 ),
% 2.93/0.98      inference(instantiation,[status(thm)],[c_3440]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_12,plain,
% 2.93/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.93/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 2.93/0.98      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 2.93/0.98      | ~ v1_funct_1(X0)
% 2.93/0.98      | ~ v1_funct_1(X3) ),
% 2.93/0.98      inference(cnf_transformation,[],[f53]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_635,plain,
% 2.93/0.98      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
% 2.93/0.98      | ~ m1_subset_1(X3_48,k1_zfmisc_1(k2_zfmisc_1(X4_48,X5_48)))
% 2.93/0.98      | m1_subset_1(k1_partfun1(X4_48,X5_48,X1_48,X2_48,X3_48,X0_48),k1_zfmisc_1(k2_zfmisc_1(X4_48,X2_48)))
% 2.93/0.98      | ~ v1_funct_1(X0_48)
% 2.93/0.98      | ~ v1_funct_1(X3_48) ),
% 2.93/0.98      inference(subtyping,[status(esa)],[c_12]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_1056,plain,
% 2.93/0.98      ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48))) != iProver_top
% 2.93/0.98      | m1_subset_1(X3_48,k1_zfmisc_1(k2_zfmisc_1(X4_48,X5_48))) != iProver_top
% 2.93/0.98      | m1_subset_1(k1_partfun1(X4_48,X5_48,X1_48,X2_48,X3_48,X0_48),k1_zfmisc_1(k2_zfmisc_1(X4_48,X2_48))) = iProver_top
% 2.93/0.98      | v1_funct_1(X0_48) != iProver_top
% 2.93/0.98      | v1_funct_1(X3_48) != iProver_top ),
% 2.93/0.98      inference(predicate_to_equality,[status(thm)],[c_635]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_8,plain,
% 2.93/0.98      ( ~ r2_relset_1(X0,X1,X2,X3)
% 2.93/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.93/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.93/0.98      | X3 = X2 ),
% 2.93/0.98      inference(cnf_transformation,[],[f47]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_18,negated_conjecture,
% 2.93/0.98      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 2.93/0.98      inference(cnf_transformation,[],[f64]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_414,plain,
% 2.93/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.93/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.93/0.98      | X3 = X0
% 2.93/0.98      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 2.93/0.98      | k6_partfun1(sK0) != X3
% 2.93/0.98      | sK0 != X2
% 2.93/0.98      | sK0 != X1 ),
% 2.93/0.98      inference(resolution_lifted,[status(thm)],[c_8,c_18]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_415,plain,
% 2.93/0.98      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.93/0.98      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.93/0.98      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 2.93/0.98      inference(unflattening,[status(thm)],[c_414]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_9,plain,
% 2.93/0.98      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 2.93/0.98      inference(cnf_transformation,[],[f67]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_55,plain,
% 2.93/0.98      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 2.93/0.98      inference(instantiation,[status(thm)],[c_9]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_417,plain,
% 2.93/0.98      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.93/0.98      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 2.93/0.98      inference(global_propositional_subsumption,
% 2.93/0.98                [status(thm)],
% 2.93/0.98                [c_415,c_55]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_623,plain,
% 2.93/0.98      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.93/0.98      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 2.93/0.98      inference(subtyping,[status(esa)],[c_417]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_1069,plain,
% 2.93/0.98      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 2.93/0.98      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 2.93/0.98      inference(predicate_to_equality,[status(thm)],[c_623]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_2147,plain,
% 2.93/0.98      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
% 2.93/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.93/0.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.93/0.98      | v1_funct_1(sK2) != iProver_top
% 2.93/0.98      | v1_funct_1(sK3) != iProver_top ),
% 2.93/0.98      inference(superposition,[status(thm)],[c_1056,c_1069]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_24,negated_conjecture,
% 2.93/0.98      ( v1_funct_1(sK2) ),
% 2.93/0.98      inference(cnf_transformation,[],[f58]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_25,plain,
% 2.93/0.98      ( v1_funct_1(sK2) = iProver_top ),
% 2.93/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_22,negated_conjecture,
% 2.93/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.93/0.98      inference(cnf_transformation,[],[f60]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_27,plain,
% 2.93/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.93/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_21,negated_conjecture,
% 2.93/0.98      ( v1_funct_1(sK3) ),
% 2.93/0.98      inference(cnf_transformation,[],[f61]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_28,plain,
% 2.93/0.98      ( v1_funct_1(sK3) = iProver_top ),
% 2.93/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_19,negated_conjecture,
% 2.93/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 2.93/0.98      inference(cnf_transformation,[],[f63]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_30,plain,
% 2.93/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 2.93/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_2396,plain,
% 2.93/0.98      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
% 2.93/0.98      inference(global_propositional_subsumption,
% 2.93/0.98                [status(thm)],
% 2.93/0.98                [c_2147,c_25,c_27,c_28,c_30]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_16,plain,
% 2.93/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.93/0.98      | ~ v1_funct_2(X3,X2,X4)
% 2.93/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.93/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
% 2.93/0.98      | ~ v1_funct_1(X3)
% 2.93/0.98      | ~ v1_funct_1(X0)
% 2.93/0.98      | v2_funct_1(X0)
% 2.93/0.98      | ~ v2_funct_1(k1_partfun1(X1,X2,X2,X4,X0,X3))
% 2.93/0.98      | k1_xboole_0 = X4 ),
% 2.93/0.98      inference(cnf_transformation,[],[f56]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_632,plain,
% 2.93/0.98      ( ~ v1_funct_2(X0_48,X1_48,X2_48)
% 2.93/0.98      | ~ v1_funct_2(X3_48,X2_48,X4_48)
% 2.93/0.98      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
% 2.93/0.98      | ~ m1_subset_1(X3_48,k1_zfmisc_1(k2_zfmisc_1(X2_48,X4_48)))
% 2.93/0.98      | ~ v1_funct_1(X0_48)
% 2.93/0.98      | ~ v1_funct_1(X3_48)
% 2.93/0.98      | v2_funct_1(X0_48)
% 2.93/0.98      | ~ v2_funct_1(k1_partfun1(X1_48,X2_48,X2_48,X4_48,X0_48,X3_48))
% 2.93/0.98      | k1_xboole_0 = X4_48 ),
% 2.93/0.98      inference(subtyping,[status(esa)],[c_16]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_1059,plain,
% 2.93/0.98      ( k1_xboole_0 = X0_48
% 2.93/0.98      | v1_funct_2(X1_48,X2_48,X3_48) != iProver_top
% 2.93/0.99      | v1_funct_2(X4_48,X3_48,X0_48) != iProver_top
% 2.93/0.99      | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_48,X3_48))) != iProver_top
% 2.93/0.99      | m1_subset_1(X4_48,k1_zfmisc_1(k2_zfmisc_1(X3_48,X0_48))) != iProver_top
% 2.93/0.99      | v1_funct_1(X1_48) != iProver_top
% 2.93/0.99      | v1_funct_1(X4_48) != iProver_top
% 2.93/0.99      | v2_funct_1(X1_48) = iProver_top
% 2.93/0.99      | v2_funct_1(k1_partfun1(X2_48,X3_48,X3_48,X0_48,X1_48,X4_48)) != iProver_top ),
% 2.93/0.99      inference(predicate_to_equality,[status(thm)],[c_632]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_2422,plain,
% 2.93/0.99      ( sK0 = k1_xboole_0
% 2.93/0.99      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 2.93/0.99      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 2.93/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.93/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.93/0.99      | v1_funct_1(sK2) != iProver_top
% 2.93/0.99      | v1_funct_1(sK3) != iProver_top
% 2.93/0.99      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 2.93/0.99      | v2_funct_1(sK2) = iProver_top ),
% 2.93/0.99      inference(superposition,[status(thm)],[c_2396,c_1059]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_636,plain,
% 2.93/0.99      ( m1_subset_1(k6_partfun1(X0_48),k1_zfmisc_1(k2_zfmisc_1(X0_48,X0_48))) ),
% 2.93/0.99      inference(subtyping,[status(esa)],[c_9]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_1055,plain,
% 2.93/0.99      ( m1_subset_1(k6_partfun1(X0_48),k1_zfmisc_1(k2_zfmisc_1(X0_48,X0_48))) = iProver_top ),
% 2.93/0.99      inference(predicate_to_equality,[status(thm)],[c_636]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_5,plain,
% 2.93/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.93/0.99      | ~ v1_xboole_0(X1)
% 2.93/0.99      | v1_xboole_0(X0) ),
% 2.93/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_638,plain,
% 2.93/0.99      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
% 2.93/0.99      | ~ v1_xboole_0(X1_48)
% 2.93/0.99      | v1_xboole_0(X0_48) ),
% 2.93/0.99      inference(subtyping,[status(esa)],[c_5]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_1053,plain,
% 2.93/0.99      ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48))) != iProver_top
% 2.93/0.99      | v1_xboole_0(X1_48) != iProver_top
% 2.93/0.99      | v1_xboole_0(X0_48) = iProver_top ),
% 2.93/0.99      inference(predicate_to_equality,[status(thm)],[c_638]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_2077,plain,
% 2.93/0.99      ( v1_xboole_0(X0_48) != iProver_top
% 2.93/0.99      | v1_xboole_0(k6_partfun1(X0_48)) = iProver_top ),
% 2.93/0.99      inference(superposition,[status(thm)],[c_1055,c_1053]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_2092,plain,
% 2.93/0.99      ( ~ v1_xboole_0(X0_48) | v1_xboole_0(k6_partfun1(X0_48)) ),
% 2.93/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_2077]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_2094,plain,
% 2.93/0.99      ( v1_xboole_0(k6_partfun1(sK0)) | ~ v1_xboole_0(sK0) ),
% 2.93/0.99      inference(instantiation,[status(thm)],[c_2092]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_628,negated_conjecture,
% 2.93/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.93/0.99      inference(subtyping,[status(esa)],[c_22]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_1063,plain,
% 2.93/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.93/0.99      inference(predicate_to_equality,[status(thm)],[c_628]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_2076,plain,
% 2.93/0.99      ( v1_xboole_0(sK2) = iProver_top
% 2.93/0.99      | v1_xboole_0(sK0) != iProver_top ),
% 2.93/0.99      inference(superposition,[status(thm)],[c_1063,c_1053]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_2091,plain,
% 2.93/0.99      ( v1_xboole_0(sK2) | ~ v1_xboole_0(sK0) ),
% 2.93/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_2076]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_631,negated_conjecture,
% 2.93/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 2.93/0.99      inference(subtyping,[status(esa)],[c_19]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_1060,plain,
% 2.93/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 2.93/0.99      inference(predicate_to_equality,[status(thm)],[c_631]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_14,plain,
% 2.93/0.99      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 2.93/0.99      | ~ v1_funct_2(X2,X0,X1)
% 2.93/0.99      | ~ v1_funct_2(X3,X1,X0)
% 2.93/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.93/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.93/0.99      | ~ v1_funct_1(X2)
% 2.93/0.99      | ~ v1_funct_1(X3)
% 2.93/0.99      | k2_relset_1(X1,X0,X3) = X0 ),
% 2.93/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_428,plain,
% 2.93/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.93/0.99      | ~ v1_funct_2(X3,X2,X1)
% 2.93/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.93/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.93/0.99      | ~ v1_funct_1(X3)
% 2.93/0.99      | ~ v1_funct_1(X0)
% 2.93/0.99      | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 2.93/0.99      | k2_relset_1(X2,X1,X3) = X1
% 2.93/0.99      | k6_partfun1(X1) != k6_partfun1(sK0)
% 2.93/0.99      | sK0 != X1 ),
% 2.93/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_18]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_429,plain,
% 2.93/0.99      ( ~ v1_funct_2(X0,X1,sK0)
% 2.93/0.99      | ~ v1_funct_2(X2,sK0,X1)
% 2.93/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 2.93/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 2.93/0.99      | ~ v1_funct_1(X2)
% 2.93/0.99      | ~ v1_funct_1(X0)
% 2.93/0.99      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 2.93/0.99      | k2_relset_1(X1,sK0,X0) = sK0
% 2.93/0.99      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 2.93/0.99      inference(unflattening,[status(thm)],[c_428]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_503,plain,
% 2.93/0.99      ( ~ v1_funct_2(X0,X1,sK0)
% 2.93/0.99      | ~ v1_funct_2(X2,sK0,X1)
% 2.93/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 2.93/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 2.93/0.99      | ~ v1_funct_1(X0)
% 2.93/0.99      | ~ v1_funct_1(X2)
% 2.93/0.99      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 2.93/0.99      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 2.93/0.99      inference(equality_resolution_simp,[status(thm)],[c_429]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_622,plain,
% 2.93/0.99      ( ~ v1_funct_2(X0_48,X1_48,sK0)
% 2.93/0.99      | ~ v1_funct_2(X2_48,sK0,X1_48)
% 2.93/0.99      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,sK0)))
% 2.93/0.99      | ~ m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(sK0,X1_48)))
% 2.93/0.99      | ~ v1_funct_1(X0_48)
% 2.93/0.99      | ~ v1_funct_1(X2_48)
% 2.93/0.99      | k1_partfun1(sK0,X1_48,X1_48,sK0,X2_48,X0_48) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 2.93/0.99      | k2_relset_1(X1_48,sK0,X0_48) = sK0 ),
% 2.93/0.99      inference(subtyping,[status(esa)],[c_503]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_1070,plain,
% 2.93/0.99      ( k1_partfun1(sK0,X0_48,X0_48,sK0,X1_48,X2_48) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 2.93/0.99      | k2_relset_1(X0_48,sK0,X2_48) = sK0
% 2.93/0.99      | v1_funct_2(X2_48,X0_48,sK0) != iProver_top
% 2.93/0.99      | v1_funct_2(X1_48,sK0,X0_48) != iProver_top
% 2.93/0.99      | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,sK0))) != iProver_top
% 2.93/0.99      | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_48))) != iProver_top
% 2.93/0.99      | v1_funct_1(X2_48) != iProver_top
% 2.93/0.99      | v1_funct_1(X1_48) != iProver_top ),
% 2.93/0.99      inference(predicate_to_equality,[status(thm)],[c_622]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_1956,plain,
% 2.93/0.99      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 2.93/0.99      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 2.93/0.99      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 2.93/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.93/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.93/0.99      | v1_funct_1(sK2) != iProver_top
% 2.93/0.99      | v1_funct_1(sK3) != iProver_top ),
% 2.93/0.99      inference(equality_resolution,[status(thm)],[c_1070]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_6,plain,
% 2.93/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.93/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.93/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_637,plain,
% 2.93/0.99      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
% 2.93/0.99      | k2_relset_1(X1_48,X2_48,X0_48) = k2_relat_1(X0_48) ),
% 2.93/0.99      inference(subtyping,[status(esa)],[c_6]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_1054,plain,
% 2.93/0.99      ( k2_relset_1(X0_48,X1_48,X2_48) = k2_relat_1(X2_48)
% 2.93/0.99      | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top ),
% 2.93/0.99      inference(predicate_to_equality,[status(thm)],[c_637]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_1639,plain,
% 2.93/0.99      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 2.93/0.99      inference(superposition,[status(thm)],[c_1060,c_1054]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_1957,plain,
% 2.93/0.99      ( k2_relat_1(sK3) = sK0
% 2.93/0.99      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 2.93/0.99      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 2.93/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.93/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.93/0.99      | v1_funct_1(sK2) != iProver_top
% 2.93/0.99      | v1_funct_1(sK3) != iProver_top ),
% 2.93/0.99      inference(demodulation,[status(thm)],[c_1956,c_1639]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_23,negated_conjecture,
% 2.93/0.99      ( v1_funct_2(sK2,sK0,sK1) ),
% 2.93/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_26,plain,
% 2.93/0.99      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 2.93/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_20,negated_conjecture,
% 2.93/0.99      ( v1_funct_2(sK3,sK1,sK0) ),
% 2.93/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_29,plain,
% 2.93/0.99      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 2.93/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_1960,plain,
% 2.93/0.99      ( k2_relat_1(sK3) = sK0 ),
% 2.93/0.99      inference(global_propositional_subsumption,
% 2.93/0.99                [status(thm)],
% 2.93/0.99                [c_1957,c_25,c_26,c_27,c_28,c_29,c_30]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_4,plain,
% 2.93/0.99      ( v5_relat_1(X0,X1)
% 2.93/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.93/0.99      inference(cnf_transformation,[],[f44]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_10,plain,
% 2.93/0.99      ( v2_funct_2(X0,k2_relat_1(X0))
% 2.93/0.99      | ~ v5_relat_1(X0,k2_relat_1(X0))
% 2.93/0.99      | ~ v1_relat_1(X0) ),
% 2.93/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_332,plain,
% 2.93/0.99      ( v2_funct_2(X0,k2_relat_1(X0))
% 2.93/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 2.93/0.99      | ~ v1_relat_1(X0)
% 2.93/0.99      | X0 != X1
% 2.93/0.99      | k2_relat_1(X0) != X3 ),
% 2.93/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_10]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_333,plain,
% 2.93/0.99      ( v2_funct_2(X0,k2_relat_1(X0))
% 2.93/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
% 2.93/0.99      | ~ v1_relat_1(X0) ),
% 2.93/0.99      inference(unflattening,[status(thm)],[c_332]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_3,plain,
% 2.93/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.93/0.99      | v1_relat_1(X0) ),
% 2.93/0.99      inference(cnf_transformation,[],[f43]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_343,plain,
% 2.93/0.99      ( v2_funct_2(X0,k2_relat_1(X0))
% 2.93/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0)))) ),
% 2.93/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_333,c_3]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_17,negated_conjecture,
% 2.93/0.99      ( ~ v2_funct_2(sK3,sK0) | ~ v2_funct_1(sK2) ),
% 2.93/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_358,plain,
% 2.93/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
% 2.93/0.99      | ~ v2_funct_1(sK2)
% 2.93/0.99      | k2_relat_1(X0) != sK0
% 2.93/0.99      | sK3 != X0 ),
% 2.93/0.99      inference(resolution_lifted,[status(thm)],[c_343,c_17]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_359,plain,
% 2.93/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3))))
% 2.93/0.99      | ~ v2_funct_1(sK2)
% 2.93/0.99      | k2_relat_1(sK3) != sK0 ),
% 2.93/0.99      inference(unflattening,[status(thm)],[c_358]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_625,plain,
% 2.93/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_48,k2_relat_1(sK3))))
% 2.93/0.99      | ~ v2_funct_1(sK2)
% 2.93/0.99      | k2_relat_1(sK3) != sK0 ),
% 2.93/0.99      inference(subtyping,[status(esa)],[c_359]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_642,plain,
% 2.93/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_48,k2_relat_1(sK3))))
% 2.93/0.99      | ~ sP0_iProver_split ),
% 2.93/0.99      inference(splitting,
% 2.93/0.99                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.93/0.99                [c_625]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_1067,plain,
% 2.93/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_48,k2_relat_1(sK3)))) != iProver_top
% 2.93/0.99      | sP0_iProver_split != iProver_top ),
% 2.93/0.99      inference(predicate_to_equality,[status(thm)],[c_642]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_1964,plain,
% 2.93/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_48,sK0))) != iProver_top
% 2.93/0.99      | sP0_iProver_split != iProver_top ),
% 2.93/0.99      inference(demodulation,[status(thm)],[c_1960,c_1067]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_2033,plain,
% 2.93/0.99      ( sP0_iProver_split != iProver_top ),
% 2.93/0.99      inference(superposition,[status(thm)],[c_1060,c_1964]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_2034,plain,
% 2.93/0.99      ( ~ sP0_iProver_split ),
% 2.93/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_2033]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_643,plain,
% 2.93/0.99      ( ~ v2_funct_1(sK2) | sP0_iProver_split | k2_relat_1(sK3) != sK0 ),
% 2.93/0.99      inference(splitting,
% 2.93/0.99                [splitting(split),new_symbols(definition,[])],
% 2.93/0.99                [c_625]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_1066,plain,
% 2.93/0.99      ( k2_relat_1(sK3) != sK0
% 2.93/0.99      | v2_funct_1(sK2) != iProver_top
% 2.93/0.99      | sP0_iProver_split = iProver_top ),
% 2.93/0.99      inference(predicate_to_equality,[status(thm)],[c_643]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_1965,plain,
% 2.93/0.99      ( sK0 != sK0
% 2.93/0.99      | v2_funct_1(sK2) != iProver_top
% 2.93/0.99      | sP0_iProver_split = iProver_top ),
% 2.93/0.99      inference(demodulation,[status(thm)],[c_1960,c_1066]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_1966,plain,
% 2.93/0.99      ( v2_funct_1(sK2) != iProver_top
% 2.93/0.99      | sP0_iProver_split = iProver_top ),
% 2.93/0.99      inference(equality_resolution_simp,[status(thm)],[c_1965]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_1,plain,
% 2.93/0.99      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X1 = X0 ),
% 2.93/0.99      inference(cnf_transformation,[],[f41]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_640,plain,
% 2.93/0.99      ( ~ v1_xboole_0(X0_48) | ~ v1_xboole_0(X1_48) | X1_48 = X0_48 ),
% 2.93/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_1650,plain,
% 2.93/0.99      ( ~ v1_xboole_0(X0_48) | ~ v1_xboole_0(sK2) | sK2 = X0_48 ),
% 2.93/0.99      inference(instantiation,[status(thm)],[c_640]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_1652,plain,
% 2.93/0.99      ( ~ v1_xboole_0(sK2) | ~ v1_xboole_0(sK0) | sK2 = sK0 ),
% 2.93/0.99      inference(instantiation,[status(thm)],[c_1650]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_1521,plain,
% 2.93/0.99      ( ~ v1_xboole_0(X0_48)
% 2.93/0.99      | ~ v1_xboole_0(k6_partfun1(X1_48))
% 2.93/0.99      | X0_48 = k6_partfun1(X1_48) ),
% 2.93/0.99      inference(instantiation,[status(thm)],[c_640]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_1523,plain,
% 2.93/0.99      ( ~ v1_xboole_0(k6_partfun1(sK0))
% 2.93/0.99      | ~ v1_xboole_0(sK0)
% 2.93/0.99      | sK0 = k6_partfun1(sK0) ),
% 2.93/0.99      inference(instantiation,[status(thm)],[c_1521]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_649,plain,
% 2.93/0.99      ( ~ v1_xboole_0(X0_48) | v1_xboole_0(X1_48) | X1_48 != X0_48 ),
% 2.93/0.99      theory(equality) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_1380,plain,
% 2.93/0.99      ( v1_xboole_0(X0_48)
% 2.93/0.99      | ~ v1_xboole_0(k1_xboole_0)
% 2.93/0.99      | X0_48 != k1_xboole_0 ),
% 2.93/0.99      inference(instantiation,[status(thm)],[c_649]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_1382,plain,
% 2.93/0.99      ( v1_xboole_0(sK0)
% 2.93/0.99      | ~ v1_xboole_0(k1_xboole_0)
% 2.93/0.99      | sK0 != k1_xboole_0 ),
% 2.93/0.99      inference(instantiation,[status(thm)],[c_1380]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_1266,plain,
% 2.93/0.99      ( v2_funct_1(X0_48)
% 2.93/0.99      | ~ v2_funct_1(k6_partfun1(X1_48))
% 2.93/0.99      | X0_48 != k6_partfun1(X1_48) ),
% 2.93/0.99      inference(instantiation,[status(thm)],[c_651]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_1268,plain,
% 2.93/0.99      ( ~ v2_funct_1(k6_partfun1(sK0))
% 2.93/0.99      | v2_funct_1(sK0)
% 2.93/0.99      | sK0 != k6_partfun1(sK0) ),
% 2.93/0.99      inference(instantiation,[status(thm)],[c_1266]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_0,plain,
% 2.93/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 2.93/0.99      inference(cnf_transformation,[],[f40]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_2,plain,
% 2.93/0.99      ( v2_funct_1(k6_partfun1(X0)) ),
% 2.93/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_73,plain,
% 2.93/0.99      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 2.93/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_75,plain,
% 2.93/0.99      ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
% 2.93/0.99      inference(instantiation,[status(thm)],[c_73]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(c_74,plain,
% 2.93/0.99      ( v2_funct_1(k6_partfun1(sK0)) ),
% 2.93/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 2.93/0.99  
% 2.93/0.99  cnf(contradiction,plain,
% 2.93/0.99      ( $false ),
% 2.93/0.99      inference(minisat,
% 2.93/0.99                [status(thm)],
% 2.93/0.99                [c_3442,c_2422,c_2094,c_2091,c_2034,c_2033,c_1966,c_1957,
% 2.93/0.99                 c_1652,c_1523,c_1382,c_1268,c_643,c_0,c_75,c_74,c_30,
% 2.93/0.99                 c_29,c_28,c_27,c_26,c_25]) ).
% 2.93/0.99  
% 2.93/0.99  
% 2.93/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.93/0.99  
% 2.93/0.99  ------                               Statistics
% 2.93/0.99  
% 2.93/0.99  ------ General
% 2.93/0.99  
% 2.93/0.99  abstr_ref_over_cycles:                  0
% 2.93/0.99  abstr_ref_under_cycles:                 0
% 2.93/0.99  gc_basic_clause_elim:                   0
% 2.93/0.99  forced_gc_time:                         0
% 2.93/0.99  parsing_time:                           0.008
% 2.93/0.99  unif_index_cands_time:                  0.
% 2.93/0.99  unif_index_add_time:                    0.
% 2.93/0.99  orderings_time:                         0.
% 2.93/0.99  out_proof_time:                         0.012
% 2.93/0.99  total_time:                             0.158
% 2.93/0.99  num_of_symbols:                         52
% 2.93/0.99  num_of_terms:                           6470
% 2.93/0.99  
% 2.93/0.99  ------ Preprocessing
% 2.93/0.99  
% 2.93/0.99  num_of_splits:                          1
% 2.93/0.99  num_of_split_atoms:                     1
% 2.93/0.99  num_of_reused_defs:                     0
% 2.93/0.99  num_eq_ax_congr_red:                    10
% 2.93/0.99  num_of_sem_filtered_clauses:            1
% 2.93/0.99  num_of_subtypes:                        3
% 2.93/0.99  monotx_restored_types:                  1
% 2.93/0.99  sat_num_of_epr_types:                   0
% 2.93/0.99  sat_num_of_non_cyclic_types:            0
% 2.93/0.99  sat_guarded_non_collapsed_types:        1
% 2.93/0.99  num_pure_diseq_elim:                    0
% 2.93/0.99  simp_replaced_by:                       0
% 2.93/0.99  res_preprocessed:                       118
% 2.93/0.99  prep_upred:                             0
% 2.93/0.99  prep_unflattend:                        17
% 2.93/0.99  smt_new_axioms:                         0
% 2.93/0.99  pred_elim_cands:                        5
% 2.93/0.99  pred_elim:                              4
% 2.93/0.99  pred_elim_cl:                           5
% 2.93/0.99  pred_elim_cycles:                       7
% 2.93/0.99  merged_defs:                            0
% 2.93/0.99  merged_defs_ncl:                        0
% 2.93/0.99  bin_hyper_res:                          0
% 2.93/0.99  prep_cycles:                            4
% 2.93/0.99  pred_elim_time:                         0.003
% 2.93/0.99  splitting_time:                         0.
% 2.93/0.99  sem_filter_time:                        0.
% 2.93/0.99  monotx_time:                            0.
% 2.93/0.99  subtype_inf_time:                       0.001
% 2.93/0.99  
% 2.93/0.99  ------ Problem properties
% 2.93/0.99  
% 2.93/0.99  clauses:                                21
% 2.93/0.99  conjectures:                            6
% 2.93/0.99  epr:                                    6
% 2.93/0.99  horn:                                   20
% 2.93/0.99  ground:                                 9
% 2.93/0.99  unary:                                  9
% 2.93/0.99  binary:                                 3
% 2.93/0.99  lits:                                   67
% 2.93/0.99  lits_eq:                                9
% 2.93/0.99  fd_pure:                                0
% 2.93/0.99  fd_pseudo:                              0
% 2.93/0.99  fd_cond:                                1
% 2.93/0.99  fd_pseudo_cond:                         1
% 2.93/0.99  ac_symbols:                             0
% 2.93/0.99  
% 2.93/0.99  ------ Propositional Solver
% 2.93/0.99  
% 2.93/0.99  prop_solver_calls:                      26
% 2.93/0.99  prop_fast_solver_calls:                 887
% 2.93/0.99  smt_solver_calls:                       0
% 2.93/0.99  smt_fast_solver_calls:                  0
% 2.93/0.99  prop_num_of_clauses:                    1421
% 2.93/0.99  prop_preprocess_simplified:             4511
% 2.93/0.99  prop_fo_subsumed:                       25
% 2.93/0.99  prop_solver_time:                       0.
% 2.93/0.99  smt_solver_time:                        0.
% 2.93/0.99  smt_fast_solver_time:                   0.
% 2.93/0.99  prop_fast_solver_time:                  0.
% 2.93/0.99  prop_unsat_core_time:                   0.
% 2.93/0.99  
% 2.93/0.99  ------ QBF
% 2.93/0.99  
% 2.93/0.99  qbf_q_res:                              0
% 2.93/0.99  qbf_num_tautologies:                    0
% 2.93/0.99  qbf_prep_cycles:                        0
% 2.93/0.99  
% 2.93/0.99  ------ BMC1
% 2.93/0.99  
% 2.93/0.99  bmc1_current_bound:                     -1
% 2.93/0.99  bmc1_last_solved_bound:                 -1
% 2.93/0.99  bmc1_unsat_core_size:                   -1
% 2.93/0.99  bmc1_unsat_core_parents_size:           -1
% 2.93/0.99  bmc1_merge_next_fun:                    0
% 2.93/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.93/0.99  
% 2.93/0.99  ------ Instantiation
% 2.93/0.99  
% 2.93/0.99  inst_num_of_clauses:                    366
% 2.93/0.99  inst_num_in_passive:                    124
% 2.93/0.99  inst_num_in_active:                     199
% 2.93/0.99  inst_num_in_unprocessed:                42
% 2.93/0.99  inst_num_of_loops:                      245
% 2.93/0.99  inst_num_of_learning_restarts:          0
% 2.93/0.99  inst_num_moves_active_passive:          42
% 2.93/0.99  inst_lit_activity:                      0
% 2.93/0.99  inst_lit_activity_moves:                0
% 2.93/0.99  inst_num_tautologies:                   0
% 2.93/0.99  inst_num_prop_implied:                  0
% 2.93/0.99  inst_num_existing_simplified:           0
% 2.93/0.99  inst_num_eq_res_simplified:             0
% 2.93/0.99  inst_num_child_elim:                    0
% 2.93/0.99  inst_num_of_dismatching_blockings:      6
% 2.93/0.99  inst_num_of_non_proper_insts:           257
% 2.93/0.99  inst_num_of_duplicates:                 0
% 2.93/0.99  inst_inst_num_from_inst_to_res:         0
% 2.93/0.99  inst_dismatching_checking_time:         0.
% 2.93/0.99  
% 2.93/0.99  ------ Resolution
% 2.93/0.99  
% 2.93/0.99  res_num_of_clauses:                     0
% 2.93/0.99  res_num_in_passive:                     0
% 2.93/0.99  res_num_in_active:                      0
% 2.93/0.99  res_num_of_loops:                       122
% 2.93/0.99  res_forward_subset_subsumed:            17
% 2.93/0.99  res_backward_subset_subsumed:           0
% 2.93/0.99  res_forward_subsumed:                   0
% 2.93/0.99  res_backward_subsumed:                  0
% 2.93/0.99  res_forward_subsumption_resolution:     3
% 2.93/0.99  res_backward_subsumption_resolution:    0
% 2.93/0.99  res_clause_to_clause_subsumption:       66
% 2.93/0.99  res_orphan_elimination:                 0
% 2.93/0.99  res_tautology_del:                      12
% 2.93/0.99  res_num_eq_res_simplified:              1
% 2.93/0.99  res_num_sel_changes:                    0
% 2.93/0.99  res_moves_from_active_to_pass:          0
% 2.93/0.99  
% 2.93/0.99  ------ Superposition
% 2.93/0.99  
% 2.93/0.99  sup_time_total:                         0.
% 2.93/0.99  sup_time_generating:                    0.
% 2.93/0.99  sup_time_sim_full:                      0.
% 2.93/0.99  sup_time_sim_immed:                     0.
% 2.93/0.99  
% 2.93/0.99  sup_num_of_clauses:                     33
% 2.93/0.99  sup_num_in_active:                      22
% 2.93/0.99  sup_num_in_passive:                     11
% 2.93/0.99  sup_num_of_loops:                       48
% 2.93/0.99  sup_fw_superposition:                   11
% 2.93/0.99  sup_bw_superposition:                   15
% 2.93/0.99  sup_immediate_simplified:               6
% 2.93/0.99  sup_given_eliminated:                   1
% 2.93/0.99  comparisons_done:                       0
% 2.93/0.99  comparisons_avoided:                    0
% 2.93/0.99  
% 2.93/0.99  ------ Simplifications
% 2.93/0.99  
% 2.93/0.99  
% 2.93/0.99  sim_fw_subset_subsumed:                 3
% 2.93/0.99  sim_bw_subset_subsumed:                 0
% 2.93/0.99  sim_fw_subsumed:                        2
% 2.93/0.99  sim_bw_subsumed:                        0
% 2.93/0.99  sim_fw_subsumption_res:                 0
% 2.93/0.99  sim_bw_subsumption_res:                 0
% 2.93/0.99  sim_tautology_del:                      0
% 2.93/0.99  sim_eq_tautology_del:                   4
% 2.93/0.99  sim_eq_res_simp:                        1
% 2.93/0.99  sim_fw_demodulated:                     1
% 2.93/0.99  sim_bw_demodulated:                     26
% 2.93/0.99  sim_light_normalised:                   0
% 2.93/0.99  sim_joinable_taut:                      0
% 2.93/0.99  sim_joinable_simp:                      0
% 2.93/0.99  sim_ac_normalised:                      0
% 2.93/0.99  sim_smt_subsumption:                    0
% 2.93/0.99  
%------------------------------------------------------------------------------

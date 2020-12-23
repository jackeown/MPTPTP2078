%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:39 EST 2020

% Result     : Theorem 7.77s
% Output     : CNFRefutation 7.77s
% Verified   : 
% Statistics : Number of formulae       :  206 (3981 expanded)
%              Number of clauses        :  133 (1068 expanded)
%              Number of leaves         :   19 (1075 expanded)
%              Depth                    :   22
%              Number of atoms          :  822 (34024 expanded)
%              Number of equality atoms :  428 (12521 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
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

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f12])).

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
    inference(flattening,[],[f28])).

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
    inference(cnf_transformation,[],[f29])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( ( v2_funct_1(X2)
              & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
              & k2_relset_1(X0,X1,X2) = X1 )
           => ( k2_funct_1(X2) = X3
              | k1_xboole_0 = X1
              | k1_xboole_0 = X0 ) ) ) ) ),
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
           => ( ( v2_funct_1(X2)
                & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
                & k2_relset_1(X0,X1,X2) = X1 )
             => ( k2_funct_1(X2) = X3
                | k1_xboole_0 = X1
                | k1_xboole_0 = X0 ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f34,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
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
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
     => ( k2_funct_1(X2) != sK3
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & v2_funct_1(X2)
        & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0))
        & k2_relset_1(X0,X1,X2) = X1
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(sK3,X1,X0)
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( k2_funct_1(X2) != X3
            & k1_xboole_0 != X1
            & k1_xboole_0 != X0
            & v2_funct_1(X2)
            & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & k2_relset_1(X0,X1,X2) = X1
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k2_funct_1(sK2) != X3
          & k1_xboole_0 != sK1
          & k1_xboole_0 != sK0
          & v2_funct_1(sK2)
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & k2_relset_1(sK0,sK1,sK2) = sK1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( k2_funct_1(sK2) != sK3
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & v2_funct_1(sK2)
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & k2_relset_1(sK0,sK1,sK2) = sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f35,f38,f37])).

fof(f70,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f39])).

fof(f63,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f64,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f65,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f39])).

fof(f66,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f67,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f68,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f39])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
            & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f72,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f39])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f22])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f8])).

fof(f11,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f82,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f51,f55])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f24])).

fof(f53,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f69,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f39])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( ( k2_relset_1(X0,X1,X3) = X1
              & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) )
           => ( ( v2_funct_1(X4)
                & v2_funct_1(X3) )
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( v2_funct_1(X4)
            & v2_funct_1(X3) )
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | k2_relset_1(X0,X1,X3) != X1
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( v2_funct_1(X4)
            & v2_funct_1(X3) )
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | k2_relset_1(X0,X1,X3) != X1
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f30])).

fof(f59,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v2_funct_1(X4)
      | k1_xboole_0 = X2
      | k2_relset_1(X0,X1,X3) != X1
      | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f77,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f45,f55])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f47,plain,(
    ! [X0] :
      ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f79,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f47,f55])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f75,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f43,f55])).

fof(f46,plain,(
    ! [X0] :
      ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f80,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f46,f55])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
              & k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f48,f55])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f71,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f73,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f39])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f26])).

fof(f54,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f74,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_15,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_26,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_363,plain,
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
    inference(resolution_lifted,[status(thm)],[c_15,c_26])).

cnf(c_364,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X0)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0
    | k6_partfun1(sK0) != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_363])).

cnf(c_445,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_364])).

cnf(c_1056,plain,
    ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X0,sK0,X2) = sK0
    | v1_funct_2(X2,X0,sK0) != iProver_top
    | v1_funct_2(X1,sK0,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_445])).

cnf(c_1593,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1056])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_34,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_35,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_36,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_37,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_38,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_39,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_1757,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1593,c_34,c_35,c_36,c_37,c_38,c_39])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1067,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2844,plain,
    ( k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(sK0)
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1757,c_1067])).

cnf(c_24,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_602,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_633,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_602])).

cnf(c_603,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1162,plain,
    ( sK0 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_603])).

cnf(c_1163,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1162])).

cnf(c_2846,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(sK0)
    | sK0 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2844])).

cnf(c_10,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X2 = X3 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_350,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_26])).

cnf(c_351,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_350])).

cnf(c_11,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_359,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_351,c_11])).

cnf(c_1057,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_359])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1164,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1750,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1057,c_33,c_31,c_30,c_28,c_359,c_1164])).

cnf(c_27,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v2_funct_1(X0)
    | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
    | k2_relset_1(X4,X1,X3) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1070,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k1_xboole_0 = X3
    | v1_funct_2(X4,X1,X3) != iProver_top
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X4) = iProver_top
    | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4572,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_27,c_1070])).

cnf(c_4577,plain,
    ( v1_funct_1(X1) != iProver_top
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | k1_xboole_0 = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4572,c_34,c_35,c_36])).

cnf(c_4578,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4577])).

cnf(c_4581,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1750,c_4578])).

cnf(c_4582,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(k6_partfun1(sK0))
    | v2_funct_1(sK3)
    | sK0 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4581])).

cnf(c_4,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_4818,plain,
    ( v2_funct_1(k6_partfun1(sK0)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_8425,plain,
    ( k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2844,c_30,c_29,c_28,c_24,c_633,c_1163,c_2846,c_4582,c_4818])).

cnf(c_4819,plain,
    ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4818])).

cnf(c_4893,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4581,c_37,c_38,c_39,c_24,c_633,c_1163,c_4819])).

cnf(c_1062,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_6,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1078,plain,
    ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2044,plain,
    ( k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(k2_relat_1(sK3))
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1062,c_1078])).

cnf(c_1064,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1082,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1957,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1064,c_1082])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_2121,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2122,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2121])).

cnf(c_2568,plain,
    ( v2_funct_1(sK3) != iProver_top
    | k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(k2_relat_1(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2044,c_1957,c_2122])).

cnf(c_2569,plain,
    ( k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(k2_relat_1(sK3))
    | v2_funct_1(sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_2568])).

cnf(c_4897,plain,
    ( k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(k2_relat_1(sK3)) ),
    inference(superposition,[status(thm)],[c_4893,c_2569])).

cnf(c_8427,plain,
    ( k6_partfun1(k2_relat_1(sK3)) = k6_partfun1(sK0) ),
    inference(demodulation,[status(thm)],[c_8425,c_4897])).

cnf(c_2,plain,
    ( k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_17389,plain,
    ( k2_relat_1(k6_partfun1(sK0)) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_8427,c_2])).

cnf(c_17390,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(demodulation,[status(thm)],[c_17389,c_2])).

cnf(c_7,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1077,plain,
    ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1962,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1062,c_1077])).

cnf(c_2161,plain,
    ( v2_funct_1(sK3) != iProver_top
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1962,c_1957,c_2122])).

cnf(c_2162,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
    | v2_funct_1(sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_2161])).

cnf(c_4898,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3)) ),
    inference(superposition,[status(thm)],[c_4893,c_2162])).

cnf(c_8,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
    | k2_funct_1(X0) = X1
    | k1_relat_1(X0) != k2_relat_1(X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1076,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k1_relat_1(X1) != k2_relat_1(X0)
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4928,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3
    | k1_relat_1(k2_funct_1(sK3)) != k2_relat_1(sK3)
    | k6_partfun1(k2_relat_1(k2_funct_1(sK3))) != k6_partfun1(k1_relat_1(sK3))
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4898,c_1076])).

cnf(c_11239,plain,
    ( v1_relat_1(k2_funct_1(sK3)) != iProver_top
    | v2_funct_1(k2_funct_1(sK3)) != iProver_top
    | k2_funct_1(k2_funct_1(sK3)) = sK3
    | k1_relat_1(k2_funct_1(sK3)) != k2_relat_1(sK3)
    | k6_partfun1(k2_relat_1(k2_funct_1(sK3))) != k6_partfun1(k1_relat_1(sK3))
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4928,c_37,c_1957,c_2122])).

cnf(c_11240,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3
    | k1_relat_1(k2_funct_1(sK3)) != k2_relat_1(sK3)
    | k6_partfun1(k2_relat_1(k2_funct_1(sK3))) != k6_partfun1(k1_relat_1(sK3))
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v2_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_11239])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1066,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2676,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_27,c_1066])).

cnf(c_1059,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_1963,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1059,c_1077])).

cnf(c_25,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1061,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_1958,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1061,c_1082])).

cnf(c_1960,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1958])).

cnf(c_1965,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1963])).

cnf(c_2124,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2166,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1963,c_25,c_1960,c_1965,c_2124])).

cnf(c_2678,plain,
    ( k6_partfun1(k1_relat_1(sK2)) = k6_partfun1(sK0)
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2676,c_2166])).

cnf(c_41,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_23,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1142,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_603])).

cnf(c_1143,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1142])).

cnf(c_3576,plain,
    ( k6_partfun1(k1_relat_1(sK2)) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2678,c_34,c_35,c_36,c_41,c_23,c_633,c_1143])).

cnf(c_3583,plain,
    ( k2_relat_1(k6_partfun1(sK0)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_3576,c_2])).

cnf(c_3584,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(demodulation,[status(thm)],[c_3583,c_2])).

cnf(c_2843,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_27,c_1067])).

cnf(c_2045,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1059,c_1078])).

cnf(c_2047,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2045])).

cnf(c_2573,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2045,c_25,c_1960,c_2047,c_2124])).

cnf(c_2845,plain,
    ( k6_partfun1(k2_relat_1(sK2)) = k6_partfun1(sK1)
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2843,c_2573])).

cnf(c_3587,plain,
    ( k6_partfun1(k2_relat_1(sK2)) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2845,c_34,c_35,c_36,c_41,c_23,c_633,c_1143])).

cnf(c_3597,plain,
    ( k2_relat_1(k6_partfun1(sK1)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_3587,c_2])).

cnf(c_3598,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(demodulation,[status(thm)],[c_3597,c_2])).

cnf(c_2677,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1757,c_1066])).

cnf(c_2679,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | sK0 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2677])).

cnf(c_5834,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2677,c_30,c_29,c_28,c_24,c_633,c_1163,c_2679,c_4582,c_4818])).

cnf(c_5836,plain,
    ( k6_partfun1(k1_relat_1(sK3)) = k6_partfun1(sK1) ),
    inference(demodulation,[status(thm)],[c_5834,c_4898])).

cnf(c_6479,plain,
    ( k2_relat_1(k6_partfun1(sK1)) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_5836,c_2])).

cnf(c_6480,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(demodulation,[status(thm)],[c_6479,c_2])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1072,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2743,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1064,c_1072])).

cnf(c_2849,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2743,c_37])).

cnf(c_2850,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_2849])).

cnf(c_2858,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1061,c_2850])).

cnf(c_2859,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2858,c_1750])).

cnf(c_4377,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2859,c_34])).

cnf(c_4379,plain,
    ( k2_funct_1(sK3) = sK2
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4377,c_1076])).

cnf(c_4380,plain,
    ( k2_funct_1(sK3) = sK2
    | k1_relat_1(sK3) != sK1
    | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4379,c_3598])).

cnf(c_1959,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1957])).

cnf(c_4381,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | k2_funct_1(sK3) = sK2
    | k1_relat_1(sK3) != sK1
    | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4380])).

cnf(c_9424,plain,
    ( k2_funct_1(sK3) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4380,c_33,c_30,c_29,c_28,c_24,c_633,c_1163,c_1959,c_1960,c_2121,c_2124,c_4381,c_4582,c_4818,c_6480,c_8427])).

cnf(c_11243,plain,
    ( k2_funct_1(sK2) = sK3
    | k2_relat_1(sK3) != sK0
    | k6_partfun1(sK1) != k6_partfun1(sK1)
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11240,c_3584,c_3598,c_6480,c_9424])).

cnf(c_11244,plain,
    ( k2_funct_1(sK2) = sK3
    | k2_relat_1(sK3) != sK0
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_11243])).

cnf(c_2125,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2124])).

cnf(c_22,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f74])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_17390,c_11244,c_2125,c_1958,c_22,c_41,c_34])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:30:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.77/1.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.77/1.48  
% 7.77/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.77/1.48  
% 7.77/1.48  ------  iProver source info
% 7.77/1.48  
% 7.77/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.77/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.77/1.48  git: non_committed_changes: false
% 7.77/1.48  git: last_make_outside_of_git: false
% 7.77/1.48  
% 7.77/1.48  ------ 
% 7.77/1.48  
% 7.77/1.48  ------ Input Options
% 7.77/1.48  
% 7.77/1.48  --out_options                           all
% 7.77/1.48  --tptp_safe_out                         true
% 7.77/1.48  --problem_path                          ""
% 7.77/1.48  --include_path                          ""
% 7.77/1.48  --clausifier                            res/vclausify_rel
% 7.77/1.48  --clausifier_options                    ""
% 7.77/1.48  --stdin                                 false
% 7.77/1.48  --stats_out                             all
% 7.77/1.48  
% 7.77/1.48  ------ General Options
% 7.77/1.48  
% 7.77/1.48  --fof                                   false
% 7.77/1.48  --time_out_real                         305.
% 7.77/1.48  --time_out_virtual                      -1.
% 7.77/1.48  --symbol_type_check                     false
% 7.77/1.48  --clausify_out                          false
% 7.77/1.48  --sig_cnt_out                           false
% 7.77/1.48  --trig_cnt_out                          false
% 7.77/1.48  --trig_cnt_out_tolerance                1.
% 7.77/1.48  --trig_cnt_out_sk_spl                   false
% 7.77/1.48  --abstr_cl_out                          false
% 7.77/1.48  
% 7.77/1.48  ------ Global Options
% 7.77/1.48  
% 7.77/1.48  --schedule                              default
% 7.77/1.48  --add_important_lit                     false
% 7.77/1.48  --prop_solver_per_cl                    1000
% 7.77/1.48  --min_unsat_core                        false
% 7.77/1.48  --soft_assumptions                      false
% 7.77/1.48  --soft_lemma_size                       3
% 7.77/1.48  --prop_impl_unit_size                   0
% 7.77/1.48  --prop_impl_unit                        []
% 7.77/1.48  --share_sel_clauses                     true
% 7.77/1.48  --reset_solvers                         false
% 7.77/1.48  --bc_imp_inh                            [conj_cone]
% 7.77/1.48  --conj_cone_tolerance                   3.
% 7.77/1.48  --extra_neg_conj                        none
% 7.77/1.48  --large_theory_mode                     true
% 7.77/1.48  --prolific_symb_bound                   200
% 7.77/1.48  --lt_threshold                          2000
% 7.77/1.48  --clause_weak_htbl                      true
% 7.77/1.48  --gc_record_bc_elim                     false
% 7.77/1.48  
% 7.77/1.48  ------ Preprocessing Options
% 7.77/1.48  
% 7.77/1.48  --preprocessing_flag                    true
% 7.77/1.48  --time_out_prep_mult                    0.1
% 7.77/1.48  --splitting_mode                        input
% 7.77/1.48  --splitting_grd                         true
% 7.77/1.48  --splitting_cvd                         false
% 7.77/1.48  --splitting_cvd_svl                     false
% 7.77/1.48  --splitting_nvd                         32
% 7.77/1.48  --sub_typing                            true
% 7.77/1.48  --prep_gs_sim                           true
% 7.77/1.48  --prep_unflatten                        true
% 7.77/1.48  --prep_res_sim                          true
% 7.77/1.48  --prep_upred                            true
% 7.77/1.48  --prep_sem_filter                       exhaustive
% 7.77/1.48  --prep_sem_filter_out                   false
% 7.77/1.48  --pred_elim                             true
% 7.77/1.48  --res_sim_input                         true
% 7.77/1.48  --eq_ax_congr_red                       true
% 7.77/1.48  --pure_diseq_elim                       true
% 7.77/1.48  --brand_transform                       false
% 7.77/1.48  --non_eq_to_eq                          false
% 7.77/1.48  --prep_def_merge                        true
% 7.77/1.48  --prep_def_merge_prop_impl              false
% 7.77/1.48  --prep_def_merge_mbd                    true
% 7.77/1.48  --prep_def_merge_tr_red                 false
% 7.77/1.48  --prep_def_merge_tr_cl                  false
% 7.77/1.48  --smt_preprocessing                     true
% 7.77/1.48  --smt_ac_axioms                         fast
% 7.77/1.48  --preprocessed_out                      false
% 7.77/1.48  --preprocessed_stats                    false
% 7.77/1.48  
% 7.77/1.48  ------ Abstraction refinement Options
% 7.77/1.48  
% 7.77/1.48  --abstr_ref                             []
% 7.77/1.48  --abstr_ref_prep                        false
% 7.77/1.48  --abstr_ref_until_sat                   false
% 7.77/1.48  --abstr_ref_sig_restrict                funpre
% 7.77/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.77/1.48  --abstr_ref_under                       []
% 7.77/1.48  
% 7.77/1.48  ------ SAT Options
% 7.77/1.48  
% 7.77/1.48  --sat_mode                              false
% 7.77/1.48  --sat_fm_restart_options                ""
% 7.77/1.48  --sat_gr_def                            false
% 7.77/1.48  --sat_epr_types                         true
% 7.77/1.48  --sat_non_cyclic_types                  false
% 7.77/1.48  --sat_finite_models                     false
% 7.77/1.48  --sat_fm_lemmas                         false
% 7.77/1.48  --sat_fm_prep                           false
% 7.77/1.48  --sat_fm_uc_incr                        true
% 7.77/1.48  --sat_out_model                         small
% 7.77/1.48  --sat_out_clauses                       false
% 7.77/1.48  
% 7.77/1.48  ------ QBF Options
% 7.77/1.48  
% 7.77/1.48  --qbf_mode                              false
% 7.77/1.48  --qbf_elim_univ                         false
% 7.77/1.48  --qbf_dom_inst                          none
% 7.77/1.48  --qbf_dom_pre_inst                      false
% 7.77/1.48  --qbf_sk_in                             false
% 7.77/1.48  --qbf_pred_elim                         true
% 7.77/1.48  --qbf_split                             512
% 7.77/1.48  
% 7.77/1.48  ------ BMC1 Options
% 7.77/1.48  
% 7.77/1.48  --bmc1_incremental                      false
% 7.77/1.48  --bmc1_axioms                           reachable_all
% 7.77/1.48  --bmc1_min_bound                        0
% 7.77/1.48  --bmc1_max_bound                        -1
% 7.77/1.48  --bmc1_max_bound_default                -1
% 7.77/1.48  --bmc1_symbol_reachability              true
% 7.77/1.48  --bmc1_property_lemmas                  false
% 7.77/1.48  --bmc1_k_induction                      false
% 7.77/1.48  --bmc1_non_equiv_states                 false
% 7.77/1.48  --bmc1_deadlock                         false
% 7.77/1.48  --bmc1_ucm                              false
% 7.77/1.48  --bmc1_add_unsat_core                   none
% 7.77/1.48  --bmc1_unsat_core_children              false
% 7.77/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.77/1.48  --bmc1_out_stat                         full
% 7.77/1.48  --bmc1_ground_init                      false
% 7.77/1.48  --bmc1_pre_inst_next_state              false
% 7.77/1.48  --bmc1_pre_inst_state                   false
% 7.77/1.48  --bmc1_pre_inst_reach_state             false
% 7.77/1.48  --bmc1_out_unsat_core                   false
% 7.77/1.48  --bmc1_aig_witness_out                  false
% 7.77/1.48  --bmc1_verbose                          false
% 7.77/1.48  --bmc1_dump_clauses_tptp                false
% 7.77/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.77/1.48  --bmc1_dump_file                        -
% 7.77/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.77/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.77/1.48  --bmc1_ucm_extend_mode                  1
% 7.77/1.48  --bmc1_ucm_init_mode                    2
% 7.77/1.48  --bmc1_ucm_cone_mode                    none
% 7.77/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.77/1.48  --bmc1_ucm_relax_model                  4
% 7.77/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.77/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.77/1.48  --bmc1_ucm_layered_model                none
% 7.77/1.48  --bmc1_ucm_max_lemma_size               10
% 7.77/1.48  
% 7.77/1.48  ------ AIG Options
% 7.77/1.48  
% 7.77/1.48  --aig_mode                              false
% 7.77/1.48  
% 7.77/1.48  ------ Instantiation Options
% 7.77/1.48  
% 7.77/1.48  --instantiation_flag                    true
% 7.77/1.48  --inst_sos_flag                         true
% 7.77/1.48  --inst_sos_phase                        true
% 7.77/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.77/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.77/1.48  --inst_lit_sel_side                     num_symb
% 7.77/1.48  --inst_solver_per_active                1400
% 7.77/1.48  --inst_solver_calls_frac                1.
% 7.77/1.48  --inst_passive_queue_type               priority_queues
% 7.77/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.77/1.48  --inst_passive_queues_freq              [25;2]
% 7.77/1.48  --inst_dismatching                      true
% 7.77/1.48  --inst_eager_unprocessed_to_passive     true
% 7.77/1.48  --inst_prop_sim_given                   true
% 7.77/1.48  --inst_prop_sim_new                     false
% 7.77/1.48  --inst_subs_new                         false
% 7.77/1.48  --inst_eq_res_simp                      false
% 7.77/1.48  --inst_subs_given                       false
% 7.77/1.48  --inst_orphan_elimination               true
% 7.77/1.48  --inst_learning_loop_flag               true
% 7.77/1.48  --inst_learning_start                   3000
% 7.77/1.48  --inst_learning_factor                  2
% 7.77/1.48  --inst_start_prop_sim_after_learn       3
% 7.77/1.48  --inst_sel_renew                        solver
% 7.77/1.48  --inst_lit_activity_flag                true
% 7.77/1.48  --inst_restr_to_given                   false
% 7.77/1.48  --inst_activity_threshold               500
% 7.77/1.48  --inst_out_proof                        true
% 7.77/1.48  
% 7.77/1.48  ------ Resolution Options
% 7.77/1.48  
% 7.77/1.48  --resolution_flag                       true
% 7.77/1.48  --res_lit_sel                           adaptive
% 7.77/1.48  --res_lit_sel_side                      none
% 7.77/1.48  --res_ordering                          kbo
% 7.77/1.48  --res_to_prop_solver                    active
% 7.77/1.48  --res_prop_simpl_new                    false
% 7.77/1.48  --res_prop_simpl_given                  true
% 7.77/1.48  --res_passive_queue_type                priority_queues
% 7.77/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.77/1.48  --res_passive_queues_freq               [15;5]
% 7.77/1.48  --res_forward_subs                      full
% 7.77/1.48  --res_backward_subs                     full
% 7.77/1.48  --res_forward_subs_resolution           true
% 7.77/1.48  --res_backward_subs_resolution          true
% 7.77/1.48  --res_orphan_elimination                true
% 7.77/1.48  --res_time_limit                        2.
% 7.77/1.48  --res_out_proof                         true
% 7.77/1.48  
% 7.77/1.48  ------ Superposition Options
% 7.77/1.48  
% 7.77/1.48  --superposition_flag                    true
% 7.77/1.48  --sup_passive_queue_type                priority_queues
% 7.77/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.77/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.77/1.48  --demod_completeness_check              fast
% 7.77/1.48  --demod_use_ground                      true
% 7.77/1.48  --sup_to_prop_solver                    passive
% 7.77/1.48  --sup_prop_simpl_new                    true
% 7.77/1.48  --sup_prop_simpl_given                  true
% 7.77/1.48  --sup_fun_splitting                     true
% 7.77/1.48  --sup_smt_interval                      50000
% 7.77/1.48  
% 7.77/1.48  ------ Superposition Simplification Setup
% 7.77/1.48  
% 7.77/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.77/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.77/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.77/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.77/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.77/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.77/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.77/1.48  --sup_immed_triv                        [TrivRules]
% 7.77/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.77/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.77/1.48  --sup_immed_bw_main                     []
% 7.77/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.77/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.77/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.77/1.48  --sup_input_bw                          []
% 7.77/1.48  
% 7.77/1.48  ------ Combination Options
% 7.77/1.48  
% 7.77/1.48  --comb_res_mult                         3
% 7.77/1.48  --comb_sup_mult                         2
% 7.77/1.48  --comb_inst_mult                        10
% 7.77/1.48  
% 7.77/1.48  ------ Debug Options
% 7.77/1.48  
% 7.77/1.48  --dbg_backtrace                         false
% 7.77/1.48  --dbg_dump_prop_clauses                 false
% 7.77/1.48  --dbg_dump_prop_clauses_file            -
% 7.77/1.48  --dbg_out_stat                          false
% 7.77/1.48  ------ Parsing...
% 7.77/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.77/1.48  
% 7.77/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.77/1.48  
% 7.77/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.77/1.48  
% 7.77/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.77/1.48  ------ Proving...
% 7.77/1.48  ------ Problem Properties 
% 7.77/1.48  
% 7.77/1.48  
% 7.77/1.48  clauses                                 33
% 7.77/1.48  conjectures                             11
% 7.77/1.48  EPR                                     7
% 7.77/1.48  Horn                                    29
% 7.77/1.48  unary                                   17
% 7.77/1.48  binary                                  1
% 7.77/1.48  lits                                    121
% 7.77/1.48  lits eq                                 29
% 7.77/1.48  fd_pure                                 0
% 7.77/1.48  fd_pseudo                               0
% 7.77/1.48  fd_cond                                 4
% 7.77/1.48  fd_pseudo_cond                          1
% 7.77/1.48  AC symbols                              0
% 7.77/1.48  
% 7.77/1.48  ------ Schedule dynamic 5 is on 
% 7.77/1.48  
% 7.77/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.77/1.48  
% 7.77/1.48  
% 7.77/1.48  ------ 
% 7.77/1.48  Current options:
% 7.77/1.48  ------ 
% 7.77/1.48  
% 7.77/1.48  ------ Input Options
% 7.77/1.48  
% 7.77/1.48  --out_options                           all
% 7.77/1.48  --tptp_safe_out                         true
% 7.77/1.48  --problem_path                          ""
% 7.77/1.48  --include_path                          ""
% 7.77/1.48  --clausifier                            res/vclausify_rel
% 7.77/1.48  --clausifier_options                    ""
% 7.77/1.48  --stdin                                 false
% 7.77/1.48  --stats_out                             all
% 7.77/1.48  
% 7.77/1.48  ------ General Options
% 7.77/1.48  
% 7.77/1.48  --fof                                   false
% 7.77/1.48  --time_out_real                         305.
% 7.77/1.48  --time_out_virtual                      -1.
% 7.77/1.48  --symbol_type_check                     false
% 7.77/1.48  --clausify_out                          false
% 7.77/1.48  --sig_cnt_out                           false
% 7.77/1.48  --trig_cnt_out                          false
% 7.77/1.48  --trig_cnt_out_tolerance                1.
% 7.77/1.48  --trig_cnt_out_sk_spl                   false
% 7.77/1.48  --abstr_cl_out                          false
% 7.77/1.48  
% 7.77/1.48  ------ Global Options
% 7.77/1.48  
% 7.77/1.48  --schedule                              default
% 7.77/1.48  --add_important_lit                     false
% 7.77/1.48  --prop_solver_per_cl                    1000
% 7.77/1.48  --min_unsat_core                        false
% 7.77/1.48  --soft_assumptions                      false
% 7.77/1.48  --soft_lemma_size                       3
% 7.77/1.48  --prop_impl_unit_size                   0
% 7.77/1.48  --prop_impl_unit                        []
% 7.77/1.48  --share_sel_clauses                     true
% 7.77/1.48  --reset_solvers                         false
% 7.77/1.48  --bc_imp_inh                            [conj_cone]
% 7.77/1.48  --conj_cone_tolerance                   3.
% 7.77/1.48  --extra_neg_conj                        none
% 7.77/1.48  --large_theory_mode                     true
% 7.77/1.48  --prolific_symb_bound                   200
% 7.77/1.48  --lt_threshold                          2000
% 7.77/1.48  --clause_weak_htbl                      true
% 7.77/1.48  --gc_record_bc_elim                     false
% 7.77/1.48  
% 7.77/1.48  ------ Preprocessing Options
% 7.77/1.48  
% 7.77/1.48  --preprocessing_flag                    true
% 7.77/1.48  --time_out_prep_mult                    0.1
% 7.77/1.48  --splitting_mode                        input
% 7.77/1.48  --splitting_grd                         true
% 7.77/1.48  --splitting_cvd                         false
% 7.77/1.48  --splitting_cvd_svl                     false
% 7.77/1.48  --splitting_nvd                         32
% 7.77/1.48  --sub_typing                            true
% 7.77/1.48  --prep_gs_sim                           true
% 7.77/1.48  --prep_unflatten                        true
% 7.77/1.48  --prep_res_sim                          true
% 7.77/1.48  --prep_upred                            true
% 7.77/1.48  --prep_sem_filter                       exhaustive
% 7.77/1.48  --prep_sem_filter_out                   false
% 7.77/1.48  --pred_elim                             true
% 7.77/1.48  --res_sim_input                         true
% 7.77/1.48  --eq_ax_congr_red                       true
% 7.77/1.48  --pure_diseq_elim                       true
% 7.77/1.48  --brand_transform                       false
% 7.77/1.48  --non_eq_to_eq                          false
% 7.77/1.48  --prep_def_merge                        true
% 7.77/1.48  --prep_def_merge_prop_impl              false
% 7.77/1.48  --prep_def_merge_mbd                    true
% 7.77/1.48  --prep_def_merge_tr_red                 false
% 7.77/1.48  --prep_def_merge_tr_cl                  false
% 7.77/1.48  --smt_preprocessing                     true
% 7.77/1.48  --smt_ac_axioms                         fast
% 7.77/1.48  --preprocessed_out                      false
% 7.77/1.48  --preprocessed_stats                    false
% 7.77/1.48  
% 7.77/1.48  ------ Abstraction refinement Options
% 7.77/1.48  
% 7.77/1.48  --abstr_ref                             []
% 7.77/1.48  --abstr_ref_prep                        false
% 7.77/1.48  --abstr_ref_until_sat                   false
% 7.77/1.48  --abstr_ref_sig_restrict                funpre
% 7.77/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.77/1.48  --abstr_ref_under                       []
% 7.77/1.48  
% 7.77/1.48  ------ SAT Options
% 7.77/1.48  
% 7.77/1.48  --sat_mode                              false
% 7.77/1.48  --sat_fm_restart_options                ""
% 7.77/1.48  --sat_gr_def                            false
% 7.77/1.48  --sat_epr_types                         true
% 7.77/1.48  --sat_non_cyclic_types                  false
% 7.77/1.48  --sat_finite_models                     false
% 7.77/1.48  --sat_fm_lemmas                         false
% 7.77/1.48  --sat_fm_prep                           false
% 7.77/1.48  --sat_fm_uc_incr                        true
% 7.77/1.48  --sat_out_model                         small
% 7.77/1.48  --sat_out_clauses                       false
% 7.77/1.48  
% 7.77/1.48  ------ QBF Options
% 7.77/1.48  
% 7.77/1.48  --qbf_mode                              false
% 7.77/1.48  --qbf_elim_univ                         false
% 7.77/1.48  --qbf_dom_inst                          none
% 7.77/1.48  --qbf_dom_pre_inst                      false
% 7.77/1.48  --qbf_sk_in                             false
% 7.77/1.48  --qbf_pred_elim                         true
% 7.77/1.48  --qbf_split                             512
% 7.77/1.48  
% 7.77/1.48  ------ BMC1 Options
% 7.77/1.48  
% 7.77/1.48  --bmc1_incremental                      false
% 7.77/1.48  --bmc1_axioms                           reachable_all
% 7.77/1.48  --bmc1_min_bound                        0
% 7.77/1.48  --bmc1_max_bound                        -1
% 7.77/1.48  --bmc1_max_bound_default                -1
% 7.77/1.48  --bmc1_symbol_reachability              true
% 7.77/1.48  --bmc1_property_lemmas                  false
% 7.77/1.48  --bmc1_k_induction                      false
% 7.77/1.48  --bmc1_non_equiv_states                 false
% 7.77/1.48  --bmc1_deadlock                         false
% 7.77/1.48  --bmc1_ucm                              false
% 7.77/1.48  --bmc1_add_unsat_core                   none
% 7.77/1.48  --bmc1_unsat_core_children              false
% 7.77/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.77/1.48  --bmc1_out_stat                         full
% 7.77/1.48  --bmc1_ground_init                      false
% 7.77/1.48  --bmc1_pre_inst_next_state              false
% 7.77/1.48  --bmc1_pre_inst_state                   false
% 7.77/1.48  --bmc1_pre_inst_reach_state             false
% 7.77/1.48  --bmc1_out_unsat_core                   false
% 7.77/1.48  --bmc1_aig_witness_out                  false
% 7.77/1.48  --bmc1_verbose                          false
% 7.77/1.48  --bmc1_dump_clauses_tptp                false
% 7.77/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.77/1.48  --bmc1_dump_file                        -
% 7.77/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.77/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.77/1.48  --bmc1_ucm_extend_mode                  1
% 7.77/1.48  --bmc1_ucm_init_mode                    2
% 7.77/1.48  --bmc1_ucm_cone_mode                    none
% 7.77/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.77/1.48  --bmc1_ucm_relax_model                  4
% 7.77/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.77/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.77/1.48  --bmc1_ucm_layered_model                none
% 7.77/1.48  --bmc1_ucm_max_lemma_size               10
% 7.77/1.48  
% 7.77/1.48  ------ AIG Options
% 7.77/1.48  
% 7.77/1.48  --aig_mode                              false
% 7.77/1.48  
% 7.77/1.48  ------ Instantiation Options
% 7.77/1.48  
% 7.77/1.48  --instantiation_flag                    true
% 7.77/1.48  --inst_sos_flag                         true
% 7.77/1.48  --inst_sos_phase                        true
% 7.77/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.77/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.77/1.48  --inst_lit_sel_side                     none
% 7.77/1.48  --inst_solver_per_active                1400
% 7.77/1.48  --inst_solver_calls_frac                1.
% 7.77/1.48  --inst_passive_queue_type               priority_queues
% 7.77/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.77/1.48  --inst_passive_queues_freq              [25;2]
% 7.77/1.48  --inst_dismatching                      true
% 7.77/1.48  --inst_eager_unprocessed_to_passive     true
% 7.77/1.48  --inst_prop_sim_given                   true
% 7.77/1.48  --inst_prop_sim_new                     false
% 7.77/1.48  --inst_subs_new                         false
% 7.77/1.48  --inst_eq_res_simp                      false
% 7.77/1.48  --inst_subs_given                       false
% 7.77/1.48  --inst_orphan_elimination               true
% 7.77/1.48  --inst_learning_loop_flag               true
% 7.77/1.48  --inst_learning_start                   3000
% 7.77/1.48  --inst_learning_factor                  2
% 7.77/1.48  --inst_start_prop_sim_after_learn       3
% 7.77/1.48  --inst_sel_renew                        solver
% 7.77/1.48  --inst_lit_activity_flag                true
% 7.77/1.48  --inst_restr_to_given                   false
% 7.77/1.48  --inst_activity_threshold               500
% 7.77/1.48  --inst_out_proof                        true
% 7.77/1.48  
% 7.77/1.48  ------ Resolution Options
% 7.77/1.48  
% 7.77/1.48  --resolution_flag                       false
% 7.77/1.48  --res_lit_sel                           adaptive
% 7.77/1.48  --res_lit_sel_side                      none
% 7.77/1.48  --res_ordering                          kbo
% 7.77/1.48  --res_to_prop_solver                    active
% 7.77/1.48  --res_prop_simpl_new                    false
% 7.77/1.48  --res_prop_simpl_given                  true
% 7.77/1.48  --res_passive_queue_type                priority_queues
% 7.77/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.77/1.48  --res_passive_queues_freq               [15;5]
% 7.77/1.48  --res_forward_subs                      full
% 7.77/1.48  --res_backward_subs                     full
% 7.77/1.48  --res_forward_subs_resolution           true
% 7.77/1.48  --res_backward_subs_resolution          true
% 7.77/1.48  --res_orphan_elimination                true
% 7.77/1.48  --res_time_limit                        2.
% 7.77/1.48  --res_out_proof                         true
% 7.77/1.48  
% 7.77/1.48  ------ Superposition Options
% 7.77/1.48  
% 7.77/1.48  --superposition_flag                    true
% 7.77/1.48  --sup_passive_queue_type                priority_queues
% 7.77/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.77/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.77/1.48  --demod_completeness_check              fast
% 7.77/1.48  --demod_use_ground                      true
% 7.77/1.48  --sup_to_prop_solver                    passive
% 7.77/1.48  --sup_prop_simpl_new                    true
% 7.77/1.48  --sup_prop_simpl_given                  true
% 7.77/1.48  --sup_fun_splitting                     true
% 7.77/1.48  --sup_smt_interval                      50000
% 7.77/1.48  
% 7.77/1.48  ------ Superposition Simplification Setup
% 7.77/1.48  
% 7.77/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.77/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.77/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.77/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.77/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.77/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.77/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.77/1.48  --sup_immed_triv                        [TrivRules]
% 7.77/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.77/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.77/1.48  --sup_immed_bw_main                     []
% 7.77/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.77/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.77/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.77/1.48  --sup_input_bw                          []
% 7.77/1.48  
% 7.77/1.48  ------ Combination Options
% 7.77/1.48  
% 7.77/1.48  --comb_res_mult                         3
% 7.77/1.48  --comb_sup_mult                         2
% 7.77/1.48  --comb_inst_mult                        10
% 7.77/1.48  
% 7.77/1.48  ------ Debug Options
% 7.77/1.48  
% 7.77/1.48  --dbg_backtrace                         false
% 7.77/1.48  --dbg_dump_prop_clauses                 false
% 7.77/1.48  --dbg_dump_prop_clauses_file            -
% 7.77/1.48  --dbg_out_stat                          false
% 7.77/1.48  
% 7.77/1.48  
% 7.77/1.48  
% 7.77/1.48  
% 7.77/1.48  ------ Proving...
% 7.77/1.48  
% 7.77/1.48  
% 7.77/1.48  % SZS status Theorem for theBenchmark.p
% 7.77/1.48  
% 7.77/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.77/1.48  
% 7.77/1.48  fof(f12,axiom,(
% 7.77/1.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 7.77/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.77/1.48  
% 7.77/1.48  fof(f28,plain,(
% 7.77/1.48    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 7.77/1.48    inference(ennf_transformation,[],[f12])).
% 7.77/1.48  
% 7.77/1.48  fof(f29,plain,(
% 7.77/1.48    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.77/1.48    inference(flattening,[],[f28])).
% 7.77/1.48  
% 7.77/1.48  fof(f56,plain,(
% 7.77/1.48    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.77/1.48    inference(cnf_transformation,[],[f29])).
% 7.77/1.48  
% 7.77/1.48  fof(f15,conjecture,(
% 7.77/1.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 7.77/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.77/1.48  
% 7.77/1.48  fof(f16,negated_conjecture,(
% 7.77/1.48    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 7.77/1.48    inference(negated_conjecture,[],[f15])).
% 7.77/1.48  
% 7.77/1.48  fof(f34,plain,(
% 7.77/1.48    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 7.77/1.48    inference(ennf_transformation,[],[f16])).
% 7.77/1.48  
% 7.77/1.48  fof(f35,plain,(
% 7.77/1.48    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 7.77/1.48    inference(flattening,[],[f34])).
% 7.77/1.48  
% 7.77/1.48  fof(f38,plain,(
% 7.77/1.48    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 7.77/1.48    introduced(choice_axiom,[])).
% 7.77/1.48  
% 7.77/1.48  fof(f37,plain,(
% 7.77/1.48    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 7.77/1.48    introduced(choice_axiom,[])).
% 7.77/1.48  
% 7.77/1.48  fof(f39,plain,(
% 7.77/1.48    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 7.77/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f35,f38,f37])).
% 7.77/1.48  
% 7.77/1.48  fof(f70,plain,(
% 7.77/1.48    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 7.77/1.48    inference(cnf_transformation,[],[f39])).
% 7.77/1.48  
% 7.77/1.48  fof(f63,plain,(
% 7.77/1.48    v1_funct_1(sK2)),
% 7.77/1.48    inference(cnf_transformation,[],[f39])).
% 7.77/1.48  
% 7.77/1.48  fof(f64,plain,(
% 7.77/1.48    v1_funct_2(sK2,sK0,sK1)),
% 7.77/1.48    inference(cnf_transformation,[],[f39])).
% 7.77/1.48  
% 7.77/1.48  fof(f65,plain,(
% 7.77/1.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 7.77/1.48    inference(cnf_transformation,[],[f39])).
% 7.77/1.48  
% 7.77/1.48  fof(f66,plain,(
% 7.77/1.48    v1_funct_1(sK3)),
% 7.77/1.48    inference(cnf_transformation,[],[f39])).
% 7.77/1.48  
% 7.77/1.48  fof(f67,plain,(
% 7.77/1.48    v1_funct_2(sK3,sK1,sK0)),
% 7.77/1.48    inference(cnf_transformation,[],[f39])).
% 7.77/1.48  
% 7.77/1.48  fof(f68,plain,(
% 7.77/1.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 7.77/1.48    inference(cnf_transformation,[],[f39])).
% 7.77/1.48  
% 7.77/1.48  fof(f14,axiom,(
% 7.77/1.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 7.77/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.77/1.48  
% 7.77/1.48  fof(f32,plain,(
% 7.77/1.48    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 7.77/1.48    inference(ennf_transformation,[],[f14])).
% 7.77/1.48  
% 7.77/1.48  fof(f33,plain,(
% 7.77/1.48    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.77/1.48    inference(flattening,[],[f32])).
% 7.77/1.48  
% 7.77/1.48  fof(f62,plain,(
% 7.77/1.48    ( ! [X2,X0,X1] : (k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.77/1.48    inference(cnf_transformation,[],[f33])).
% 7.77/1.48  
% 7.77/1.48  fof(f72,plain,(
% 7.77/1.48    k1_xboole_0 != sK0),
% 7.77/1.48    inference(cnf_transformation,[],[f39])).
% 7.77/1.48  
% 7.77/1.48  fof(f7,axiom,(
% 7.77/1.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 7.77/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.77/1.48  
% 7.77/1.48  fof(f22,plain,(
% 7.77/1.48    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 7.77/1.48    inference(ennf_transformation,[],[f7])).
% 7.77/1.48  
% 7.77/1.48  fof(f23,plain,(
% 7.77/1.48    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.77/1.48    inference(flattening,[],[f22])).
% 7.77/1.48  
% 7.77/1.48  fof(f36,plain,(
% 7.77/1.48    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.77/1.48    inference(nnf_transformation,[],[f23])).
% 7.77/1.48  
% 7.77/1.48  fof(f49,plain,(
% 7.77/1.48    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.77/1.48    inference(cnf_transformation,[],[f36])).
% 7.77/1.48  
% 7.77/1.48  fof(f8,axiom,(
% 7.77/1.48    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 7.77/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.77/1.48  
% 7.77/1.48  fof(f51,plain,(
% 7.77/1.48    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 7.77/1.48    inference(cnf_transformation,[],[f8])).
% 7.77/1.48  
% 7.77/1.48  fof(f11,axiom,(
% 7.77/1.48    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 7.77/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.77/1.48  
% 7.77/1.48  fof(f55,plain,(
% 7.77/1.48    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 7.77/1.48    inference(cnf_transformation,[],[f11])).
% 7.77/1.48  
% 7.77/1.48  fof(f82,plain,(
% 7.77/1.48    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 7.77/1.48    inference(definition_unfolding,[],[f51,f55])).
% 7.77/1.48  
% 7.77/1.48  fof(f9,axiom,(
% 7.77/1.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 7.77/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.77/1.48  
% 7.77/1.48  fof(f24,plain,(
% 7.77/1.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 7.77/1.48    inference(ennf_transformation,[],[f9])).
% 7.77/1.48  
% 7.77/1.48  fof(f25,plain,(
% 7.77/1.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 7.77/1.48    inference(flattening,[],[f24])).
% 7.77/1.48  
% 7.77/1.48  fof(f53,plain,(
% 7.77/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 7.77/1.48    inference(cnf_transformation,[],[f25])).
% 7.77/1.48  
% 7.77/1.48  fof(f69,plain,(
% 7.77/1.48    k2_relset_1(sK0,sK1,sK2) = sK1),
% 7.77/1.48    inference(cnf_transformation,[],[f39])).
% 7.77/1.48  
% 7.77/1.48  fof(f13,axiom,(
% 7.77/1.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 7.77/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.77/1.48  
% 7.77/1.48  fof(f30,plain,(
% 7.77/1.48    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 7.77/1.48    inference(ennf_transformation,[],[f13])).
% 7.77/1.48  
% 7.77/1.48  fof(f31,plain,(
% 7.77/1.48    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 7.77/1.48    inference(flattening,[],[f30])).
% 7.77/1.48  
% 7.77/1.48  fof(f59,plain,(
% 7.77/1.48    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X4) | k1_xboole_0 = X2 | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 7.77/1.48    inference(cnf_transformation,[],[f31])).
% 7.77/1.48  
% 7.77/1.48  fof(f4,axiom,(
% 7.77/1.48    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 7.77/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.77/1.48  
% 7.77/1.48  fof(f45,plain,(
% 7.77/1.48    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 7.77/1.48    inference(cnf_transformation,[],[f4])).
% 7.77/1.48  
% 7.77/1.48  fof(f77,plain,(
% 7.77/1.48    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 7.77/1.48    inference(definition_unfolding,[],[f45,f55])).
% 7.77/1.48  
% 7.77/1.48  fof(f5,axiom,(
% 7.77/1.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)))))),
% 7.77/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.77/1.48  
% 7.77/1.48  fof(f18,plain,(
% 7.77/1.48    ! [X0] : (((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.77/1.48    inference(ennf_transformation,[],[f5])).
% 7.77/1.48  
% 7.77/1.48  fof(f19,plain,(
% 7.77/1.48    ! [X0] : ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.77/1.48    inference(flattening,[],[f18])).
% 7.77/1.48  
% 7.77/1.48  fof(f47,plain,(
% 7.77/1.48    ( ! [X0] : (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.77/1.48    inference(cnf_transformation,[],[f19])).
% 7.77/1.48  
% 7.77/1.48  fof(f79,plain,(
% 7.77/1.48    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.77/1.48    inference(definition_unfolding,[],[f47,f55])).
% 7.77/1.48  
% 7.77/1.48  fof(f1,axiom,(
% 7.77/1.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 7.77/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.77/1.48  
% 7.77/1.48  fof(f17,plain,(
% 7.77/1.48    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 7.77/1.48    inference(ennf_transformation,[],[f1])).
% 7.77/1.48  
% 7.77/1.48  fof(f40,plain,(
% 7.77/1.48    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 7.77/1.48    inference(cnf_transformation,[],[f17])).
% 7.77/1.48  
% 7.77/1.48  fof(f2,axiom,(
% 7.77/1.48    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 7.77/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.77/1.48  
% 7.77/1.48  fof(f41,plain,(
% 7.77/1.48    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 7.77/1.48    inference(cnf_transformation,[],[f2])).
% 7.77/1.48  
% 7.77/1.48  fof(f3,axiom,(
% 7.77/1.48    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 7.77/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.77/1.48  
% 7.77/1.48  fof(f43,plain,(
% 7.77/1.48    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 7.77/1.48    inference(cnf_transformation,[],[f3])).
% 7.77/1.48  
% 7.77/1.48  fof(f75,plain,(
% 7.77/1.48    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 7.77/1.48    inference(definition_unfolding,[],[f43,f55])).
% 7.77/1.48  
% 7.77/1.48  fof(f46,plain,(
% 7.77/1.48    ( ! [X0] : (k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.77/1.48    inference(cnf_transformation,[],[f19])).
% 7.77/1.48  
% 7.77/1.48  fof(f80,plain,(
% 7.77/1.48    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.77/1.48    inference(definition_unfolding,[],[f46,f55])).
% 7.77/1.48  
% 7.77/1.48  fof(f6,axiom,(
% 7.77/1.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 7.77/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.77/1.48  
% 7.77/1.48  fof(f20,plain,(
% 7.77/1.48    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.77/1.48    inference(ennf_transformation,[],[f6])).
% 7.77/1.48  
% 7.77/1.48  fof(f21,plain,(
% 7.77/1.48    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.77/1.48    inference(flattening,[],[f20])).
% 7.77/1.48  
% 7.77/1.48  fof(f48,plain,(
% 7.77/1.48    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.77/1.48    inference(cnf_transformation,[],[f21])).
% 7.77/1.48  
% 7.77/1.48  fof(f81,plain,(
% 7.77/1.48    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.77/1.48    inference(definition_unfolding,[],[f48,f55])).
% 7.77/1.48  
% 7.77/1.48  fof(f61,plain,(
% 7.77/1.48    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.77/1.48    inference(cnf_transformation,[],[f33])).
% 7.77/1.48  
% 7.77/1.48  fof(f71,plain,(
% 7.77/1.48    v2_funct_1(sK2)),
% 7.77/1.48    inference(cnf_transformation,[],[f39])).
% 7.77/1.48  
% 7.77/1.48  fof(f73,plain,(
% 7.77/1.48    k1_xboole_0 != sK1),
% 7.77/1.48    inference(cnf_transformation,[],[f39])).
% 7.77/1.48  
% 7.77/1.48  fof(f10,axiom,(
% 7.77/1.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 7.77/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.77/1.48  
% 7.77/1.48  fof(f26,plain,(
% 7.77/1.48    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 7.77/1.48    inference(ennf_transformation,[],[f10])).
% 7.77/1.48  
% 7.77/1.48  fof(f27,plain,(
% 7.77/1.48    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 7.77/1.48    inference(flattening,[],[f26])).
% 7.77/1.48  
% 7.77/1.48  fof(f54,plain,(
% 7.77/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 7.77/1.48    inference(cnf_transformation,[],[f27])).
% 7.77/1.48  
% 7.77/1.48  fof(f74,plain,(
% 7.77/1.48    k2_funct_1(sK2) != sK3),
% 7.77/1.48    inference(cnf_transformation,[],[f39])).
% 7.77/1.48  
% 7.77/1.48  cnf(c_15,plain,
% 7.77/1.48      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 7.77/1.48      | ~ v1_funct_2(X2,X0,X1)
% 7.77/1.48      | ~ v1_funct_2(X3,X1,X0)
% 7.77/1.48      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.77/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 7.77/1.48      | ~ v1_funct_1(X3)
% 7.77/1.48      | ~ v1_funct_1(X2)
% 7.77/1.48      | k2_relset_1(X1,X0,X3) = X0 ),
% 7.77/1.48      inference(cnf_transformation,[],[f56]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_26,negated_conjecture,
% 7.77/1.48      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 7.77/1.48      inference(cnf_transformation,[],[f70]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_363,plain,
% 7.77/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 7.77/1.48      | ~ v1_funct_2(X3,X2,X1)
% 7.77/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.77/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 7.77/1.48      | ~ v1_funct_1(X3)
% 7.77/1.48      | ~ v1_funct_1(X0)
% 7.77/1.48      | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.77/1.48      | k2_relset_1(X2,X1,X3) = X1
% 7.77/1.48      | k6_partfun1(X1) != k6_partfun1(sK0)
% 7.77/1.48      | sK0 != X1 ),
% 7.77/1.48      inference(resolution_lifted,[status(thm)],[c_15,c_26]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_364,plain,
% 7.77/1.48      ( ~ v1_funct_2(X0,X1,sK0)
% 7.77/1.48      | ~ v1_funct_2(X2,sK0,X1)
% 7.77/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 7.77/1.48      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 7.77/1.48      | ~ v1_funct_1(X2)
% 7.77/1.48      | ~ v1_funct_1(X0)
% 7.77/1.48      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.77/1.48      | k2_relset_1(X1,sK0,X0) = sK0
% 7.77/1.48      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 7.77/1.48      inference(unflattening,[status(thm)],[c_363]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_445,plain,
% 7.77/1.48      ( ~ v1_funct_2(X0,X1,sK0)
% 7.77/1.48      | ~ v1_funct_2(X2,sK0,X1)
% 7.77/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 7.77/1.48      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 7.77/1.48      | ~ v1_funct_1(X0)
% 7.77/1.48      | ~ v1_funct_1(X2)
% 7.77/1.48      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.77/1.48      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 7.77/1.48      inference(equality_resolution_simp,[status(thm)],[c_364]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_1056,plain,
% 7.77/1.48      ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.77/1.48      | k2_relset_1(X0,sK0,X2) = sK0
% 7.77/1.48      | v1_funct_2(X2,X0,sK0) != iProver_top
% 7.77/1.48      | v1_funct_2(X1,sK0,X0) != iProver_top
% 7.77/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 7.77/1.48      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 7.77/1.48      | v1_funct_1(X2) != iProver_top
% 7.77/1.48      | v1_funct_1(X1) != iProver_top ),
% 7.77/1.48      inference(predicate_to_equality,[status(thm)],[c_445]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_1593,plain,
% 7.77/1.48      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 7.77/1.48      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 7.77/1.48      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 7.77/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.77/1.48      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.77/1.48      | v1_funct_1(sK3) != iProver_top
% 7.77/1.48      | v1_funct_1(sK2) != iProver_top ),
% 7.77/1.48      inference(equality_resolution,[status(thm)],[c_1056]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_33,negated_conjecture,
% 7.77/1.48      ( v1_funct_1(sK2) ),
% 7.77/1.48      inference(cnf_transformation,[],[f63]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_34,plain,
% 7.77/1.48      ( v1_funct_1(sK2) = iProver_top ),
% 7.77/1.48      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_32,negated_conjecture,
% 7.77/1.48      ( v1_funct_2(sK2,sK0,sK1) ),
% 7.77/1.48      inference(cnf_transformation,[],[f64]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_35,plain,
% 7.77/1.48      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 7.77/1.48      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_31,negated_conjecture,
% 7.77/1.48      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 7.77/1.48      inference(cnf_transformation,[],[f65]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_36,plain,
% 7.77/1.48      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.77/1.48      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_30,negated_conjecture,
% 7.77/1.48      ( v1_funct_1(sK3) ),
% 7.77/1.48      inference(cnf_transformation,[],[f66]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_37,plain,
% 7.77/1.48      ( v1_funct_1(sK3) = iProver_top ),
% 7.77/1.48      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_29,negated_conjecture,
% 7.77/1.48      ( v1_funct_2(sK3,sK1,sK0) ),
% 7.77/1.48      inference(cnf_transformation,[],[f67]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_38,plain,
% 7.77/1.48      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 7.77/1.48      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_28,negated_conjecture,
% 7.77/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 7.77/1.48      inference(cnf_transformation,[],[f68]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_39,plain,
% 7.77/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 7.77/1.48      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_1757,plain,
% 7.77/1.48      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 7.77/1.48      inference(global_propositional_subsumption,
% 7.77/1.48                [status(thm)],
% 7.77/1.48                [c_1593,c_34,c_35,c_36,c_37,c_38,c_39]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_20,plain,
% 7.77/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 7.77/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.77/1.48      | ~ v1_funct_1(X0)
% 7.77/1.48      | ~ v2_funct_1(X0)
% 7.77/1.48      | k2_relset_1(X1,X2,X0) != X2
% 7.77/1.48      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
% 7.77/1.48      | k1_xboole_0 = X2 ),
% 7.77/1.48      inference(cnf_transformation,[],[f62]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_1067,plain,
% 7.77/1.48      ( k2_relset_1(X0,X1,X2) != X1
% 7.77/1.48      | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
% 7.77/1.48      | k1_xboole_0 = X1
% 7.77/1.48      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.77/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.77/1.48      | v1_funct_1(X2) != iProver_top
% 7.77/1.48      | v2_funct_1(X2) != iProver_top ),
% 7.77/1.48      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_2844,plain,
% 7.77/1.48      ( k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(sK0)
% 7.77/1.48      | sK0 = k1_xboole_0
% 7.77/1.48      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 7.77/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.77/1.48      | v1_funct_1(sK3) != iProver_top
% 7.77/1.48      | v2_funct_1(sK3) != iProver_top ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_1757,c_1067]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_24,negated_conjecture,
% 7.77/1.48      ( k1_xboole_0 != sK0 ),
% 7.77/1.48      inference(cnf_transformation,[],[f72]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_602,plain,( X0 = X0 ),theory(equality) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_633,plain,
% 7.77/1.48      ( k1_xboole_0 = k1_xboole_0 ),
% 7.77/1.48      inference(instantiation,[status(thm)],[c_602]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_603,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_1162,plain,
% 7.77/1.48      ( sK0 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK0 ),
% 7.77/1.48      inference(instantiation,[status(thm)],[c_603]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_1163,plain,
% 7.77/1.48      ( sK0 != k1_xboole_0
% 7.77/1.48      | k1_xboole_0 = sK0
% 7.77/1.48      | k1_xboole_0 != k1_xboole_0 ),
% 7.77/1.48      inference(instantiation,[status(thm)],[c_1162]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_2846,plain,
% 7.77/1.48      ( ~ v1_funct_2(sK3,sK1,sK0)
% 7.77/1.48      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 7.77/1.48      | ~ v1_funct_1(sK3)
% 7.77/1.48      | ~ v2_funct_1(sK3)
% 7.77/1.48      | k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(sK0)
% 7.77/1.48      | sK0 = k1_xboole_0 ),
% 7.77/1.48      inference(predicate_to_equality_rev,[status(thm)],[c_2844]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_10,plain,
% 7.77/1.48      ( ~ r2_relset_1(X0,X1,X2,X3)
% 7.77/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.77/1.48      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.77/1.48      | X2 = X3 ),
% 7.77/1.48      inference(cnf_transformation,[],[f49]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_350,plain,
% 7.77/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.77/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.77/1.48      | X3 = X0
% 7.77/1.48      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 7.77/1.48      | k6_partfun1(sK0) != X3
% 7.77/1.48      | sK0 != X2
% 7.77/1.48      | sK0 != X1 ),
% 7.77/1.48      inference(resolution_lifted,[status(thm)],[c_10,c_26]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_351,plain,
% 7.77/1.48      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.77/1.48      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.77/1.48      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.77/1.48      inference(unflattening,[status(thm)],[c_350]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_11,plain,
% 7.77/1.48      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 7.77/1.48      inference(cnf_transformation,[],[f82]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_359,plain,
% 7.77/1.48      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.77/1.48      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.77/1.48      inference(forward_subsumption_resolution,
% 7.77/1.48                [status(thm)],
% 7.77/1.48                [c_351,c_11]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_1057,plain,
% 7.77/1.48      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.77/1.48      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 7.77/1.48      inference(predicate_to_equality,[status(thm)],[c_359]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_12,plain,
% 7.77/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.77/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.77/1.48      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.77/1.48      | ~ v1_funct_1(X0)
% 7.77/1.48      | ~ v1_funct_1(X3) ),
% 7.77/1.49      inference(cnf_transformation,[],[f53]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_1164,plain,
% 7.77/1.49      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.77/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 7.77/1.49      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.77/1.49      | ~ v1_funct_1(sK3)
% 7.77/1.49      | ~ v1_funct_1(sK2) ),
% 7.77/1.49      inference(instantiation,[status(thm)],[c_12]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_1750,plain,
% 7.77/1.49      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.77/1.49      inference(global_propositional_subsumption,
% 7.77/1.49                [status(thm)],
% 7.77/1.49                [c_1057,c_33,c_31,c_30,c_28,c_359,c_1164]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_27,negated_conjecture,
% 7.77/1.49      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 7.77/1.49      inference(cnf_transformation,[],[f69]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_17,plain,
% 7.77/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.77/1.49      | ~ v1_funct_2(X3,X4,X1)
% 7.77/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 7.77/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.77/1.49      | ~ v1_funct_1(X0)
% 7.77/1.49      | ~ v1_funct_1(X3)
% 7.77/1.49      | v2_funct_1(X0)
% 7.77/1.49      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 7.77/1.49      | k2_relset_1(X4,X1,X3) != X1
% 7.77/1.49      | k1_xboole_0 = X2 ),
% 7.77/1.49      inference(cnf_transformation,[],[f59]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_1070,plain,
% 7.77/1.49      ( k2_relset_1(X0,X1,X2) != X1
% 7.77/1.49      | k1_xboole_0 = X3
% 7.77/1.49      | v1_funct_2(X4,X1,X3) != iProver_top
% 7.77/1.49      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.77/1.49      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
% 7.77/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.77/1.49      | v1_funct_1(X4) != iProver_top
% 7.77/1.49      | v1_funct_1(X2) != iProver_top
% 7.77/1.49      | v2_funct_1(X4) = iProver_top
% 7.77/1.49      | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top ),
% 7.77/1.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_4572,plain,
% 7.77/1.49      ( k1_xboole_0 = X0
% 7.77/1.49      | v1_funct_2(X1,sK1,X0) != iProver_top
% 7.77/1.49      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 7.77/1.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 7.77/1.49      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.77/1.49      | v1_funct_1(X1) != iProver_top
% 7.77/1.49      | v1_funct_1(sK2) != iProver_top
% 7.77/1.49      | v2_funct_1(X1) = iProver_top
% 7.77/1.49      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
% 7.77/1.49      inference(superposition,[status(thm)],[c_27,c_1070]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_4577,plain,
% 7.77/1.49      ( v1_funct_1(X1) != iProver_top
% 7.77/1.49      | v1_funct_2(X1,sK1,X0) != iProver_top
% 7.77/1.49      | k1_xboole_0 = X0
% 7.77/1.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 7.77/1.49      | v2_funct_1(X1) = iProver_top
% 7.77/1.49      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
% 7.77/1.49      inference(global_propositional_subsumption,
% 7.77/1.49                [status(thm)],
% 7.77/1.49                [c_4572,c_34,c_35,c_36]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_4578,plain,
% 7.77/1.49      ( k1_xboole_0 = X0
% 7.77/1.49      | v1_funct_2(X1,sK1,X0) != iProver_top
% 7.77/1.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 7.77/1.49      | v1_funct_1(X1) != iProver_top
% 7.77/1.49      | v2_funct_1(X1) = iProver_top
% 7.77/1.49      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
% 7.77/1.49      inference(renaming,[status(thm)],[c_4577]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_4581,plain,
% 7.77/1.49      ( sK0 = k1_xboole_0
% 7.77/1.49      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 7.77/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.77/1.49      | v1_funct_1(sK3) != iProver_top
% 7.77/1.49      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 7.77/1.49      | v2_funct_1(sK3) = iProver_top ),
% 7.77/1.49      inference(superposition,[status(thm)],[c_1750,c_4578]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_4582,plain,
% 7.77/1.49      ( ~ v1_funct_2(sK3,sK1,sK0)
% 7.77/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 7.77/1.49      | ~ v1_funct_1(sK3)
% 7.77/1.49      | ~ v2_funct_1(k6_partfun1(sK0))
% 7.77/1.49      | v2_funct_1(sK3)
% 7.77/1.49      | sK0 = k1_xboole_0 ),
% 7.77/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_4581]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_4,plain,
% 7.77/1.49      ( v2_funct_1(k6_partfun1(X0)) ),
% 7.77/1.49      inference(cnf_transformation,[],[f77]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_4818,plain,
% 7.77/1.49      ( v2_funct_1(k6_partfun1(sK0)) ),
% 7.77/1.49      inference(instantiation,[status(thm)],[c_4]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_8425,plain,
% 7.77/1.49      ( k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(sK0) ),
% 7.77/1.49      inference(global_propositional_subsumption,
% 7.77/1.49                [status(thm)],
% 7.77/1.49                [c_2844,c_30,c_29,c_28,c_24,c_633,c_1163,c_2846,c_4582,
% 7.77/1.49                 c_4818]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_4819,plain,
% 7.77/1.49      ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
% 7.77/1.49      inference(predicate_to_equality,[status(thm)],[c_4818]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_4893,plain,
% 7.77/1.49      ( v2_funct_1(sK3) = iProver_top ),
% 7.77/1.49      inference(global_propositional_subsumption,
% 7.77/1.49                [status(thm)],
% 7.77/1.49                [c_4581,c_37,c_38,c_39,c_24,c_633,c_1163,c_4819]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_1062,plain,
% 7.77/1.49      ( v1_funct_1(sK3) = iProver_top ),
% 7.77/1.49      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_6,plain,
% 7.77/1.49      ( ~ v1_funct_1(X0)
% 7.77/1.49      | ~ v2_funct_1(X0)
% 7.77/1.49      | ~ v1_relat_1(X0)
% 7.77/1.49      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
% 7.77/1.49      inference(cnf_transformation,[],[f79]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_1078,plain,
% 7.77/1.49      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
% 7.77/1.49      | v1_funct_1(X0) != iProver_top
% 7.77/1.49      | v2_funct_1(X0) != iProver_top
% 7.77/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.77/1.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_2044,plain,
% 7.77/1.49      ( k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(k2_relat_1(sK3))
% 7.77/1.49      | v2_funct_1(sK3) != iProver_top
% 7.77/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.77/1.49      inference(superposition,[status(thm)],[c_1062,c_1078]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_1064,plain,
% 7.77/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 7.77/1.49      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_0,plain,
% 7.77/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.77/1.49      | ~ v1_relat_1(X1)
% 7.77/1.49      | v1_relat_1(X0) ),
% 7.77/1.49      inference(cnf_transformation,[],[f40]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_1082,plain,
% 7.77/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.77/1.49      | v1_relat_1(X1) != iProver_top
% 7.77/1.49      | v1_relat_1(X0) = iProver_top ),
% 7.77/1.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_1957,plain,
% 7.77/1.49      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 7.77/1.49      | v1_relat_1(sK3) = iProver_top ),
% 7.77/1.49      inference(superposition,[status(thm)],[c_1064,c_1082]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_1,plain,
% 7.77/1.49      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 7.77/1.49      inference(cnf_transformation,[],[f41]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_2121,plain,
% 7.77/1.49      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
% 7.77/1.49      inference(instantiation,[status(thm)],[c_1]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_2122,plain,
% 7.77/1.49      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
% 7.77/1.49      inference(predicate_to_equality,[status(thm)],[c_2121]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_2568,plain,
% 7.77/1.49      ( v2_funct_1(sK3) != iProver_top
% 7.77/1.49      | k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(k2_relat_1(sK3)) ),
% 7.77/1.49      inference(global_propositional_subsumption,
% 7.77/1.49                [status(thm)],
% 7.77/1.49                [c_2044,c_1957,c_2122]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_2569,plain,
% 7.77/1.49      ( k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(k2_relat_1(sK3))
% 7.77/1.49      | v2_funct_1(sK3) != iProver_top ),
% 7.77/1.49      inference(renaming,[status(thm)],[c_2568]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_4897,plain,
% 7.77/1.49      ( k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(k2_relat_1(sK3)) ),
% 7.77/1.49      inference(superposition,[status(thm)],[c_4893,c_2569]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_8427,plain,
% 7.77/1.49      ( k6_partfun1(k2_relat_1(sK3)) = k6_partfun1(sK0) ),
% 7.77/1.49      inference(demodulation,[status(thm)],[c_8425,c_4897]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_2,plain,
% 7.77/1.49      ( k2_relat_1(k6_partfun1(X0)) = X0 ),
% 7.77/1.49      inference(cnf_transformation,[],[f75]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_17389,plain,
% 7.77/1.49      ( k2_relat_1(k6_partfun1(sK0)) = k2_relat_1(sK3) ),
% 7.77/1.49      inference(superposition,[status(thm)],[c_8427,c_2]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_17390,plain,
% 7.77/1.49      ( k2_relat_1(sK3) = sK0 ),
% 7.77/1.49      inference(demodulation,[status(thm)],[c_17389,c_2]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_7,plain,
% 7.77/1.49      ( ~ v1_funct_1(X0)
% 7.77/1.49      | ~ v2_funct_1(X0)
% 7.77/1.49      | ~ v1_relat_1(X0)
% 7.77/1.49      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
% 7.77/1.49      inference(cnf_transformation,[],[f80]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_1077,plain,
% 7.77/1.49      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
% 7.77/1.49      | v1_funct_1(X0) != iProver_top
% 7.77/1.49      | v2_funct_1(X0) != iProver_top
% 7.77/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.77/1.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_1962,plain,
% 7.77/1.49      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
% 7.77/1.49      | v2_funct_1(sK3) != iProver_top
% 7.77/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.77/1.49      inference(superposition,[status(thm)],[c_1062,c_1077]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_2161,plain,
% 7.77/1.49      ( v2_funct_1(sK3) != iProver_top
% 7.77/1.49      | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3)) ),
% 7.77/1.49      inference(global_propositional_subsumption,
% 7.77/1.49                [status(thm)],
% 7.77/1.49                [c_1962,c_1957,c_2122]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_2162,plain,
% 7.77/1.49      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
% 7.77/1.49      | v2_funct_1(sK3) != iProver_top ),
% 7.77/1.49      inference(renaming,[status(thm)],[c_2161]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_4898,plain,
% 7.77/1.49      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3)) ),
% 7.77/1.49      inference(superposition,[status(thm)],[c_4893,c_2162]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_8,plain,
% 7.77/1.49      ( ~ v1_funct_1(X0)
% 7.77/1.49      | ~ v1_funct_1(X1)
% 7.77/1.49      | ~ v2_funct_1(X0)
% 7.77/1.49      | ~ v1_relat_1(X0)
% 7.77/1.49      | ~ v1_relat_1(X1)
% 7.77/1.49      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
% 7.77/1.49      | k2_funct_1(X0) = X1
% 7.77/1.49      | k1_relat_1(X0) != k2_relat_1(X1) ),
% 7.77/1.49      inference(cnf_transformation,[],[f81]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_1076,plain,
% 7.77/1.49      ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 7.77/1.49      | k2_funct_1(X1) = X0
% 7.77/1.49      | k1_relat_1(X1) != k2_relat_1(X0)
% 7.77/1.49      | v1_funct_1(X1) != iProver_top
% 7.77/1.49      | v1_funct_1(X0) != iProver_top
% 7.77/1.49      | v2_funct_1(X1) != iProver_top
% 7.77/1.49      | v1_relat_1(X1) != iProver_top
% 7.77/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.77/1.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_4928,plain,
% 7.77/1.49      ( k2_funct_1(k2_funct_1(sK3)) = sK3
% 7.77/1.49      | k1_relat_1(k2_funct_1(sK3)) != k2_relat_1(sK3)
% 7.77/1.49      | k6_partfun1(k2_relat_1(k2_funct_1(sK3))) != k6_partfun1(k1_relat_1(sK3))
% 7.77/1.49      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 7.77/1.49      | v1_funct_1(sK3) != iProver_top
% 7.77/1.49      | v2_funct_1(k2_funct_1(sK3)) != iProver_top
% 7.77/1.49      | v1_relat_1(k2_funct_1(sK3)) != iProver_top
% 7.77/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.77/1.49      inference(superposition,[status(thm)],[c_4898,c_1076]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_11239,plain,
% 7.77/1.49      ( v1_relat_1(k2_funct_1(sK3)) != iProver_top
% 7.77/1.49      | v2_funct_1(k2_funct_1(sK3)) != iProver_top
% 7.77/1.49      | k2_funct_1(k2_funct_1(sK3)) = sK3
% 7.77/1.49      | k1_relat_1(k2_funct_1(sK3)) != k2_relat_1(sK3)
% 7.77/1.49      | k6_partfun1(k2_relat_1(k2_funct_1(sK3))) != k6_partfun1(k1_relat_1(sK3))
% 7.77/1.49      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 7.77/1.49      inference(global_propositional_subsumption,
% 7.77/1.49                [status(thm)],
% 7.77/1.49                [c_4928,c_37,c_1957,c_2122]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_11240,plain,
% 7.77/1.49      ( k2_funct_1(k2_funct_1(sK3)) = sK3
% 7.77/1.49      | k1_relat_1(k2_funct_1(sK3)) != k2_relat_1(sK3)
% 7.77/1.49      | k6_partfun1(k2_relat_1(k2_funct_1(sK3))) != k6_partfun1(k1_relat_1(sK3))
% 7.77/1.49      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 7.77/1.49      | v2_funct_1(k2_funct_1(sK3)) != iProver_top
% 7.77/1.49      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 7.77/1.49      inference(renaming,[status(thm)],[c_11239]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_21,plain,
% 7.77/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.77/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.77/1.49      | ~ v1_funct_1(X0)
% 7.77/1.49      | ~ v2_funct_1(X0)
% 7.77/1.49      | k2_relset_1(X1,X2,X0) != X2
% 7.77/1.49      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 7.77/1.49      | k1_xboole_0 = X2 ),
% 7.77/1.49      inference(cnf_transformation,[],[f61]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_1066,plain,
% 7.77/1.49      ( k2_relset_1(X0,X1,X2) != X1
% 7.77/1.49      | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
% 7.77/1.49      | k1_xboole_0 = X1
% 7.77/1.49      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.77/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.77/1.49      | v1_funct_1(X2) != iProver_top
% 7.77/1.49      | v2_funct_1(X2) != iProver_top ),
% 7.77/1.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_2676,plain,
% 7.77/1.49      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
% 7.77/1.49      | sK1 = k1_xboole_0
% 7.77/1.49      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 7.77/1.49      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.77/1.49      | v1_funct_1(sK2) != iProver_top
% 7.77/1.49      | v2_funct_1(sK2) != iProver_top ),
% 7.77/1.49      inference(superposition,[status(thm)],[c_27,c_1066]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_1059,plain,
% 7.77/1.49      ( v1_funct_1(sK2) = iProver_top ),
% 7.77/1.49      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_1963,plain,
% 7.77/1.49      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
% 7.77/1.49      | v2_funct_1(sK2) != iProver_top
% 7.77/1.49      | v1_relat_1(sK2) != iProver_top ),
% 7.77/1.49      inference(superposition,[status(thm)],[c_1059,c_1077]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_25,negated_conjecture,
% 7.77/1.49      ( v2_funct_1(sK2) ),
% 7.77/1.49      inference(cnf_transformation,[],[f71]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_1061,plain,
% 7.77/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.77/1.49      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_1958,plain,
% 7.77/1.49      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 7.77/1.49      | v1_relat_1(sK2) = iProver_top ),
% 7.77/1.49      inference(superposition,[status(thm)],[c_1061,c_1082]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_1960,plain,
% 7.77/1.49      ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK2) ),
% 7.77/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_1958]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_1965,plain,
% 7.77/1.49      ( ~ v2_funct_1(sK2)
% 7.77/1.49      | ~ v1_relat_1(sK2)
% 7.77/1.49      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
% 7.77/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_1963]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_2124,plain,
% 7.77/1.49      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 7.77/1.49      inference(instantiation,[status(thm)],[c_1]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_2166,plain,
% 7.77/1.49      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
% 7.77/1.49      inference(global_propositional_subsumption,
% 7.77/1.49                [status(thm)],
% 7.77/1.49                [c_1963,c_25,c_1960,c_1965,c_2124]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_2678,plain,
% 7.77/1.49      ( k6_partfun1(k1_relat_1(sK2)) = k6_partfun1(sK0)
% 7.77/1.49      | sK1 = k1_xboole_0
% 7.77/1.49      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 7.77/1.49      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.77/1.49      | v1_funct_1(sK2) != iProver_top
% 7.77/1.49      | v2_funct_1(sK2) != iProver_top ),
% 7.77/1.49      inference(demodulation,[status(thm)],[c_2676,c_2166]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_41,plain,
% 7.77/1.49      ( v2_funct_1(sK2) = iProver_top ),
% 7.77/1.49      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_23,negated_conjecture,
% 7.77/1.49      ( k1_xboole_0 != sK1 ),
% 7.77/1.49      inference(cnf_transformation,[],[f73]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_1142,plain,
% 7.77/1.49      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 7.77/1.49      inference(instantiation,[status(thm)],[c_603]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_1143,plain,
% 7.77/1.49      ( sK1 != k1_xboole_0
% 7.77/1.49      | k1_xboole_0 = sK1
% 7.77/1.49      | k1_xboole_0 != k1_xboole_0 ),
% 7.77/1.49      inference(instantiation,[status(thm)],[c_1142]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_3576,plain,
% 7.77/1.49      ( k6_partfun1(k1_relat_1(sK2)) = k6_partfun1(sK0) ),
% 7.77/1.49      inference(global_propositional_subsumption,
% 7.77/1.49                [status(thm)],
% 7.77/1.49                [c_2678,c_34,c_35,c_36,c_41,c_23,c_633,c_1143]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_3583,plain,
% 7.77/1.49      ( k2_relat_1(k6_partfun1(sK0)) = k1_relat_1(sK2) ),
% 7.77/1.49      inference(superposition,[status(thm)],[c_3576,c_2]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_3584,plain,
% 7.77/1.49      ( k1_relat_1(sK2) = sK0 ),
% 7.77/1.49      inference(demodulation,[status(thm)],[c_3583,c_2]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_2843,plain,
% 7.77/1.49      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 7.77/1.49      | sK1 = k1_xboole_0
% 7.77/1.49      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 7.77/1.49      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.77/1.49      | v1_funct_1(sK2) != iProver_top
% 7.77/1.49      | v2_funct_1(sK2) != iProver_top ),
% 7.77/1.49      inference(superposition,[status(thm)],[c_27,c_1067]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_2045,plain,
% 7.77/1.49      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
% 7.77/1.49      | v2_funct_1(sK2) != iProver_top
% 7.77/1.49      | v1_relat_1(sK2) != iProver_top ),
% 7.77/1.49      inference(superposition,[status(thm)],[c_1059,c_1078]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_2047,plain,
% 7.77/1.49      ( ~ v2_funct_1(sK2)
% 7.77/1.49      | ~ v1_relat_1(sK2)
% 7.77/1.49      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 7.77/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_2045]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_2573,plain,
% 7.77/1.49      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 7.77/1.49      inference(global_propositional_subsumption,
% 7.77/1.49                [status(thm)],
% 7.77/1.49                [c_2045,c_25,c_1960,c_2047,c_2124]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_2845,plain,
% 7.77/1.49      ( k6_partfun1(k2_relat_1(sK2)) = k6_partfun1(sK1)
% 7.77/1.49      | sK1 = k1_xboole_0
% 7.77/1.49      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 7.77/1.49      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.77/1.49      | v1_funct_1(sK2) != iProver_top
% 7.77/1.49      | v2_funct_1(sK2) != iProver_top ),
% 7.77/1.49      inference(demodulation,[status(thm)],[c_2843,c_2573]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_3587,plain,
% 7.77/1.49      ( k6_partfun1(k2_relat_1(sK2)) = k6_partfun1(sK1) ),
% 7.77/1.49      inference(global_propositional_subsumption,
% 7.77/1.49                [status(thm)],
% 7.77/1.49                [c_2845,c_34,c_35,c_36,c_41,c_23,c_633,c_1143]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_3597,plain,
% 7.77/1.49      ( k2_relat_1(k6_partfun1(sK1)) = k2_relat_1(sK2) ),
% 7.77/1.49      inference(superposition,[status(thm)],[c_3587,c_2]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_3598,plain,
% 7.77/1.49      ( k2_relat_1(sK2) = sK1 ),
% 7.77/1.49      inference(demodulation,[status(thm)],[c_3597,c_2]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_2677,plain,
% 7.77/1.49      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 7.77/1.49      | sK0 = k1_xboole_0
% 7.77/1.49      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 7.77/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.77/1.49      | v1_funct_1(sK3) != iProver_top
% 7.77/1.49      | v2_funct_1(sK3) != iProver_top ),
% 7.77/1.49      inference(superposition,[status(thm)],[c_1757,c_1066]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_2679,plain,
% 7.77/1.49      ( ~ v1_funct_2(sK3,sK1,sK0)
% 7.77/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 7.77/1.49      | ~ v1_funct_1(sK3)
% 7.77/1.49      | ~ v2_funct_1(sK3)
% 7.77/1.49      | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 7.77/1.49      | sK0 = k1_xboole_0 ),
% 7.77/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_2677]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_5834,plain,
% 7.77/1.49      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
% 7.77/1.49      inference(global_propositional_subsumption,
% 7.77/1.49                [status(thm)],
% 7.77/1.49                [c_2677,c_30,c_29,c_28,c_24,c_633,c_1163,c_2679,c_4582,
% 7.77/1.49                 c_4818]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_5836,plain,
% 7.77/1.49      ( k6_partfun1(k1_relat_1(sK3)) = k6_partfun1(sK1) ),
% 7.77/1.49      inference(demodulation,[status(thm)],[c_5834,c_4898]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_6479,plain,
% 7.77/1.49      ( k2_relat_1(k6_partfun1(sK1)) = k1_relat_1(sK3) ),
% 7.77/1.49      inference(superposition,[status(thm)],[c_5836,c_2]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_6480,plain,
% 7.77/1.49      ( k1_relat_1(sK3) = sK1 ),
% 7.77/1.49      inference(demodulation,[status(thm)],[c_6479,c_2]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_14,plain,
% 7.77/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.77/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.77/1.49      | ~ v1_funct_1(X0)
% 7.77/1.49      | ~ v1_funct_1(X3)
% 7.77/1.49      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 7.77/1.49      inference(cnf_transformation,[],[f54]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_1072,plain,
% 7.77/1.49      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 7.77/1.49      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 7.77/1.49      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.77/1.49      | v1_funct_1(X5) != iProver_top
% 7.77/1.49      | v1_funct_1(X4) != iProver_top ),
% 7.77/1.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_2743,plain,
% 7.77/1.49      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 7.77/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.77/1.49      | v1_funct_1(X2) != iProver_top
% 7.77/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.77/1.49      inference(superposition,[status(thm)],[c_1064,c_1072]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_2849,plain,
% 7.77/1.49      ( v1_funct_1(X2) != iProver_top
% 7.77/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.77/1.49      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 7.77/1.49      inference(global_propositional_subsumption,
% 7.77/1.49                [status(thm)],
% 7.77/1.49                [c_2743,c_37]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_2850,plain,
% 7.77/1.49      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 7.77/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.77/1.49      | v1_funct_1(X2) != iProver_top ),
% 7.77/1.49      inference(renaming,[status(thm)],[c_2849]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_2858,plain,
% 7.77/1.49      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 7.77/1.49      | v1_funct_1(sK2) != iProver_top ),
% 7.77/1.49      inference(superposition,[status(thm)],[c_1061,c_2850]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_2859,plain,
% 7.77/1.49      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 7.77/1.49      | v1_funct_1(sK2) != iProver_top ),
% 7.77/1.49      inference(light_normalisation,[status(thm)],[c_2858,c_1750]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_4377,plain,
% 7.77/1.49      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 7.77/1.49      inference(global_propositional_subsumption,
% 7.77/1.49                [status(thm)],
% 7.77/1.49                [c_2859,c_34]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_4379,plain,
% 7.77/1.49      ( k2_funct_1(sK3) = sK2
% 7.77/1.49      | k1_relat_1(sK3) != k2_relat_1(sK2)
% 7.77/1.49      | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
% 7.77/1.49      | v1_funct_1(sK3) != iProver_top
% 7.77/1.49      | v1_funct_1(sK2) != iProver_top
% 7.77/1.49      | v2_funct_1(sK3) != iProver_top
% 7.77/1.49      | v1_relat_1(sK3) != iProver_top
% 7.77/1.49      | v1_relat_1(sK2) != iProver_top ),
% 7.77/1.49      inference(superposition,[status(thm)],[c_4377,c_1076]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_4380,plain,
% 7.77/1.49      ( k2_funct_1(sK3) = sK2
% 7.77/1.49      | k1_relat_1(sK3) != sK1
% 7.77/1.49      | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
% 7.77/1.49      | v1_funct_1(sK3) != iProver_top
% 7.77/1.49      | v1_funct_1(sK2) != iProver_top
% 7.77/1.49      | v2_funct_1(sK3) != iProver_top
% 7.77/1.49      | v1_relat_1(sK3) != iProver_top
% 7.77/1.49      | v1_relat_1(sK2) != iProver_top ),
% 7.77/1.49      inference(light_normalisation,[status(thm)],[c_4379,c_3598]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_1959,plain,
% 7.77/1.49      ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0)) | v1_relat_1(sK3) ),
% 7.77/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_1957]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_4381,plain,
% 7.77/1.49      ( ~ v1_funct_1(sK3)
% 7.77/1.49      | ~ v1_funct_1(sK2)
% 7.77/1.49      | ~ v2_funct_1(sK3)
% 7.77/1.49      | ~ v1_relat_1(sK3)
% 7.77/1.49      | ~ v1_relat_1(sK2)
% 7.77/1.49      | k2_funct_1(sK3) = sK2
% 7.77/1.49      | k1_relat_1(sK3) != sK1
% 7.77/1.49      | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0) ),
% 7.77/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_4380]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_9424,plain,
% 7.77/1.49      ( k2_funct_1(sK3) = sK2 ),
% 7.77/1.49      inference(global_propositional_subsumption,
% 7.77/1.49                [status(thm)],
% 7.77/1.49                [c_4380,c_33,c_30,c_29,c_28,c_24,c_633,c_1163,c_1959,
% 7.77/1.49                 c_1960,c_2121,c_2124,c_4381,c_4582,c_4818,c_6480,c_8427]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_11243,plain,
% 7.77/1.49      ( k2_funct_1(sK2) = sK3
% 7.77/1.49      | k2_relat_1(sK3) != sK0
% 7.77/1.49      | k6_partfun1(sK1) != k6_partfun1(sK1)
% 7.77/1.49      | v1_funct_1(sK2) != iProver_top
% 7.77/1.49      | v2_funct_1(sK2) != iProver_top
% 7.77/1.49      | v1_relat_1(sK2) != iProver_top ),
% 7.77/1.49      inference(light_normalisation,
% 7.77/1.49                [status(thm)],
% 7.77/1.49                [c_11240,c_3584,c_3598,c_6480,c_9424]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_11244,plain,
% 7.77/1.49      ( k2_funct_1(sK2) = sK3
% 7.77/1.49      | k2_relat_1(sK3) != sK0
% 7.77/1.49      | v1_funct_1(sK2) != iProver_top
% 7.77/1.49      | v2_funct_1(sK2) != iProver_top
% 7.77/1.49      | v1_relat_1(sK2) != iProver_top ),
% 7.77/1.49      inference(equality_resolution_simp,[status(thm)],[c_11243]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_2125,plain,
% 7.77/1.49      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 7.77/1.49      inference(predicate_to_equality,[status(thm)],[c_2124]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_22,negated_conjecture,
% 7.77/1.49      ( k2_funct_1(sK2) != sK3 ),
% 7.77/1.49      inference(cnf_transformation,[],[f74]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(contradiction,plain,
% 7.77/1.49      ( $false ),
% 7.77/1.49      inference(minisat,
% 7.77/1.49                [status(thm)],
% 7.77/1.49                [c_17390,c_11244,c_2125,c_1958,c_22,c_41,c_34]) ).
% 7.77/1.49  
% 7.77/1.49  
% 7.77/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.77/1.49  
% 7.77/1.49  ------                               Statistics
% 7.77/1.49  
% 7.77/1.49  ------ General
% 7.77/1.49  
% 7.77/1.49  abstr_ref_over_cycles:                  0
% 7.77/1.49  abstr_ref_under_cycles:                 0
% 7.77/1.49  gc_basic_clause_elim:                   0
% 7.77/1.49  forced_gc_time:                         0
% 7.77/1.49  parsing_time:                           0.009
% 7.77/1.49  unif_index_cands_time:                  0.
% 7.77/1.49  unif_index_add_time:                    0.
% 7.77/1.49  orderings_time:                         0.
% 7.77/1.49  out_proof_time:                         0.015
% 7.77/1.49  total_time:                             0.712
% 7.77/1.49  num_of_symbols:                         51
% 7.77/1.49  num_of_terms:                           27503
% 7.77/1.49  
% 7.77/1.49  ------ Preprocessing
% 7.77/1.49  
% 7.77/1.49  num_of_splits:                          0
% 7.77/1.49  num_of_split_atoms:                     0
% 7.77/1.49  num_of_reused_defs:                     0
% 7.77/1.49  num_eq_ax_congr_red:                    0
% 7.77/1.49  num_of_sem_filtered_clauses:            1
% 7.77/1.49  num_of_subtypes:                        0
% 7.77/1.49  monotx_restored_types:                  0
% 7.77/1.49  sat_num_of_epr_types:                   0
% 7.77/1.49  sat_num_of_non_cyclic_types:            0
% 7.77/1.49  sat_guarded_non_collapsed_types:        0
% 7.77/1.49  num_pure_diseq_elim:                    0
% 7.77/1.49  simp_replaced_by:                       0
% 7.77/1.49  res_preprocessed:                       166
% 7.77/1.49  prep_upred:                             0
% 7.77/1.49  prep_unflattend:                        12
% 7.77/1.49  smt_new_axioms:                         0
% 7.77/1.49  pred_elim_cands:                        5
% 7.77/1.49  pred_elim:                              1
% 7.77/1.49  pred_elim_cl:                           1
% 7.77/1.49  pred_elim_cycles:                       3
% 7.77/1.49  merged_defs:                            0
% 7.77/1.49  merged_defs_ncl:                        0
% 7.77/1.49  bin_hyper_res:                          0
% 7.77/1.49  prep_cycles:                            4
% 7.77/1.49  pred_elim_time:                         0.005
% 7.77/1.49  splitting_time:                         0.
% 7.77/1.49  sem_filter_time:                        0.
% 7.77/1.49  monotx_time:                            0.
% 7.77/1.49  subtype_inf_time:                       0.
% 7.77/1.49  
% 7.77/1.49  ------ Problem properties
% 7.77/1.49  
% 7.77/1.49  clauses:                                33
% 7.77/1.49  conjectures:                            11
% 7.77/1.49  epr:                                    7
% 7.77/1.49  horn:                                   29
% 7.77/1.49  ground:                                 12
% 7.77/1.49  unary:                                  17
% 7.77/1.49  binary:                                 1
% 7.77/1.49  lits:                                   121
% 7.77/1.49  lits_eq:                                29
% 7.77/1.49  fd_pure:                                0
% 7.77/1.49  fd_pseudo:                              0
% 7.77/1.49  fd_cond:                                4
% 7.77/1.49  fd_pseudo_cond:                         1
% 7.77/1.49  ac_symbols:                             0
% 7.77/1.49  
% 7.77/1.49  ------ Propositional Solver
% 7.77/1.49  
% 7.77/1.49  prop_solver_calls:                      33
% 7.77/1.49  prop_fast_solver_calls:                 2859
% 7.77/1.49  smt_solver_calls:                       0
% 7.77/1.49  smt_fast_solver_calls:                  0
% 7.77/1.49  prop_num_of_clauses:                    9303
% 7.77/1.49  prop_preprocess_simplified:             16460
% 7.77/1.49  prop_fo_subsumed:                       642
% 7.77/1.49  prop_solver_time:                       0.
% 7.77/1.49  smt_solver_time:                        0.
% 7.77/1.49  smt_fast_solver_time:                   0.
% 7.77/1.49  prop_fast_solver_time:                  0.
% 7.77/1.49  prop_unsat_core_time:                   0.001
% 7.77/1.49  
% 7.77/1.49  ------ QBF
% 7.77/1.49  
% 7.77/1.49  qbf_q_res:                              0
% 7.77/1.49  qbf_num_tautologies:                    0
% 7.77/1.49  qbf_prep_cycles:                        0
% 7.77/1.49  
% 7.77/1.49  ------ BMC1
% 7.77/1.49  
% 7.77/1.49  bmc1_current_bound:                     -1
% 7.77/1.49  bmc1_last_solved_bound:                 -1
% 7.77/1.49  bmc1_unsat_core_size:                   -1
% 7.77/1.49  bmc1_unsat_core_parents_size:           -1
% 7.77/1.49  bmc1_merge_next_fun:                    0
% 7.77/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.77/1.49  
% 7.77/1.49  ------ Instantiation
% 7.77/1.49  
% 7.77/1.49  inst_num_of_clauses:                    2365
% 7.77/1.49  inst_num_in_passive:                    937
% 7.77/1.49  inst_num_in_active:                     1269
% 7.77/1.49  inst_num_in_unprocessed:                159
% 7.77/1.49  inst_num_of_loops:                      1450
% 7.77/1.49  inst_num_of_learning_restarts:          0
% 7.77/1.49  inst_num_moves_active_passive:          177
% 7.77/1.49  inst_lit_activity:                      0
% 7.77/1.49  inst_lit_activity_moves:                1
% 7.77/1.49  inst_num_tautologies:                   0
% 7.77/1.49  inst_num_prop_implied:                  0
% 7.77/1.49  inst_num_existing_simplified:           0
% 7.77/1.49  inst_num_eq_res_simplified:             0
% 7.77/1.49  inst_num_child_elim:                    0
% 7.77/1.49  inst_num_of_dismatching_blockings:      521
% 7.77/1.49  inst_num_of_non_proper_insts:           2159
% 7.77/1.49  inst_num_of_duplicates:                 0
% 7.77/1.49  inst_inst_num_from_inst_to_res:         0
% 7.77/1.49  inst_dismatching_checking_time:         0.
% 7.77/1.49  
% 7.77/1.49  ------ Resolution
% 7.77/1.49  
% 7.77/1.49  res_num_of_clauses:                     0
% 7.77/1.49  res_num_in_passive:                     0
% 7.77/1.49  res_num_in_active:                      0
% 7.77/1.49  res_num_of_loops:                       170
% 7.77/1.49  res_forward_subset_subsumed:            179
% 7.77/1.49  res_backward_subset_subsumed:           0
% 7.77/1.49  res_forward_subsumed:                   0
% 7.77/1.49  res_backward_subsumed:                  0
% 7.77/1.49  res_forward_subsumption_resolution:     2
% 7.77/1.49  res_backward_subsumption_resolution:    0
% 7.77/1.49  res_clause_to_clause_subsumption:       1508
% 7.77/1.49  res_orphan_elimination:                 0
% 7.77/1.49  res_tautology_del:                      120
% 7.77/1.49  res_num_eq_res_simplified:              1
% 7.77/1.49  res_num_sel_changes:                    0
% 7.77/1.49  res_moves_from_active_to_pass:          0
% 7.77/1.49  
% 7.77/1.49  ------ Superposition
% 7.77/1.49  
% 7.77/1.49  sup_time_total:                         0.
% 7.77/1.49  sup_time_generating:                    0.
% 7.77/1.49  sup_time_sim_full:                      0.
% 7.77/1.49  sup_time_sim_immed:                     0.
% 7.77/1.49  
% 7.77/1.49  sup_num_of_clauses:                     707
% 7.77/1.49  sup_num_in_active:                      269
% 7.77/1.49  sup_num_in_passive:                     438
% 7.77/1.49  sup_num_of_loops:                       289
% 7.77/1.49  sup_fw_superposition:                   229
% 7.77/1.49  sup_bw_superposition:                   608
% 7.77/1.49  sup_immediate_simplified:               250
% 7.77/1.49  sup_given_eliminated:                   4
% 7.77/1.49  comparisons_done:                       0
% 7.77/1.49  comparisons_avoided:                    0
% 7.77/1.49  
% 7.77/1.49  ------ Simplifications
% 7.77/1.49  
% 7.77/1.49  
% 7.77/1.49  sim_fw_subset_subsumed:                 18
% 7.77/1.49  sim_bw_subset_subsumed:                 42
% 7.77/1.49  sim_fw_subsumed:                        24
% 7.77/1.49  sim_bw_subsumed:                        7
% 7.77/1.49  sim_fw_subsumption_res:                 0
% 7.77/1.49  sim_bw_subsumption_res:                 0
% 7.77/1.49  sim_tautology_del:                      0
% 7.77/1.49  sim_eq_tautology_del:                   18
% 7.77/1.49  sim_eq_res_simp:                        1
% 7.77/1.49  sim_fw_demodulated:                     12
% 7.77/1.49  sim_bw_demodulated:                     11
% 7.77/1.49  sim_light_normalised:                   215
% 7.77/1.49  sim_joinable_taut:                      0
% 7.77/1.49  sim_joinable_simp:                      0
% 7.77/1.49  sim_ac_normalised:                      0
% 7.77/1.49  sim_smt_subsumption:                    0
% 7.77/1.49  
%------------------------------------------------------------------------------

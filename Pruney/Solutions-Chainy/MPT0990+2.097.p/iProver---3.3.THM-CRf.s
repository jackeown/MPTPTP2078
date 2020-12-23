%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:17 EST 2020

% Result     : Theorem 2.48s
% Output     : CNFRefutation 2.48s
% Verified   : 
% Statistics : Number of formulae       :  173 (1002 expanded)
%              Number of clauses        :  102 ( 264 expanded)
%              Number of leaves         :   19 ( 271 expanded)
%              Depth                    :   19
%              Number of atoms          :  701 (8672 expanded)
%              Number of equality atoms :  340 (3185 expanded)
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
    inference(ennf_transformation,[],[f12])).

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
    inference(cnf_transformation,[],[f30])).

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
           => ( ( v2_funct_1(X2)
                & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
                & k2_relset_1(X0,X1,X2) = X1 )
             => ( k2_funct_1(X2) = X3
                | k1_xboole_0 = X1
                | k1_xboole_0 = X0 ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

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
    inference(ennf_transformation,[],[f16])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f39,plain,(
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

fof(f38,plain,
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

fof(f40,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f36,f39,f38])).

fof(f71,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f40])).

fof(f64,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f65,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f66,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f40])).

fof(f67,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f68,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f69,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f40])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f14])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f73,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f40])).

fof(f7,axiom,(
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
    inference(ennf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f23])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f8])).

fof(f11,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f83,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f52,f56])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f25])).

fof(f54,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f70,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f40])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f60,plain,(
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
    inference(cnf_transformation,[],[f32])).

fof(f2,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f78,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f44,f56])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f18,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f45,plain,(
    ! [X0] :
      ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f81,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f45,f56])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f76,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f42,f56])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f27])).

fof(f55,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1)
              & k1_relat_1(X1) = k2_relat_1(X0)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
          | k1_relat_1(X1) != k2_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
          | k1_relat_1(X1) != k2_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
      | k1_relat_1(X1) != k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
      | k1_relat_1(X1) != k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f47,f56])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f72,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f74,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f40])).

fof(f75,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f40])).

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

cnf(c_26,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_367,plain,
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
    inference(resolution_lifted,[status(thm)],[c_15,c_26])).

cnf(c_368,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0
    | k6_partfun1(sK0) != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_367])).

cnf(c_449,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_368])).

cnf(c_1066,plain,
    ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X0,sK0,X2) = sK0
    | v1_funct_2(X2,X0,sK0) != iProver_top
    | v1_funct_2(X1,sK0,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_449])).

cnf(c_1596,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1066])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_34,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_35,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_36,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_37,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_38,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_39,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_1765,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1596,c_34,c_35,c_36,c_37,c_38,c_39])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1076,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2685,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1765,c_1076])).

cnf(c_24,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_608,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_639,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_608])).

cnf(c_609,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1172,plain,
    ( sK0 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_609])).

cnf(c_1173,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1172])).

cnf(c_2688,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | sK0 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2685])).

cnf(c_10,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_354,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_26])).

cnf(c_355,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_354])).

cnf(c_11,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_363,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_355,c_11])).

cnf(c_1067,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_363])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1174,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1758,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1067,c_33,c_31,c_30,c_28,c_363,c_1174])).

cnf(c_27,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f70])).

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
    inference(cnf_transformation,[],[f60])).

cnf(c_1080,plain,
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

cnf(c_4709,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_27,c_1080])).

cnf(c_4716,plain,
    ( v1_funct_1(X1) != iProver_top
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | k1_xboole_0 = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4709,c_34,c_35,c_36])).

cnf(c_4717,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4716])).

cnf(c_4720,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1758,c_4717])).

cnf(c_4721,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(k6_partfun1(sK0))
    | v2_funct_1(sK3)
    | sK0 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4720])).

cnf(c_2,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_4741,plain,
    ( v2_funct_1(k6_partfun1(sK0)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_5216,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2685,c_30,c_29,c_28,c_24,c_639,c_1173,c_2688,c_4721,c_4741])).

cnf(c_4742,plain,
    ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4741])).

cnf(c_4964,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4720,c_37,c_38,c_39,c_24,c_639,c_1173,c_4742])).

cnf(c_1072,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_5,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v2_funct_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1089,plain,
    ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2031,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
    | v1_relat_1(sK3) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1072,c_1089])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1214,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1573,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1214])).

cnf(c_1574,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1573])).

cnf(c_2233,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
    | v2_funct_1(sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2031,c_39,c_1574])).

cnf(c_4969,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3)) ),
    inference(superposition,[status(thm)],[c_4964,c_2233])).

cnf(c_5218,plain,
    ( k6_partfun1(k1_relat_1(sK3)) = k6_partfun1(sK1) ),
    inference(demodulation,[status(thm)],[c_5216,c_4969])).

cnf(c_0,plain,
    ( k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_5703,plain,
    ( k2_relat_1(k6_partfun1(sK1)) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_5218,c_0])).

cnf(c_5704,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(demodulation,[status(thm)],[c_5703,c_0])).

cnf(c_1071,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_1074,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1082,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2748,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1074,c_1082])).

cnf(c_2812,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2748,c_37])).

cnf(c_2813,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_2812])).

cnf(c_2821,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1071,c_2813])).

cnf(c_2822,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2821,c_1758])).

cnf(c_3651,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2822,c_34])).

cnf(c_6,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v2_funct_1(X0)
    | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
    | k2_funct_1(X0) = X1
    | k1_relat_1(X1) != k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1088,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
    | k2_funct_1(X0) = X1
    | k1_relat_1(X1) != k2_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3772,plain,
    ( k2_funct_1(sK2) = sK3
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | k6_partfun1(k1_relat_1(sK2)) != k6_partfun1(sK0)
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3651,c_1088])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1086,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1991,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1071,c_1086])).

cnf(c_1992,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_1991,c_27])).

cnf(c_2684,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_27,c_1076])).

cnf(c_1069,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_2032,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
    | v1_relat_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1069,c_1089])).

cnf(c_25,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_41,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1684,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1685,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1684])).

cnf(c_2238,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2032,c_36,c_41,c_1685])).

cnf(c_2687,plain,
    ( k6_partfun1(k1_relat_1(sK2)) = k6_partfun1(sK0)
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2684,c_2238])).

cnf(c_23,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1152,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_609])).

cnf(c_1153,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1152])).

cnf(c_3571,plain,
    ( k6_partfun1(k1_relat_1(sK2)) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2687,c_34,c_35,c_36,c_41,c_23,c_639,c_1153])).

cnf(c_3579,plain,
    ( k2_relat_1(k6_partfun1(sK0)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_3571,c_0])).

cnf(c_3580,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(demodulation,[status(thm)],[c_3579,c_0])).

cnf(c_3776,plain,
    ( k2_funct_1(sK2) = sK3
    | k1_relat_1(sK3) != sK1
    | k6_partfun1(sK0) != k6_partfun1(sK0)
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3772,c_1992,c_3580])).

cnf(c_3777,plain,
    ( k2_funct_1(sK2) = sK3
    | k1_relat_1(sK3) != sK1
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3776])).

cnf(c_22,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f75])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5704,c_3777,c_1685,c_1574,c_22,c_41,c_39,c_37,c_36,c_34])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:50:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.48/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.02  
% 2.48/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.48/1.02  
% 2.48/1.02  ------  iProver source info
% 2.48/1.02  
% 2.48/1.02  git: date: 2020-06-30 10:37:57 +0100
% 2.48/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.48/1.02  git: non_committed_changes: false
% 2.48/1.02  git: last_make_outside_of_git: false
% 2.48/1.02  
% 2.48/1.02  ------ 
% 2.48/1.02  
% 2.48/1.02  ------ Input Options
% 2.48/1.02  
% 2.48/1.02  --out_options                           all
% 2.48/1.02  --tptp_safe_out                         true
% 2.48/1.02  --problem_path                          ""
% 2.48/1.02  --include_path                          ""
% 2.48/1.02  --clausifier                            res/vclausify_rel
% 2.48/1.02  --clausifier_options                    ""
% 2.48/1.02  --stdin                                 false
% 2.48/1.02  --stats_out                             all
% 2.48/1.02  
% 2.48/1.02  ------ General Options
% 2.48/1.02  
% 2.48/1.02  --fof                                   false
% 2.48/1.02  --time_out_real                         305.
% 2.48/1.02  --time_out_virtual                      -1.
% 2.48/1.02  --symbol_type_check                     false
% 2.48/1.02  --clausify_out                          false
% 2.48/1.02  --sig_cnt_out                           false
% 2.48/1.02  --trig_cnt_out                          false
% 2.48/1.02  --trig_cnt_out_tolerance                1.
% 2.48/1.02  --trig_cnt_out_sk_spl                   false
% 2.48/1.02  --abstr_cl_out                          false
% 2.48/1.02  
% 2.48/1.02  ------ Global Options
% 2.48/1.02  
% 2.48/1.02  --schedule                              default
% 2.48/1.02  --add_important_lit                     false
% 2.48/1.02  --prop_solver_per_cl                    1000
% 2.48/1.02  --min_unsat_core                        false
% 2.48/1.02  --soft_assumptions                      false
% 2.48/1.02  --soft_lemma_size                       3
% 2.48/1.02  --prop_impl_unit_size                   0
% 2.48/1.02  --prop_impl_unit                        []
% 2.48/1.02  --share_sel_clauses                     true
% 2.48/1.02  --reset_solvers                         false
% 2.48/1.02  --bc_imp_inh                            [conj_cone]
% 2.48/1.02  --conj_cone_tolerance                   3.
% 2.48/1.02  --extra_neg_conj                        none
% 2.48/1.02  --large_theory_mode                     true
% 2.48/1.02  --prolific_symb_bound                   200
% 2.48/1.02  --lt_threshold                          2000
% 2.48/1.02  --clause_weak_htbl                      true
% 2.48/1.02  --gc_record_bc_elim                     false
% 2.48/1.02  
% 2.48/1.02  ------ Preprocessing Options
% 2.48/1.02  
% 2.48/1.02  --preprocessing_flag                    true
% 2.48/1.02  --time_out_prep_mult                    0.1
% 2.48/1.02  --splitting_mode                        input
% 2.48/1.02  --splitting_grd                         true
% 2.48/1.02  --splitting_cvd                         false
% 2.48/1.02  --splitting_cvd_svl                     false
% 2.48/1.02  --splitting_nvd                         32
% 2.48/1.02  --sub_typing                            true
% 2.48/1.02  --prep_gs_sim                           true
% 2.48/1.02  --prep_unflatten                        true
% 2.48/1.02  --prep_res_sim                          true
% 2.48/1.02  --prep_upred                            true
% 2.48/1.02  --prep_sem_filter                       exhaustive
% 2.48/1.02  --prep_sem_filter_out                   false
% 2.48/1.02  --pred_elim                             true
% 2.48/1.02  --res_sim_input                         true
% 2.48/1.02  --eq_ax_congr_red                       true
% 2.48/1.02  --pure_diseq_elim                       true
% 2.48/1.02  --brand_transform                       false
% 2.48/1.02  --non_eq_to_eq                          false
% 2.48/1.02  --prep_def_merge                        true
% 2.48/1.02  --prep_def_merge_prop_impl              false
% 2.48/1.02  --prep_def_merge_mbd                    true
% 2.48/1.02  --prep_def_merge_tr_red                 false
% 2.48/1.02  --prep_def_merge_tr_cl                  false
% 2.48/1.02  --smt_preprocessing                     true
% 2.48/1.02  --smt_ac_axioms                         fast
% 2.48/1.02  --preprocessed_out                      false
% 2.48/1.02  --preprocessed_stats                    false
% 2.48/1.02  
% 2.48/1.02  ------ Abstraction refinement Options
% 2.48/1.02  
% 2.48/1.02  --abstr_ref                             []
% 2.48/1.02  --abstr_ref_prep                        false
% 2.48/1.02  --abstr_ref_until_sat                   false
% 2.48/1.02  --abstr_ref_sig_restrict                funpre
% 2.48/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.48/1.02  --abstr_ref_under                       []
% 2.48/1.02  
% 2.48/1.02  ------ SAT Options
% 2.48/1.02  
% 2.48/1.02  --sat_mode                              false
% 2.48/1.02  --sat_fm_restart_options                ""
% 2.48/1.02  --sat_gr_def                            false
% 2.48/1.02  --sat_epr_types                         true
% 2.48/1.02  --sat_non_cyclic_types                  false
% 2.48/1.02  --sat_finite_models                     false
% 2.48/1.02  --sat_fm_lemmas                         false
% 2.48/1.02  --sat_fm_prep                           false
% 2.48/1.02  --sat_fm_uc_incr                        true
% 2.48/1.02  --sat_out_model                         small
% 2.48/1.02  --sat_out_clauses                       false
% 2.48/1.02  
% 2.48/1.02  ------ QBF Options
% 2.48/1.02  
% 2.48/1.02  --qbf_mode                              false
% 2.48/1.02  --qbf_elim_univ                         false
% 2.48/1.02  --qbf_dom_inst                          none
% 2.48/1.02  --qbf_dom_pre_inst                      false
% 2.48/1.02  --qbf_sk_in                             false
% 2.48/1.02  --qbf_pred_elim                         true
% 2.48/1.02  --qbf_split                             512
% 2.48/1.02  
% 2.48/1.02  ------ BMC1 Options
% 2.48/1.02  
% 2.48/1.02  --bmc1_incremental                      false
% 2.48/1.02  --bmc1_axioms                           reachable_all
% 2.48/1.02  --bmc1_min_bound                        0
% 2.48/1.02  --bmc1_max_bound                        -1
% 2.48/1.02  --bmc1_max_bound_default                -1
% 2.48/1.02  --bmc1_symbol_reachability              true
% 2.48/1.02  --bmc1_property_lemmas                  false
% 2.48/1.02  --bmc1_k_induction                      false
% 2.48/1.02  --bmc1_non_equiv_states                 false
% 2.48/1.02  --bmc1_deadlock                         false
% 2.48/1.02  --bmc1_ucm                              false
% 2.48/1.02  --bmc1_add_unsat_core                   none
% 2.48/1.02  --bmc1_unsat_core_children              false
% 2.48/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.48/1.02  --bmc1_out_stat                         full
% 2.48/1.02  --bmc1_ground_init                      false
% 2.48/1.02  --bmc1_pre_inst_next_state              false
% 2.48/1.02  --bmc1_pre_inst_state                   false
% 2.48/1.02  --bmc1_pre_inst_reach_state             false
% 2.48/1.02  --bmc1_out_unsat_core                   false
% 2.48/1.02  --bmc1_aig_witness_out                  false
% 2.48/1.02  --bmc1_verbose                          false
% 2.48/1.02  --bmc1_dump_clauses_tptp                false
% 2.48/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.48/1.02  --bmc1_dump_file                        -
% 2.48/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.48/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.48/1.02  --bmc1_ucm_extend_mode                  1
% 2.48/1.02  --bmc1_ucm_init_mode                    2
% 2.48/1.02  --bmc1_ucm_cone_mode                    none
% 2.48/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.48/1.02  --bmc1_ucm_relax_model                  4
% 2.48/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.48/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.48/1.02  --bmc1_ucm_layered_model                none
% 2.48/1.02  --bmc1_ucm_max_lemma_size               10
% 2.48/1.02  
% 2.48/1.02  ------ AIG Options
% 2.48/1.02  
% 2.48/1.02  --aig_mode                              false
% 2.48/1.02  
% 2.48/1.02  ------ Instantiation Options
% 2.48/1.02  
% 2.48/1.02  --instantiation_flag                    true
% 2.48/1.02  --inst_sos_flag                         true
% 2.48/1.02  --inst_sos_phase                        true
% 2.48/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.48/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.48/1.02  --inst_lit_sel_side                     num_symb
% 2.48/1.02  --inst_solver_per_active                1400
% 2.48/1.02  --inst_solver_calls_frac                1.
% 2.48/1.02  --inst_passive_queue_type               priority_queues
% 2.48/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.48/1.02  --inst_passive_queues_freq              [25;2]
% 2.48/1.02  --inst_dismatching                      true
% 2.48/1.02  --inst_eager_unprocessed_to_passive     true
% 2.48/1.02  --inst_prop_sim_given                   true
% 2.48/1.02  --inst_prop_sim_new                     false
% 2.48/1.02  --inst_subs_new                         false
% 2.48/1.02  --inst_eq_res_simp                      false
% 2.48/1.02  --inst_subs_given                       false
% 2.48/1.02  --inst_orphan_elimination               true
% 2.48/1.02  --inst_learning_loop_flag               true
% 2.48/1.02  --inst_learning_start                   3000
% 2.48/1.02  --inst_learning_factor                  2
% 2.48/1.02  --inst_start_prop_sim_after_learn       3
% 2.48/1.02  --inst_sel_renew                        solver
% 2.48/1.02  --inst_lit_activity_flag                true
% 2.48/1.02  --inst_restr_to_given                   false
% 2.48/1.02  --inst_activity_threshold               500
% 2.48/1.02  --inst_out_proof                        true
% 2.48/1.02  
% 2.48/1.02  ------ Resolution Options
% 2.48/1.02  
% 2.48/1.02  --resolution_flag                       true
% 2.48/1.02  --res_lit_sel                           adaptive
% 2.48/1.02  --res_lit_sel_side                      none
% 2.48/1.02  --res_ordering                          kbo
% 2.48/1.02  --res_to_prop_solver                    active
% 2.48/1.02  --res_prop_simpl_new                    false
% 2.48/1.02  --res_prop_simpl_given                  true
% 2.48/1.02  --res_passive_queue_type                priority_queues
% 2.48/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.48/1.02  --res_passive_queues_freq               [15;5]
% 2.48/1.02  --res_forward_subs                      full
% 2.48/1.02  --res_backward_subs                     full
% 2.48/1.02  --res_forward_subs_resolution           true
% 2.48/1.02  --res_backward_subs_resolution          true
% 2.48/1.02  --res_orphan_elimination                true
% 2.48/1.02  --res_time_limit                        2.
% 2.48/1.02  --res_out_proof                         true
% 2.48/1.02  
% 2.48/1.02  ------ Superposition Options
% 2.48/1.02  
% 2.48/1.02  --superposition_flag                    true
% 2.48/1.02  --sup_passive_queue_type                priority_queues
% 2.48/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.48/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.48/1.02  --demod_completeness_check              fast
% 2.48/1.02  --demod_use_ground                      true
% 2.48/1.02  --sup_to_prop_solver                    passive
% 2.48/1.02  --sup_prop_simpl_new                    true
% 2.48/1.02  --sup_prop_simpl_given                  true
% 2.48/1.02  --sup_fun_splitting                     true
% 2.48/1.02  --sup_smt_interval                      50000
% 2.48/1.02  
% 2.48/1.02  ------ Superposition Simplification Setup
% 2.48/1.02  
% 2.48/1.02  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 2.48/1.02  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 2.48/1.02  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 2.48/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 2.48/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.48/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 2.48/1.02  --sup_full_bw                           [BwDemod;BwSubsumption]
% 2.48/1.02  --sup_immed_triv                        [TrivRules]
% 2.48/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.48/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 2.48/1.02  --sup_immed_bw_main                     []
% 2.48/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 2.48/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.48/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 2.48/1.02  --sup_input_bw                          []
% 2.48/1.02  
% 2.48/1.02  ------ Combination Options
% 2.48/1.02  
% 2.48/1.02  --comb_res_mult                         3
% 2.48/1.02  --comb_sup_mult                         2
% 2.48/1.02  --comb_inst_mult                        10
% 2.48/1.02  
% 2.48/1.02  ------ Debug Options
% 2.48/1.02  
% 2.48/1.02  --dbg_backtrace                         false
% 2.48/1.02  --dbg_dump_prop_clauses                 false
% 2.48/1.02  --dbg_dump_prop_clauses_file            -
% 2.48/1.02  --dbg_out_stat                          false
% 2.48/1.02  ------ Parsing...
% 2.48/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.48/1.02  
% 2.48/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.48/1.02  
% 2.48/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.48/1.02  
% 2.48/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.48/1.02  ------ Proving...
% 2.48/1.02  ------ Problem Properties 
% 2.48/1.02  
% 2.48/1.02  
% 2.48/1.02  clauses                                 33
% 2.48/1.02  conjectures                             11
% 2.48/1.02  EPR                                     7
% 2.48/1.02  Horn                                    29
% 2.48/1.02  unary                                   16
% 2.48/1.02  binary                                  3
% 2.48/1.02  lits                                    121
% 2.48/1.02  lits eq                                 30
% 2.48/1.02  fd_pure                                 0
% 2.48/1.02  fd_pseudo                               0
% 2.48/1.02  fd_cond                                 4
% 2.48/1.02  fd_pseudo_cond                          1
% 2.48/1.02  AC symbols                              0
% 2.48/1.02  
% 2.48/1.02  ------ Schedule dynamic 5 is on 
% 2.48/1.02  
% 2.48/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.48/1.02  
% 2.48/1.02  
% 2.48/1.02  ------ 
% 2.48/1.02  Current options:
% 2.48/1.02  ------ 
% 2.48/1.02  
% 2.48/1.02  ------ Input Options
% 2.48/1.02  
% 2.48/1.02  --out_options                           all
% 2.48/1.02  --tptp_safe_out                         true
% 2.48/1.02  --problem_path                          ""
% 2.48/1.02  --include_path                          ""
% 2.48/1.02  --clausifier                            res/vclausify_rel
% 2.48/1.02  --clausifier_options                    ""
% 2.48/1.02  --stdin                                 false
% 2.48/1.02  --stats_out                             all
% 2.48/1.02  
% 2.48/1.02  ------ General Options
% 2.48/1.02  
% 2.48/1.02  --fof                                   false
% 2.48/1.02  --time_out_real                         305.
% 2.48/1.02  --time_out_virtual                      -1.
% 2.48/1.02  --symbol_type_check                     false
% 2.48/1.02  --clausify_out                          false
% 2.48/1.02  --sig_cnt_out                           false
% 2.48/1.02  --trig_cnt_out                          false
% 2.48/1.02  --trig_cnt_out_tolerance                1.
% 2.48/1.02  --trig_cnt_out_sk_spl                   false
% 2.48/1.02  --abstr_cl_out                          false
% 2.48/1.02  
% 2.48/1.02  ------ Global Options
% 2.48/1.02  
% 2.48/1.02  --schedule                              default
% 2.48/1.02  --add_important_lit                     false
% 2.48/1.02  --prop_solver_per_cl                    1000
% 2.48/1.02  --min_unsat_core                        false
% 2.48/1.02  --soft_assumptions                      false
% 2.48/1.02  --soft_lemma_size                       3
% 2.48/1.02  --prop_impl_unit_size                   0
% 2.48/1.02  --prop_impl_unit                        []
% 2.48/1.02  --share_sel_clauses                     true
% 2.48/1.02  --reset_solvers                         false
% 2.48/1.02  --bc_imp_inh                            [conj_cone]
% 2.48/1.02  --conj_cone_tolerance                   3.
% 2.48/1.02  --extra_neg_conj                        none
% 2.48/1.02  --large_theory_mode                     true
% 2.48/1.02  --prolific_symb_bound                   200
% 2.48/1.02  --lt_threshold                          2000
% 2.48/1.02  --clause_weak_htbl                      true
% 2.48/1.02  --gc_record_bc_elim                     false
% 2.48/1.02  
% 2.48/1.02  ------ Preprocessing Options
% 2.48/1.02  
% 2.48/1.02  --preprocessing_flag                    true
% 2.48/1.02  --time_out_prep_mult                    0.1
% 2.48/1.02  --splitting_mode                        input
% 2.48/1.02  --splitting_grd                         true
% 2.48/1.02  --splitting_cvd                         false
% 2.48/1.02  --splitting_cvd_svl                     false
% 2.48/1.02  --splitting_nvd                         32
% 2.48/1.02  --sub_typing                            true
% 2.48/1.02  --prep_gs_sim                           true
% 2.48/1.02  --prep_unflatten                        true
% 2.48/1.02  --prep_res_sim                          true
% 2.48/1.02  --prep_upred                            true
% 2.48/1.02  --prep_sem_filter                       exhaustive
% 2.48/1.02  --prep_sem_filter_out                   false
% 2.48/1.02  --pred_elim                             true
% 2.48/1.02  --res_sim_input                         true
% 2.48/1.02  --eq_ax_congr_red                       true
% 2.48/1.02  --pure_diseq_elim                       true
% 2.48/1.02  --brand_transform                       false
% 2.48/1.02  --non_eq_to_eq                          false
% 2.48/1.02  --prep_def_merge                        true
% 2.48/1.02  --prep_def_merge_prop_impl              false
% 2.48/1.02  --prep_def_merge_mbd                    true
% 2.48/1.02  --prep_def_merge_tr_red                 false
% 2.48/1.02  --prep_def_merge_tr_cl                  false
% 2.48/1.02  --smt_preprocessing                     true
% 2.48/1.02  --smt_ac_axioms                         fast
% 2.48/1.02  --preprocessed_out                      false
% 2.48/1.02  --preprocessed_stats                    false
% 2.48/1.02  
% 2.48/1.02  ------ Abstraction refinement Options
% 2.48/1.02  
% 2.48/1.02  --abstr_ref                             []
% 2.48/1.02  --abstr_ref_prep                        false
% 2.48/1.02  --abstr_ref_until_sat                   false
% 2.48/1.02  --abstr_ref_sig_restrict                funpre
% 2.48/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.48/1.02  --abstr_ref_under                       []
% 2.48/1.02  
% 2.48/1.02  ------ SAT Options
% 2.48/1.02  
% 2.48/1.02  --sat_mode                              false
% 2.48/1.02  --sat_fm_restart_options                ""
% 2.48/1.02  --sat_gr_def                            false
% 2.48/1.02  --sat_epr_types                         true
% 2.48/1.02  --sat_non_cyclic_types                  false
% 2.48/1.02  --sat_finite_models                     false
% 2.48/1.02  --sat_fm_lemmas                         false
% 2.48/1.02  --sat_fm_prep                           false
% 2.48/1.02  --sat_fm_uc_incr                        true
% 2.48/1.02  --sat_out_model                         small
% 2.48/1.02  --sat_out_clauses                       false
% 2.48/1.02  
% 2.48/1.02  ------ QBF Options
% 2.48/1.02  
% 2.48/1.02  --qbf_mode                              false
% 2.48/1.02  --qbf_elim_univ                         false
% 2.48/1.02  --qbf_dom_inst                          none
% 2.48/1.02  --qbf_dom_pre_inst                      false
% 2.48/1.02  --qbf_sk_in                             false
% 2.48/1.02  --qbf_pred_elim                         true
% 2.48/1.02  --qbf_split                             512
% 2.48/1.02  
% 2.48/1.02  ------ BMC1 Options
% 2.48/1.02  
% 2.48/1.02  --bmc1_incremental                      false
% 2.48/1.02  --bmc1_axioms                           reachable_all
% 2.48/1.02  --bmc1_min_bound                        0
% 2.48/1.02  --bmc1_max_bound                        -1
% 2.48/1.02  --bmc1_max_bound_default                -1
% 2.48/1.02  --bmc1_symbol_reachability              true
% 2.48/1.02  --bmc1_property_lemmas                  false
% 2.48/1.02  --bmc1_k_induction                      false
% 2.48/1.02  --bmc1_non_equiv_states                 false
% 2.48/1.02  --bmc1_deadlock                         false
% 2.48/1.02  --bmc1_ucm                              false
% 2.48/1.02  --bmc1_add_unsat_core                   none
% 2.48/1.02  --bmc1_unsat_core_children              false
% 2.48/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.48/1.02  --bmc1_out_stat                         full
% 2.48/1.02  --bmc1_ground_init                      false
% 2.48/1.02  --bmc1_pre_inst_next_state              false
% 2.48/1.02  --bmc1_pre_inst_state                   false
% 2.48/1.02  --bmc1_pre_inst_reach_state             false
% 2.48/1.02  --bmc1_out_unsat_core                   false
% 2.48/1.02  --bmc1_aig_witness_out                  false
% 2.48/1.02  --bmc1_verbose                          false
% 2.48/1.02  --bmc1_dump_clauses_tptp                false
% 2.48/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.48/1.02  --bmc1_dump_file                        -
% 2.48/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.48/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.48/1.02  --bmc1_ucm_extend_mode                  1
% 2.48/1.02  --bmc1_ucm_init_mode                    2
% 2.48/1.02  --bmc1_ucm_cone_mode                    none
% 2.48/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.48/1.02  --bmc1_ucm_relax_model                  4
% 2.48/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.48/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.48/1.02  --bmc1_ucm_layered_model                none
% 2.48/1.02  --bmc1_ucm_max_lemma_size               10
% 2.48/1.02  
% 2.48/1.02  ------ AIG Options
% 2.48/1.02  
% 2.48/1.02  --aig_mode                              false
% 2.48/1.02  
% 2.48/1.02  ------ Instantiation Options
% 2.48/1.02  
% 2.48/1.02  --instantiation_flag                    true
% 2.48/1.02  --inst_sos_flag                         true
% 2.48/1.02  --inst_sos_phase                        true
% 2.48/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.48/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.48/1.02  --inst_lit_sel_side                     none
% 2.48/1.02  --inst_solver_per_active                1400
% 2.48/1.02  --inst_solver_calls_frac                1.
% 2.48/1.02  --inst_passive_queue_type               priority_queues
% 2.48/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.48/1.02  --inst_passive_queues_freq              [25;2]
% 2.48/1.02  --inst_dismatching                      true
% 2.48/1.02  --inst_eager_unprocessed_to_passive     true
% 2.48/1.02  --inst_prop_sim_given                   true
% 2.48/1.02  --inst_prop_sim_new                     false
% 2.48/1.02  --inst_subs_new                         false
% 2.48/1.02  --inst_eq_res_simp                      false
% 2.48/1.02  --inst_subs_given                       false
% 2.48/1.02  --inst_orphan_elimination               true
% 2.48/1.02  --inst_learning_loop_flag               true
% 2.48/1.02  --inst_learning_start                   3000
% 2.48/1.02  --inst_learning_factor                  2
% 2.48/1.02  --inst_start_prop_sim_after_learn       3
% 2.48/1.02  --inst_sel_renew                        solver
% 2.48/1.02  --inst_lit_activity_flag                true
% 2.48/1.02  --inst_restr_to_given                   false
% 2.48/1.02  --inst_activity_threshold               500
% 2.48/1.02  --inst_out_proof                        true
% 2.48/1.02  
% 2.48/1.02  ------ Resolution Options
% 2.48/1.02  
% 2.48/1.02  --resolution_flag                       false
% 2.48/1.02  --res_lit_sel                           adaptive
% 2.48/1.02  --res_lit_sel_side                      none
% 2.48/1.02  --res_ordering                          kbo
% 2.48/1.02  --res_to_prop_solver                    active
% 2.48/1.02  --res_prop_simpl_new                    false
% 2.48/1.02  --res_prop_simpl_given                  true
% 2.48/1.02  --res_passive_queue_type                priority_queues
% 2.48/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.48/1.02  --res_passive_queues_freq               [15;5]
% 2.48/1.02  --res_forward_subs                      full
% 2.48/1.02  --res_backward_subs                     full
% 2.48/1.02  --res_forward_subs_resolution           true
% 2.48/1.02  --res_backward_subs_resolution          true
% 2.48/1.02  --res_orphan_elimination                true
% 2.48/1.02  --res_time_limit                        2.
% 2.48/1.02  --res_out_proof                         true
% 2.48/1.02  
% 2.48/1.02  ------ Superposition Options
% 2.48/1.02  
% 2.48/1.02  --superposition_flag                    true
% 2.48/1.02  --sup_passive_queue_type                priority_queues
% 2.48/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.48/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.48/1.02  --demod_completeness_check              fast
% 2.48/1.02  --demod_use_ground                      true
% 2.48/1.02  --sup_to_prop_solver                    passive
% 2.48/1.02  --sup_prop_simpl_new                    true
% 2.48/1.02  --sup_prop_simpl_given                  true
% 2.48/1.02  --sup_fun_splitting                     true
% 2.48/1.02  --sup_smt_interval                      50000
% 2.48/1.02  
% 2.48/1.02  ------ Superposition Simplification Setup
% 2.48/1.02  
% 2.48/1.02  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 2.48/1.02  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 2.48/1.02  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 2.48/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 2.48/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.48/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 2.48/1.02  --sup_full_bw                           [BwDemod;BwSubsumption]
% 2.48/1.02  --sup_immed_triv                        [TrivRules]
% 2.48/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.48/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 2.48/1.02  --sup_immed_bw_main                     []
% 2.48/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 2.48/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.48/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 2.48/1.02  --sup_input_bw                          []
% 2.48/1.02  
% 2.48/1.02  ------ Combination Options
% 2.48/1.02  
% 2.48/1.02  --comb_res_mult                         3
% 2.48/1.02  --comb_sup_mult                         2
% 2.48/1.02  --comb_inst_mult                        10
% 2.48/1.02  
% 2.48/1.02  ------ Debug Options
% 2.48/1.02  
% 2.48/1.02  --dbg_backtrace                         false
% 2.48/1.02  --dbg_dump_prop_clauses                 false
% 2.48/1.02  --dbg_dump_prop_clauses_file            -
% 2.48/1.02  --dbg_out_stat                          false
% 2.48/1.02  
% 2.48/1.02  
% 2.48/1.02  
% 2.48/1.02  
% 2.48/1.02  ------ Proving...
% 2.48/1.02  
% 2.48/1.02  
% 2.48/1.02  % SZS status Theorem for theBenchmark.p
% 2.48/1.02  
% 2.48/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 2.48/1.02  
% 2.48/1.02  fof(f12,axiom,(
% 2.48/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 2.48/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.48/1.02  
% 2.48/1.02  fof(f29,plain,(
% 2.48/1.02    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.48/1.02    inference(ennf_transformation,[],[f12])).
% 2.48/1.02  
% 2.48/1.02  fof(f30,plain,(
% 2.48/1.02    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.48/1.02    inference(flattening,[],[f29])).
% 2.48/1.02  
% 2.48/1.02  fof(f57,plain,(
% 2.48/1.02    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.48/1.02    inference(cnf_transformation,[],[f30])).
% 2.48/1.02  
% 2.48/1.02  fof(f15,conjecture,(
% 2.48/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.48/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.48/1.02  
% 2.48/1.02  fof(f16,negated_conjecture,(
% 2.48/1.02    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.48/1.02    inference(negated_conjecture,[],[f15])).
% 2.48/1.02  
% 2.48/1.02  fof(f35,plain,(
% 2.48/1.02    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.48/1.02    inference(ennf_transformation,[],[f16])).
% 2.48/1.02  
% 2.48/1.02  fof(f36,plain,(
% 2.48/1.02    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.48/1.02    inference(flattening,[],[f35])).
% 2.48/1.02  
% 2.48/1.02  fof(f39,plain,(
% 2.48/1.02    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 2.48/1.02    introduced(choice_axiom,[])).
% 2.48/1.02  
% 2.48/1.02  fof(f38,plain,(
% 2.48/1.02    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 2.48/1.02    introduced(choice_axiom,[])).
% 2.48/1.02  
% 2.48/1.02  fof(f40,plain,(
% 2.48/1.02    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 2.48/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f36,f39,f38])).
% 2.48/1.02  
% 2.48/1.02  fof(f71,plain,(
% 2.48/1.02    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.48/1.02    inference(cnf_transformation,[],[f40])).
% 2.48/1.02  
% 2.48/1.02  fof(f64,plain,(
% 2.48/1.02    v1_funct_1(sK2)),
% 2.48/1.02    inference(cnf_transformation,[],[f40])).
% 2.48/1.02  
% 2.48/1.02  fof(f65,plain,(
% 2.48/1.02    v1_funct_2(sK2,sK0,sK1)),
% 2.48/1.02    inference(cnf_transformation,[],[f40])).
% 2.48/1.02  
% 2.48/1.02  fof(f66,plain,(
% 2.48/1.02    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.48/1.02    inference(cnf_transformation,[],[f40])).
% 2.48/1.02  
% 2.48/1.02  fof(f67,plain,(
% 2.48/1.02    v1_funct_1(sK3)),
% 2.48/1.02    inference(cnf_transformation,[],[f40])).
% 2.48/1.02  
% 2.48/1.02  fof(f68,plain,(
% 2.48/1.02    v1_funct_2(sK3,sK1,sK0)),
% 2.48/1.02    inference(cnf_transformation,[],[f40])).
% 2.48/1.02  
% 2.48/1.02  fof(f69,plain,(
% 2.48/1.02    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.48/1.02    inference(cnf_transformation,[],[f40])).
% 2.48/1.02  
% 2.48/1.02  fof(f14,axiom,(
% 2.48/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 2.48/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.48/1.02  
% 2.48/1.02  fof(f33,plain,(
% 2.48/1.02    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.48/1.02    inference(ennf_transformation,[],[f14])).
% 2.48/1.02  
% 2.48/1.02  fof(f34,plain,(
% 2.48/1.02    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.48/1.02    inference(flattening,[],[f33])).
% 2.48/1.02  
% 2.48/1.02  fof(f62,plain,(
% 2.48/1.02    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.48/1.02    inference(cnf_transformation,[],[f34])).
% 2.48/1.02  
% 2.48/1.02  fof(f73,plain,(
% 2.48/1.02    k1_xboole_0 != sK0),
% 2.48/1.02    inference(cnf_transformation,[],[f40])).
% 2.48/1.02  
% 2.48/1.02  fof(f7,axiom,(
% 2.48/1.02    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.48/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.48/1.02  
% 2.48/1.02  fof(f23,plain,(
% 2.48/1.02    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.48/1.02    inference(ennf_transformation,[],[f7])).
% 2.48/1.02  
% 2.48/1.02  fof(f24,plain,(
% 2.48/1.02    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.48/1.02    inference(flattening,[],[f23])).
% 2.48/1.02  
% 2.48/1.02  fof(f37,plain,(
% 2.48/1.02    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.48/1.02    inference(nnf_transformation,[],[f24])).
% 2.48/1.02  
% 2.48/1.02  fof(f50,plain,(
% 2.48/1.02    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.48/1.02    inference(cnf_transformation,[],[f37])).
% 2.48/1.02  
% 2.48/1.02  fof(f8,axiom,(
% 2.48/1.02    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 2.48/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.48/1.02  
% 2.48/1.02  fof(f52,plain,(
% 2.48/1.02    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.48/1.02    inference(cnf_transformation,[],[f8])).
% 2.48/1.02  
% 2.48/1.02  fof(f11,axiom,(
% 2.48/1.02    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.48/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.48/1.02  
% 2.48/1.02  fof(f56,plain,(
% 2.48/1.02    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.48/1.02    inference(cnf_transformation,[],[f11])).
% 2.48/1.02  
% 2.48/1.02  fof(f83,plain,(
% 2.48/1.02    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.48/1.02    inference(definition_unfolding,[],[f52,f56])).
% 2.48/1.02  
% 2.48/1.02  fof(f9,axiom,(
% 2.48/1.02    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 2.48/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.48/1.02  
% 2.48/1.02  fof(f25,plain,(
% 2.48/1.02    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.48/1.02    inference(ennf_transformation,[],[f9])).
% 2.48/1.02  
% 2.48/1.02  fof(f26,plain,(
% 2.48/1.02    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.48/1.02    inference(flattening,[],[f25])).
% 2.48/1.02  
% 2.48/1.02  fof(f54,plain,(
% 2.48/1.02    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.48/1.02    inference(cnf_transformation,[],[f26])).
% 2.48/1.02  
% 2.48/1.02  fof(f70,plain,(
% 2.48/1.02    k2_relset_1(sK0,sK1,sK2) = sK1),
% 2.48/1.02    inference(cnf_transformation,[],[f40])).
% 2.48/1.02  
% 2.48/1.02  fof(f13,axiom,(
% 2.48/1.02    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 2.48/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.48/1.02  
% 2.48/1.02  fof(f31,plain,(
% 2.48/1.02    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.48/1.02    inference(ennf_transformation,[],[f13])).
% 2.48/1.02  
% 2.48/1.02  fof(f32,plain,(
% 2.48/1.02    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.48/1.02    inference(flattening,[],[f31])).
% 2.48/1.02  
% 2.48/1.02  fof(f60,plain,(
% 2.48/1.02    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X4) | k1_xboole_0 = X2 | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.48/1.02    inference(cnf_transformation,[],[f32])).
% 2.48/1.02  
% 2.48/1.02  fof(f2,axiom,(
% 2.48/1.02    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.48/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.48/1.02  
% 2.48/1.02  fof(f44,plain,(
% 2.48/1.02    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 2.48/1.02    inference(cnf_transformation,[],[f2])).
% 2.48/1.02  
% 2.48/1.02  fof(f78,plain,(
% 2.48/1.02    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 2.48/1.02    inference(definition_unfolding,[],[f44,f56])).
% 2.48/1.02  
% 2.48/1.02  fof(f3,axiom,(
% 2.48/1.02    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)))))),
% 2.48/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.48/1.02  
% 2.48/1.02  fof(f17,plain,(
% 2.48/1.02    ! [X0] : (((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.48/1.02    inference(ennf_transformation,[],[f3])).
% 2.48/1.02  
% 2.48/1.02  fof(f18,plain,(
% 2.48/1.02    ! [X0] : ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.48/1.02    inference(flattening,[],[f17])).
% 2.48/1.02  
% 2.48/1.02  fof(f45,plain,(
% 2.48/1.02    ( ! [X0] : (k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.48/1.02    inference(cnf_transformation,[],[f18])).
% 2.48/1.02  
% 2.48/1.02  fof(f81,plain,(
% 2.48/1.02    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.48/1.02    inference(definition_unfolding,[],[f45,f56])).
% 2.48/1.02  
% 2.48/1.02  fof(f5,axiom,(
% 2.48/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.48/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.48/1.02  
% 2.48/1.02  fof(f21,plain,(
% 2.48/1.02    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.48/1.02    inference(ennf_transformation,[],[f5])).
% 2.48/1.02  
% 2.48/1.02  fof(f48,plain,(
% 2.48/1.02    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.48/1.02    inference(cnf_transformation,[],[f21])).
% 2.48/1.02  
% 2.48/1.02  fof(f1,axiom,(
% 2.48/1.02    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.48/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.48/1.02  
% 2.48/1.02  fof(f42,plain,(
% 2.48/1.02    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 2.48/1.02    inference(cnf_transformation,[],[f1])).
% 2.48/1.02  
% 2.48/1.02  fof(f76,plain,(
% 2.48/1.02    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 2.48/1.02    inference(definition_unfolding,[],[f42,f56])).
% 2.48/1.02  
% 2.48/1.02  fof(f10,axiom,(
% 2.48/1.02    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 2.48/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.48/1.02  
% 2.48/1.02  fof(f27,plain,(
% 2.48/1.02    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.48/1.02    inference(ennf_transformation,[],[f10])).
% 2.48/1.02  
% 2.48/1.02  fof(f28,plain,(
% 2.48/1.02    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.48/1.02    inference(flattening,[],[f27])).
% 2.48/1.02  
% 2.48/1.02  fof(f55,plain,(
% 2.48/1.02    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.48/1.02    inference(cnf_transformation,[],[f28])).
% 2.48/1.02  
% 2.48/1.02  fof(f4,axiom,(
% 2.48/1.02    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1) & k1_relat_1(X1) = k2_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 2.48/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.48/1.02  
% 2.48/1.02  fof(f19,plain,(
% 2.48/1.02    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | k1_relat_1(X1) != k2_relat_1(X0) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.48/1.02    inference(ennf_transformation,[],[f4])).
% 2.48/1.02  
% 2.48/1.02  fof(f20,plain,(
% 2.48/1.02    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | k1_relat_1(X1) != k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.48/1.02    inference(flattening,[],[f19])).
% 2.48/1.02  
% 2.48/1.02  fof(f47,plain,(
% 2.48/1.02    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | k1_relat_1(X1) != k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.48/1.02    inference(cnf_transformation,[],[f20])).
% 2.48/1.02  
% 2.48/1.02  fof(f82,plain,(
% 2.48/1.02    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0)) | k1_relat_1(X1) != k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.48/1.02    inference(definition_unfolding,[],[f47,f56])).
% 2.48/1.02  
% 2.48/1.02  fof(f6,axiom,(
% 2.48/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.48/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.48/1.02  
% 2.48/1.02  fof(f22,plain,(
% 2.48/1.02    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.48/1.02    inference(ennf_transformation,[],[f6])).
% 2.48/1.02  
% 2.48/1.02  fof(f49,plain,(
% 2.48/1.02    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.48/1.02    inference(cnf_transformation,[],[f22])).
% 2.48/1.02  
% 2.48/1.02  fof(f72,plain,(
% 2.48/1.02    v2_funct_1(sK2)),
% 2.48/1.02    inference(cnf_transformation,[],[f40])).
% 2.48/1.02  
% 2.48/1.02  fof(f74,plain,(
% 2.48/1.02    k1_xboole_0 != sK1),
% 2.48/1.02    inference(cnf_transformation,[],[f40])).
% 2.48/1.02  
% 2.48/1.02  fof(f75,plain,(
% 2.48/1.02    k2_funct_1(sK2) != sK3),
% 2.48/1.02    inference(cnf_transformation,[],[f40])).
% 2.48/1.02  
% 2.48/1.02  cnf(c_15,plain,
% 2.48/1.02      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 2.48/1.02      | ~ v1_funct_2(X2,X0,X1)
% 2.48/1.02      | ~ v1_funct_2(X3,X1,X0)
% 2.48/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.48/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.48/1.02      | ~ v1_funct_1(X2)
% 2.48/1.02      | ~ v1_funct_1(X3)
% 2.48/1.02      | k2_relset_1(X1,X0,X3) = X0 ),
% 2.48/1.02      inference(cnf_transformation,[],[f57]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_26,negated_conjecture,
% 2.48/1.02      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 2.48/1.02      inference(cnf_transformation,[],[f71]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_367,plain,
% 2.48/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 2.48/1.02      | ~ v1_funct_2(X3,X2,X1)
% 2.48/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.48/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.48/1.02      | ~ v1_funct_1(X0)
% 2.48/1.02      | ~ v1_funct_1(X3)
% 2.48/1.02      | k1_partfun1(X2,X1,X1,X2,X3,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 2.48/1.02      | k2_relset_1(X1,X2,X0) = X2
% 2.48/1.02      | k6_partfun1(X2) != k6_partfun1(sK0)
% 2.48/1.02      | sK0 != X2 ),
% 2.48/1.02      inference(resolution_lifted,[status(thm)],[c_15,c_26]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_368,plain,
% 2.48/1.02      ( ~ v1_funct_2(X0,X1,sK0)
% 2.48/1.02      | ~ v1_funct_2(X2,sK0,X1)
% 2.48/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 2.48/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 2.48/1.02      | ~ v1_funct_1(X0)
% 2.48/1.02      | ~ v1_funct_1(X2)
% 2.48/1.02      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 2.48/1.02      | k2_relset_1(X1,sK0,X0) = sK0
% 2.48/1.02      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 2.48/1.02      inference(unflattening,[status(thm)],[c_367]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_449,plain,
% 2.48/1.02      ( ~ v1_funct_2(X0,X1,sK0)
% 2.48/1.02      | ~ v1_funct_2(X2,sK0,X1)
% 2.48/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 2.48/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 2.48/1.02      | ~ v1_funct_1(X0)
% 2.48/1.02      | ~ v1_funct_1(X2)
% 2.48/1.02      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 2.48/1.02      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 2.48/1.02      inference(equality_resolution_simp,[status(thm)],[c_368]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_1066,plain,
% 2.48/1.02      ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 2.48/1.02      | k2_relset_1(X0,sK0,X2) = sK0
% 2.48/1.02      | v1_funct_2(X2,X0,sK0) != iProver_top
% 2.48/1.02      | v1_funct_2(X1,sK0,X0) != iProver_top
% 2.48/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 2.48/1.02      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 2.48/1.02      | v1_funct_1(X2) != iProver_top
% 2.48/1.02      | v1_funct_1(X1) != iProver_top ),
% 2.48/1.02      inference(predicate_to_equality,[status(thm)],[c_449]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_1596,plain,
% 2.48/1.02      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 2.48/1.02      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 2.48/1.02      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 2.48/1.02      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.48/1.02      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.48/1.02      | v1_funct_1(sK3) != iProver_top
% 2.48/1.02      | v1_funct_1(sK2) != iProver_top ),
% 2.48/1.02      inference(equality_resolution,[status(thm)],[c_1066]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_33,negated_conjecture,
% 2.48/1.02      ( v1_funct_1(sK2) ),
% 2.48/1.02      inference(cnf_transformation,[],[f64]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_34,plain,
% 2.48/1.02      ( v1_funct_1(sK2) = iProver_top ),
% 2.48/1.02      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_32,negated_conjecture,
% 2.48/1.02      ( v1_funct_2(sK2,sK0,sK1) ),
% 2.48/1.02      inference(cnf_transformation,[],[f65]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_35,plain,
% 2.48/1.02      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 2.48/1.02      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_31,negated_conjecture,
% 2.48/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.48/1.02      inference(cnf_transformation,[],[f66]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_36,plain,
% 2.48/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.48/1.02      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_30,negated_conjecture,
% 2.48/1.02      ( v1_funct_1(sK3) ),
% 2.48/1.02      inference(cnf_transformation,[],[f67]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_37,plain,
% 2.48/1.02      ( v1_funct_1(sK3) = iProver_top ),
% 2.48/1.02      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_29,negated_conjecture,
% 2.48/1.02      ( v1_funct_2(sK3,sK1,sK0) ),
% 2.48/1.02      inference(cnf_transformation,[],[f68]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_38,plain,
% 2.48/1.02      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 2.48/1.02      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_28,negated_conjecture,
% 2.48/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 2.48/1.02      inference(cnf_transformation,[],[f69]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_39,plain,
% 2.48/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 2.48/1.02      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_1765,plain,
% 2.48/1.02      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 2.48/1.02      inference(global_propositional_subsumption,
% 2.48/1.02                [status(thm)],
% 2.48/1.02                [c_1596,c_34,c_35,c_36,c_37,c_38,c_39]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_21,plain,
% 2.48/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 2.48/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.48/1.02      | ~ v1_funct_1(X0)
% 2.48/1.02      | ~ v2_funct_1(X0)
% 2.48/1.02      | k2_relset_1(X1,X2,X0) != X2
% 2.48/1.02      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 2.48/1.02      | k1_xboole_0 = X2 ),
% 2.48/1.02      inference(cnf_transformation,[],[f62]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_1076,plain,
% 2.48/1.02      ( k2_relset_1(X0,X1,X2) != X1
% 2.48/1.02      | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
% 2.48/1.02      | k1_xboole_0 = X1
% 2.48/1.02      | v1_funct_2(X2,X0,X1) != iProver_top
% 2.48/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.48/1.02      | v1_funct_1(X2) != iProver_top
% 2.48/1.02      | v2_funct_1(X2) != iProver_top ),
% 2.48/1.02      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_2685,plain,
% 2.48/1.02      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 2.48/1.02      | sK0 = k1_xboole_0
% 2.48/1.02      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 2.48/1.02      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.48/1.02      | v1_funct_1(sK3) != iProver_top
% 2.48/1.02      | v2_funct_1(sK3) != iProver_top ),
% 2.48/1.02      inference(superposition,[status(thm)],[c_1765,c_1076]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_24,negated_conjecture,
% 2.48/1.02      ( k1_xboole_0 != sK0 ),
% 2.48/1.02      inference(cnf_transformation,[],[f73]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_608,plain,( X0 = X0 ),theory(equality) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_639,plain,
% 2.48/1.02      ( k1_xboole_0 = k1_xboole_0 ),
% 2.48/1.02      inference(instantiation,[status(thm)],[c_608]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_609,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_1172,plain,
% 2.48/1.02      ( sK0 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK0 ),
% 2.48/1.02      inference(instantiation,[status(thm)],[c_609]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_1173,plain,
% 2.48/1.02      ( sK0 != k1_xboole_0
% 2.48/1.02      | k1_xboole_0 = sK0
% 2.48/1.02      | k1_xboole_0 != k1_xboole_0 ),
% 2.48/1.02      inference(instantiation,[status(thm)],[c_1172]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_2688,plain,
% 2.48/1.02      ( ~ v1_funct_2(sK3,sK1,sK0)
% 2.48/1.02      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.48/1.02      | ~ v1_funct_1(sK3)
% 2.48/1.02      | ~ v2_funct_1(sK3)
% 2.48/1.02      | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 2.48/1.02      | sK0 = k1_xboole_0 ),
% 2.48/1.02      inference(predicate_to_equality_rev,[status(thm)],[c_2685]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_10,plain,
% 2.48/1.02      ( ~ r2_relset_1(X0,X1,X2,X3)
% 2.48/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.48/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.48/1.02      | X3 = X2 ),
% 2.48/1.02      inference(cnf_transformation,[],[f50]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_354,plain,
% 2.48/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.48/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.48/1.02      | X3 = X0
% 2.48/1.02      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 2.48/1.02      | k6_partfun1(sK0) != X3
% 2.48/1.02      | sK0 != X2
% 2.48/1.02      | sK0 != X1 ),
% 2.48/1.02      inference(resolution_lifted,[status(thm)],[c_10,c_26]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_355,plain,
% 2.48/1.02      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.48/1.02      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.48/1.02      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 2.48/1.02      inference(unflattening,[status(thm)],[c_354]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_11,plain,
% 2.48/1.02      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 2.48/1.02      inference(cnf_transformation,[],[f83]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_363,plain,
% 2.48/1.02      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.48/1.02      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 2.48/1.02      inference(forward_subsumption_resolution,
% 2.48/1.02                [status(thm)],
% 2.48/1.02                [c_355,c_11]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_1067,plain,
% 2.48/1.02      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 2.48/1.02      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 2.48/1.02      inference(predicate_to_equality,[status(thm)],[c_363]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_12,plain,
% 2.48/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.48/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 2.48/1.02      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 2.48/1.02      | ~ v1_funct_1(X0)
% 2.48/1.02      | ~ v1_funct_1(X3) ),
% 2.48/1.02      inference(cnf_transformation,[],[f54]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_1174,plain,
% 2.48/1.02      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.48/1.02      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.48/1.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.48/1.02      | ~ v1_funct_1(sK3)
% 2.48/1.02      | ~ v1_funct_1(sK2) ),
% 2.48/1.02      inference(instantiation,[status(thm)],[c_12]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_1758,plain,
% 2.48/1.02      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 2.48/1.02      inference(global_propositional_subsumption,
% 2.48/1.02                [status(thm)],
% 2.48/1.02                [c_1067,c_33,c_31,c_30,c_28,c_363,c_1174]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_27,negated_conjecture,
% 2.48/1.02      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 2.48/1.02      inference(cnf_transformation,[],[f70]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_17,plain,
% 2.48/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 2.48/1.02      | ~ v1_funct_2(X3,X4,X1)
% 2.48/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 2.48/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.48/1.02      | ~ v1_funct_1(X0)
% 2.48/1.02      | ~ v1_funct_1(X3)
% 2.48/1.02      | v2_funct_1(X0)
% 2.48/1.02      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 2.48/1.02      | k2_relset_1(X4,X1,X3) != X1
% 2.48/1.02      | k1_xboole_0 = X2 ),
% 2.48/1.02      inference(cnf_transformation,[],[f60]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_1080,plain,
% 2.48/1.02      ( k2_relset_1(X0,X1,X2) != X1
% 2.48/1.02      | k1_xboole_0 = X3
% 2.48/1.02      | v1_funct_2(X4,X1,X3) != iProver_top
% 2.48/1.02      | v1_funct_2(X2,X0,X1) != iProver_top
% 2.48/1.02      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
% 2.48/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.48/1.02      | v1_funct_1(X4) != iProver_top
% 2.48/1.02      | v1_funct_1(X2) != iProver_top
% 2.48/1.02      | v2_funct_1(X4) = iProver_top
% 2.48/1.02      | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top ),
% 2.48/1.02      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_4709,plain,
% 2.48/1.02      ( k1_xboole_0 = X0
% 2.48/1.02      | v1_funct_2(X1,sK1,X0) != iProver_top
% 2.48/1.02      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 2.48/1.02      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 2.48/1.02      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.48/1.02      | v1_funct_1(X1) != iProver_top
% 2.48/1.02      | v1_funct_1(sK2) != iProver_top
% 2.48/1.02      | v2_funct_1(X1) = iProver_top
% 2.48/1.02      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
% 2.48/1.02      inference(superposition,[status(thm)],[c_27,c_1080]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_4716,plain,
% 2.48/1.02      ( v1_funct_1(X1) != iProver_top
% 2.48/1.02      | v1_funct_2(X1,sK1,X0) != iProver_top
% 2.48/1.02      | k1_xboole_0 = X0
% 2.48/1.02      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 2.48/1.02      | v2_funct_1(X1) = iProver_top
% 2.48/1.02      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
% 2.48/1.02      inference(global_propositional_subsumption,
% 2.48/1.02                [status(thm)],
% 2.48/1.02                [c_4709,c_34,c_35,c_36]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_4717,plain,
% 2.48/1.02      ( k1_xboole_0 = X0
% 2.48/1.02      | v1_funct_2(X1,sK1,X0) != iProver_top
% 2.48/1.02      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 2.48/1.02      | v1_funct_1(X1) != iProver_top
% 2.48/1.02      | v2_funct_1(X1) = iProver_top
% 2.48/1.02      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
% 2.48/1.02      inference(renaming,[status(thm)],[c_4716]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_4720,plain,
% 2.48/1.02      ( sK0 = k1_xboole_0
% 2.48/1.02      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 2.48/1.02      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.48/1.02      | v1_funct_1(sK3) != iProver_top
% 2.48/1.02      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 2.48/1.02      | v2_funct_1(sK3) = iProver_top ),
% 2.48/1.02      inference(superposition,[status(thm)],[c_1758,c_4717]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_4721,plain,
% 2.48/1.02      ( ~ v1_funct_2(sK3,sK1,sK0)
% 2.48/1.02      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.48/1.02      | ~ v1_funct_1(sK3)
% 2.48/1.02      | ~ v2_funct_1(k6_partfun1(sK0))
% 2.48/1.02      | v2_funct_1(sK3)
% 2.48/1.02      | sK0 = k1_xboole_0 ),
% 2.48/1.02      inference(predicate_to_equality_rev,[status(thm)],[c_4720]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_2,plain,
% 2.48/1.02      ( v2_funct_1(k6_partfun1(X0)) ),
% 2.48/1.02      inference(cnf_transformation,[],[f78]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_4741,plain,
% 2.48/1.02      ( v2_funct_1(k6_partfun1(sK0)) ),
% 2.48/1.02      inference(instantiation,[status(thm)],[c_2]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_5216,plain,
% 2.48/1.02      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
% 2.48/1.02      inference(global_propositional_subsumption,
% 2.48/1.02                [status(thm)],
% 2.48/1.02                [c_2685,c_30,c_29,c_28,c_24,c_639,c_1173,c_2688,c_4721,
% 2.48/1.02                 c_4741]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_4742,plain,
% 2.48/1.02      ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
% 2.48/1.02      inference(predicate_to_equality,[status(thm)],[c_4741]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_4964,plain,
% 2.48/1.02      ( v2_funct_1(sK3) = iProver_top ),
% 2.48/1.02      inference(global_propositional_subsumption,
% 2.48/1.02                [status(thm)],
% 2.48/1.02                [c_4720,c_37,c_38,c_39,c_24,c_639,c_1173,c_4742]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_1072,plain,
% 2.48/1.02      ( v1_funct_1(sK3) = iProver_top ),
% 2.48/1.02      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_5,plain,
% 2.48/1.02      ( ~ v1_funct_1(X0)
% 2.48/1.02      | ~ v1_relat_1(X0)
% 2.48/1.02      | ~ v2_funct_1(X0)
% 2.48/1.02      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
% 2.48/1.02      inference(cnf_transformation,[],[f81]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_1089,plain,
% 2.48/1.02      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
% 2.48/1.02      | v1_funct_1(X0) != iProver_top
% 2.48/1.02      | v1_relat_1(X0) != iProver_top
% 2.48/1.02      | v2_funct_1(X0) != iProver_top ),
% 2.48/1.02      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_2031,plain,
% 2.48/1.02      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
% 2.48/1.02      | v1_relat_1(sK3) != iProver_top
% 2.48/1.02      | v2_funct_1(sK3) != iProver_top ),
% 2.48/1.02      inference(superposition,[status(thm)],[c_1072,c_1089]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_7,plain,
% 2.48/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.48/1.02      | v1_relat_1(X0) ),
% 2.48/1.02      inference(cnf_transformation,[],[f48]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_1214,plain,
% 2.48/1.02      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.48/1.02      | v1_relat_1(sK3) ),
% 2.48/1.02      inference(instantiation,[status(thm)],[c_7]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_1573,plain,
% 2.48/1.02      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.48/1.02      | v1_relat_1(sK3) ),
% 2.48/1.02      inference(instantiation,[status(thm)],[c_1214]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_1574,plain,
% 2.48/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.48/1.02      | v1_relat_1(sK3) = iProver_top ),
% 2.48/1.02      inference(predicate_to_equality,[status(thm)],[c_1573]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_2233,plain,
% 2.48/1.02      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
% 2.48/1.02      | v2_funct_1(sK3) != iProver_top ),
% 2.48/1.02      inference(global_propositional_subsumption,
% 2.48/1.02                [status(thm)],
% 2.48/1.02                [c_2031,c_39,c_1574]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_4969,plain,
% 2.48/1.02      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3)) ),
% 2.48/1.02      inference(superposition,[status(thm)],[c_4964,c_2233]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_5218,plain,
% 2.48/1.02      ( k6_partfun1(k1_relat_1(sK3)) = k6_partfun1(sK1) ),
% 2.48/1.02      inference(demodulation,[status(thm)],[c_5216,c_4969]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_0,plain,
% 2.48/1.02      ( k2_relat_1(k6_partfun1(X0)) = X0 ),
% 2.48/1.02      inference(cnf_transformation,[],[f76]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_5703,plain,
% 2.48/1.02      ( k2_relat_1(k6_partfun1(sK1)) = k1_relat_1(sK3) ),
% 2.48/1.02      inference(superposition,[status(thm)],[c_5218,c_0]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_5704,plain,
% 2.48/1.02      ( k1_relat_1(sK3) = sK1 ),
% 2.48/1.02      inference(demodulation,[status(thm)],[c_5703,c_0]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_1071,plain,
% 2.48/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.48/1.02      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_1074,plain,
% 2.48/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 2.48/1.02      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_14,plain,
% 2.48/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.48/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 2.48/1.02      | ~ v1_funct_1(X0)
% 2.48/1.02      | ~ v1_funct_1(X3)
% 2.48/1.02      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 2.48/1.02      inference(cnf_transformation,[],[f55]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_1082,plain,
% 2.48/1.02      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 2.48/1.02      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 2.48/1.02      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.48/1.02      | v1_funct_1(X5) != iProver_top
% 2.48/1.02      | v1_funct_1(X4) != iProver_top ),
% 2.48/1.02      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_2748,plain,
% 2.48/1.02      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 2.48/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.48/1.02      | v1_funct_1(X2) != iProver_top
% 2.48/1.02      | v1_funct_1(sK3) != iProver_top ),
% 2.48/1.02      inference(superposition,[status(thm)],[c_1074,c_1082]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_2812,plain,
% 2.48/1.02      ( v1_funct_1(X2) != iProver_top
% 2.48/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.48/1.02      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 2.48/1.02      inference(global_propositional_subsumption,
% 2.48/1.02                [status(thm)],
% 2.48/1.02                [c_2748,c_37]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_2813,plain,
% 2.48/1.02      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 2.48/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.48/1.02      | v1_funct_1(X2) != iProver_top ),
% 2.48/1.02      inference(renaming,[status(thm)],[c_2812]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_2821,plain,
% 2.48/1.02      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 2.48/1.02      | v1_funct_1(sK2) != iProver_top ),
% 2.48/1.02      inference(superposition,[status(thm)],[c_1071,c_2813]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_2822,plain,
% 2.48/1.02      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 2.48/1.02      | v1_funct_1(sK2) != iProver_top ),
% 2.48/1.02      inference(light_normalisation,[status(thm)],[c_2821,c_1758]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_3651,plain,
% 2.48/1.02      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 2.48/1.02      inference(global_propositional_subsumption,
% 2.48/1.02                [status(thm)],
% 2.48/1.02                [c_2822,c_34]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_6,plain,
% 2.48/1.02      ( ~ v1_funct_1(X0)
% 2.48/1.02      | ~ v1_funct_1(X1)
% 2.48/1.02      | ~ v1_relat_1(X0)
% 2.48/1.02      | ~ v1_relat_1(X1)
% 2.48/1.02      | ~ v2_funct_1(X0)
% 2.48/1.02      | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
% 2.48/1.02      | k2_funct_1(X0) = X1
% 2.48/1.02      | k1_relat_1(X1) != k2_relat_1(X0) ),
% 2.48/1.02      inference(cnf_transformation,[],[f82]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_1088,plain,
% 2.48/1.02      ( k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
% 2.48/1.02      | k2_funct_1(X0) = X1
% 2.48/1.02      | k1_relat_1(X1) != k2_relat_1(X0)
% 2.48/1.02      | v1_funct_1(X0) != iProver_top
% 2.48/1.02      | v1_funct_1(X1) != iProver_top
% 2.48/1.02      | v1_relat_1(X0) != iProver_top
% 2.48/1.02      | v1_relat_1(X1) != iProver_top
% 2.48/1.02      | v2_funct_1(X0) != iProver_top ),
% 2.48/1.02      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_3772,plain,
% 2.48/1.02      ( k2_funct_1(sK2) = sK3
% 2.48/1.02      | k1_relat_1(sK3) != k2_relat_1(sK2)
% 2.48/1.02      | k6_partfun1(k1_relat_1(sK2)) != k6_partfun1(sK0)
% 2.48/1.02      | v1_funct_1(sK3) != iProver_top
% 2.48/1.02      | v1_funct_1(sK2) != iProver_top
% 2.48/1.02      | v1_relat_1(sK3) != iProver_top
% 2.48/1.02      | v1_relat_1(sK2) != iProver_top
% 2.48/1.02      | v2_funct_1(sK2) != iProver_top ),
% 2.48/1.02      inference(superposition,[status(thm)],[c_3651,c_1088]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_8,plain,
% 2.48/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.48/1.02      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.48/1.02      inference(cnf_transformation,[],[f49]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_1086,plain,
% 2.48/1.02      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.48/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.48/1.02      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_1991,plain,
% 2.48/1.02      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 2.48/1.02      inference(superposition,[status(thm)],[c_1071,c_1086]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_1992,plain,
% 2.48/1.02      ( k2_relat_1(sK2) = sK1 ),
% 2.48/1.02      inference(light_normalisation,[status(thm)],[c_1991,c_27]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_2684,plain,
% 2.48/1.02      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
% 2.48/1.02      | sK1 = k1_xboole_0
% 2.48/1.02      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 2.48/1.02      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.48/1.02      | v1_funct_1(sK2) != iProver_top
% 2.48/1.02      | v2_funct_1(sK2) != iProver_top ),
% 2.48/1.02      inference(superposition,[status(thm)],[c_27,c_1076]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_1069,plain,
% 2.48/1.02      ( v1_funct_1(sK2) = iProver_top ),
% 2.48/1.02      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_2032,plain,
% 2.48/1.02      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
% 2.48/1.02      | v1_relat_1(sK2) != iProver_top
% 2.48/1.02      | v2_funct_1(sK2) != iProver_top ),
% 2.48/1.02      inference(superposition,[status(thm)],[c_1069,c_1089]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_25,negated_conjecture,
% 2.48/1.02      ( v2_funct_1(sK2) ),
% 2.48/1.02      inference(cnf_transformation,[],[f72]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_41,plain,
% 2.48/1.02      ( v2_funct_1(sK2) = iProver_top ),
% 2.48/1.02      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_1684,plain,
% 2.48/1.02      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.48/1.02      | v1_relat_1(sK2) ),
% 2.48/1.02      inference(instantiation,[status(thm)],[c_7]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_1685,plain,
% 2.48/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.48/1.02      | v1_relat_1(sK2) = iProver_top ),
% 2.48/1.02      inference(predicate_to_equality,[status(thm)],[c_1684]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_2238,plain,
% 2.48/1.02      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
% 2.48/1.02      inference(global_propositional_subsumption,
% 2.48/1.02                [status(thm)],
% 2.48/1.02                [c_2032,c_36,c_41,c_1685]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_2687,plain,
% 2.48/1.02      ( k6_partfun1(k1_relat_1(sK2)) = k6_partfun1(sK0)
% 2.48/1.02      | sK1 = k1_xboole_0
% 2.48/1.02      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 2.48/1.02      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.48/1.02      | v1_funct_1(sK2) != iProver_top
% 2.48/1.02      | v2_funct_1(sK2) != iProver_top ),
% 2.48/1.02      inference(demodulation,[status(thm)],[c_2684,c_2238]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_23,negated_conjecture,
% 2.48/1.02      ( k1_xboole_0 != sK1 ),
% 2.48/1.02      inference(cnf_transformation,[],[f74]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_1152,plain,
% 2.48/1.02      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 2.48/1.02      inference(instantiation,[status(thm)],[c_609]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_1153,plain,
% 2.48/1.02      ( sK1 != k1_xboole_0
% 2.48/1.02      | k1_xboole_0 = sK1
% 2.48/1.02      | k1_xboole_0 != k1_xboole_0 ),
% 2.48/1.02      inference(instantiation,[status(thm)],[c_1152]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_3571,plain,
% 2.48/1.02      ( k6_partfun1(k1_relat_1(sK2)) = k6_partfun1(sK0) ),
% 2.48/1.02      inference(global_propositional_subsumption,
% 2.48/1.02                [status(thm)],
% 2.48/1.02                [c_2687,c_34,c_35,c_36,c_41,c_23,c_639,c_1153]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_3579,plain,
% 2.48/1.02      ( k2_relat_1(k6_partfun1(sK0)) = k1_relat_1(sK2) ),
% 2.48/1.02      inference(superposition,[status(thm)],[c_3571,c_0]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_3580,plain,
% 2.48/1.02      ( k1_relat_1(sK2) = sK0 ),
% 2.48/1.02      inference(demodulation,[status(thm)],[c_3579,c_0]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_3776,plain,
% 2.48/1.02      ( k2_funct_1(sK2) = sK3
% 2.48/1.02      | k1_relat_1(sK3) != sK1
% 2.48/1.02      | k6_partfun1(sK0) != k6_partfun1(sK0)
% 2.48/1.02      | v1_funct_1(sK3) != iProver_top
% 2.48/1.02      | v1_funct_1(sK2) != iProver_top
% 2.48/1.02      | v1_relat_1(sK3) != iProver_top
% 2.48/1.02      | v1_relat_1(sK2) != iProver_top
% 2.48/1.02      | v2_funct_1(sK2) != iProver_top ),
% 2.48/1.02      inference(light_normalisation,[status(thm)],[c_3772,c_1992,c_3580]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_3777,plain,
% 2.48/1.02      ( k2_funct_1(sK2) = sK3
% 2.48/1.02      | k1_relat_1(sK3) != sK1
% 2.48/1.02      | v1_funct_1(sK3) != iProver_top
% 2.48/1.02      | v1_funct_1(sK2) != iProver_top
% 2.48/1.02      | v1_relat_1(sK3) != iProver_top
% 2.48/1.02      | v1_relat_1(sK2) != iProver_top
% 2.48/1.02      | v2_funct_1(sK2) != iProver_top ),
% 2.48/1.02      inference(equality_resolution_simp,[status(thm)],[c_3776]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(c_22,negated_conjecture,
% 2.48/1.02      ( k2_funct_1(sK2) != sK3 ),
% 2.48/1.02      inference(cnf_transformation,[],[f75]) ).
% 2.48/1.02  
% 2.48/1.02  cnf(contradiction,plain,
% 2.48/1.02      ( $false ),
% 2.48/1.02      inference(minisat,
% 2.48/1.02                [status(thm)],
% 2.48/1.02                [c_5704,c_3777,c_1685,c_1574,c_22,c_41,c_39,c_37,c_36,
% 2.48/1.02                 c_34]) ).
% 2.48/1.02  
% 2.48/1.02  
% 2.48/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 2.48/1.02  
% 2.48/1.02  ------                               Statistics
% 2.48/1.02  
% 2.48/1.02  ------ General
% 2.48/1.02  
% 2.48/1.02  abstr_ref_over_cycles:                  0
% 2.48/1.02  abstr_ref_under_cycles:                 0
% 2.48/1.02  gc_basic_clause_elim:                   0
% 2.48/1.02  forced_gc_time:                         0
% 2.48/1.02  parsing_time:                           0.025
% 2.48/1.02  unif_index_cands_time:                  0.
% 2.48/1.02  unif_index_add_time:                    0.
% 2.48/1.02  orderings_time:                         0.
% 2.48/1.02  out_proof_time:                         0.025
% 2.48/1.02  total_time:                             0.307
% 2.48/1.02  num_of_symbols:                         51
% 2.48/1.02  num_of_terms:                           9321
% 2.48/1.02  
% 2.48/1.02  ------ Preprocessing
% 2.48/1.02  
% 2.48/1.02  num_of_splits:                          0
% 2.48/1.02  num_of_split_atoms:                     0
% 2.48/1.02  num_of_reused_defs:                     0
% 2.48/1.02  num_eq_ax_congr_red:                    0
% 2.48/1.02  num_of_sem_filtered_clauses:            1
% 2.48/1.02  num_of_subtypes:                        0
% 2.48/1.02  monotx_restored_types:                  0
% 2.48/1.02  sat_num_of_epr_types:                   0
% 2.48/1.02  sat_num_of_non_cyclic_types:            0
% 2.48/1.02  sat_guarded_non_collapsed_types:        0
% 2.48/1.02  num_pure_diseq_elim:                    0
% 2.48/1.02  simp_replaced_by:                       0
% 2.48/1.02  res_preprocessed:                       166
% 2.48/1.02  prep_upred:                             0
% 2.48/1.02  prep_unflattend:                        12
% 2.48/1.02  smt_new_axioms:                         0
% 2.48/1.02  pred_elim_cands:                        5
% 2.48/1.02  pred_elim:                              1
% 2.48/1.02  pred_elim_cl:                           1
% 2.48/1.02  pred_elim_cycles:                       3
% 2.48/1.02  merged_defs:                            0
% 2.48/1.02  merged_defs_ncl:                        0
% 2.48/1.02  bin_hyper_res:                          0
% 2.48/1.02  prep_cycles:                            4
% 2.48/1.02  pred_elim_time:                         0.005
% 2.48/1.02  splitting_time:                         0.
% 2.48/1.02  sem_filter_time:                        0.
% 2.48/1.02  monotx_time:                            0.001
% 2.48/1.02  subtype_inf_time:                       0.
% 2.48/1.02  
% 2.48/1.02  ------ Problem properties
% 2.48/1.02  
% 2.48/1.02  clauses:                                33
% 2.48/1.02  conjectures:                            11
% 2.48/1.02  epr:                                    7
% 2.48/1.02  horn:                                   29
% 2.48/1.02  ground:                                 12
% 2.48/1.02  unary:                                  16
% 2.48/1.02  binary:                                 3
% 2.48/1.02  lits:                                   121
% 2.48/1.02  lits_eq:                                30
% 2.48/1.02  fd_pure:                                0
% 2.48/1.02  fd_pseudo:                              0
% 2.48/1.02  fd_cond:                                4
% 2.48/1.02  fd_pseudo_cond:                         1
% 2.48/1.02  ac_symbols:                             0
% 2.48/1.02  
% 2.48/1.02  ------ Propositional Solver
% 2.48/1.02  
% 2.48/1.02  prop_solver_calls:                      29
% 2.48/1.02  prop_fast_solver_calls:                 1490
% 2.48/1.02  smt_solver_calls:                       0
% 2.48/1.02  smt_fast_solver_calls:                  0
% 2.48/1.02  prop_num_of_clauses:                    2976
% 2.48/1.02  prop_preprocess_simplified:             8117
% 2.48/1.02  prop_fo_subsumed:                       66
% 2.48/1.02  prop_solver_time:                       0.
% 2.48/1.02  smt_solver_time:                        0.
% 2.48/1.02  smt_fast_solver_time:                   0.
% 2.48/1.02  prop_fast_solver_time:                  0.
% 2.48/1.02  prop_unsat_core_time:                   0.
% 2.48/1.02  
% 2.48/1.02  ------ QBF
% 2.48/1.02  
% 2.48/1.02  qbf_q_res:                              0
% 2.48/1.02  qbf_num_tautologies:                    0
% 2.48/1.02  qbf_prep_cycles:                        0
% 2.48/1.02  
% 2.48/1.02  ------ BMC1
% 2.48/1.02  
% 2.48/1.02  bmc1_current_bound:                     -1
% 2.48/1.02  bmc1_last_solved_bound:                 -1
% 2.48/1.02  bmc1_unsat_core_size:                   -1
% 2.48/1.02  bmc1_unsat_core_parents_size:           -1
% 2.48/1.02  bmc1_merge_next_fun:                    0
% 2.48/1.02  bmc1_unsat_core_clauses_time:           0.
% 2.48/1.02  
% 2.48/1.02  ------ Instantiation
% 2.48/1.02  
% 2.48/1.02  inst_num_of_clauses:                    775
% 2.48/1.02  inst_num_in_passive:                    150
% 2.48/1.02  inst_num_in_active:                     407
% 2.48/1.02  inst_num_in_unprocessed:                218
% 2.48/1.02  inst_num_of_loops:                      420
% 2.48/1.02  inst_num_of_learning_restarts:          0
% 2.48/1.02  inst_num_moves_active_passive:          11
% 2.48/1.02  inst_lit_activity:                      0
% 2.48/1.02  inst_lit_activity_moves:                0
% 2.48/1.02  inst_num_tautologies:                   0
% 2.48/1.02  inst_num_prop_implied:                  0
% 2.48/1.02  inst_num_existing_simplified:           0
% 2.48/1.02  inst_num_eq_res_simplified:             0
% 2.48/1.02  inst_num_child_elim:                    0
% 2.48/1.02  inst_num_of_dismatching_blockings:      56
% 2.48/1.02  inst_num_of_non_proper_insts:           638
% 2.48/1.02  inst_num_of_duplicates:                 0
% 2.48/1.02  inst_inst_num_from_inst_to_res:         0
% 2.48/1.02  inst_dismatching_checking_time:         0.
% 2.48/1.02  
% 2.48/1.02  ------ Resolution
% 2.48/1.02  
% 2.48/1.02  res_num_of_clauses:                     0
% 2.48/1.02  res_num_in_passive:                     0
% 2.48/1.02  res_num_in_active:                      0
% 2.48/1.02  res_num_of_loops:                       170
% 2.48/1.02  res_forward_subset_subsumed:            56
% 2.48/1.02  res_backward_subset_subsumed:           0
% 2.48/1.02  res_forward_subsumed:                   0
% 2.48/1.02  res_backward_subsumed:                  0
% 2.48/1.02  res_forward_subsumption_resolution:     2
% 2.48/1.02  res_backward_subsumption_resolution:    0
% 2.48/1.02  res_clause_to_clause_subsumption:       267
% 2.48/1.02  res_orphan_elimination:                 0
% 2.48/1.02  res_tautology_del:                      24
% 2.48/1.02  res_num_eq_res_simplified:              1
% 2.48/1.02  res_num_sel_changes:                    0
% 2.48/1.02  res_moves_from_active_to_pass:          0
% 2.48/1.02  
% 2.48/1.02  ------ Superposition
% 2.48/1.02  
% 2.48/1.02  sup_time_total:                         0.
% 2.48/1.02  sup_time_generating:                    0.
% 2.48/1.02  sup_time_sim_full:                      0.
% 2.48/1.02  sup_time_sim_immed:                     0.
% 2.48/1.02  
% 2.48/1.02  sup_num_of_clauses:                     137
% 2.48/1.02  sup_num_in_active:                      75
% 2.48/1.02  sup_num_in_passive:                     62
% 2.48/1.02  sup_num_of_loops:                       82
% 2.48/1.02  sup_fw_superposition:                   65
% 2.48/1.02  sup_bw_superposition:                   79
% 2.48/1.02  sup_immediate_simplified:               48
% 2.48/1.02  sup_given_eliminated:                   2
% 2.48/1.02  comparisons_done:                       0
% 2.48/1.02  comparisons_avoided:                    0
% 2.48/1.02  
% 2.48/1.02  ------ Simplifications
% 2.48/1.02  
% 2.48/1.02  
% 2.48/1.02  sim_fw_subset_subsumed:                 5
% 2.48/1.02  sim_bw_subset_subsumed:                 6
% 2.48/1.02  sim_fw_subsumed:                        12
% 2.48/1.02  sim_bw_subsumed:                        0
% 2.48/1.02  sim_fw_subsumption_res:                 0
% 2.48/1.02  sim_bw_subsumption_res:                 0
% 2.48/1.02  sim_tautology_del:                      0
% 2.48/1.02  sim_eq_tautology_del:                   11
% 2.48/1.02  sim_eq_res_simp:                        1
% 2.48/1.02  sim_fw_demodulated:                     3
% 2.48/1.02  sim_bw_demodulated:                     5
% 2.48/1.02  sim_light_normalised:                   34
% 2.48/1.02  sim_joinable_taut:                      0
% 2.48/1.02  sim_joinable_simp:                      0
% 2.48/1.02  sim_ac_normalised:                      0
% 2.48/1.02  sim_smt_subsumption:                    0
% 2.48/1.02  
%------------------------------------------------------------------------------

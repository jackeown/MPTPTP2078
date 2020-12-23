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
% DateTime   : Thu Dec  3 12:03:16 EST 2020

% Result     : Theorem 11.20s
% Output     : CNFRefutation 11.20s
% Verified   : 
% Statistics : Number of formulae       :  200 (3030 expanded)
%              Number of clauses        :  127 ( 815 expanded)
%              Number of leaves         :   22 ( 808 expanded)
%              Depth                    :   23
%              Number of atoms          :  788 (27103 expanded)
%              Number of equality atoms :  391 (9832 expanded)
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
    inference(ennf_transformation,[],[f12])).

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

fof(f58,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f40,plain,(
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

fof(f39,plain,
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

fof(f41,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f37,f40,f39])).

fof(f72,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f41])).

fof(f65,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f66,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f67,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f41])).

fof(f68,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f69,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f70,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f41])).

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
    inference(ennf_transformation,[],[f14])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f74,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f41])).

fof(f2,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f11,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f79,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f45,f57])).

fof(f7,axiom,(
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
    inference(ennf_transformation,[],[f7])).

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

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f9,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f55,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f26])).

fof(f54,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f71,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f41])).

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
    inference(ennf_transformation,[],[f13])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f61,plain,(
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
    inference(cnf_transformation,[],[f33])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f4])).

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
    inference(definition_unfolding,[],[f48,f57])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f73,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f28])).

fof(f56,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f19,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f47,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f77,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f43,f57])).

fof(f75,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f41])).

fof(f46,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f42,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f78,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f42,f57])).

fof(f76,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_15,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_26,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f72])).

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
    inference(cnf_transformation,[],[f65])).

cnf(c_34,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_35,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_36,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_37,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_38,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f70])).

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
    inference(cnf_transformation,[],[f63])).

cnf(c_1076,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2673,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1765,c_1076])).

cnf(c_24,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f74])).

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

cnf(c_2,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_4709,plain,
    ( v2_funct_1(k6_partfun1(sK0)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_4710,plain,
    ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4709])).

cnf(c_10,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f51])).

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

cnf(c_13,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_363,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_355,c_13])).

cnf(c_1067,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_363])).

cnf(c_11,plain,
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
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1758,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1067,c_33,c_31,c_30,c_28,c_363,c_1174])).

cnf(c_27,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f71])).

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
    inference(cnf_transformation,[],[f61])).

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

cnf(c_4850,plain,
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

cnf(c_4857,plain,
    ( v1_funct_1(X1) != iProver_top
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | k1_xboole_0 = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4850,c_34,c_35,c_36])).

cnf(c_4858,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4857])).

cnf(c_4861,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1758,c_4858])).

cnf(c_5185,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2673,c_37,c_38,c_39,c_24,c_639,c_1173,c_4710,c_4861])).

cnf(c_6,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v2_funct_1(X0)
    | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
    | k2_funct_1(X0) = X1
    | k1_relat_1(X0) != k2_relat_1(X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1088,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k1_relat_1(X1) != k2_relat_1(X0)
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v2_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5191,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3
    | k1_relat_1(k2_funct_1(sK3)) != k2_relat_1(sK3)
    | k6_partfun1(k2_relat_1(k2_funct_1(sK3))) != k6_partfun1(sK1)
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v2_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5185,c_1088])).

cnf(c_1074,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1086,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1990,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1074,c_1086])).

cnf(c_1993,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_1990,c_1765])).

cnf(c_5192,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3
    | k1_relat_1(k2_funct_1(sK3)) != sK0
    | k6_partfun1(k2_relat_1(k2_funct_1(sK3))) != k6_partfun1(sK1)
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v2_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5191,c_1993])).

cnf(c_25,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1214,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1573,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1214])).

cnf(c_1684,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1071,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1082,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2775,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1074,c_1082])).

cnf(c_2787,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2775,c_37])).

cnf(c_2788,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_2787])).

cnf(c_2795,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1071,c_2788])).

cnf(c_2796,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2795,c_1758])).

cnf(c_3532,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2796,c_34])).

cnf(c_4044,plain,
    ( k2_funct_1(sK3) = sK2
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3532,c_1088])).

cnf(c_1991,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1071,c_1086])).

cnf(c_1992,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_1991,c_27])).

cnf(c_4045,plain,
    ( k2_funct_1(sK3) = sK2
    | k1_relat_1(sK3) != sK1
    | k6_partfun1(sK0) != k6_partfun1(sK0)
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4044,c_1992,c_1993])).

cnf(c_4046,plain,
    ( k2_funct_1(sK3) = sK2
    | k1_relat_1(sK3) != sK1
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4045])).

cnf(c_1574,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1573])).

cnf(c_1685,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1684])).

cnf(c_5123,plain,
    ( k1_relat_1(sK3) != sK1
    | k2_funct_1(sK3) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4046,c_34,c_36,c_37,c_38,c_39,c_24,c_639,c_1173,c_1574,c_1685,c_4710,c_4861])).

cnf(c_5124,plain,
    ( k2_funct_1(sK3) = sK2
    | k1_relat_1(sK3) != sK1 ),
    inference(renaming,[status(thm)],[c_5123])).

cnf(c_4937,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4861,c_37,c_38,c_39,c_24,c_639,c_1173,c_4710])).

cnf(c_1072,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_4,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1090,plain,
    ( k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2276,plain,
    ( k2_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) = k1_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1072,c_1090])).

cnf(c_2607,plain,
    ( k2_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) = k1_relat_1(sK3)
    | v2_funct_1(sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2276,c_39,c_1574])).

cnf(c_4941,plain,
    ( k2_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_4937,c_2607])).

cnf(c_5188,plain,
    ( k2_relat_1(k6_partfun1(sK1)) = k1_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_5185,c_4941])).

cnf(c_0,plain,
    ( k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_5189,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(demodulation,[status(thm)],[c_5188,c_0])).

cnf(c_5193,plain,
    ( ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v2_funct_1(k2_funct_1(sK3))
    | k2_funct_1(k2_funct_1(sK3)) = sK3
    | k1_relat_1(k2_funct_1(sK3)) != sK0
    | k6_partfun1(k2_relat_1(k2_funct_1(sK3))) != k6_partfun1(sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5192])).

cnf(c_617,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1351,plain,
    ( v1_funct_1(X0)
    | ~ v1_funct_1(sK2)
    | X0 != sK2 ),
    inference(instantiation,[status(thm)],[c_617])).

cnf(c_1430,plain,
    ( v1_funct_1(k2_funct_1(X0))
    | ~ v1_funct_1(sK2)
    | k2_funct_1(X0) != sK2 ),
    inference(instantiation,[status(thm)],[c_1351])).

cnf(c_7858,plain,
    ( v1_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK2)
    | k2_funct_1(sK3) != sK2 ),
    inference(instantiation,[status(thm)],[c_1430])).

cnf(c_614,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1737,plain,
    ( v1_relat_1(X0)
    | ~ v1_relat_1(sK2)
    | X0 != sK2 ),
    inference(instantiation,[status(thm)],[c_614])).

cnf(c_2256,plain,
    ( v1_relat_1(k2_funct_1(X0))
    | ~ v1_relat_1(sK2)
    | k2_funct_1(X0) != sK2 ),
    inference(instantiation,[status(thm)],[c_1737])).

cnf(c_7856,plain,
    ( v1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK2)
    | k2_funct_1(sK3) != sK2 ),
    inference(instantiation,[status(thm)],[c_2256])).

cnf(c_613,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2108,plain,
    ( v2_funct_1(X0)
    | ~ v2_funct_1(sK2)
    | X0 != sK2 ),
    inference(instantiation,[status(thm)],[c_613])).

cnf(c_2527,plain,
    ( v2_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(sK2)
    | k2_funct_1(X0) != sK2 ),
    inference(instantiation,[status(thm)],[c_2108])).

cnf(c_7855,plain,
    ( v2_funct_1(k2_funct_1(sK3))
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK3) != sK2 ),
    inference(instantiation,[status(thm)],[c_2527])).

cnf(c_25869,plain,
    ( k6_partfun1(k2_relat_1(k2_funct_1(sK3))) != k6_partfun1(sK1)
    | k1_relat_1(k2_funct_1(sK3)) != sK0
    | k2_funct_1(k2_funct_1(sK3)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5192,c_33,c_34,c_31,c_36,c_30,c_37,c_38,c_28,c_39,c_25,c_24,c_639,c_1173,c_1573,c_1574,c_1684,c_1685,c_4046,c_4710,c_4861,c_5189,c_5193,c_7858,c_7856,c_7855])).

cnf(c_25870,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3
    | k1_relat_1(k2_funct_1(sK3)) != sK0
    | k6_partfun1(k2_relat_1(k2_funct_1(sK3))) != k6_partfun1(sK1) ),
    inference(renaming,[status(thm)],[c_25869])).

cnf(c_2672,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_27,c_1076])).

cnf(c_23,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1137,plain,
    ( ~ v1_funct_2(X0,X1,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,sK1,X0) != sK1
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_1265,plain,
    ( ~ v1_funct_2(sK2,X0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(X0,sK1,sK2) != sK1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1137])).

cnf(c_1482,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(sK0,sK1,sK2) != sK1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1265])).

cnf(c_2679,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2672,c_33,c_32,c_31,c_27,c_25,c_23,c_1482])).

cnf(c_1069,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_5,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v2_funct_1(X0)
    | k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1089,plain,
    ( k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2032,plain,
    ( k1_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1069,c_1089])).

cnf(c_41,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2228,plain,
    ( k1_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2032,c_36,c_41,c_1685])).

cnf(c_2682,plain,
    ( k1_relat_1(k6_partfun1(sK0)) = k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2679,c_2228])).

cnf(c_1,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2683,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(demodulation,[status(thm)],[c_2682,c_1])).

cnf(c_5221,plain,
    ( k2_funct_1(sK3) = sK2
    | sK1 != sK1 ),
    inference(demodulation,[status(thm)],[c_5189,c_5124])).

cnf(c_5319,plain,
    ( k2_funct_1(sK3) = sK2 ),
    inference(equality_resolution_simp,[status(thm)],[c_5221])).

cnf(c_25871,plain,
    ( k2_funct_1(sK2) = sK3
    | k6_partfun1(sK1) != k6_partfun1(sK1)
    | sK0 != sK0 ),
    inference(light_normalisation,[status(thm)],[c_25870,c_1992,c_2683,c_5319])).

cnf(c_25872,plain,
    ( k2_funct_1(sK2) = sK3 ),
    inference(equality_resolution_simp,[status(thm)],[c_25871])).

cnf(c_22,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f76])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_25872,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:08:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 11.20/2.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.20/2.01  
% 11.20/2.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.20/2.01  
% 11.20/2.01  ------  iProver source info
% 11.20/2.01  
% 11.20/2.01  git: date: 2020-06-30 10:37:57 +0100
% 11.20/2.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.20/2.01  git: non_committed_changes: false
% 11.20/2.01  git: last_make_outside_of_git: false
% 11.20/2.01  
% 11.20/2.01  ------ 
% 11.20/2.01  
% 11.20/2.01  ------ Input Options
% 11.20/2.01  
% 11.20/2.01  --out_options                           all
% 11.20/2.01  --tptp_safe_out                         true
% 11.20/2.01  --problem_path                          ""
% 11.20/2.01  --include_path                          ""
% 11.20/2.01  --clausifier                            res/vclausify_rel
% 11.20/2.01  --clausifier_options                    ""
% 11.20/2.01  --stdin                                 false
% 11.20/2.01  --stats_out                             all
% 11.20/2.01  
% 11.20/2.01  ------ General Options
% 11.20/2.01  
% 11.20/2.01  --fof                                   false
% 11.20/2.01  --time_out_real                         305.
% 11.20/2.01  --time_out_virtual                      -1.
% 11.20/2.01  --symbol_type_check                     false
% 11.20/2.01  --clausify_out                          false
% 11.20/2.01  --sig_cnt_out                           false
% 11.20/2.01  --trig_cnt_out                          false
% 11.20/2.01  --trig_cnt_out_tolerance                1.
% 11.20/2.01  --trig_cnt_out_sk_spl                   false
% 11.20/2.01  --abstr_cl_out                          false
% 11.20/2.01  
% 11.20/2.01  ------ Global Options
% 11.20/2.01  
% 11.20/2.01  --schedule                              default
% 11.20/2.01  --add_important_lit                     false
% 11.20/2.01  --prop_solver_per_cl                    1000
% 11.20/2.01  --min_unsat_core                        false
% 11.20/2.01  --soft_assumptions                      false
% 11.20/2.01  --soft_lemma_size                       3
% 11.20/2.01  --prop_impl_unit_size                   0
% 11.20/2.01  --prop_impl_unit                        []
% 11.20/2.01  --share_sel_clauses                     true
% 11.20/2.01  --reset_solvers                         false
% 11.20/2.01  --bc_imp_inh                            [conj_cone]
% 11.20/2.01  --conj_cone_tolerance                   3.
% 11.20/2.01  --extra_neg_conj                        none
% 11.20/2.01  --large_theory_mode                     true
% 11.20/2.01  --prolific_symb_bound                   200
% 11.20/2.01  --lt_threshold                          2000
% 11.20/2.01  --clause_weak_htbl                      true
% 11.20/2.01  --gc_record_bc_elim                     false
% 11.20/2.01  
% 11.20/2.01  ------ Preprocessing Options
% 11.20/2.01  
% 11.20/2.01  --preprocessing_flag                    true
% 11.20/2.01  --time_out_prep_mult                    0.1
% 11.20/2.01  --splitting_mode                        input
% 11.20/2.01  --splitting_grd                         true
% 11.20/2.01  --splitting_cvd                         false
% 11.20/2.01  --splitting_cvd_svl                     false
% 11.20/2.01  --splitting_nvd                         32
% 11.20/2.01  --sub_typing                            true
% 11.20/2.01  --prep_gs_sim                           true
% 11.20/2.01  --prep_unflatten                        true
% 11.20/2.01  --prep_res_sim                          true
% 11.20/2.01  --prep_upred                            true
% 11.20/2.01  --prep_sem_filter                       exhaustive
% 11.20/2.01  --prep_sem_filter_out                   false
% 11.20/2.01  --pred_elim                             true
% 11.20/2.01  --res_sim_input                         true
% 11.20/2.01  --eq_ax_congr_red                       true
% 11.20/2.01  --pure_diseq_elim                       true
% 11.20/2.01  --brand_transform                       false
% 11.20/2.01  --non_eq_to_eq                          false
% 11.20/2.01  --prep_def_merge                        true
% 11.20/2.01  --prep_def_merge_prop_impl              false
% 11.20/2.01  --prep_def_merge_mbd                    true
% 11.20/2.01  --prep_def_merge_tr_red                 false
% 11.20/2.01  --prep_def_merge_tr_cl                  false
% 11.20/2.01  --smt_preprocessing                     true
% 11.20/2.01  --smt_ac_axioms                         fast
% 11.20/2.01  --preprocessed_out                      false
% 11.20/2.01  --preprocessed_stats                    false
% 11.20/2.01  
% 11.20/2.01  ------ Abstraction refinement Options
% 11.20/2.01  
% 11.20/2.01  --abstr_ref                             []
% 11.20/2.01  --abstr_ref_prep                        false
% 11.20/2.01  --abstr_ref_until_sat                   false
% 11.20/2.01  --abstr_ref_sig_restrict                funpre
% 11.20/2.01  --abstr_ref_af_restrict_to_split_sk     false
% 11.20/2.01  --abstr_ref_under                       []
% 11.20/2.01  
% 11.20/2.01  ------ SAT Options
% 11.20/2.01  
% 11.20/2.01  --sat_mode                              false
% 11.20/2.01  --sat_fm_restart_options                ""
% 11.20/2.01  --sat_gr_def                            false
% 11.20/2.01  --sat_epr_types                         true
% 11.20/2.01  --sat_non_cyclic_types                  false
% 11.20/2.01  --sat_finite_models                     false
% 11.20/2.01  --sat_fm_lemmas                         false
% 11.20/2.01  --sat_fm_prep                           false
% 11.20/2.01  --sat_fm_uc_incr                        true
% 11.20/2.01  --sat_out_model                         small
% 11.20/2.01  --sat_out_clauses                       false
% 11.20/2.01  
% 11.20/2.01  ------ QBF Options
% 11.20/2.01  
% 11.20/2.01  --qbf_mode                              false
% 11.20/2.01  --qbf_elim_univ                         false
% 11.20/2.01  --qbf_dom_inst                          none
% 11.20/2.01  --qbf_dom_pre_inst                      false
% 11.20/2.01  --qbf_sk_in                             false
% 11.20/2.01  --qbf_pred_elim                         true
% 11.20/2.01  --qbf_split                             512
% 11.20/2.01  
% 11.20/2.01  ------ BMC1 Options
% 11.20/2.01  
% 11.20/2.01  --bmc1_incremental                      false
% 11.20/2.01  --bmc1_axioms                           reachable_all
% 11.20/2.01  --bmc1_min_bound                        0
% 11.20/2.01  --bmc1_max_bound                        -1
% 11.20/2.01  --bmc1_max_bound_default                -1
% 11.20/2.01  --bmc1_symbol_reachability              true
% 11.20/2.01  --bmc1_property_lemmas                  false
% 11.20/2.01  --bmc1_k_induction                      false
% 11.20/2.01  --bmc1_non_equiv_states                 false
% 11.20/2.01  --bmc1_deadlock                         false
% 11.20/2.01  --bmc1_ucm                              false
% 11.20/2.01  --bmc1_add_unsat_core                   none
% 11.20/2.01  --bmc1_unsat_core_children              false
% 11.20/2.01  --bmc1_unsat_core_extrapolate_axioms    false
% 11.20/2.01  --bmc1_out_stat                         full
% 11.20/2.01  --bmc1_ground_init                      false
% 11.20/2.01  --bmc1_pre_inst_next_state              false
% 11.20/2.01  --bmc1_pre_inst_state                   false
% 11.20/2.01  --bmc1_pre_inst_reach_state             false
% 11.20/2.01  --bmc1_out_unsat_core                   false
% 11.20/2.01  --bmc1_aig_witness_out                  false
% 11.20/2.01  --bmc1_verbose                          false
% 11.20/2.01  --bmc1_dump_clauses_tptp                false
% 11.20/2.01  --bmc1_dump_unsat_core_tptp             false
% 11.20/2.01  --bmc1_dump_file                        -
% 11.20/2.01  --bmc1_ucm_expand_uc_limit              128
% 11.20/2.01  --bmc1_ucm_n_expand_iterations          6
% 11.20/2.01  --bmc1_ucm_extend_mode                  1
% 11.20/2.01  --bmc1_ucm_init_mode                    2
% 11.20/2.01  --bmc1_ucm_cone_mode                    none
% 11.20/2.01  --bmc1_ucm_reduced_relation_type        0
% 11.20/2.01  --bmc1_ucm_relax_model                  4
% 11.20/2.01  --bmc1_ucm_full_tr_after_sat            true
% 11.20/2.01  --bmc1_ucm_expand_neg_assumptions       false
% 11.20/2.01  --bmc1_ucm_layered_model                none
% 11.20/2.01  --bmc1_ucm_max_lemma_size               10
% 11.20/2.01  
% 11.20/2.01  ------ AIG Options
% 11.20/2.01  
% 11.20/2.01  --aig_mode                              false
% 11.20/2.01  
% 11.20/2.01  ------ Instantiation Options
% 11.20/2.01  
% 11.20/2.01  --instantiation_flag                    true
% 11.20/2.01  --inst_sos_flag                         true
% 11.20/2.01  --inst_sos_phase                        true
% 11.20/2.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.20/2.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.20/2.01  --inst_lit_sel_side                     num_symb
% 11.20/2.01  --inst_solver_per_active                1400
% 11.20/2.01  --inst_solver_calls_frac                1.
% 11.20/2.01  --inst_passive_queue_type               priority_queues
% 11.20/2.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.20/2.01  --inst_passive_queues_freq              [25;2]
% 11.20/2.01  --inst_dismatching                      true
% 11.20/2.01  --inst_eager_unprocessed_to_passive     true
% 11.20/2.01  --inst_prop_sim_given                   true
% 11.20/2.01  --inst_prop_sim_new                     false
% 11.20/2.01  --inst_subs_new                         false
% 11.20/2.01  --inst_eq_res_simp                      false
% 11.20/2.01  --inst_subs_given                       false
% 11.20/2.01  --inst_orphan_elimination               true
% 11.20/2.01  --inst_learning_loop_flag               true
% 11.20/2.01  --inst_learning_start                   3000
% 11.20/2.01  --inst_learning_factor                  2
% 11.20/2.01  --inst_start_prop_sim_after_learn       3
% 11.20/2.01  --inst_sel_renew                        solver
% 11.20/2.01  --inst_lit_activity_flag                true
% 11.20/2.01  --inst_restr_to_given                   false
% 11.20/2.01  --inst_activity_threshold               500
% 11.20/2.01  --inst_out_proof                        true
% 11.20/2.01  
% 11.20/2.01  ------ Resolution Options
% 11.20/2.01  
% 11.20/2.01  --resolution_flag                       true
% 11.20/2.01  --res_lit_sel                           adaptive
% 11.20/2.01  --res_lit_sel_side                      none
% 11.20/2.01  --res_ordering                          kbo
% 11.20/2.01  --res_to_prop_solver                    active
% 11.20/2.01  --res_prop_simpl_new                    false
% 11.20/2.01  --res_prop_simpl_given                  true
% 11.20/2.01  --res_passive_queue_type                priority_queues
% 11.20/2.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.20/2.01  --res_passive_queues_freq               [15;5]
% 11.20/2.01  --res_forward_subs                      full
% 11.20/2.01  --res_backward_subs                     full
% 11.20/2.01  --res_forward_subs_resolution           true
% 11.20/2.01  --res_backward_subs_resolution          true
% 11.20/2.01  --res_orphan_elimination                true
% 11.20/2.01  --res_time_limit                        2.
% 11.20/2.01  --res_out_proof                         true
% 11.20/2.01  
% 11.20/2.01  ------ Superposition Options
% 11.20/2.01  
% 11.20/2.01  --superposition_flag                    true
% 11.20/2.01  --sup_passive_queue_type                priority_queues
% 11.20/2.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.20/2.01  --sup_passive_queues_freq               [8;1;4]
% 11.20/2.01  --demod_completeness_check              fast
% 11.20/2.01  --demod_use_ground                      true
% 11.20/2.01  --sup_to_prop_solver                    passive
% 11.20/2.01  --sup_prop_simpl_new                    true
% 11.20/2.01  --sup_prop_simpl_given                  true
% 11.20/2.01  --sup_fun_splitting                     true
% 11.20/2.01  --sup_smt_interval                      50000
% 11.20/2.01  
% 11.20/2.01  ------ Superposition Simplification Setup
% 11.20/2.01  
% 11.20/2.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.20/2.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.20/2.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.20/2.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.20/2.01  --sup_full_triv                         [TrivRules;PropSubs]
% 11.20/2.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.20/2.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.20/2.01  --sup_immed_triv                        [TrivRules]
% 11.20/2.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.20/2.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.20/2.01  --sup_immed_bw_main                     []
% 11.20/2.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.20/2.01  --sup_input_triv                        [Unflattening;TrivRules]
% 11.20/2.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.20/2.01  --sup_input_bw                          []
% 11.20/2.01  
% 11.20/2.01  ------ Combination Options
% 11.20/2.01  
% 11.20/2.01  --comb_res_mult                         3
% 11.20/2.01  --comb_sup_mult                         2
% 11.20/2.01  --comb_inst_mult                        10
% 11.20/2.01  
% 11.20/2.01  ------ Debug Options
% 11.20/2.01  
% 11.20/2.01  --dbg_backtrace                         false
% 11.20/2.01  --dbg_dump_prop_clauses                 false
% 11.20/2.01  --dbg_dump_prop_clauses_file            -
% 11.20/2.01  --dbg_out_stat                          false
% 11.20/2.01  ------ Parsing...
% 11.20/2.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.20/2.01  
% 11.20/2.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 11.20/2.01  
% 11.20/2.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.20/2.01  
% 11.20/2.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.20/2.01  ------ Proving...
% 11.20/2.01  ------ Problem Properties 
% 11.20/2.01  
% 11.20/2.01  
% 11.20/2.01  clauses                                 33
% 11.20/2.01  conjectures                             11
% 11.20/2.01  EPR                                     7
% 11.20/2.01  Horn                                    29
% 11.20/2.01  unary                                   16
% 11.20/2.01  binary                                  3
% 11.20/2.01  lits                                    121
% 11.20/2.01  lits eq                                 30
% 11.20/2.01  fd_pure                                 0
% 11.20/2.01  fd_pseudo                               0
% 11.20/2.01  fd_cond                                 4
% 11.20/2.01  fd_pseudo_cond                          1
% 11.20/2.01  AC symbols                              0
% 11.20/2.01  
% 11.20/2.01  ------ Schedule dynamic 5 is on 
% 11.20/2.01  
% 11.20/2.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.20/2.01  
% 11.20/2.01  
% 11.20/2.01  ------ 
% 11.20/2.01  Current options:
% 11.20/2.01  ------ 
% 11.20/2.01  
% 11.20/2.01  ------ Input Options
% 11.20/2.01  
% 11.20/2.01  --out_options                           all
% 11.20/2.01  --tptp_safe_out                         true
% 11.20/2.01  --problem_path                          ""
% 11.20/2.01  --include_path                          ""
% 11.20/2.01  --clausifier                            res/vclausify_rel
% 11.20/2.01  --clausifier_options                    ""
% 11.20/2.01  --stdin                                 false
% 11.20/2.01  --stats_out                             all
% 11.20/2.01  
% 11.20/2.01  ------ General Options
% 11.20/2.01  
% 11.20/2.01  --fof                                   false
% 11.20/2.01  --time_out_real                         305.
% 11.20/2.01  --time_out_virtual                      -1.
% 11.20/2.01  --symbol_type_check                     false
% 11.20/2.01  --clausify_out                          false
% 11.20/2.01  --sig_cnt_out                           false
% 11.20/2.01  --trig_cnt_out                          false
% 11.20/2.01  --trig_cnt_out_tolerance                1.
% 11.20/2.01  --trig_cnt_out_sk_spl                   false
% 11.20/2.01  --abstr_cl_out                          false
% 11.20/2.01  
% 11.20/2.01  ------ Global Options
% 11.20/2.01  
% 11.20/2.01  --schedule                              default
% 11.20/2.01  --add_important_lit                     false
% 11.20/2.01  --prop_solver_per_cl                    1000
% 11.20/2.01  --min_unsat_core                        false
% 11.20/2.01  --soft_assumptions                      false
% 11.20/2.01  --soft_lemma_size                       3
% 11.20/2.01  --prop_impl_unit_size                   0
% 11.20/2.01  --prop_impl_unit                        []
% 11.20/2.01  --share_sel_clauses                     true
% 11.20/2.01  --reset_solvers                         false
% 11.20/2.01  --bc_imp_inh                            [conj_cone]
% 11.20/2.01  --conj_cone_tolerance                   3.
% 11.20/2.01  --extra_neg_conj                        none
% 11.20/2.01  --large_theory_mode                     true
% 11.20/2.01  --prolific_symb_bound                   200
% 11.20/2.01  --lt_threshold                          2000
% 11.20/2.01  --clause_weak_htbl                      true
% 11.20/2.01  --gc_record_bc_elim                     false
% 11.20/2.01  
% 11.20/2.01  ------ Preprocessing Options
% 11.20/2.01  
% 11.20/2.01  --preprocessing_flag                    true
% 11.20/2.01  --time_out_prep_mult                    0.1
% 11.20/2.01  --splitting_mode                        input
% 11.20/2.01  --splitting_grd                         true
% 11.20/2.01  --splitting_cvd                         false
% 11.20/2.01  --splitting_cvd_svl                     false
% 11.20/2.01  --splitting_nvd                         32
% 11.20/2.01  --sub_typing                            true
% 11.20/2.01  --prep_gs_sim                           true
% 11.20/2.01  --prep_unflatten                        true
% 11.20/2.01  --prep_res_sim                          true
% 11.20/2.01  --prep_upred                            true
% 11.20/2.01  --prep_sem_filter                       exhaustive
% 11.20/2.01  --prep_sem_filter_out                   false
% 11.20/2.01  --pred_elim                             true
% 11.20/2.01  --res_sim_input                         true
% 11.20/2.01  --eq_ax_congr_red                       true
% 11.20/2.01  --pure_diseq_elim                       true
% 11.20/2.01  --brand_transform                       false
% 11.20/2.01  --non_eq_to_eq                          false
% 11.20/2.01  --prep_def_merge                        true
% 11.20/2.01  --prep_def_merge_prop_impl              false
% 11.20/2.01  --prep_def_merge_mbd                    true
% 11.20/2.01  --prep_def_merge_tr_red                 false
% 11.20/2.01  --prep_def_merge_tr_cl                  false
% 11.20/2.01  --smt_preprocessing                     true
% 11.20/2.01  --smt_ac_axioms                         fast
% 11.20/2.01  --preprocessed_out                      false
% 11.20/2.01  --preprocessed_stats                    false
% 11.20/2.01  
% 11.20/2.01  ------ Abstraction refinement Options
% 11.20/2.01  
% 11.20/2.01  --abstr_ref                             []
% 11.20/2.01  --abstr_ref_prep                        false
% 11.20/2.01  --abstr_ref_until_sat                   false
% 11.20/2.01  --abstr_ref_sig_restrict                funpre
% 11.20/2.01  --abstr_ref_af_restrict_to_split_sk     false
% 11.20/2.01  --abstr_ref_under                       []
% 11.20/2.01  
% 11.20/2.01  ------ SAT Options
% 11.20/2.01  
% 11.20/2.01  --sat_mode                              false
% 11.20/2.01  --sat_fm_restart_options                ""
% 11.20/2.01  --sat_gr_def                            false
% 11.20/2.01  --sat_epr_types                         true
% 11.20/2.01  --sat_non_cyclic_types                  false
% 11.20/2.01  --sat_finite_models                     false
% 11.20/2.01  --sat_fm_lemmas                         false
% 11.20/2.01  --sat_fm_prep                           false
% 11.20/2.01  --sat_fm_uc_incr                        true
% 11.20/2.01  --sat_out_model                         small
% 11.20/2.01  --sat_out_clauses                       false
% 11.20/2.01  
% 11.20/2.01  ------ QBF Options
% 11.20/2.01  
% 11.20/2.01  --qbf_mode                              false
% 11.20/2.01  --qbf_elim_univ                         false
% 11.20/2.01  --qbf_dom_inst                          none
% 11.20/2.01  --qbf_dom_pre_inst                      false
% 11.20/2.01  --qbf_sk_in                             false
% 11.20/2.01  --qbf_pred_elim                         true
% 11.20/2.01  --qbf_split                             512
% 11.20/2.01  
% 11.20/2.01  ------ BMC1 Options
% 11.20/2.01  
% 11.20/2.01  --bmc1_incremental                      false
% 11.20/2.01  --bmc1_axioms                           reachable_all
% 11.20/2.01  --bmc1_min_bound                        0
% 11.20/2.01  --bmc1_max_bound                        -1
% 11.20/2.01  --bmc1_max_bound_default                -1
% 11.20/2.01  --bmc1_symbol_reachability              true
% 11.20/2.01  --bmc1_property_lemmas                  false
% 11.20/2.01  --bmc1_k_induction                      false
% 11.20/2.01  --bmc1_non_equiv_states                 false
% 11.20/2.01  --bmc1_deadlock                         false
% 11.20/2.01  --bmc1_ucm                              false
% 11.20/2.01  --bmc1_add_unsat_core                   none
% 11.20/2.01  --bmc1_unsat_core_children              false
% 11.20/2.01  --bmc1_unsat_core_extrapolate_axioms    false
% 11.20/2.01  --bmc1_out_stat                         full
% 11.20/2.01  --bmc1_ground_init                      false
% 11.20/2.01  --bmc1_pre_inst_next_state              false
% 11.20/2.01  --bmc1_pre_inst_state                   false
% 11.20/2.01  --bmc1_pre_inst_reach_state             false
% 11.20/2.01  --bmc1_out_unsat_core                   false
% 11.20/2.01  --bmc1_aig_witness_out                  false
% 11.20/2.01  --bmc1_verbose                          false
% 11.20/2.01  --bmc1_dump_clauses_tptp                false
% 11.20/2.01  --bmc1_dump_unsat_core_tptp             false
% 11.20/2.01  --bmc1_dump_file                        -
% 11.20/2.01  --bmc1_ucm_expand_uc_limit              128
% 11.20/2.01  --bmc1_ucm_n_expand_iterations          6
% 11.20/2.01  --bmc1_ucm_extend_mode                  1
% 11.20/2.01  --bmc1_ucm_init_mode                    2
% 11.20/2.01  --bmc1_ucm_cone_mode                    none
% 11.20/2.01  --bmc1_ucm_reduced_relation_type        0
% 11.20/2.01  --bmc1_ucm_relax_model                  4
% 11.20/2.01  --bmc1_ucm_full_tr_after_sat            true
% 11.20/2.01  --bmc1_ucm_expand_neg_assumptions       false
% 11.20/2.01  --bmc1_ucm_layered_model                none
% 11.20/2.01  --bmc1_ucm_max_lemma_size               10
% 11.20/2.01  
% 11.20/2.01  ------ AIG Options
% 11.20/2.01  
% 11.20/2.01  --aig_mode                              false
% 11.20/2.01  
% 11.20/2.01  ------ Instantiation Options
% 11.20/2.01  
% 11.20/2.01  --instantiation_flag                    true
% 11.20/2.01  --inst_sos_flag                         true
% 11.20/2.01  --inst_sos_phase                        true
% 11.20/2.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.20/2.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.20/2.01  --inst_lit_sel_side                     none
% 11.20/2.01  --inst_solver_per_active                1400
% 11.20/2.01  --inst_solver_calls_frac                1.
% 11.20/2.01  --inst_passive_queue_type               priority_queues
% 11.20/2.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.20/2.01  --inst_passive_queues_freq              [25;2]
% 11.20/2.01  --inst_dismatching                      true
% 11.20/2.01  --inst_eager_unprocessed_to_passive     true
% 11.20/2.01  --inst_prop_sim_given                   true
% 11.20/2.01  --inst_prop_sim_new                     false
% 11.20/2.01  --inst_subs_new                         false
% 11.20/2.01  --inst_eq_res_simp                      false
% 11.20/2.01  --inst_subs_given                       false
% 11.20/2.01  --inst_orphan_elimination               true
% 11.20/2.01  --inst_learning_loop_flag               true
% 11.20/2.01  --inst_learning_start                   3000
% 11.20/2.01  --inst_learning_factor                  2
% 11.20/2.01  --inst_start_prop_sim_after_learn       3
% 11.20/2.01  --inst_sel_renew                        solver
% 11.20/2.01  --inst_lit_activity_flag                true
% 11.20/2.01  --inst_restr_to_given                   false
% 11.20/2.01  --inst_activity_threshold               500
% 11.20/2.01  --inst_out_proof                        true
% 11.20/2.01  
% 11.20/2.01  ------ Resolution Options
% 11.20/2.01  
% 11.20/2.01  --resolution_flag                       false
% 11.20/2.01  --res_lit_sel                           adaptive
% 11.20/2.01  --res_lit_sel_side                      none
% 11.20/2.01  --res_ordering                          kbo
% 11.20/2.01  --res_to_prop_solver                    active
% 11.20/2.01  --res_prop_simpl_new                    false
% 11.20/2.01  --res_prop_simpl_given                  true
% 11.20/2.01  --res_passive_queue_type                priority_queues
% 11.20/2.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.20/2.01  --res_passive_queues_freq               [15;5]
% 11.20/2.01  --res_forward_subs                      full
% 11.20/2.01  --res_backward_subs                     full
% 11.20/2.01  --res_forward_subs_resolution           true
% 11.20/2.01  --res_backward_subs_resolution          true
% 11.20/2.01  --res_orphan_elimination                true
% 11.20/2.01  --res_time_limit                        2.
% 11.20/2.01  --res_out_proof                         true
% 11.20/2.01  
% 11.20/2.01  ------ Superposition Options
% 11.20/2.01  
% 11.20/2.01  --superposition_flag                    true
% 11.20/2.01  --sup_passive_queue_type                priority_queues
% 11.20/2.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.20/2.01  --sup_passive_queues_freq               [8;1;4]
% 11.20/2.01  --demod_completeness_check              fast
% 11.20/2.01  --demod_use_ground                      true
% 11.20/2.01  --sup_to_prop_solver                    passive
% 11.20/2.01  --sup_prop_simpl_new                    true
% 11.20/2.01  --sup_prop_simpl_given                  true
% 11.20/2.01  --sup_fun_splitting                     true
% 11.20/2.01  --sup_smt_interval                      50000
% 11.20/2.01  
% 11.20/2.01  ------ Superposition Simplification Setup
% 11.20/2.01  
% 11.20/2.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.20/2.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.20/2.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.20/2.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.20/2.01  --sup_full_triv                         [TrivRules;PropSubs]
% 11.20/2.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.20/2.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.20/2.01  --sup_immed_triv                        [TrivRules]
% 11.20/2.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.20/2.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.20/2.01  --sup_immed_bw_main                     []
% 11.20/2.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.20/2.01  --sup_input_triv                        [Unflattening;TrivRules]
% 11.20/2.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.20/2.01  --sup_input_bw                          []
% 11.20/2.01  
% 11.20/2.01  ------ Combination Options
% 11.20/2.01  
% 11.20/2.01  --comb_res_mult                         3
% 11.20/2.01  --comb_sup_mult                         2
% 11.20/2.01  --comb_inst_mult                        10
% 11.20/2.01  
% 11.20/2.01  ------ Debug Options
% 11.20/2.01  
% 11.20/2.01  --dbg_backtrace                         false
% 11.20/2.01  --dbg_dump_prop_clauses                 false
% 11.20/2.01  --dbg_dump_prop_clauses_file            -
% 11.20/2.01  --dbg_out_stat                          false
% 11.20/2.01  
% 11.20/2.01  
% 11.20/2.01  
% 11.20/2.01  
% 11.20/2.01  ------ Proving...
% 11.20/2.01  
% 11.20/2.01  
% 11.20/2.01  % SZS status Theorem for theBenchmark.p
% 11.20/2.01  
% 11.20/2.01  % SZS output start CNFRefutation for theBenchmark.p
% 11.20/2.01  
% 11.20/2.01  fof(f12,axiom,(
% 11.20/2.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 11.20/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.20/2.01  
% 11.20/2.01  fof(f30,plain,(
% 11.20/2.01    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 11.20/2.01    inference(ennf_transformation,[],[f12])).
% 11.20/2.01  
% 11.20/2.01  fof(f31,plain,(
% 11.20/2.01    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 11.20/2.01    inference(flattening,[],[f30])).
% 11.20/2.01  
% 11.20/2.01  fof(f58,plain,(
% 11.20/2.01    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 11.20/2.01    inference(cnf_transformation,[],[f31])).
% 11.20/2.01  
% 11.20/2.01  fof(f15,conjecture,(
% 11.20/2.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 11.20/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.20/2.01  
% 11.20/2.01  fof(f16,negated_conjecture,(
% 11.20/2.01    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 11.20/2.01    inference(negated_conjecture,[],[f15])).
% 11.20/2.01  
% 11.20/2.01  fof(f36,plain,(
% 11.20/2.01    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 11.20/2.01    inference(ennf_transformation,[],[f16])).
% 11.20/2.01  
% 11.20/2.01  fof(f37,plain,(
% 11.20/2.01    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 11.20/2.01    inference(flattening,[],[f36])).
% 11.20/2.01  
% 11.20/2.01  fof(f40,plain,(
% 11.20/2.01    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 11.20/2.01    introduced(choice_axiom,[])).
% 11.20/2.01  
% 11.20/2.01  fof(f39,plain,(
% 11.20/2.01    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 11.20/2.01    introduced(choice_axiom,[])).
% 11.20/2.01  
% 11.20/2.01  fof(f41,plain,(
% 11.20/2.01    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 11.20/2.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f37,f40,f39])).
% 11.20/2.01  
% 11.20/2.01  fof(f72,plain,(
% 11.20/2.01    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 11.20/2.01    inference(cnf_transformation,[],[f41])).
% 11.20/2.01  
% 11.20/2.01  fof(f65,plain,(
% 11.20/2.01    v1_funct_1(sK2)),
% 11.20/2.01    inference(cnf_transformation,[],[f41])).
% 11.20/2.01  
% 11.20/2.01  fof(f66,plain,(
% 11.20/2.01    v1_funct_2(sK2,sK0,sK1)),
% 11.20/2.01    inference(cnf_transformation,[],[f41])).
% 11.20/2.01  
% 11.20/2.01  fof(f67,plain,(
% 11.20/2.01    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 11.20/2.01    inference(cnf_transformation,[],[f41])).
% 11.20/2.01  
% 11.20/2.01  fof(f68,plain,(
% 11.20/2.01    v1_funct_1(sK3)),
% 11.20/2.01    inference(cnf_transformation,[],[f41])).
% 11.20/2.01  
% 11.20/2.01  fof(f69,plain,(
% 11.20/2.01    v1_funct_2(sK3,sK1,sK0)),
% 11.20/2.01    inference(cnf_transformation,[],[f41])).
% 11.20/2.01  
% 11.20/2.01  fof(f70,plain,(
% 11.20/2.01    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 11.20/2.01    inference(cnf_transformation,[],[f41])).
% 11.20/2.01  
% 11.20/2.01  fof(f14,axiom,(
% 11.20/2.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 11.20/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.20/2.01  
% 11.20/2.01  fof(f34,plain,(
% 11.20/2.01    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 11.20/2.01    inference(ennf_transformation,[],[f14])).
% 11.20/2.01  
% 11.20/2.01  fof(f35,plain,(
% 11.20/2.01    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 11.20/2.01    inference(flattening,[],[f34])).
% 11.20/2.01  
% 11.20/2.01  fof(f63,plain,(
% 11.20/2.01    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 11.20/2.01    inference(cnf_transformation,[],[f35])).
% 11.20/2.01  
% 11.20/2.01  fof(f74,plain,(
% 11.20/2.01    k1_xboole_0 != sK0),
% 11.20/2.01    inference(cnf_transformation,[],[f41])).
% 11.20/2.01  
% 11.20/2.01  fof(f2,axiom,(
% 11.20/2.01    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 11.20/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.20/2.01  
% 11.20/2.01  fof(f45,plain,(
% 11.20/2.01    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 11.20/2.01    inference(cnf_transformation,[],[f2])).
% 11.20/2.01  
% 11.20/2.01  fof(f11,axiom,(
% 11.20/2.01    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 11.20/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.20/2.01  
% 11.20/2.01  fof(f57,plain,(
% 11.20/2.01    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 11.20/2.01    inference(cnf_transformation,[],[f11])).
% 11.20/2.01  
% 11.20/2.01  fof(f79,plain,(
% 11.20/2.01    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 11.20/2.01    inference(definition_unfolding,[],[f45,f57])).
% 11.20/2.01  
% 11.20/2.01  fof(f7,axiom,(
% 11.20/2.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 11.20/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.20/2.01  
% 11.20/2.01  fof(f24,plain,(
% 11.20/2.01    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 11.20/2.01    inference(ennf_transformation,[],[f7])).
% 11.20/2.01  
% 11.20/2.01  fof(f25,plain,(
% 11.20/2.01    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.20/2.01    inference(flattening,[],[f24])).
% 11.20/2.01  
% 11.20/2.01  fof(f38,plain,(
% 11.20/2.01    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.20/2.01    inference(nnf_transformation,[],[f25])).
% 11.20/2.01  
% 11.20/2.01  fof(f51,plain,(
% 11.20/2.01    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.20/2.01    inference(cnf_transformation,[],[f38])).
% 11.20/2.01  
% 11.20/2.01  fof(f9,axiom,(
% 11.20/2.01    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 11.20/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.20/2.01  
% 11.20/2.01  fof(f17,plain,(
% 11.20/2.01    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 11.20/2.01    inference(pure_predicate_removal,[],[f9])).
% 11.20/2.01  
% 11.20/2.01  fof(f55,plain,(
% 11.20/2.01    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 11.20/2.01    inference(cnf_transformation,[],[f17])).
% 11.20/2.01  
% 11.20/2.01  fof(f8,axiom,(
% 11.20/2.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 11.20/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.20/2.01  
% 11.20/2.01  fof(f26,plain,(
% 11.20/2.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 11.20/2.01    inference(ennf_transformation,[],[f8])).
% 11.20/2.01  
% 11.20/2.01  fof(f27,plain,(
% 11.20/2.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 11.20/2.01    inference(flattening,[],[f26])).
% 11.20/2.01  
% 11.20/2.01  fof(f54,plain,(
% 11.20/2.01    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 11.20/2.01    inference(cnf_transformation,[],[f27])).
% 11.20/2.01  
% 11.20/2.01  fof(f71,plain,(
% 11.20/2.01    k2_relset_1(sK0,sK1,sK2) = sK1),
% 11.20/2.01    inference(cnf_transformation,[],[f41])).
% 11.20/2.01  
% 11.20/2.01  fof(f13,axiom,(
% 11.20/2.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 11.20/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.20/2.01  
% 11.20/2.01  fof(f32,plain,(
% 11.20/2.01    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 11.20/2.01    inference(ennf_transformation,[],[f13])).
% 11.20/2.01  
% 11.20/2.01  fof(f33,plain,(
% 11.20/2.01    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 11.20/2.01    inference(flattening,[],[f32])).
% 11.20/2.01  
% 11.20/2.01  fof(f61,plain,(
% 11.20/2.01    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X4) | k1_xboole_0 = X2 | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 11.20/2.01    inference(cnf_transformation,[],[f33])).
% 11.20/2.01  
% 11.20/2.01  fof(f4,axiom,(
% 11.20/2.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 11.20/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.20/2.01  
% 11.20/2.01  fof(f20,plain,(
% 11.20/2.01    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.20/2.01    inference(ennf_transformation,[],[f4])).
% 11.20/2.01  
% 11.20/2.01  fof(f21,plain,(
% 11.20/2.01    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.20/2.01    inference(flattening,[],[f20])).
% 11.20/2.01  
% 11.20/2.01  fof(f48,plain,(
% 11.20/2.01    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.20/2.01    inference(cnf_transformation,[],[f21])).
% 11.20/2.01  
% 11.20/2.01  fof(f81,plain,(
% 11.20/2.01    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.20/2.01    inference(definition_unfolding,[],[f48,f57])).
% 11.20/2.01  
% 11.20/2.01  fof(f6,axiom,(
% 11.20/2.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 11.20/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.20/2.01  
% 11.20/2.01  fof(f23,plain,(
% 11.20/2.01    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.20/2.01    inference(ennf_transformation,[],[f6])).
% 11.20/2.01  
% 11.20/2.01  fof(f50,plain,(
% 11.20/2.01    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.20/2.01    inference(cnf_transformation,[],[f23])).
% 11.20/2.01  
% 11.20/2.01  fof(f73,plain,(
% 11.20/2.01    v2_funct_1(sK2)),
% 11.20/2.01    inference(cnf_transformation,[],[f41])).
% 11.20/2.01  
% 11.20/2.01  fof(f5,axiom,(
% 11.20/2.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 11.20/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.20/2.01  
% 11.20/2.01  fof(f22,plain,(
% 11.20/2.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.20/2.01    inference(ennf_transformation,[],[f5])).
% 11.20/2.01  
% 11.20/2.01  fof(f49,plain,(
% 11.20/2.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.20/2.01    inference(cnf_transformation,[],[f22])).
% 11.20/2.01  
% 11.20/2.01  fof(f10,axiom,(
% 11.20/2.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 11.20/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.20/2.01  
% 11.20/2.01  fof(f28,plain,(
% 11.20/2.01    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 11.20/2.01    inference(ennf_transformation,[],[f10])).
% 11.20/2.01  
% 11.20/2.01  fof(f29,plain,(
% 11.20/2.01    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 11.20/2.01    inference(flattening,[],[f28])).
% 11.20/2.01  
% 11.20/2.01  fof(f56,plain,(
% 11.20/2.01    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 11.20/2.01    inference(cnf_transformation,[],[f29])).
% 11.20/2.01  
% 11.20/2.01  fof(f3,axiom,(
% 11.20/2.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 11.20/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.20/2.01  
% 11.20/2.01  fof(f18,plain,(
% 11.20/2.01    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.20/2.01    inference(ennf_transformation,[],[f3])).
% 11.20/2.01  
% 11.20/2.01  fof(f19,plain,(
% 11.20/2.01    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.20/2.01    inference(flattening,[],[f18])).
% 11.20/2.01  
% 11.20/2.01  fof(f47,plain,(
% 11.20/2.01    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.20/2.01    inference(cnf_transformation,[],[f19])).
% 11.20/2.01  
% 11.20/2.01  fof(f1,axiom,(
% 11.20/2.01    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 11.20/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.20/2.01  
% 11.20/2.01  fof(f43,plain,(
% 11.20/2.01    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 11.20/2.01    inference(cnf_transformation,[],[f1])).
% 11.20/2.01  
% 11.20/2.01  fof(f77,plain,(
% 11.20/2.01    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 11.20/2.01    inference(definition_unfolding,[],[f43,f57])).
% 11.20/2.01  
% 11.20/2.01  fof(f75,plain,(
% 11.20/2.01    k1_xboole_0 != sK1),
% 11.20/2.01    inference(cnf_transformation,[],[f41])).
% 11.20/2.01  
% 11.20/2.01  fof(f46,plain,(
% 11.20/2.01    ( ! [X0] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.20/2.01    inference(cnf_transformation,[],[f19])).
% 11.20/2.01  
% 11.20/2.01  fof(f42,plain,(
% 11.20/2.01    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 11.20/2.01    inference(cnf_transformation,[],[f1])).
% 11.20/2.01  
% 11.20/2.01  fof(f78,plain,(
% 11.20/2.01    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 11.20/2.01    inference(definition_unfolding,[],[f42,f57])).
% 11.20/2.01  
% 11.20/2.01  fof(f76,plain,(
% 11.20/2.01    k2_funct_1(sK2) != sK3),
% 11.20/2.01    inference(cnf_transformation,[],[f41])).
% 11.20/2.01  
% 11.20/2.01  cnf(c_15,plain,
% 11.20/2.01      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 11.20/2.01      | ~ v1_funct_2(X2,X0,X1)
% 11.20/2.01      | ~ v1_funct_2(X3,X1,X0)
% 11.20/2.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 11.20/2.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.20/2.01      | ~ v1_funct_1(X2)
% 11.20/2.01      | ~ v1_funct_1(X3)
% 11.20/2.01      | k2_relset_1(X1,X0,X3) = X0 ),
% 11.20/2.01      inference(cnf_transformation,[],[f58]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_26,negated_conjecture,
% 11.20/2.01      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 11.20/2.01      inference(cnf_transformation,[],[f72]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_367,plain,
% 11.20/2.01      ( ~ v1_funct_2(X0,X1,X2)
% 11.20/2.01      | ~ v1_funct_2(X3,X2,X1)
% 11.20/2.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 11.20/2.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.20/2.01      | ~ v1_funct_1(X0)
% 11.20/2.01      | ~ v1_funct_1(X3)
% 11.20/2.01      | k1_partfun1(X2,X1,X1,X2,X3,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 11.20/2.01      | k2_relset_1(X1,X2,X0) = X2
% 11.20/2.01      | k6_partfun1(X2) != k6_partfun1(sK0)
% 11.20/2.01      | sK0 != X2 ),
% 11.20/2.01      inference(resolution_lifted,[status(thm)],[c_15,c_26]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_368,plain,
% 11.20/2.01      ( ~ v1_funct_2(X0,X1,sK0)
% 11.20/2.01      | ~ v1_funct_2(X2,sK0,X1)
% 11.20/2.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 11.20/2.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 11.20/2.01      | ~ v1_funct_1(X0)
% 11.20/2.01      | ~ v1_funct_1(X2)
% 11.20/2.01      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 11.20/2.01      | k2_relset_1(X1,sK0,X0) = sK0
% 11.20/2.01      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 11.20/2.01      inference(unflattening,[status(thm)],[c_367]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_449,plain,
% 11.20/2.01      ( ~ v1_funct_2(X0,X1,sK0)
% 11.20/2.01      | ~ v1_funct_2(X2,sK0,X1)
% 11.20/2.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 11.20/2.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 11.20/2.01      | ~ v1_funct_1(X0)
% 11.20/2.01      | ~ v1_funct_1(X2)
% 11.20/2.01      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 11.20/2.01      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 11.20/2.01      inference(equality_resolution_simp,[status(thm)],[c_368]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_1066,plain,
% 11.20/2.01      ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 11.20/2.01      | k2_relset_1(X0,sK0,X2) = sK0
% 11.20/2.01      | v1_funct_2(X2,X0,sK0) != iProver_top
% 11.20/2.01      | v1_funct_2(X1,sK0,X0) != iProver_top
% 11.20/2.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 11.20/2.01      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 11.20/2.01      | v1_funct_1(X2) != iProver_top
% 11.20/2.01      | v1_funct_1(X1) != iProver_top ),
% 11.20/2.01      inference(predicate_to_equality,[status(thm)],[c_449]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_1596,plain,
% 11.20/2.01      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 11.20/2.01      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 11.20/2.01      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 11.20/2.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 11.20/2.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 11.20/2.01      | v1_funct_1(sK3) != iProver_top
% 11.20/2.01      | v1_funct_1(sK2) != iProver_top ),
% 11.20/2.01      inference(equality_resolution,[status(thm)],[c_1066]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_33,negated_conjecture,
% 11.20/2.01      ( v1_funct_1(sK2) ),
% 11.20/2.01      inference(cnf_transformation,[],[f65]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_34,plain,
% 11.20/2.01      ( v1_funct_1(sK2) = iProver_top ),
% 11.20/2.01      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_32,negated_conjecture,
% 11.20/2.01      ( v1_funct_2(sK2,sK0,sK1) ),
% 11.20/2.01      inference(cnf_transformation,[],[f66]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_35,plain,
% 11.20/2.01      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 11.20/2.01      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_31,negated_conjecture,
% 11.20/2.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 11.20/2.01      inference(cnf_transformation,[],[f67]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_36,plain,
% 11.20/2.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 11.20/2.01      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_30,negated_conjecture,
% 11.20/2.01      ( v1_funct_1(sK3) ),
% 11.20/2.01      inference(cnf_transformation,[],[f68]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_37,plain,
% 11.20/2.01      ( v1_funct_1(sK3) = iProver_top ),
% 11.20/2.01      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_29,negated_conjecture,
% 11.20/2.01      ( v1_funct_2(sK3,sK1,sK0) ),
% 11.20/2.01      inference(cnf_transformation,[],[f69]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_38,plain,
% 11.20/2.01      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 11.20/2.01      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_28,negated_conjecture,
% 11.20/2.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 11.20/2.01      inference(cnf_transformation,[],[f70]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_39,plain,
% 11.20/2.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 11.20/2.01      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_1765,plain,
% 11.20/2.01      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 11.20/2.01      inference(global_propositional_subsumption,
% 11.20/2.01                [status(thm)],
% 11.20/2.01                [c_1596,c_34,c_35,c_36,c_37,c_38,c_39]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_21,plain,
% 11.20/2.01      ( ~ v1_funct_2(X0,X1,X2)
% 11.20/2.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.20/2.01      | ~ v1_funct_1(X0)
% 11.20/2.01      | ~ v2_funct_1(X0)
% 11.20/2.01      | k2_relset_1(X1,X2,X0) != X2
% 11.20/2.01      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 11.20/2.01      | k1_xboole_0 = X2 ),
% 11.20/2.01      inference(cnf_transformation,[],[f63]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_1076,plain,
% 11.20/2.01      ( k2_relset_1(X0,X1,X2) != X1
% 11.20/2.01      | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
% 11.20/2.01      | k1_xboole_0 = X1
% 11.20/2.01      | v1_funct_2(X2,X0,X1) != iProver_top
% 11.20/2.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.20/2.01      | v1_funct_1(X2) != iProver_top
% 11.20/2.01      | v2_funct_1(X2) != iProver_top ),
% 11.20/2.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_2673,plain,
% 11.20/2.01      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 11.20/2.01      | sK0 = k1_xboole_0
% 11.20/2.01      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 11.20/2.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 11.20/2.01      | v1_funct_1(sK3) != iProver_top
% 11.20/2.01      | v2_funct_1(sK3) != iProver_top ),
% 11.20/2.01      inference(superposition,[status(thm)],[c_1765,c_1076]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_24,negated_conjecture,
% 11.20/2.01      ( k1_xboole_0 != sK0 ),
% 11.20/2.01      inference(cnf_transformation,[],[f74]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_608,plain,( X0 = X0 ),theory(equality) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_639,plain,
% 11.20/2.01      ( k1_xboole_0 = k1_xboole_0 ),
% 11.20/2.01      inference(instantiation,[status(thm)],[c_608]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_609,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_1172,plain,
% 11.20/2.01      ( sK0 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK0 ),
% 11.20/2.01      inference(instantiation,[status(thm)],[c_609]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_1173,plain,
% 11.20/2.01      ( sK0 != k1_xboole_0
% 11.20/2.01      | k1_xboole_0 = sK0
% 11.20/2.01      | k1_xboole_0 != k1_xboole_0 ),
% 11.20/2.01      inference(instantiation,[status(thm)],[c_1172]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_2,plain,
% 11.20/2.01      ( v2_funct_1(k6_partfun1(X0)) ),
% 11.20/2.01      inference(cnf_transformation,[],[f79]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_4709,plain,
% 11.20/2.01      ( v2_funct_1(k6_partfun1(sK0)) ),
% 11.20/2.01      inference(instantiation,[status(thm)],[c_2]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_4710,plain,
% 11.20/2.01      ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
% 11.20/2.01      inference(predicate_to_equality,[status(thm)],[c_4709]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_10,plain,
% 11.20/2.01      ( ~ r2_relset_1(X0,X1,X2,X3)
% 11.20/2.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.20/2.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.20/2.01      | X3 = X2 ),
% 11.20/2.01      inference(cnf_transformation,[],[f51]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_354,plain,
% 11.20/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.20/2.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.20/2.01      | X3 = X0
% 11.20/2.01      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 11.20/2.01      | k6_partfun1(sK0) != X3
% 11.20/2.01      | sK0 != X2
% 11.20/2.01      | sK0 != X1 ),
% 11.20/2.01      inference(resolution_lifted,[status(thm)],[c_10,c_26]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_355,plain,
% 11.20/2.01      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.20/2.01      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.20/2.01      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 11.20/2.01      inference(unflattening,[status(thm)],[c_354]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_13,plain,
% 11.20/2.01      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 11.20/2.01      inference(cnf_transformation,[],[f55]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_363,plain,
% 11.20/2.01      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.20/2.01      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 11.20/2.01      inference(forward_subsumption_resolution,
% 11.20/2.01                [status(thm)],
% 11.20/2.01                [c_355,c_13]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_1067,plain,
% 11.20/2.01      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 11.20/2.01      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 11.20/2.01      inference(predicate_to_equality,[status(thm)],[c_363]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_11,plain,
% 11.20/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.20/2.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 11.20/2.01      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 11.20/2.01      | ~ v1_funct_1(X0)
% 11.20/2.01      | ~ v1_funct_1(X3) ),
% 11.20/2.01      inference(cnf_transformation,[],[f54]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_1174,plain,
% 11.20/2.01      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.20/2.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 11.20/2.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 11.20/2.01      | ~ v1_funct_1(sK3)
% 11.20/2.01      | ~ v1_funct_1(sK2) ),
% 11.20/2.01      inference(instantiation,[status(thm)],[c_11]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_1758,plain,
% 11.20/2.01      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 11.20/2.01      inference(global_propositional_subsumption,
% 11.20/2.01                [status(thm)],
% 11.20/2.01                [c_1067,c_33,c_31,c_30,c_28,c_363,c_1174]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_27,negated_conjecture,
% 11.20/2.01      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 11.20/2.01      inference(cnf_transformation,[],[f71]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_17,plain,
% 11.20/2.01      ( ~ v1_funct_2(X0,X1,X2)
% 11.20/2.01      | ~ v1_funct_2(X3,X4,X1)
% 11.20/2.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 11.20/2.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.20/2.01      | ~ v1_funct_1(X0)
% 11.20/2.01      | ~ v1_funct_1(X3)
% 11.20/2.01      | v2_funct_1(X0)
% 11.20/2.01      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 11.20/2.01      | k2_relset_1(X4,X1,X3) != X1
% 11.20/2.01      | k1_xboole_0 = X2 ),
% 11.20/2.01      inference(cnf_transformation,[],[f61]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_1080,plain,
% 11.20/2.01      ( k2_relset_1(X0,X1,X2) != X1
% 11.20/2.01      | k1_xboole_0 = X3
% 11.20/2.01      | v1_funct_2(X4,X1,X3) != iProver_top
% 11.20/2.01      | v1_funct_2(X2,X0,X1) != iProver_top
% 11.20/2.01      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
% 11.20/2.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.20/2.01      | v1_funct_1(X4) != iProver_top
% 11.20/2.01      | v1_funct_1(X2) != iProver_top
% 11.20/2.01      | v2_funct_1(X4) = iProver_top
% 11.20/2.01      | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top ),
% 11.20/2.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_4850,plain,
% 11.20/2.01      ( k1_xboole_0 = X0
% 11.20/2.01      | v1_funct_2(X1,sK1,X0) != iProver_top
% 11.20/2.01      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 11.20/2.01      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 11.20/2.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 11.20/2.01      | v1_funct_1(X1) != iProver_top
% 11.20/2.01      | v1_funct_1(sK2) != iProver_top
% 11.20/2.01      | v2_funct_1(X1) = iProver_top
% 11.20/2.01      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
% 11.20/2.01      inference(superposition,[status(thm)],[c_27,c_1080]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_4857,plain,
% 11.20/2.01      ( v1_funct_1(X1) != iProver_top
% 11.20/2.01      | v1_funct_2(X1,sK1,X0) != iProver_top
% 11.20/2.01      | k1_xboole_0 = X0
% 11.20/2.01      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 11.20/2.01      | v2_funct_1(X1) = iProver_top
% 11.20/2.01      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
% 11.20/2.01      inference(global_propositional_subsumption,
% 11.20/2.01                [status(thm)],
% 11.20/2.01                [c_4850,c_34,c_35,c_36]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_4858,plain,
% 11.20/2.01      ( k1_xboole_0 = X0
% 11.20/2.01      | v1_funct_2(X1,sK1,X0) != iProver_top
% 11.20/2.01      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 11.20/2.01      | v1_funct_1(X1) != iProver_top
% 11.20/2.01      | v2_funct_1(X1) = iProver_top
% 11.20/2.01      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
% 11.20/2.01      inference(renaming,[status(thm)],[c_4857]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_4861,plain,
% 11.20/2.01      ( sK0 = k1_xboole_0
% 11.20/2.01      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 11.20/2.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 11.20/2.01      | v1_funct_1(sK3) != iProver_top
% 11.20/2.01      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 11.20/2.01      | v2_funct_1(sK3) = iProver_top ),
% 11.20/2.01      inference(superposition,[status(thm)],[c_1758,c_4858]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_5185,plain,
% 11.20/2.01      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
% 11.20/2.01      inference(global_propositional_subsumption,
% 11.20/2.01                [status(thm)],
% 11.20/2.01                [c_2673,c_37,c_38,c_39,c_24,c_639,c_1173,c_4710,c_4861]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_6,plain,
% 11.20/2.01      ( ~ v1_funct_1(X0)
% 11.20/2.01      | ~ v1_funct_1(X1)
% 11.20/2.01      | ~ v1_relat_1(X0)
% 11.20/2.01      | ~ v1_relat_1(X1)
% 11.20/2.01      | ~ v2_funct_1(X0)
% 11.20/2.01      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
% 11.20/2.01      | k2_funct_1(X0) = X1
% 11.20/2.01      | k1_relat_1(X0) != k2_relat_1(X1) ),
% 11.20/2.01      inference(cnf_transformation,[],[f81]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_1088,plain,
% 11.20/2.01      ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 11.20/2.01      | k2_funct_1(X1) = X0
% 11.20/2.01      | k1_relat_1(X1) != k2_relat_1(X0)
% 11.20/2.01      | v1_funct_1(X1) != iProver_top
% 11.20/2.01      | v1_funct_1(X0) != iProver_top
% 11.20/2.01      | v1_relat_1(X1) != iProver_top
% 11.20/2.01      | v1_relat_1(X0) != iProver_top
% 11.20/2.01      | v2_funct_1(X1) != iProver_top ),
% 11.20/2.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_5191,plain,
% 11.20/2.01      ( k2_funct_1(k2_funct_1(sK3)) = sK3
% 11.20/2.01      | k1_relat_1(k2_funct_1(sK3)) != k2_relat_1(sK3)
% 11.20/2.01      | k6_partfun1(k2_relat_1(k2_funct_1(sK3))) != k6_partfun1(sK1)
% 11.20/2.01      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 11.20/2.01      | v1_funct_1(sK3) != iProver_top
% 11.20/2.01      | v1_relat_1(k2_funct_1(sK3)) != iProver_top
% 11.20/2.01      | v1_relat_1(sK3) != iProver_top
% 11.20/2.01      | v2_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 11.20/2.01      inference(superposition,[status(thm)],[c_5185,c_1088]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_1074,plain,
% 11.20/2.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 11.20/2.01      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_8,plain,
% 11.20/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.20/2.01      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 11.20/2.01      inference(cnf_transformation,[],[f50]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_1086,plain,
% 11.20/2.01      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 11.20/2.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.20/2.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_1990,plain,
% 11.20/2.01      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 11.20/2.01      inference(superposition,[status(thm)],[c_1074,c_1086]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_1993,plain,
% 11.20/2.01      ( k2_relat_1(sK3) = sK0 ),
% 11.20/2.01      inference(light_normalisation,[status(thm)],[c_1990,c_1765]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_5192,plain,
% 11.20/2.01      ( k2_funct_1(k2_funct_1(sK3)) = sK3
% 11.20/2.01      | k1_relat_1(k2_funct_1(sK3)) != sK0
% 11.20/2.01      | k6_partfun1(k2_relat_1(k2_funct_1(sK3))) != k6_partfun1(sK1)
% 11.20/2.01      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 11.20/2.01      | v1_funct_1(sK3) != iProver_top
% 11.20/2.01      | v1_relat_1(k2_funct_1(sK3)) != iProver_top
% 11.20/2.01      | v1_relat_1(sK3) != iProver_top
% 11.20/2.01      | v2_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 11.20/2.01      inference(light_normalisation,[status(thm)],[c_5191,c_1993]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_25,negated_conjecture,
% 11.20/2.01      ( v2_funct_1(sK2) ),
% 11.20/2.01      inference(cnf_transformation,[],[f73]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_7,plain,
% 11.20/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.20/2.01      | v1_relat_1(X0) ),
% 11.20/2.01      inference(cnf_transformation,[],[f49]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_1214,plain,
% 11.20/2.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.20/2.01      | v1_relat_1(sK3) ),
% 11.20/2.01      inference(instantiation,[status(thm)],[c_7]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_1573,plain,
% 11.20/2.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 11.20/2.01      | v1_relat_1(sK3) ),
% 11.20/2.01      inference(instantiation,[status(thm)],[c_1214]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_1684,plain,
% 11.20/2.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 11.20/2.01      | v1_relat_1(sK2) ),
% 11.20/2.01      inference(instantiation,[status(thm)],[c_7]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_1071,plain,
% 11.20/2.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 11.20/2.01      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_14,plain,
% 11.20/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.20/2.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 11.20/2.01      | ~ v1_funct_1(X0)
% 11.20/2.01      | ~ v1_funct_1(X3)
% 11.20/2.01      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 11.20/2.01      inference(cnf_transformation,[],[f56]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_1082,plain,
% 11.20/2.01      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 11.20/2.01      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 11.20/2.01      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.20/2.01      | v1_funct_1(X5) != iProver_top
% 11.20/2.01      | v1_funct_1(X4) != iProver_top ),
% 11.20/2.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_2775,plain,
% 11.20/2.01      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 11.20/2.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.20/2.01      | v1_funct_1(X2) != iProver_top
% 11.20/2.01      | v1_funct_1(sK3) != iProver_top ),
% 11.20/2.01      inference(superposition,[status(thm)],[c_1074,c_1082]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_2787,plain,
% 11.20/2.01      ( v1_funct_1(X2) != iProver_top
% 11.20/2.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.20/2.01      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 11.20/2.01      inference(global_propositional_subsumption,
% 11.20/2.01                [status(thm)],
% 11.20/2.01                [c_2775,c_37]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_2788,plain,
% 11.20/2.01      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 11.20/2.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.20/2.01      | v1_funct_1(X2) != iProver_top ),
% 11.20/2.01      inference(renaming,[status(thm)],[c_2787]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_2795,plain,
% 11.20/2.01      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 11.20/2.01      | v1_funct_1(sK2) != iProver_top ),
% 11.20/2.01      inference(superposition,[status(thm)],[c_1071,c_2788]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_2796,plain,
% 11.20/2.01      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 11.20/2.01      | v1_funct_1(sK2) != iProver_top ),
% 11.20/2.01      inference(light_normalisation,[status(thm)],[c_2795,c_1758]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_3532,plain,
% 11.20/2.01      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 11.20/2.01      inference(global_propositional_subsumption,
% 11.20/2.01                [status(thm)],
% 11.20/2.01                [c_2796,c_34]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_4044,plain,
% 11.20/2.01      ( k2_funct_1(sK3) = sK2
% 11.20/2.01      | k1_relat_1(sK3) != k2_relat_1(sK2)
% 11.20/2.01      | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
% 11.20/2.01      | v1_funct_1(sK3) != iProver_top
% 11.20/2.01      | v1_funct_1(sK2) != iProver_top
% 11.20/2.01      | v1_relat_1(sK3) != iProver_top
% 11.20/2.01      | v1_relat_1(sK2) != iProver_top
% 11.20/2.01      | v2_funct_1(sK3) != iProver_top ),
% 11.20/2.01      inference(superposition,[status(thm)],[c_3532,c_1088]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_1991,plain,
% 11.20/2.01      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 11.20/2.01      inference(superposition,[status(thm)],[c_1071,c_1086]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_1992,plain,
% 11.20/2.01      ( k2_relat_1(sK2) = sK1 ),
% 11.20/2.01      inference(light_normalisation,[status(thm)],[c_1991,c_27]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_4045,plain,
% 11.20/2.01      ( k2_funct_1(sK3) = sK2
% 11.20/2.01      | k1_relat_1(sK3) != sK1
% 11.20/2.01      | k6_partfun1(sK0) != k6_partfun1(sK0)
% 11.20/2.01      | v1_funct_1(sK3) != iProver_top
% 11.20/2.01      | v1_funct_1(sK2) != iProver_top
% 11.20/2.01      | v1_relat_1(sK3) != iProver_top
% 11.20/2.01      | v1_relat_1(sK2) != iProver_top
% 11.20/2.01      | v2_funct_1(sK3) != iProver_top ),
% 11.20/2.01      inference(light_normalisation,[status(thm)],[c_4044,c_1992,c_1993]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_4046,plain,
% 11.20/2.01      ( k2_funct_1(sK3) = sK2
% 11.20/2.01      | k1_relat_1(sK3) != sK1
% 11.20/2.01      | v1_funct_1(sK3) != iProver_top
% 11.20/2.01      | v1_funct_1(sK2) != iProver_top
% 11.20/2.01      | v1_relat_1(sK3) != iProver_top
% 11.20/2.01      | v1_relat_1(sK2) != iProver_top
% 11.20/2.01      | v2_funct_1(sK3) != iProver_top ),
% 11.20/2.01      inference(equality_resolution_simp,[status(thm)],[c_4045]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_1574,plain,
% 11.20/2.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 11.20/2.01      | v1_relat_1(sK3) = iProver_top ),
% 11.20/2.01      inference(predicate_to_equality,[status(thm)],[c_1573]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_1685,plain,
% 11.20/2.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 11.20/2.01      | v1_relat_1(sK2) = iProver_top ),
% 11.20/2.01      inference(predicate_to_equality,[status(thm)],[c_1684]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_5123,plain,
% 11.20/2.01      ( k1_relat_1(sK3) != sK1 | k2_funct_1(sK3) = sK2 ),
% 11.20/2.01      inference(global_propositional_subsumption,
% 11.20/2.01                [status(thm)],
% 11.20/2.01                [c_4046,c_34,c_36,c_37,c_38,c_39,c_24,c_639,c_1173,
% 11.20/2.01                 c_1574,c_1685,c_4710,c_4861]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_5124,plain,
% 11.20/2.01      ( k2_funct_1(sK3) = sK2 | k1_relat_1(sK3) != sK1 ),
% 11.20/2.01      inference(renaming,[status(thm)],[c_5123]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_4937,plain,
% 11.20/2.01      ( v2_funct_1(sK3) = iProver_top ),
% 11.20/2.01      inference(global_propositional_subsumption,
% 11.20/2.01                [status(thm)],
% 11.20/2.01                [c_4861,c_37,c_38,c_39,c_24,c_639,c_1173,c_4710]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_1072,plain,
% 11.20/2.01      ( v1_funct_1(sK3) = iProver_top ),
% 11.20/2.01      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_4,plain,
% 11.20/2.01      ( ~ v1_funct_1(X0)
% 11.20/2.01      | ~ v1_relat_1(X0)
% 11.20/2.01      | ~ v2_funct_1(X0)
% 11.20/2.01      | k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ),
% 11.20/2.01      inference(cnf_transformation,[],[f47]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_1090,plain,
% 11.20/2.01      ( k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
% 11.20/2.01      | v1_funct_1(X0) != iProver_top
% 11.20/2.01      | v1_relat_1(X0) != iProver_top
% 11.20/2.01      | v2_funct_1(X0) != iProver_top ),
% 11.20/2.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_2276,plain,
% 11.20/2.01      ( k2_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) = k1_relat_1(sK3)
% 11.20/2.01      | v1_relat_1(sK3) != iProver_top
% 11.20/2.01      | v2_funct_1(sK3) != iProver_top ),
% 11.20/2.01      inference(superposition,[status(thm)],[c_1072,c_1090]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_2607,plain,
% 11.20/2.01      ( k2_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) = k1_relat_1(sK3)
% 11.20/2.01      | v2_funct_1(sK3) != iProver_top ),
% 11.20/2.01      inference(global_propositional_subsumption,
% 11.20/2.01                [status(thm)],
% 11.20/2.01                [c_2276,c_39,c_1574]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_4941,plain,
% 11.20/2.01      ( k2_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) = k1_relat_1(sK3) ),
% 11.20/2.01      inference(superposition,[status(thm)],[c_4937,c_2607]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_5188,plain,
% 11.20/2.01      ( k2_relat_1(k6_partfun1(sK1)) = k1_relat_1(sK3) ),
% 11.20/2.01      inference(demodulation,[status(thm)],[c_5185,c_4941]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_0,plain,
% 11.20/2.01      ( k2_relat_1(k6_partfun1(X0)) = X0 ),
% 11.20/2.01      inference(cnf_transformation,[],[f77]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_5189,plain,
% 11.20/2.01      ( k1_relat_1(sK3) = sK1 ),
% 11.20/2.01      inference(demodulation,[status(thm)],[c_5188,c_0]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_5193,plain,
% 11.20/2.01      ( ~ v1_funct_1(k2_funct_1(sK3))
% 11.20/2.01      | ~ v1_funct_1(sK3)
% 11.20/2.01      | ~ v1_relat_1(k2_funct_1(sK3))
% 11.20/2.01      | ~ v1_relat_1(sK3)
% 11.20/2.01      | ~ v2_funct_1(k2_funct_1(sK3))
% 11.20/2.01      | k2_funct_1(k2_funct_1(sK3)) = sK3
% 11.20/2.01      | k1_relat_1(k2_funct_1(sK3)) != sK0
% 11.20/2.01      | k6_partfun1(k2_relat_1(k2_funct_1(sK3))) != k6_partfun1(sK1) ),
% 11.20/2.01      inference(predicate_to_equality_rev,[status(thm)],[c_5192]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_617,plain,
% 11.20/2.01      ( ~ v1_funct_1(X0) | v1_funct_1(X1) | X1 != X0 ),
% 11.20/2.01      theory(equality) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_1351,plain,
% 11.20/2.01      ( v1_funct_1(X0) | ~ v1_funct_1(sK2) | X0 != sK2 ),
% 11.20/2.01      inference(instantiation,[status(thm)],[c_617]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_1430,plain,
% 11.20/2.01      ( v1_funct_1(k2_funct_1(X0))
% 11.20/2.01      | ~ v1_funct_1(sK2)
% 11.20/2.01      | k2_funct_1(X0) != sK2 ),
% 11.20/2.01      inference(instantiation,[status(thm)],[c_1351]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_7858,plain,
% 11.20/2.01      ( v1_funct_1(k2_funct_1(sK3))
% 11.20/2.01      | ~ v1_funct_1(sK2)
% 11.20/2.01      | k2_funct_1(sK3) != sK2 ),
% 11.20/2.01      inference(instantiation,[status(thm)],[c_1430]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_614,plain,
% 11.20/2.01      ( ~ v1_relat_1(X0) | v1_relat_1(X1) | X1 != X0 ),
% 11.20/2.01      theory(equality) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_1737,plain,
% 11.20/2.01      ( v1_relat_1(X0) | ~ v1_relat_1(sK2) | X0 != sK2 ),
% 11.20/2.01      inference(instantiation,[status(thm)],[c_614]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_2256,plain,
% 11.20/2.01      ( v1_relat_1(k2_funct_1(X0))
% 11.20/2.01      | ~ v1_relat_1(sK2)
% 11.20/2.01      | k2_funct_1(X0) != sK2 ),
% 11.20/2.01      inference(instantiation,[status(thm)],[c_1737]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_7856,plain,
% 11.20/2.01      ( v1_relat_1(k2_funct_1(sK3))
% 11.20/2.01      | ~ v1_relat_1(sK2)
% 11.20/2.01      | k2_funct_1(sK3) != sK2 ),
% 11.20/2.01      inference(instantiation,[status(thm)],[c_2256]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_613,plain,
% 11.20/2.01      ( ~ v2_funct_1(X0) | v2_funct_1(X1) | X1 != X0 ),
% 11.20/2.01      theory(equality) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_2108,plain,
% 11.20/2.01      ( v2_funct_1(X0) | ~ v2_funct_1(sK2) | X0 != sK2 ),
% 11.20/2.01      inference(instantiation,[status(thm)],[c_613]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_2527,plain,
% 11.20/2.01      ( v2_funct_1(k2_funct_1(X0))
% 11.20/2.01      | ~ v2_funct_1(sK2)
% 11.20/2.01      | k2_funct_1(X0) != sK2 ),
% 11.20/2.01      inference(instantiation,[status(thm)],[c_2108]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_7855,plain,
% 11.20/2.01      ( v2_funct_1(k2_funct_1(sK3))
% 11.20/2.01      | ~ v2_funct_1(sK2)
% 11.20/2.01      | k2_funct_1(sK3) != sK2 ),
% 11.20/2.01      inference(instantiation,[status(thm)],[c_2527]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_25869,plain,
% 11.20/2.01      ( k6_partfun1(k2_relat_1(k2_funct_1(sK3))) != k6_partfun1(sK1)
% 11.20/2.01      | k1_relat_1(k2_funct_1(sK3)) != sK0
% 11.20/2.01      | k2_funct_1(k2_funct_1(sK3)) = sK3 ),
% 11.20/2.01      inference(global_propositional_subsumption,
% 11.20/2.01                [status(thm)],
% 11.20/2.01                [c_5192,c_33,c_34,c_31,c_36,c_30,c_37,c_38,c_28,c_39,
% 11.20/2.01                 c_25,c_24,c_639,c_1173,c_1573,c_1574,c_1684,c_1685,
% 11.20/2.01                 c_4046,c_4710,c_4861,c_5189,c_5193,c_7858,c_7856,c_7855]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_25870,plain,
% 11.20/2.01      ( k2_funct_1(k2_funct_1(sK3)) = sK3
% 11.20/2.01      | k1_relat_1(k2_funct_1(sK3)) != sK0
% 11.20/2.01      | k6_partfun1(k2_relat_1(k2_funct_1(sK3))) != k6_partfun1(sK1) ),
% 11.20/2.01      inference(renaming,[status(thm)],[c_25869]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_2672,plain,
% 11.20/2.01      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
% 11.20/2.01      | sK1 = k1_xboole_0
% 11.20/2.01      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 11.20/2.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 11.20/2.01      | v1_funct_1(sK2) != iProver_top
% 11.20/2.01      | v2_funct_1(sK2) != iProver_top ),
% 11.20/2.01      inference(superposition,[status(thm)],[c_27,c_1076]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_23,negated_conjecture,
% 11.20/2.01      ( k1_xboole_0 != sK1 ),
% 11.20/2.01      inference(cnf_transformation,[],[f75]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_1137,plain,
% 11.20/2.01      ( ~ v1_funct_2(X0,X1,sK1)
% 11.20/2.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 11.20/2.01      | ~ v1_funct_1(X0)
% 11.20/2.01      | ~ v2_funct_1(X0)
% 11.20/2.01      | k2_relset_1(X1,sK1,X0) != sK1
% 11.20/2.01      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 11.20/2.01      | k1_xboole_0 = sK1 ),
% 11.20/2.01      inference(instantiation,[status(thm)],[c_21]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_1265,plain,
% 11.20/2.01      ( ~ v1_funct_2(sK2,X0,sK1)
% 11.20/2.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
% 11.20/2.01      | ~ v1_funct_1(sK2)
% 11.20/2.01      | ~ v2_funct_1(sK2)
% 11.20/2.01      | k2_relset_1(X0,sK1,sK2) != sK1
% 11.20/2.01      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
% 11.20/2.01      | k1_xboole_0 = sK1 ),
% 11.20/2.01      inference(instantiation,[status(thm)],[c_1137]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_1482,plain,
% 11.20/2.01      ( ~ v1_funct_2(sK2,sK0,sK1)
% 11.20/2.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 11.20/2.01      | ~ v1_funct_1(sK2)
% 11.20/2.01      | ~ v2_funct_1(sK2)
% 11.20/2.01      | k2_relset_1(sK0,sK1,sK2) != sK1
% 11.20/2.01      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
% 11.20/2.01      | k1_xboole_0 = sK1 ),
% 11.20/2.01      inference(instantiation,[status(thm)],[c_1265]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_2679,plain,
% 11.20/2.01      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
% 11.20/2.01      inference(global_propositional_subsumption,
% 11.20/2.01                [status(thm)],
% 11.20/2.01                [c_2672,c_33,c_32,c_31,c_27,c_25,c_23,c_1482]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_1069,plain,
% 11.20/2.01      ( v1_funct_1(sK2) = iProver_top ),
% 11.20/2.01      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_5,plain,
% 11.20/2.01      ( ~ v1_funct_1(X0)
% 11.20/2.01      | ~ v1_relat_1(X0)
% 11.20/2.01      | ~ v2_funct_1(X0)
% 11.20/2.01      | k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ),
% 11.20/2.01      inference(cnf_transformation,[],[f46]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_1089,plain,
% 11.20/2.01      ( k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
% 11.20/2.01      | v1_funct_1(X0) != iProver_top
% 11.20/2.01      | v1_relat_1(X0) != iProver_top
% 11.20/2.01      | v2_funct_1(X0) != iProver_top ),
% 11.20/2.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_2032,plain,
% 11.20/2.01      ( k1_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) = k1_relat_1(sK2)
% 11.20/2.01      | v1_relat_1(sK2) != iProver_top
% 11.20/2.01      | v2_funct_1(sK2) != iProver_top ),
% 11.20/2.01      inference(superposition,[status(thm)],[c_1069,c_1089]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_41,plain,
% 11.20/2.01      ( v2_funct_1(sK2) = iProver_top ),
% 11.20/2.01      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_2228,plain,
% 11.20/2.01      ( k1_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) = k1_relat_1(sK2) ),
% 11.20/2.01      inference(global_propositional_subsumption,
% 11.20/2.01                [status(thm)],
% 11.20/2.01                [c_2032,c_36,c_41,c_1685]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_2682,plain,
% 11.20/2.01      ( k1_relat_1(k6_partfun1(sK0)) = k1_relat_1(sK2) ),
% 11.20/2.01      inference(demodulation,[status(thm)],[c_2679,c_2228]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_1,plain,
% 11.20/2.01      ( k1_relat_1(k6_partfun1(X0)) = X0 ),
% 11.20/2.01      inference(cnf_transformation,[],[f78]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_2683,plain,
% 11.20/2.01      ( k1_relat_1(sK2) = sK0 ),
% 11.20/2.01      inference(demodulation,[status(thm)],[c_2682,c_1]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_5221,plain,
% 11.20/2.01      ( k2_funct_1(sK3) = sK2 | sK1 != sK1 ),
% 11.20/2.01      inference(demodulation,[status(thm)],[c_5189,c_5124]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_5319,plain,
% 11.20/2.01      ( k2_funct_1(sK3) = sK2 ),
% 11.20/2.01      inference(equality_resolution_simp,[status(thm)],[c_5221]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_25871,plain,
% 11.20/2.01      ( k2_funct_1(sK2) = sK3
% 11.20/2.01      | k6_partfun1(sK1) != k6_partfun1(sK1)
% 11.20/2.01      | sK0 != sK0 ),
% 11.20/2.01      inference(light_normalisation,
% 11.20/2.01                [status(thm)],
% 11.20/2.01                [c_25870,c_1992,c_2683,c_5319]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_25872,plain,
% 11.20/2.01      ( k2_funct_1(sK2) = sK3 ),
% 11.20/2.01      inference(equality_resolution_simp,[status(thm)],[c_25871]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(c_22,negated_conjecture,
% 11.20/2.01      ( k2_funct_1(sK2) != sK3 ),
% 11.20/2.01      inference(cnf_transformation,[],[f76]) ).
% 11.20/2.01  
% 11.20/2.01  cnf(contradiction,plain,
% 11.20/2.01      ( $false ),
% 11.20/2.01      inference(minisat,[status(thm)],[c_25872,c_22]) ).
% 11.20/2.01  
% 11.20/2.01  
% 11.20/2.01  % SZS output end CNFRefutation for theBenchmark.p
% 11.20/2.01  
% 11.20/2.01  ------                               Statistics
% 11.20/2.01  
% 11.20/2.01  ------ General
% 11.20/2.01  
% 11.20/2.01  abstr_ref_over_cycles:                  0
% 11.20/2.01  abstr_ref_under_cycles:                 0
% 11.20/2.01  gc_basic_clause_elim:                   0
% 11.20/2.01  forced_gc_time:                         0
% 11.20/2.01  parsing_time:                           0.01
% 11.20/2.01  unif_index_cands_time:                  0.
% 11.20/2.01  unif_index_add_time:                    0.
% 11.20/2.01  orderings_time:                         0.
% 11.20/2.01  out_proof_time:                         0.017
% 11.20/2.01  total_time:                             1.116
% 11.20/2.01  num_of_symbols:                         51
% 11.20/2.01  num_of_terms:                           42061
% 11.20/2.01  
% 11.20/2.01  ------ Preprocessing
% 11.20/2.01  
% 11.20/2.01  num_of_splits:                          0
% 11.20/2.01  num_of_split_atoms:                     0
% 11.20/2.01  num_of_reused_defs:                     0
% 11.20/2.01  num_eq_ax_congr_red:                    0
% 11.20/2.01  num_of_sem_filtered_clauses:            1
% 11.20/2.01  num_of_subtypes:                        0
% 11.20/2.01  monotx_restored_types:                  0
% 11.20/2.01  sat_num_of_epr_types:                   0
% 11.20/2.01  sat_num_of_non_cyclic_types:            0
% 11.20/2.01  sat_guarded_non_collapsed_types:        0
% 11.20/2.01  num_pure_diseq_elim:                    0
% 11.20/2.01  simp_replaced_by:                       0
% 11.20/2.01  res_preprocessed:                       166
% 11.20/2.01  prep_upred:                             0
% 11.20/2.01  prep_unflattend:                        12
% 11.20/2.01  smt_new_axioms:                         0
% 11.20/2.01  pred_elim_cands:                        5
% 11.20/2.01  pred_elim:                              1
% 11.20/2.01  pred_elim_cl:                           1
% 11.20/2.01  pred_elim_cycles:                       3
% 11.20/2.01  merged_defs:                            0
% 11.20/2.01  merged_defs_ncl:                        0
% 11.20/2.01  bin_hyper_res:                          0
% 11.20/2.01  prep_cycles:                            4
% 11.20/2.01  pred_elim_time:                         0.005
% 11.20/2.01  splitting_time:                         0.
% 11.20/2.01  sem_filter_time:                        0.
% 11.20/2.01  monotx_time:                            0.001
% 11.20/2.01  subtype_inf_time:                       0.
% 11.20/2.01  
% 11.20/2.01  ------ Problem properties
% 11.20/2.01  
% 11.20/2.01  clauses:                                33
% 11.20/2.01  conjectures:                            11
% 11.20/2.01  epr:                                    7
% 11.20/2.01  horn:                                   29
% 11.20/2.01  ground:                                 12
% 11.20/2.01  unary:                                  16
% 11.20/2.01  binary:                                 3
% 11.20/2.01  lits:                                   121
% 11.20/2.01  lits_eq:                                30
% 11.20/2.01  fd_pure:                                0
% 11.20/2.01  fd_pseudo:                              0
% 11.20/2.01  fd_cond:                                4
% 11.20/2.01  fd_pseudo_cond:                         1
% 11.20/2.01  ac_symbols:                             0
% 11.20/2.01  
% 11.20/2.01  ------ Propositional Solver
% 11.20/2.01  
% 11.20/2.01  prop_solver_calls:                      35
% 11.20/2.01  prop_fast_solver_calls:                 2969
% 11.20/2.01  smt_solver_calls:                       0
% 11.20/2.01  smt_fast_solver_calls:                  0
% 11.20/2.01  prop_num_of_clauses:                    14592
% 11.20/2.01  prop_preprocess_simplified:             21255
% 11.20/2.01  prop_fo_subsumed:                       626
% 11.20/2.01  prop_solver_time:                       0.
% 11.20/2.01  smt_solver_time:                        0.
% 11.20/2.01  smt_fast_solver_time:                   0.
% 11.20/2.01  prop_fast_solver_time:                  0.
% 11.20/2.01  prop_unsat_core_time:                   0.002
% 11.20/2.01  
% 11.20/2.01  ------ QBF
% 11.20/2.01  
% 11.20/2.01  qbf_q_res:                              0
% 11.20/2.01  qbf_num_tautologies:                    0
% 11.20/2.01  qbf_prep_cycles:                        0
% 11.20/2.01  
% 11.20/2.01  ------ BMC1
% 11.20/2.01  
% 11.20/2.01  bmc1_current_bound:                     -1
% 11.20/2.01  bmc1_last_solved_bound:                 -1
% 11.20/2.01  bmc1_unsat_core_size:                   -1
% 11.20/2.01  bmc1_unsat_core_parents_size:           -1
% 11.20/2.01  bmc1_merge_next_fun:                    0
% 11.20/2.01  bmc1_unsat_core_clauses_time:           0.
% 11.20/2.01  
% 11.20/2.01  ------ Instantiation
% 11.20/2.01  
% 11.20/2.01  inst_num_of_clauses:                    3954
% 11.20/2.01  inst_num_in_passive:                    554
% 11.20/2.01  inst_num_in_active:                     1675
% 11.20/2.01  inst_num_in_unprocessed:                1725
% 11.20/2.01  inst_num_of_loops:                      1860
% 11.20/2.01  inst_num_of_learning_restarts:          0
% 11.20/2.01  inst_num_moves_active_passive:          181
% 11.20/2.01  inst_lit_activity:                      0
% 11.20/2.01  inst_lit_activity_moves:                3
% 11.20/2.01  inst_num_tautologies:                   0
% 11.20/2.01  inst_num_prop_implied:                  0
% 11.20/2.01  inst_num_existing_simplified:           0
% 11.20/2.01  inst_num_eq_res_simplified:             0
% 11.20/2.01  inst_num_child_elim:                    0
% 11.20/2.01  inst_num_of_dismatching_blockings:      1086
% 11.20/2.01  inst_num_of_non_proper_insts:           3047
% 11.20/2.01  inst_num_of_duplicates:                 0
% 11.20/2.01  inst_inst_num_from_inst_to_res:         0
% 11.20/2.01  inst_dismatching_checking_time:         0.
% 11.20/2.01  
% 11.20/2.01  ------ Resolution
% 11.20/2.01  
% 11.20/2.01  res_num_of_clauses:                     0
% 11.20/2.01  res_num_in_passive:                     0
% 11.20/2.01  res_num_in_active:                      0
% 11.20/2.01  res_num_of_loops:                       170
% 11.20/2.01  res_forward_subset_subsumed:            259
% 11.20/2.01  res_backward_subset_subsumed:           0
% 11.20/2.01  res_forward_subsumed:                   0
% 11.20/2.01  res_backward_subsumed:                  0
% 11.20/2.01  res_forward_subsumption_resolution:     2
% 11.20/2.01  res_backward_subsumption_resolution:    0
% 11.20/2.01  res_clause_to_clause_subsumption:       2653
% 11.20/2.01  res_orphan_elimination:                 0
% 11.20/2.01  res_tautology_del:                      221
% 11.20/2.01  res_num_eq_res_simplified:              1
% 11.20/2.01  res_num_sel_changes:                    0
% 11.20/2.01  res_moves_from_active_to_pass:          0
% 11.20/2.01  
% 11.20/2.01  ------ Superposition
% 11.20/2.01  
% 11.20/2.01  sup_time_total:                         0.
% 11.20/2.01  sup_time_generating:                    0.
% 11.20/2.01  sup_time_sim_full:                      0.
% 11.20/2.01  sup_time_sim_immed:                     0.
% 11.20/2.01  
% 11.20/2.01  sup_num_of_clauses:                     1266
% 11.20/2.01  sup_num_in_active:                      355
% 11.20/2.01  sup_num_in_passive:                     911
% 11.20/2.01  sup_num_of_loops:                       371
% 11.20/2.01  sup_fw_superposition:                   479
% 11.20/2.01  sup_bw_superposition:                   907
% 11.20/2.01  sup_immediate_simplified:               392
% 11.20/2.01  sup_given_eliminated:                   0
% 11.20/2.01  comparisons_done:                       0
% 11.20/2.01  comparisons_avoided:                    4
% 11.20/2.01  
% 11.20/2.01  ------ Simplifications
% 11.20/2.01  
% 11.20/2.01  
% 11.20/2.01  sim_fw_subset_subsumed:                 26
% 11.20/2.01  sim_bw_subset_subsumed:                 43
% 11.20/2.01  sim_fw_subsumed:                        22
% 11.20/2.01  sim_bw_subsumed:                        9
% 11.20/2.01  sim_fw_subsumption_res:                 0
% 11.20/2.01  sim_bw_subsumption_res:                 0
% 11.20/2.01  sim_tautology_del:                      0
% 11.20/2.01  sim_eq_tautology_del:                   23
% 11.20/2.01  sim_eq_res_simp:                        3
% 11.20/2.01  sim_fw_demodulated:                     35
% 11.20/2.01  sim_bw_demodulated:                     7
% 11.20/2.01  sim_light_normalised:                   364
% 11.20/2.01  sim_joinable_taut:                      0
% 11.20/2.01  sim_joinable_simp:                      0
% 11.20/2.01  sim_ac_normalised:                      0
% 11.20/2.01  sim_smt_subsumption:                    0
% 11.20/2.01  
%------------------------------------------------------------------------------
